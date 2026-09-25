#!/usr/bin/env python3
"""
OpenRGB Keeper (persistent lighting + battery management + device replug recovery)

  1. Start OpenRGB if needed (--startminimized --profile 123 --server)
  2. Capture profile state (mode + colors)
  3. Simple main loop (every ~5s):
     - Watch device presence via WMI events (daemon thread)
     - On physical removal: wait for return, fast-restart OpenRGB
     - On device event: re-apply state via SDK directly
     - Periodic state push (every 30s)
     - Battery check (every 300s): below 35% off, above 50% on (hysteresis)
     - Charging status fast refresh (every 5s) for tray red dot
     - SDK heartbeat (every 120s)
  4. Battery info written to battery.txt for OpenRGB tray icon / status bar
"""

import os
import sys
import faulthandler
import time
import logging
import subprocess
import socket
import ctypes
import ctypes.wintypes as wintypes
import threading
import configparser
from pathlib import Path

from openrgb import OpenRGBClient
from openrgb.utils import RGBColor, LocalProfile

import libusb_package
import usb.core
import usb.util

# Explicitly get the libusb1 backend — without this, pythonw running via
# Scheduled Task sometimes fails with "No backend available"
_USB_BACKEND = libusb_package.get_libusb1_backend()

# ── Configuration ─────────────────────────────────────
OPENRGB_HOST = "localhost"
OPENRGB_PORT = 6742
OPENRGB_EXE = r"C:\Program Files\OpenRGB\OpenRGB.exe"
OPENRGB_ARGS = "--startminimized --profile 123 --server"

HIGH_FREQ_INTERVAL = 30
LOW_FREQ_INTERVAL = 120       # fallback push every 2 minutes
RECONNECT_DELAY = 10
STATE_CAPTURE_DELAY = 20
STABILITY_CHECK_INTERVAL = 10
STABILITY_CHECK_COUNT = 3
OPENRGB_START_DELAY = 30
MAX_START_RETRIES = 6

RAZER_VID = 0x1532
# Known Razer Naga Pro PIDs (receiver enumerates as different PIDs)
RAZER_PIDS = (0x0090, 0x008F, 0x008E, 0x0091)
BATTERY_CHECK_INTERVAL = 300
CHARGE_CHECK_INTERVAL = 5
BATTERY_LOW_THRESHOLD = 35
BATTERY_HIGH_THRESHOLD = 50

# Battery info file path - read by OpenRGB tray icon to display battery %
BATTERY_FILE = r"C:\Users\Luther\AppData\Roaming\OpenRGB\keeper\battery.txt"


def write_battery_file(pct, charging):
    """Write battery info to file for OpenRGB tray icon to read.
    Format: "pct charging" (e.g. "53 1" means 53% charging, "85 0" means 85% not charging)
    """
    try:
        with open(BATTERY_FILE, "w") as f:
            f.write("%d %d" % (pct, 1 if charging else 0))
    except Exception:
        pass



# Devices known to NOT support DeviceSaveMode() (OpenRGB base class is a no-op)
# PowerPlay/Candy: RGBController_LogitechGPowerPlay does not override DeviceSaveMode(), @save :x:
# Razer Naga Pro: RazerController does not implement DeviceSaveMode()
UNSUPPORTED_SAVE_KEYWORDS = ["candy", "powerplay", "razer naga pro"]

KILL_RETRY_MAX = 5
KILL_VERIFY_INTERVAL = 2
KILL_COOLDOWN = 60  # seconds between force-kills (WinRing0 protection)
last_force_kill_ts = 0.0

# ── Logging ──────────────────────────────────────────
LOG_DIR  = Path(os.environ.get("APPDATA", ".")) / "OpenRGB" / "keeper"
LOG_FILE = LOG_DIR / "keeper.log"

LOG_DIR.mkdir(parents=True, exist_ok=True)
from logging.handlers import RotatingFileHandler
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        RotatingFileHandler(str(LOG_FILE), maxBytes=5*1024*1024, backupCount=3, encoding="utf-8"),
    ],
)
if sys.stdout is not None:
    log_root = logging.getLogger()
    log_root.addHandler(logging.StreamHandler(sys.stdout))
log = logging.getLogger("OpenRGBKeeper")

# Enable faulthandler to log segfaults / crashes to a separate file.
# NOTE: opening the main keeper.log here would hold a handle that blocks
# RotatingFileHandler rollover (os.rename fails on Windows).
_fault_log = open(str(LOG_FILE.with_name("keeper_fault.log")), "a", encoding="utf-8")
faulthandler.enable(file=_fault_log)


# ══════════════════════════════════════════════════════
# USB Device Change Detection (WMI polling — no ctypes message pump)
# ══════════════════════════════════════════════════════

# Signal event: set when a device change is detected
device_wake_event = threading.Event()

# When True, OpenRGB's internal USB handles are stale and must be refreshed via restart
need_openrgb_restart = False
saw_device_removal = False

# Target device to monitor for physical presence
# Candy: Logitech companion chip (VID_046D&PID_C53A)
# Razer Naga Pro receiver (VID_1532&PID_0090) is NOT monitored because
# the USB receiver stays online even when the mouse is powered off,
# so polling it would waste CPU for no detection benefit.
MONITORED_DEVICES = [
    "VID_046D&PID_C53A",  # Candy mousepad only
]


def check_device_present(vid_pid):
    """Check if a device is currently present using Get-CimInstance.
    Returns True if present, False if not."""
    try:
        result = subprocess.run(
            ["powershell", "-NoProfile", "-NonInteractive", "-Command",
             "if (Get-CimInstance -ClassName Win32_PnPEntity -Filter "
             "\"DeviceId LIKE '%%%s%%'\" -ErrorAction SilentlyContinue) "
             "{ 'present' } else { 'absent' }" % vid_pid],
            capture_output=True, text=True, timeout=8,
            creationflags=0x08000000  # CREATE_NO_WINDOW
        )
        return "present" in result.stdout.lower()
    except Exception as e:
        log.warning("Device check failed for %s: %s" % (vid_pid, e))
        return True  # Assume present to avoid false restarts


# Persistent PowerShell process that subscribes to WMI device-change events.
# Replaces the old every-3s PowerShell polling (one process, idle until an event).
_WMI_WATCHER_PS = (
    "$watcher = New-Object System.Management.ManagementEventWatcher; "
    "$watcher.Query = New-Object System.Management.WqlEventQuery('SELECT * FROM Win32_DeviceChangeEvent'); "
    "$watcher.Start(); "
    "while ($true) { $null = $watcher.WaitForNextEvent(); "
    "[Console]::WriteLine('change'); [Console]::Out.Flush() }"
)


def start_device_listener():
    """Start a daemon thread that watches USB device presence via WMI events."""

    def listener_thread():
        global need_openrgb_restart, saw_device_removal
        log.info("Device presence poller started (WMI event subscription)")

        # Track presence state for each device
        presence = {}
        for vid_pid in MONITORED_DEVICES:
            presence[vid_pid] = check_device_present(vid_pid)
            log.info("  %s: %s" % (vid_pid, "present" if presence[vid_pid] else "absent"))

        proc = None
        heartbeat_counter = 0
        while True:
            try:
                if proc is None or proc.poll() is not None:
                    log.info("Starting WMI device watcher...")
                    proc = subprocess.Popen(
                        ["powershell", "-NoProfile", "-NonInteractive", "-Command", _WMI_WATCHER_PS],
                        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                        creationflags=0x08000000  # CREATE_NO_WINDOW
                    )
                line = proc.stdout.readline()
                if not line:
                    # Watcher exited without output — wait and restart
                    time.sleep(2)
                    continue

                # A device change event fired — re-check monitored devices
                for vid_pid in MONITORED_DEVICES:
                    is_present = check_device_present(vid_pid)
                    was_present = presence[vid_pid]

                    if was_present and not is_present:
                        # Device was removed
                        need_openrgb_restart = True
                        saw_device_removal = True
                        log.info("*** %s REMOVED: OpenRGB restart needed ***" % vid_pid)
                        device_wake_event.set()

                    elif not was_present and is_present:
                        # Device came back
                        log.info("*** %s ARRIVED ***" % vid_pid)
                        device_wake_event.set()

                    elif not is_present and saw_device_removal:
                        # Still absent
                        log.info("%s still absent, waiting for return..." % vid_pid)

                    presence[vid_pid] = is_present

                heartbeat_counter += 1
                if heartbeat_counter % 60 == 0:
                    states_str = ", ".join("%s:%s" % (v, "present" if p else "absent")
                                           for v, p in presence.items())
                    log.info("Poller heartbeat: %s (check #%d)" % (states_str, heartbeat_counter))

            except Exception as e:
                log.warning("Device poll error: %s" % e)
                time.sleep(1)

    t = threading.Thread(target=listener_thread, daemon=True)
    t.start()
    return t


# ══════════════════════════════════════════════════════
# OpenRGB Management
# ══════════════════════════════════════════════════════

def is_process_elevated():
    """Check if current process is running with admin privileges."""
    try:
        return bool(ctypes.windll.shell32.IsUserAnAdmin())
    except:
        return False


def supports_save_mode(dev_name):
    """Check if device is known to support DeviceSaveMode().
    Returns False for devices where OpenRGB's controller has an empty no-op implementation."""
    name_lower = dev_name.lower()
    for keyword in UNSUPPORTED_SAVE_KEYWORDS:
        if keyword in name_lower:
            return False
    return True


def save_mode_safe(devs, skip_index=-1):
    """Call save_mode() on devices that support it, with logging."""
    for i, dev in enumerate(devs):
        if i == skip_index:
            continue
        if not supports_save_mode(dev.name):
            log.info("  Device %d [%s]: save_mode() SKIPPED (not supported by controller)" % (i, dev.name))
            continue
        try:
            dev.save_mode()
            log.info("  Device %d [%s]: save_mode() OK" % (i, dev.name))
        except Exception as e:
            log.warning("  Device %d [%s]: save_mode() failed: %s" % (i, dev.name, e))


def is_openrgb_running():
    try:
        result = subprocess.run(
            ["tasklist", "/FI", "IMAGENAME eq OpenRGB.exe"],
            capture_output=True, text=True, timeout=10,
            creationflags=0x08000000  # CREATE_NO_WINDOW
        )
        return "OpenRGB.exe" in result.stdout
    except Exception:
        return False


def is_sdk_responding():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        s.settimeout(3)
        s.connect((OPENRGB_HOST, OPENRGB_PORT))
        s.close()
        return True
    except Exception:
        return False


def kill_openrgb():
    """Kill all OpenRGB processes with verification loop.
    Cooldown: skip repeated force-kills within KILL_COOLDOWN seconds to
    protect the WinRing0 driver (force-kill can wedge it).
    Returns True if all processes are dead, False if kill failed."""
    global last_force_kill_ts
    if not is_openrgb_running():
        return True
    now = time.time()
    if now - last_force_kill_ts < KILL_COOLDOWN:
        log.warning("Force-kill cooldown active (%ds left); waiting for graceful exit..." %
                    int(KILL_COOLDOWN - (now - last_force_kill_ts)))
        for _ in range(int(KILL_COOLDOWN / 3)):
            time.sleep(3)
            if not is_openrgb_running():
                log.info("OpenRGB exited during cooldown wait (no force-kill needed)")
                return True
        if not is_openrgb_running():
            return True
        log.warning("Cooldown wait expired, force-killing anyway")
    last_force_kill_ts = time.time()
    log.info("Killing OpenRGB processes...")

    for attempt in range(KILL_RETRY_MAX):
        # Use /F (force) /T (kill child processes too)
        result = subprocess.run(
            ["taskkill", "/F", "/T", "/IM", "OpenRGB.exe"],
            capture_output=True, text=True, timeout=10,
            creationflags=0x08000000  # CREATE_NO_WINDOW
        )

        if result.returncode == 0:
            log.info("taskkill succeeded: %s" % result.stdout.strip())
        elif "not found" in result.stderr.lower() or "no tasks" in result.stderr.lower():
            log.info("No OpenRGB process found")
            return True
        else:
            log.info("taskkill rc=%d: %s" % (result.returncode, result.stderr.strip()))

        # Wait and verify
        time.sleep(KILL_VERIFY_INTERVAL)
        if not is_openrgb_running():
            log.info("All OpenRGB processes killed (attempt %d)" % (attempt + 1))
            return True

        log.warning("OpenRGB still running after attempt %d/%d" % (attempt + 1, KILL_RETRY_MAX))

        # If we're not elevated, try elevated taskkill via PowerShell (waits for completion)
        if not is_process_elevated():
            log.info("Not elevated, trying elevated taskkill via PowerShell...")
            try:
                subprocess.run(
                    ["powershell", "-NoProfile", "-Command",
                     "Start-Process -Verb RunAs -Wait -FilePath taskkill.exe -ArgumentList '/F /T /IM OpenRGB.exe'"],
                    capture_output=True, text=True, timeout=30,
                    creationflags=0x08000000  # CREATE_NO_WINDOW
                )
                time.sleep(KILL_VERIFY_INTERVAL)
                if not is_openrgb_running():
                    log.info("OpenRGB killed via elevated taskkill")
                    return True
            except Exception as e:
                log.warning("Elevated taskkill failed: %s" % e)

        time.sleep(3)

    log.error("Failed to kill OpenRGB after %d attempts" % KILL_RETRY_MAX)
    return False


def start_openrgb():
    """Start OpenRGB, ensuring no duplicate processes exist first.
    Returns True if OpenRGB was started (or already running with SDK responsive)."""
    # Kill any existing instances first — verify they're actually dead
    if is_openrgb_running():
        if not kill_openrgb():
            log.error("Cannot kill existing OpenRGB process, aborting start to avoid duplicates")
            return False

    # Double-check: verify no OpenRGB process remains
    if is_openrgb_running():
        log.error("OpenRGB still running after kill, aborting start to avoid duplicates")
        return False

    log.info("Starting OpenRGB: %s %s" % (OPENRGB_EXE, OPENRGB_ARGS))
    try:
        if is_process_elevated():
            # Already elevated — use subprocess directly (no UAC prompt)
            subprocess.Popen(
                [OPENRGB_EXE] + OPENRGB_ARGS.split(),
                creationflags=subprocess.CREATE_NO_WINDOW
            )
            log.info("OpenRGB started via subprocess (elevated)")
        else:
            # Need elevation for hardware access
            ctypes.windll.shell32.ShellExecuteW(
                None, "runas", OPENRGB_EXE, OPENRGB_ARGS, None, 0
            )
            log.info("OpenRGB started via ShellExecuteW (runas)")
    except Exception as e:
        log.error("Failed to start OpenRGB: %s" % e)
        return False
    return True


def ensure_openrgb_running():
    if is_openrgb_running():
        if is_sdk_responding():
            log.info("OpenRGB is running, SDK is responsive")
            return True
        else:
            log.info("OpenRGB is running but SDK not ready, waiting...")
            for i in range(MAX_START_RETRIES):
                time.sleep(10)
                if is_sdk_responding():
                    log.info("SDK is ready")
                    return True
            log.error("SDK wait timeout, killing and restarting OpenRGB...")
            kill_openrgb()
            start_openrgb()
            time.sleep(OPENRGB_START_DELAY)
            for i in range(MAX_START_RETRIES):
                if is_sdk_responding():
                    log.info("SDK is ready after restart")
                    return True
                log.info("SDK not ready, waiting 10s... (%d/%d)" % (i + 1, MAX_START_RETRIES))
                time.sleep(10)
            log.error("SDK wait timeout after restart")
            return False
    else:
        log.info("OpenRGB is not running, starting...")
        if not start_openrgb():
            log.error("Failed to start OpenRGB")
            return False
        log.info("Waiting %d seconds for OpenRGB to start..." % OPENRGB_START_DELAY)
        time.sleep(OPENRGB_START_DELAY)
        for i in range(MAX_START_RETRIES):
            if is_sdk_responding():
                log.info("SDK is ready")
                return True
            if not is_openrgb_running():
                log.warning("OpenRGB process not found, retrying start...")
                start_openrgb()
                time.sleep(OPENRGB_START_DELAY)
                continue
            log.info("SDK not ready, waiting 10s... (%d/%d)" % (i + 1, MAX_START_RETRIES))
            time.sleep(10)
        log.error("SDK wait timeout")
        return False


def connect():
    for attempt in range(MAX_START_RETRIES):
        try:
            client = OpenRGBClient(address=OPENRGB_HOST, port=OPENRGB_PORT)
            devs = client.ee_devices
            if len(devs) == 0:
                log.warning("Connected to SDK but no devices yet, retry in %ds..." % RECONNECT_DELAY)
                time.sleep(RECONNECT_DELAY)
                continue
            log.info("Connected to SDK, %d devices, waiting for stability..." % len(devs))
            stable_count = 0
            prev_count = len(devs)
            while True:
                time.sleep(STABILITY_CHECK_INTERVAL)
                devs = client.ee_devices
                curr_count = len(devs)
                if curr_count == prev_count:
                    stable_count += 1
                    if stable_count >= STABILITY_CHECK_COUNT:
                        break
                    log.info("Device count %d stable (%d/%d)..." % (curr_count, stable_count, STABILITY_CHECK_COUNT))
                else:
                    log.info("Device count changed: %d -> %d, waiting..." % (prev_count, curr_count))
                    stable_count = 0
                    prev_count = curr_count
            log.info("Devices stable: %d devices" % len(devs))
            for i, dev in enumerate(devs):
                log.info("  Device %d: %s" % (i, dev.name))
            return client, devs
        except Exception as e:
            log.warning("Connection failed: %s, retry in %ds... (%d/%d)" % (e, RECONNECT_DELAY, attempt + 1, MAX_START_RETRIES))
            time.sleep(RECONNECT_DELAY)
    log.error("Failed to connect to OpenRGB SDK after max retries")
    return None, None


def connect_fast():
    """Fast connect for restart recovery: shorter delays, fewer stability checks."""
    for attempt in range(4):
        try:
            client = OpenRGBClient(address=OPENRGB_HOST, port=OPENRGB_PORT)
            devs = client.ee_devices
            if len(devs) == 0:
                log.warning("Fast connect: no devices yet, retry in 5s...")
                time.sleep(5)
                continue
            log.info("Fast connect: %d devices, checking stability..." % len(devs))
            stable_count = 0
            prev_count = len(devs)
            for _ in range(6):
                time.sleep(5)
                devs = client.ee_devices
                curr_count = len(devs)
                if curr_count == prev_count:
                    stable_count += 1
                    if stable_count >= 2:
                        break
                else:
                    stable_count = 0
                    prev_count = curr_count
            log.info("Fast connect stable: %d devices" % len(devs))
            for i, dev in enumerate(devs):
                log.info("  Device %d: %s" % (i, dev.name))
            return client, devs
        except Exception as e:
            log.warning("Fast connect failed: %s, retry in 5s... (%d/4)" % (e, attempt + 1))
            time.sleep(5)
    log.error("Fast connect failed after max retries")
    return None, None


def restart_openrgb_fast(states_backup=None):
    """Kill and restart OpenRGB with optimized timing for physical replug recovery.
    Returns (client, devs, states) or (None, None, None) on failure."""
    log.info("=== FAST RESTART: killing OpenRGB for USB handle refresh ===")
    kill_openrgb()

    log.info("Starting OpenRGB (fast restart)...")
    if not start_openrgb():
        log.error("Failed to start OpenRGB during fast restart")
        return None, None, None

    # Wait for SDK to become available (shorter than normal)
    log.info("Waiting 15s for OpenRGB to start...")
    time.sleep(15)
    for i in range(6):
        if is_sdk_responding():
            log.info("SDK ready after fast restart")
            break
        time.sleep(5)
    else:
        log.error("SDK not ready after fast restart")
        return None, None, None

    client, devs = connect_fast()
    if client is None:
        return None, None, None

    # Apply saved state immediately (no profile wait — we have the state in memory)
    if states_backup:
        razer_idx = find_razer_index(devs)
        skip = razer_idx if lighting_state == "off" else -1
        apply_state(devs, states_backup, skip_index=skip)
        save_mode_safe(devs, skip_index=skip)
        log.info("State re-applied after fast restart")
    else:
        states_backup = capture_state(devs)

    return client, devs, states_backup


def parse_orp_profile(profile_path):
    """Parse an OpenRGB profile (.orp) file using the SDK's built-in parser.
    Returns list of (name, active_mode, [RGBColor]) in file order."""
    with open(profile_path, "rb") as f:
        profile = LocalProfile.unpack(f)
    return [(c.name, c.active_mode, list(c.colors)) for c in profile.controllers]


def load_expected_dram_states():
    """Load ENE DRAM expected states from profile 123.orp (by occurrence order).
    Returns list of (mode_idx, [RGBColor]) for each ENE DRAM in the profile."""
    profile_path = os.path.join(os.environ.get("APPDATA", ""), "OpenRGB", "123.orp")
    try:
        devices = parse_orp_profile(profile_path)
        drams = []
        for name, mode_idx, colors in devices:
            if "ENE DRAM" in name:
                drams.append((mode_idx, list(colors)))
        if drams:
            log.info("Profile expected states loaded: %d ENE DRAM device(s) from %s" % (len(drams), os.path.basename(profile_path)))
        return drams
    except Exception as e:
        log.warning("Failed to parse profile for DRAM states: %s" % e)
        return []


def capture_state(devs):
    states = []
    dram_expected = load_expected_dram_states()
    dram_idx = 0
    for i, dev in enumerate(devs):
        try:
            mode_idx = dev.active_mode
            colors = list(dev.colors)
            # ENE DRAM may report Off after boot even though the saved profile
            # expects Direct+color. Use the profile expected state instead so
            # the periodic push keeps the DRAM lighting on.
            if "ENE DRAM" in dev.name and dram_idx < len(dram_expected):
                exp_mode, exp_colors = dram_expected[dram_idx]
                mode_idx = exp_mode
                colors = list(exp_colors)
                log.info("  Device %d [%s]: using profile expected state (mode=%d, leds=%d)" % (i, dev.name, mode_idx, len(colors)))
                dram_idx += 1
            states.append({"mode": mode_idx, "colors": colors})
            log.info("  Device %d [%s]: mode=%d, leds=%d" % (i, dev.name, mode_idx, len(colors)))
        except Exception as e:
            log.error("  Device %d [%s] state read failed: %s" % (i, dev.name, e))
            states.append(None)
    return states


def apply_state(devs, states, skip_index=-1):
    success_count = 0
    fail_count = 0
    for i, state in enumerate(states):
        if state is None or i >= len(devs) or i == skip_index:
            continue
        try:
            dev = devs[i]
            dev.set_mode(state["mode"])
            dev.set_colors(state["colors"])
            success_count += 1
        except Exception as e:
            log.error("  Device %d [%s] state apply failed: %s" % (i, dev.name, e))
            fail_count += 1
    return success_count, fail_count


# ══════════════════════════════════════════════════════
# Battery Management (pyusb)
# ══════════════════════════════════════════════════════

def get_transaction_id():
    tran_id = 0x3F
    for path in [
        os.path.join(os.environ.get("USERPROFILE", ""), "rebt.ini"),
        os.path.join(os.environ.get("APPDATA", ""), "rebt", "rebt.ini"),
    ]:
        if os.path.exists(path):
            try:
                config = configparser.ConfigParser()
                config.read(path)
                for section in config.sections():
                    if "tranid" in config[section]:
                        val = config[section]["tranid"]
                        tran_id = int(val, 16) if val.startswith("0x") else int(val)
                        if not (0 <= tran_id <= 0xFF):
                            tran_id = 0x3F
                        log.info("Transaction ID from rebt.ini: 0x%02X" % tran_id)
            except (ValueError, configparser.Error) as e:
                log.warning("Failed to parse rebt.ini (%s), using default tranid" % e)
                tran_id = 0x3F
            break
    return tran_id

TRANSACTION_ID = get_transaction_id()

# Serialize USB access (read_battery_raw vs read_charging_only)
_usb_lock = threading.Lock()


def generate_msg(command_class, command_id, data_size=0x02):
    msgs = [0x00, TRANSACTION_ID, 0x00, 0x00, 0x00, data_size, command_class, command_id]
    msg = bytes(msgs)
    crc = 0
    for b in msg[2:]:
        crc ^= b
    msg += bytes(80)
    msg += bytes([crc, 0])
    return msg


def read_battery_raw():
    """Read battery level and charging status. Returns (battery_pct, is_charging).
    Returns (-1, False) on failure. Retries on transient USB errors."""
    with _usb_lock:
        return _read_battery_raw_locked()

def _read_battery_raw_locked():
    for attempt in range(3):
        try:
            dev = usb.core.find(idVendor=RAZER_VID, custom_match=lambda d: d.idProduct in RAZER_PIDS, backend=_USB_BACKEND)
            if dev is None:
                devs = list(usb.core.find(find_all=True, idVendor=RAZER_VID, custom_match=lambda d: d.idProduct in RAZER_PIDS, backend=_USB_BACKEND))
                if not devs:
                    return -1, False
                dev = devs[0]

            usb.util.claim_interface(dev, 0)
            dev.set_configuration()

            battery_msg = generate_msg(0x07, 0x80, 0x02)
            dev.ctrl_transfer(bmRequestType=0x21, bRequest=0x09, wValue=0x0300, data_or_wLength=battery_msg)
            time.sleep(0.1)
            result = dev.ctrl_transfer(bmRequestType=0xa1, bRequest=0x01, wValue=0x0300, data_or_wLength=90)
            result_bytes = bytes(result)
            raw_battery = result_bytes[9]

            charge_msg = generate_msg(0x07, 0x84, 0x02)
            dev.ctrl_transfer(bmRequestType=0x21, bRequest=0x09, wValue=0x0300, data_or_wLength=charge_msg)
            time.sleep(0.1)
            result2 = dev.ctrl_transfer(bmRequestType=0xa1, bRequest=0x01, wValue=0x0300, data_or_wLength=90)
            result2_bytes = bytes(result2)
            charging = result2_bytes[9]

            usb.util.release_interface(dev, 0)
            usb.util.dispose_resources(dev)

            if charging == 0xFF:
                log.warning("Charging byte returned 0xFF (sentinel/unknown), retrying... (attempt %d)" % (attempt + 1))
                if attempt < 2:
                    time.sleep(1)
                    continue
                log.error("Charging status consistently 0xFF - mouse firmware may need a power cycle")
                return -1, False

            # 0xFF (255) is a sentinel value meaning the mouse firmware
            # failed to return a valid battery reading. This is a known
            # issue with Razer wireless mice (OpenRazer issue #2109, #2122).
            # Treating it as 100% would incorrectly keep lighting on when
            # the battery may actually be low.
            if raw_battery == 0xFF:
                log.warning("Battery read returned 0xFF (sentinel/unknown), retrying... (attempt %d)" % (attempt + 1))
                if attempt < 2:
                    time.sleep(1)
                    continue
                log.error("Battery consistently returning 0xFF - mouse firmware may need a power cycle")
                return -1, False

            # Only treat raw=0 or raw=1 as corrupted reads (USB conflict)
            # Real low battery values (raw >= 2) should NOT be ignored,
            # even if charging — the battery may genuinely be very low.
            if raw_battery <= 1:
                log.warning("Corrupted battery read (raw=%d), retrying..." % raw_battery)
                if attempt < 2:
                    time.sleep(1)
                    continue
                return -1, False

            battery_pct = int(raw_battery / 255 * 100)
            is_charging = (charging == 1)

            return battery_pct, is_charging
        except Exception as e:
            log.warning("Battery read attempt %d failed: %s" % (attempt + 1, e))
            try:
                usb.util.release_interface(dev, 0)
                usb.util.dispose_resources(dev)
            except:
                pass
            if attempt < 2:
                time.sleep(1)
    return -1, False


# ══════════════════════════════════════════════════════
# Lighting Logic
# ══════════════════════════════════════════════════════

lighting_state = "on"
last_battery_pct = -1
last_charging_state = 0  # last known charging state for heartbeat fallback

def find_razer_index(devs):
    for i, dev in enumerate(devs):
        if "Razer" in dev.name:
            return i
    return -1

def set_mouse_light_off(devs, razer_idx):
    try:
        dev = devs[razer_idx]
        dev.set_mode(0)  # Direct mode
        dev.set_colors([RGBColor(0, 0, 0)] * len(dev.colors))
        log.info("  Mouse lighting: OFF")
    except Exception as e:
        log.error("  Failed to turn off mouse lighting: %s" % e)

def _profile_mouse_state(dev_name):
    """Read the mouse state (mode + colors) from the saved profile file."""
    profile_path = os.path.join(os.environ.get("APPDATA", ""), "OpenRGB", "123.orp")
    try:
        devices = parse_orp_profile(profile_path)
        for name, mode_idx, colors in devices:
            if name == dev_name or "Razer" in name:
                return {"mode": mode_idx, "colors": list(colors)}
    except Exception as e:
        log.warning("Failed to parse profile for mouse state: %s" % e)
    return None

def set_mouse_light_on(devs, states, razer_idx):
    """Turn on mouse lighting by loading the OpenRGB profile."""
    try:
        client = OpenRGBClient(address=OPENRGB_HOST, port=OPENRGB_PORT)
        client.update_profiles()
        profile = None
        for p in client.profiles:
            if p.name == "123":
                profile = p
                break
        if profile is None and client.profiles:
            profile = client.profiles[0]
        if profile is not None:
            client.load_profile(profile.name)
            log.info("  Mouse lighting: ON (loaded profile '%s')" % profile.name)
            mouse_state = _profile_mouse_state(devs[razer_idx].name)
            if mouse_state is not None:
                states[razer_idx] = mouse_state
            return
        log.warning("  No profiles found, falling back to saved colors")
    except Exception as e:
        log.error("  Failed to load profile: %s" % e)
    # Fallback: restore the saved state
    try:
        dev = devs[razer_idx]
        state = states[razer_idx]
        if state is not None:
            dev.set_mode(state["mode"])
            dev.set_colors(state["colors"])
            log.info("  Mouse lighting: ON (restored saved state)")
    except Exception as e:
        log.error("  Failed to restore mouse lighting: %s" % e)

def read_charging_only():
    """Lightweight: read only charging state (0x07/0x84) for tray red dot.
    Returns 0/1, or None on failure. Does NOT read battery level."""
    with _usb_lock:
        return _read_charging_only_locked()

def _read_charging_only_locked():
    dev = None
    try:
        dev = usb.core.find(idVendor=RAZER_VID, custom_match=lambda d: d.idProduct in RAZER_PIDS, backend=_USB_BACKEND)
        if dev is None:
            devs = list(usb.core.find(find_all=True, idVendor=RAZER_VID, custom_match=lambda d: d.idProduct in RAZER_PIDS, backend=_USB_BACKEND))
            if not devs:
                return None
            dev = devs[0]
        usb.util.claim_interface(dev, 0)
        dev.set_configuration()
        charge_msg = generate_msg(0x07, 0x84, 0x02)
        dev.ctrl_transfer(bmRequestType=0x21, bRequest=0x09, wValue=0x0300, data_or_wLength=charge_msg)
        time.sleep(0.05)
        result2 = dev.ctrl_transfer(bmRequestType=0xa1, bRequest=0x01, wValue=0x0300, data_or_wLength=90)
        ch_raw = result2[9]
        if ch_raw == 0xFF:
            log.warning("Charging read returned 0xFF (unknown), keeping previous state")
            return None
        return 1 if ch_raw == 1 else 0
    except Exception as e:
        log.warning("Charging read failed: %s" % e)
        return None
    finally:
        if dev is not None:
            try:
                usb.util.release_interface(dev, 0)
            except Exception:
                pass
            try:
                usb.util.dispose_resources(dev)
            except Exception:
                pass


def check_battery_and_manage_lighting(devs, states):
    global lighting_state, last_battery_pct, last_charging_state
    razer_idx = find_razer_index(devs)
    if razer_idx < 0:
        log.warning("Razer mouse not found in device list")
        return

    battery_pct, is_charging = read_battery_raw()

    if battery_pct < 0:
        log.warning("Battery read failed, keeping current lighting state: %s" % lighting_state)
        write_battery_file(-1, False)
        return

    log.info("Battery: %d%%, charging: %s, lighting: %s" %
             (battery_pct, "yes" if is_charging else "no", lighting_state))
    # Write battery info to file for OpenRGB tray icon
    write_battery_file(battery_pct, is_charging)
    last_battery_pct = battery_pct
    last_charging_state = 1 if is_charging else 0

    if lighting_state == "on" and battery_pct < BATTERY_LOW_THRESHOLD:
        lighting_state = "off"
        log.info("Battery below %d%%, turning OFF mouse lighting" % BATTERY_LOW_THRESHOLD)
        set_mouse_light_off(devs, razer_idx)
    elif lighting_state == "off" and battery_pct >= BATTERY_HIGH_THRESHOLD:
        lighting_state = "on"
        log.info("Battery above %d%%, turning ON mouse lighting" % BATTERY_HIGH_THRESHOLD)
        set_mouse_light_on(devs, states, razer_idx)


# ══════════════════════════════════════════════════════
# Main
# ══════════════════════════════════════════════════════

def main():
    global need_openrgb_restart, saw_device_removal, last_charging_state
    log.info("=" * 60)
    log.info("OpenRGB Keeper started (WMI event mode)")
    log.info("Push interval: %ds, Battery check: %ds" %
             (HIGH_FREQ_INTERVAL, BATTERY_CHECK_INTERVAL))
    log.info("=" * 60)

    # Start device presence poller (daemon thread)
    log.info("Starting device presence poller...")
    start_device_listener()
    time.sleep(2)

    # Ensure OpenRGB is running
    if not ensure_openrgb_running():
        log.error("OpenRGB not running and could not be started, exiting")
        sys.exit(1)

    log.info("Waiting %d seconds for profile to load..." % STATE_CAPTURE_DELAY)
    time.sleep(STATE_CAPTURE_DELAY)

    # Connect to SDK
    client, devs = connect()
    if client is None or devs is None:
        if need_openrgb_restart:
            log.info("Connect failed + device replug detected, restarting...")
            need_openrgb_restart = False
            saw_device_removal = False
            result = restart_openrgb_fast()
            if result and result[0] is not None:
                client, devs, _ = result
            else:
                client, devs = connect()
        if client is None or devs is None:
            log.error("Cannot connect to OpenRGB SDK, exiting")
            sys.exit(1)

    log.info("Capturing device states...")
    states = capture_state(devs)
    expected_device_count = len(devs)  # Track expected device count for missing-device detection
    log.info("Expected device count: %d" % expected_device_count)

    log.info("Initial battery check...")
    check_battery_and_manage_lighting(devs, states)

    # ── Simple main loop ──────────────────────────────
    # Single loop, no nested high-freq/event-driven modes.
    # The poller thread sets need_openrgb_restart on monitored-device removal,
    # and device_wake_event on any monitored-device change (Candy only).
    last_push = time.time()
    last_battery_check = time.time()
    last_charge_check = time.time()
    push_count = 0

    while True:
        try:
            # 1) Check for physical device removal → must restart OpenRGB
            if need_openrgb_restart:
                need_openrgb_restart = False
                log.info("*** Device REMOVAL detected — waiting for return ***")

                # Wait for poller to signal device return
                device_wake_event.clear()
                if device_wake_event.wait(timeout=120):
                    log.info("Device returned, restarting OpenRGB for USB handle refresh...")
                else:
                    log.warning("Device did not return within 120s, restarting anyway...")

                saw_device_removal = False
                result = restart_openrgb_fast(states_backup=states)
                if result and result[0] is not None:
                    client, devs, states = result
                    expected_device_count = max(expected_device_count, len(devs))
                    log.info("OpenRGB restarted, %d devices (expected: %d)" %
                             (len(devs), expected_device_count))
                    check_battery_and_manage_lighting(devs, states)
                    razer_idx = find_razer_index(devs)
                    skip = razer_idx if lighting_state == "off" else -1
                    apply_state(devs, states, skip_index=skip)
                    save_mode_safe(devs, skip_index=skip)
                    log.info("State re-applied after restart")
                else:
                    log.error("Fast restart failed, trying normal connect...")
                    new_client, new_devs = connect()
                    if new_client is not None:
                        client, devs = new_client, new_devs
                        states = capture_state(devs)
                        razer_idx = find_razer_index(devs)
                        skip = razer_idx if lighting_state == "off" else -1
                        apply_state(devs, states, skip_index=skip)
                    else:
                        log.error("Reconnect failed, will retry on next push")

                last_push = time.time()
                last_battery_check = time.time()
                push_count = 0
                continue

            # 2) Check for monitored-device event (Candy change; not mouse wake/sleep)
            if device_wake_event.is_set():
                device_wake_event.clear()
                if not need_openrgb_restart:
                    log.info("Device event (monitored device), fast recovery...")
                    time.sleep(3)
                    try:
                        devs = client.ee_devices
                        if len(devs) != len(states):
                            states = capture_state(devs)
                        razer_idx = find_razer_index(devs)
                        skip = razer_idx if lighting_state == "off" else -1
                        apply_state(devs, states, skip_index=skip)
                        save_mode_safe(devs, skip_index=skip)
                        log.info("Fast recovery done")
                    except Exception as e:
                        log.warning("Fast recovery failed: %s" % e)
                    last_push = time.time()
                    continue

            # 3) Periodic state push
            now = time.time()
            if now - last_push >= HIGH_FREQ_INTERVAL:
                push_count += 1

                # Re-fetch device list to detect new/missing devices
                try:
                    current_devs = client.ee_devices
                    if len(current_devs) != len(devs):
                        log.info("Device count changed: %d -> %d, re-capturing" %
                                 (len(devs), len(current_devs)))
                        devs = current_devs
                        states = capture_state(devs)
                except Exception as e:
                    log.warning("Device list refresh failed: %s" % e)

                # Check if Razer mouse is missing (was present before but now gone)
                razer_idx = find_razer_index(devs)
                if razer_idx < 0 and len(devs) < expected_device_count:
                    log.info("Razer mouse missing (devices: %d/%d), restarting OpenRGB..." %
                             (len(devs), expected_device_count))
                    need_openrgb_restart = True
                    # Don't clear device_wake_event — let the restart handler pick it up
                    # Wait a bit for device to come back
                    log.info("Waiting 10s for device to return before restart...")
                    time.sleep(10)
                    # Re-check
                    try:
                        current_devs = client.ee_devices
                        if len(current_devs) > len(devs):
                            log.info("Device came back: %d -> %d" % (len(devs), len(current_devs)))
                            devs = current_devs
                            states = capture_state(devs)
                            need_openrgb_restart = False
                    except:
                        pass
                    if need_openrgb_restart:
                        # Skip this push, let the restart handler in step 1 handle it
                        last_push = now
                        continue

                log.info("Periodic push #%d (%d devices)" % (push_count, len(devs)))
                skip = razer_idx if lighting_state == "off" else -1
                try:
                    success, fail = apply_state(devs, states, skip_index=skip)
                    # apply_state catches exceptions internally; check return values
                    # to detect dead SDK connection and trigger reconnect
                    if fail > 0 and success == 0:
                        raise ConnectionError("All %d device(s) failed to apply state" % fail)
                    if fail > 0:
                        # Partial failure: refresh state once (e.g. LED count changed)
                        log.warning("Partial push failure (%d/%d failed), re-capturing state..." %
                                    (fail, len(devs)))
                        current_devs = client.ee_devices
                        if len(current_devs) == len(devs):
                            states = capture_state(devs)
                            apply_state(devs, states, skip_index=skip)
                        else:
                            devs = current_devs
                            states = capture_state(devs)
                            apply_state(devs, states, skip_index=skip)
                except (ConnectionError, OSError, BrokenPipeError) as e:
                    log.error("Push failed (connection): %s, reconnecting..." % e)
                    if not is_openrgb_running():
                        start_openrgb()
                        time.sleep(OPENRGB_START_DELAY)
                    else:
                        kill_openrgb()
                        start_openrgb()
                        time.sleep(OPENRGB_START_DELAY)
                    new_client, new_devs = connect()
                    if new_client is not None:
                        client, devs = new_client, new_devs
                        states = capture_state(devs)
                        razer_idx = find_razer_index(devs)
                        skip = razer_idx if lighting_state == "off" else -1
                        apply_state(devs, states, skip_index=skip)
                    else:
                        log.error("Reconnect failed, will retry on next push")
                except Exception as e:
                    log.warning("Push failed: %s" % e)
                last_push = now

            # 4) Battery check
            if now - last_battery_check >= BATTERY_CHECK_INTERVAL:
                check_battery_and_manage_lighting(devs, states)
                last_battery_check = now

            # 4b) Charging status fast refresh (tray red dot every 5s)
            # Heartbeat: always write battery.txt (even on failure) so the
            # OpenRGB status bar / tray tooltip can tell keeper is alive.
            # On failure, fall back to the last known charging state.
            if now - last_charge_check >= CHARGE_CHECK_INTERVAL:
                ch = read_charging_only()
                if ch is not None:
                    write_battery_file(last_battery_pct, ch)
                    last_charging_state = ch
                else:
                    write_battery_file(last_battery_pct, last_charging_state)
                last_charge_check = now

            # 5) SDK heartbeat (only if no push for a while)
            if now - last_push >= LOW_FREQ_INTERVAL:
                if not is_sdk_responding():
                    log.warning("SDK heartbeat failed, restarting OpenRGB...")
                    kill_openrgb()
                    start_openrgb()
                    time.sleep(OPENRGB_START_DELAY)
                    client, devs = connect()
                    if client is not None:
                        states = capture_state(devs)
                        razer_idx = find_razer_index(devs)
                        skip = razer_idx if lighting_state == "off" else -1
                        apply_state(devs, states, skip_index=skip)
                    last_push = time.time()
                    last_battery_check = time.time()

            # 6) Sleep until next charge-check boundary (keeps 5s timing precise)
            time.sleep(max(0.5, min(5.0, CHARGE_CHECK_INTERVAL - (time.time() - last_charge_check))))

        except KeyboardInterrupt:
            log.info("Shutting down...")
            break
        except Exception as e:
            log.error("Unexpected error in main loop: %s" % e)
            time.sleep(RECONNECT_DELAY)


if __name__ == "__main__":
    # Single-instance guard: refuse to run if another keeper is alive
    _mutex = ctypes.windll.kernel32.CreateMutexW(None, False, "OpenRGBKeeperMutex")
    if ctypes.windll.kernel32.GetLastError() == 183:  # ERROR_ALREADY_EXISTS
        print("Another OpenRGB Keeper instance is already running, exiting.")
        sys.exit(0)
    try:
        main()
    finally:
        ctypes.windll.kernel32.ReleaseMutex(_mutex)
        ctypes.windll.kernel32.CloseHandle(_mutex)
