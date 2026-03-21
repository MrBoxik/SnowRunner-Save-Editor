# =============================================================================
# SECTION: Imports & Optional Dependencies
# Used In: Entire application (core runtime, UI, and utilities)
# =============================================================================
from __future__ import annotations
import sys
import platform
import os
if platform.system() == "Windows":
    import ctypes
    from ctypes import wintypes
    try:
        wintypes.HRESULT = ctypes.c_long
    except Exception:
        pass
import time
import struct
import zlib
import copy
import traceback
import shutil
import threading
import subprocess
import csv
import codecs
import tempfile
import ssl
import gzip
import urllib.request
import urllib.error
from urllib.parse import urljoin, urlparse
from typing import List, Dict, Any, Iterator, Optional, Set
import random
import re
import json
import math
import hashlib
import uuid
from datetime import datetime, timezone

# Pillow is intentionally not imported. Fog/image features below use
# tkinter + pure-Python pixel buffers so we can avoid bundling Pillow.

import webbrowser
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, PhotoImage, colorchooser
import tkinter.font as tkfont

# Preserve native messagebox functions so we can fall back when needed.
_NATIVE_SHOWINFO = messagebox.showinfo
_NATIVE_SHOWWARNING = messagebox.showwarning
_NATIVE_SHOWERROR = messagebox.showerror

# =============================================================================
# APP VERSION (manual)
# =============================================================================
APP_VERSION = 100
_UPDATE_STATUS = None  # "update", "dev", "none"

# -----------------------------------------------------------------------------
# END SECTION: Imports & Optional Dependencies
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Season Config (edit here)
# Used In: Missions tab, Objectives/Contests, Game Stats, Watchtowers
# =============================================================================
SEASON_REGION_MAP = {
    1: ("RU_03", "Season 1: Search & Recover (Kola Peninsula)"),
    2: ("US_04", "Season 2: Explore & Expand (Yukon)"),
    3: ("US_03", "Season 3: Locate & Deliver (Wisconsin)"),
    4: ("RU_04", "Season 4: New Frontiers (Amur)"),
    5: ("RU_05", "Season 5: Build & Dispatch (Don)"),
    6: ("US_06", "Season 6: Haul & Hustle (Maine)"),
    7: ("US_07", "Season 7: Compete & Conquer (Tennessee)"),
    8: ("RU_08", "Season 8: Grand Harvest (Glades)"),
    9: ("US_09", "Season 9: Renew & Rebuild (Ontario)"),
    10: ("US_10", "Season 10: Fix & Connect (British Columbia)"),
    11: ("US_11", "Season 11: Lights & Cameras (Scandinavia)"),
    12: ("US_12", "Season 12: Public Energy (North Carolina)"),
    13: ("RU_13", "Season 13: Dig & Drill (Almaty)"),
    14: ("US_14", "Season 14: Reap & Sow (Austria)"),
    15: ("US_15", "Season 15: Oil & Dirt (Quebec)"),
    16: ("US_16", "Season 16: High Voltage (Washington)"),
    17: ("RU_17", "Season 17: Repair & Rescue (Zurdania)"),
}

BASE_MAPS = [
    ("US_01", "Michigan"),
    ("US_02", "Alaska"),
    ("RU_02", "Taymyr"),
]

# --- Derived from season config (do not edit) ---
SEASON_ENTRIES = sorted(SEASON_REGION_MAP.items(), key=lambda kv: kv[0])
SEASON_ID_MAP = {season: code for season, (code, _) in SEASON_ENTRIES}
SEASON_LABELS = [label for _, (_, label) in SEASON_ENTRIES]
SEASON_CODE_LABELS = [(code, label) for _, (code, label) in SEASON_ENTRIES]
ALL_REGION_CODE_LABELS = BASE_MAPS + SEASON_CODE_LABELS

def _season_short_name(label: str) -> str:
    match = re.search(r"\(([^)]+)\)\s*$", label)
    return match.group(1) if match else label

# Short names (used by tooltips and misc UI)
REGION_NAME_MAP = {code: name for code, name in BASE_MAPS}
REGION_NAME_MAP.update({code: _season_short_name(label) for _, (code, label) in SEASON_ENTRIES})

# Full names (used by stats UI)
REGION_LONG_NAME_MAP = {code: name for code, name in BASE_MAPS}
REGION_LONG_NAME_MAP.update({code: label for _, (code, label) in SEASON_ENTRIES})
REGION_LONG_NAME_MAP["TRIALS"] = "Trials"

# -----------------------------------------------------------------------------
# END SECTION: Season Config
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Global Tk/Editor State (shared UI variables)
# Used In: launch_gui and all tab builders
# =============================================================================
make_backup_var = None
full_backup_var = None
max_backups_var = None
max_autobackups_var = None
save_path_var = None
money_var = None
rank_var = None
xp_var = None
time_preset_var = None 
skip_time_var = None
custom_day_var = None
custom_night_var = None
other_season_var = None
# time_presets mappings are defined further below in the file, but some
# functions reference `time_presets` before that definition. Provide a
# safe default here so static analyzers (Pylance) don't report an
# undefined-variable warning. The full mapping is assigned later.
time_presets = {}
season_vars = []
map_vars = []
tyre_var = None
delete_path_on_close_var = None
dont_remember_path_var = None
difficulty_var = None
truck_avail_var = None
truck_price_var = None
addon_avail_var = None
addon_amount_var = None
time_day_var = None
time_night_var = None
garage_refuel_var = None
autosave_var = None
dark_mode_var = None
theme_preset_var = None
objectives_safe_fallback_var = None
_AUTOSAVE_THREAD = None
_AUTOSAVE_STOP_EVENT = None
_AUTOSAVE_STATE_LOCK = threading.Lock()
_AUTOSAVE_ENABLED = False
_AUTOSAVE_FULL_BACKUP = False
_AUTOSAVE_SAVE_PATH = ""
_AUTOSAVE_STATE_TRACES_BOUND = False
_WINDOWS_UPDATE_IN_PROGRESS = False
_TIME_SYNC_GUARD = False
_BASE_TTK_THEME = None
_THEME_CUSTOM_PRESETS = {}
_ACTIVE_THEME = None
_ACTIVE_THEME_NAME = "Light"
_ACTIVE_THEME_MODE = "light"
_APP_ROOT = None
_APP_STATUS_VAR = None
_APP_STATUS_CLEAR_JOB = None
_DEFAULT_STATUS_TEXT = "Status: Ready. Select an action."

SAVE_FILE_NAME = "snowrunner_editor_save.json"
_SAVE_FILE_PATH = None
EDITOR_DATA_DIR_NAME = "snowrunner_save_editor_data"
_EDITOR_DATA_DIR = None
_STATUS_LOG_PATH = None
_STATUS_LOG_LOCK = threading.Lock()
_LOG_STREAMS_INSTALLED = False
_OBJECTIVES_PREFETCH_LOCK = threading.Lock()
_OBJECTIVES_PREFETCH_STATE = {
    "started": False,
    "inflight": False,
    "completed": False,
    "built": False,
    "error": "",
    "last_completed_ts": 0.0,
}

# Optional "Make editor better" upload (desktop app, Save File tab)
IMPROVE_UPLOAD_ENDPOINT = "https://broad-star-66c2.mrtnhliza.workers.dev/"
IMPROVE_UPLOAD_ORIGIN_HEADER = "https://mrboxik.github.io"
IMPROVE_UPLOAD_REFERER_HEADER = "https://mrboxik.github.io/snowrunner-save-editor-web/"
IMPROVE_UPLOAD_TIMEOUT_MS = 45000
IMPROVE_UPLOAD_MAX_FILES_PER_REQUEST = 1
IMPROVE_UPLOAD_BETWEEN_CHUNKS_MS = 5000

# -----------------------------------------------------------------------------
# END SECTION: Global Tk/Editor State
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Local Save-Data Path Helpers
# Used In: Minesweeper mini-game + app settings persistence
# =============================================================================

def configure_app_status(root, status_var):
    """Register root + StringVar used by the global status bar."""
    global _APP_ROOT, _APP_STATUS_VAR, _APP_STATUS_CLEAR_JOB
    _APP_ROOT = root
    _APP_STATUS_VAR = status_var
    _APP_STATUS_CLEAR_JOB = None

def _compact_status_text(message, max_len=280):
    text = "" if message is None else str(message)
    text = re.sub(r"\s+", " ", text).strip()
    if len(text) > max_len:
        text = text[: max_len - 3].rstrip() + "..."
    return text

def set_app_status(message, timeout_ms=6000):
    """
    Update the bottom status bar. Safe to call from worker threads.
    timeout_ms <= 0 keeps the message until replaced.
    """
    text = _compact_status_text(message)
    if not text:
        return
    try:
        _append_status_log_line(text, source="status")
    except Exception:
        pass

    root = _APP_ROOT
    status_var = _APP_STATUS_VAR
    if root is None or status_var is None:
        print(f"[Status] {text}")
        return

    def _apply():
        global _APP_STATUS_CLEAR_JOB
        try:
            status_var.set(text)
        except Exception:
            return

        if _APP_STATUS_CLEAR_JOB is not None:
            try:
                root.after_cancel(_APP_STATUS_CLEAR_JOB)
            except Exception:
                pass
            _APP_STATUS_CLEAR_JOB = None

        if timeout_ms and timeout_ms > 0:
            try:
                _APP_STATUS_CLEAR_JOB = root.after(timeout_ms, lambda: status_var.set(_DEFAULT_STATUS_TEXT))
            except Exception:
                _APP_STATUS_CLEAR_JOB = None

    try:
        if threading.current_thread() is threading.main_thread():
            _apply()
        else:
            root.after(0, _apply)
    except Exception:
        print(f"[Status] {text}")

def show_info(title=None, message=None, popup=False, timeout_ms=6000, **options):
    """
    Default info surface: status bar (non-blocking).
    Set popup=True for rare cases where a modal info dialog is still wanted.
    """
    title_txt = "" if title is None else str(title).strip()
    msg_txt = "" if message is None else str(message).strip()
    if title_txt and msg_txt:
        set_app_status(f"{title_txt}: {msg_txt}", timeout_ms=timeout_ms)
    else:
        set_app_status(msg_txt or title_txt, timeout_ms=timeout_ms)
    if popup:
        return messagebox.showinfo(title, message, **options)
    return "ok"

def _ensure_dir(path):
    try:
        os.makedirs(path, exist_ok=True)
        return True
    except Exception:
        return False


def get_editor_data_dir():
    """Central folder for app-generated non-save files/logs/caches."""
    global _EDITOR_DATA_DIR
    if _EDITOR_DATA_DIR:
        return _EDITOR_DATA_DIR

    base_dir = ""
    try:
        home = os.path.expanduser("~")
    except Exception:
        home = ""
    if home:
        base_dir = os.path.join(home, EDITOR_DATA_DIR_NAME)

    if base_dir and _ensure_dir(base_dir):
        _EDITOR_DATA_DIR = base_dir
        return _EDITOR_DATA_DIR

    # Fallback to current working directory if home path is unavailable.
    try:
        fallback = os.path.join(os.getcwd(), EDITOR_DATA_DIR_NAME)
        _ensure_dir(fallback)
        _EDITOR_DATA_DIR = fallback
    except Exception:
        _EDITOR_DATA_DIR = os.getcwd()
    return _EDITOR_DATA_DIR


def get_status_log_path():
    global _STATUS_LOG_PATH
    if _STATUS_LOG_PATH:
        return _STATUS_LOG_PATH
    try:
        _STATUS_LOG_PATH = os.path.join(get_editor_data_dir(), "status_logs.txt")
    except Exception:
        _STATUS_LOG_PATH = os.path.join(os.getcwd(), "status_logs.txt")
    return _STATUS_LOG_PATH


def _append_status_log_line(message, source="status"):
    text = str(message or "").replace("\r", "")
    if not text:
        return
    try:
        lines = [ln for ln in text.split("\n") if ln.strip()]
        if not lines:
            return
        path = get_status_log_path()
        folder = os.path.dirname(path)
        if folder:
            _ensure_dir(folder)
        stamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        with _STATUS_LOG_LOCK:
            with open(path, "a", encoding="utf-8") as fh:
                for line in lines:
                    fh.write(f"[{stamp}] [{source}] {line}\n")
    except Exception:
        # logging should never break app behavior
        pass


class _StreamTee:
    """Mirror stdout/stderr to terminal and append complete lines to status log."""

    def __init__(self, original, source):
        self._original = original
        self._source = str(source or "stdout")
        self._buffer = ""

    def write(self, data):
        text = "" if data is None else str(data)
        try:
            self._original.write(text)
        except Exception:
            pass

        if not text:
            return 0

        self._buffer += text
        while "\n" in self._buffer:
            line, self._buffer = self._buffer.split("\n", 1)
            if line.strip():
                _append_status_log_line(line, source=self._source)
        return len(text)

    def flush(self):
        try:
            self._original.flush()
        except Exception:
            pass
        if self._buffer.strip():
            _append_status_log_line(self._buffer, source=self._source)
        self._buffer = ""

    def isatty(self):
        try:
            return bool(self._original.isatty())
        except Exception:
            return False


def install_status_log_stream_tee():
    """Install stdout/stderr tees once so terminal output is stored in status_logs.txt."""
    global _LOG_STREAMS_INSTALLED
    if _LOG_STREAMS_INSTALLED:
        return
    try:
        if not isinstance(sys.stdout, _StreamTee):
            sys.stdout = _StreamTee(sys.stdout, "stdout")
        if not isinstance(sys.stderr, _StreamTee):
            sys.stderr = _StreamTee(sys.stderr, "stderr")
        _LOG_STREAMS_INSTALLED = True
        _append_status_log_line("Status log capture initialized.", source="system")
    except Exception:
        pass

def _legacy_save_candidates():
    candidates = []
    try:
        candidates.append(os.path.join(os.getcwd(), SAVE_FILE_NAME))
    except Exception:
        pass
    try:
        candidates.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), SAVE_FILE_NAME))
    except Exception:
        pass
    # Remove duplicates while preserving order
    seen = set()
    unique = []
    for p in candidates:
        if p and p not in seen:
            seen.add(p)
            unique.append(p)
    return unique

def _migrate_legacy_save(target_path):
    if os.path.exists(target_path):
        return
    for candidate in _legacy_save_candidates():
        try:
            if not candidate:
                continue
            if os.path.abspath(candidate) == os.path.abspath(target_path):
                continue
            if os.path.isfile(candidate):
                try:
                    shutil.copy2(candidate, target_path)
                except Exception:
                    pass
                return
        except Exception:
            pass

def get_save_file_path():
    """Return a writable path for legacy/migrated Minesweeper progress data."""
    global _SAVE_FILE_PATH
    if _SAVE_FILE_PATH:
        return _SAVE_FILE_PATH

    try:
        base_dir = get_editor_data_dir()
    except Exception:
        base_dir = ""

    if base_dir and _ensure_dir(base_dir):
        _SAVE_FILE_PATH = os.path.join(base_dir, SAVE_FILE_NAME)
        _migrate_legacy_save(_SAVE_FILE_PATH)
        return _SAVE_FILE_PATH

    # Fallback: current working directory
    try:
        _SAVE_FILE_PATH = os.path.join(os.getcwd(), SAVE_FILE_NAME)
    except Exception:
        _SAVE_FILE_PATH = SAVE_FILE_NAME
    return _SAVE_FILE_PATH

# -----------------------------------------------------------------------------
# END SECTION: Local Save-Data Path Helpers
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Resource Paths & App Icon
# Used In: launch_gui and all Tk/Toplevel windows
# =============================================================================
def resource_path(relative_path):
    """ Get absolute path to resource, works for dev and for PyInstaller """
    try:
        base_path = sys._MEIPASS
    except AttributeError:
        base_path = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base_path, relative_path)
dropdown_widgets = {}
def _load_iconphotos_from_ico(ico_path):
    """No-op helper kept for compatibility; we avoid Pillow-based ICO parsing."""
    return []
def _set_windows_taskbar_icon(root, ico_path) -> bool:
    """Best-effort: set Windows taskbar icon via WM_SETICON."""
    try:
        if platform.system() != "Windows":
            return False
        try:
            import ctypes  # local import for safety
        except Exception:
            return False
        if not ico_path or not os.path.exists(ico_path):
            return False
        try:
            root.update_idletasks()
        except Exception:
            pass
        try:
            hwnd = root.winfo_id()
        except Exception:
            return False
        if not hwnd:
            return False
        user32 = ctypes.windll.user32
        SM_CXICON = 11
        SM_CYICON = 12
        SM_CXSMICON = 49
        SM_CYSMICON = 50
        cx = user32.GetSystemMetrics(SM_CXICON)
        cy = user32.GetSystemMetrics(SM_CYICON)
        cx_sm = user32.GetSystemMetrics(SM_CXSMICON)
        cy_sm = user32.GetSystemMetrics(SM_CYSMICON)
        IMAGE_ICON = 1
        LR_LOADFROMFILE = 0x00000010
        hicon_big = user32.LoadImageW(0, ico_path, IMAGE_ICON, cx, cy, LR_LOADFROMFILE)
        hicon_small = user32.LoadImageW(0, ico_path, IMAGE_ICON, cx_sm, cy_sm, LR_LOADFROMFILE)
        WM_SETICON = 0x80
        ICON_SMALL = 0
        ICON_BIG = 1
        if hicon_big:
            user32.SendMessageW(hwnd, WM_SETICON, ICON_BIG, hicon_big)
            try:
                setattr(root, "_win_icon_big", hicon_big)
            except Exception:
                pass
        if hicon_small:
            user32.SendMessageW(hwnd, WM_SETICON, ICON_SMALL, hicon_small)
            try:
                setattr(root, "_win_icon_small", hicon_small)
            except Exception:
                pass
        return bool(hicon_big or hicon_small)
    except Exception:
        return False
def set_app_icon(root) -> None:
    """Set cross-platform app icon for the given Tk root.

    Prefers app_icon.ico on Windows and app_icon.png elsewhere.
    Uses tkinter-native icon handling. Non-fatal.
    """
    try:
        system = platform.system()
        # Windows: prefer .ico and explicitly set taskbar icon
        if system == "Windows":
            ico = resource_path("app_icon.ico")
            if os.path.exists(ico):
                did_set = False
                # Try loading multi-size .ico frames into iconphoto (best effort)
                icons = _load_iconphotos_from_ico(ico)
                if icons:
                    try:
                        root.iconphoto(True, *icons)
                        setattr(root, "_app_icon_images", icons)
                        did_set = True
                    except Exception:
                        pass
                # Force taskbar icon via WinAPI (covers cases where Tk only sets small icon)
                if _set_windows_taskbar_icon(root, ico):
                    did_set = True
                try:
                    root.iconbitmap(ico)
                    did_set = True
                except Exception:
                    pass
                if did_set:
                    return

        # Try PNG icon via tkinter PhotoImage (no Pillow required)
        png = resource_path("app_icon.png")
        if os.path.exists(png):
            try:
                ph = PhotoImage(file=png)
                try:
                    root.iconphoto(False, ph)
                except Exception:
                    try:
                        root.iconphoto(ph)
                    except Exception:
                        pass
                try:
                    setattr(root, "_app_icon_image", ph)
                except Exception:
                    pass
                return
            except Exception:
                pass
        # Non-Windows fallback: if no PNG but ICO exists, try using ICO helper
        if system != "Windows":
            ico = resource_path("app_icon.ico")
            icons = _load_iconphotos_from_ico(ico)
            if icons:
                try:
                    root.iconphoto(True, *icons)
                    setattr(root, "_app_icon_images", icons)
                    return
                except Exception:
                    pass
    except Exception:
        try:
            print("[set_app_icon] failed:\n", traceback.format_exc())
        except Exception:
            pass

# Ensure newly-created Toplevel windows also attempt to use the same app icon
# This avoids duplicate ad-hoc icon code elsewhere and centralizes behavior.
try:
    _orig_toplevel_init = tk.Toplevel.__init__

    def _toplevel_init_with_icon(self, *args, **kwargs):
        _orig_toplevel_init(self, *args, **kwargs)
        try:
            set_app_icon(self)
        except Exception:
            pass
        try:
            apply_fn = globals().get("_apply_editor_theme")
            dark_fn = globals().get("_is_dark_mode_active")
            if callable(apply_fn):
                dark_mode = bool(dark_fn()) if callable(dark_fn) else False
                apply_fn(self, dark_mode=dark_mode)
        except Exception:
            pass

    tk.Toplevel.__init__ = _toplevel_init_with_icon
except Exception:
    # Non-fatal: if tkinter internals differ, fall back to default behavior
    pass

# -----------------------------------------------------------------------------
# END SECTION: Resource Paths & App Icon
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Minesweeper Mini-Game (Settings tab)
# Used In: Settings tab -> "Minesweeper" widget
# =============================================================================
def load_progress():
    default = {"level": 1, "title": "", "has_bronze": False, "has_silver": False, "has_gold": False}
    cfg = _load_config_safe()
    prog = cfg.get("minesweeper_progress")
    if isinstance(prog, dict):
        return {**default, **prog}
    # Legacy migration: snowrunner_editor_save.json
    try:
        path = get_save_file_path()
        if os.path.exists(path):
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict):
                cfg["minesweeper_progress"] = data
                _save_config_safe(cfg)
                try:
                    os.remove(path)
                except Exception:
                    pass
                return {**default, **data}
    except Exception:
        pass
    return default

def save_progress(data):
    try:
        cfg = _load_config_safe()
        cfg["minesweeper_progress"] = data
        if not _save_config_safe(cfg):
            raise RuntimeError("config save failed")
    except Exception as e:
        try:
            messagebox.showerror("Save Error", f"Could not save Minesweeper progress:\n{e}")
        except Exception:
            pass
LEVELS = {
    1: {"size": 10, "mines": 15, "title": "Master of Just Enough Time on Your Hands"},
    2: {"size": 12, "mines": 25, "title": "Master of Too Much Time on Your Hands"},
    3: {"size": 15, "mines": 40, "title": "Master of Way Too Much Time on Your Hands"}
}
LEVEL_COLORS = {1: "#964B00", 2: "#808080", 3: "#FFA500"}  # Bronze, Silver, Gold
EMOJI_BOMB, EMOJI_FLAG = "💣", "🚩"
CELL_COLORS = {"default": "#bdbdbd", "empty": "#f8f8f8", "flagged": "#e0e0e0"}
class Cell:
    def __init__(self, row, col, btn):
        self.row, self.col, self.btn = row, col, btn
        self.has_mine = self.revealed = self.flagged = False
class MinesweeperApp:
    def __init__(self, root):
        self.root = root
        if isinstance(root, tk.Tk):
            root.title("Minesweeper")

        self.data = load_progress()
        self.level = self.data.get("level", 1)
        self.first_click = True

        theme, parent_bg, _grid_bg = self._current_theme()
        self.title_label = tk.Label(
            root,
            font=("Arial", 16),
            bg=parent_bg,
            fg=theme["fg"],
            bd=0,
            highlightthickness=0,
        )
        self.title_label.pack(pady=10)
        self.frame = tk.Frame(root, bg=parent_bg, bd=0, highlightthickness=0)
        self.frame.pack()

        self.start_level()

    def _resolve_parent_bg(self, fallback):
        parent = None
        try:
            parent = self.root.master
        except Exception:
            parent = None
        if parent is None:
            return fallback

        try:
            return parent.cget("bg")
        except Exception:
            pass

        try:
            style = ttk.Style(parent)
            style_candidates = []
            try:
                st = str(parent.cget("style") or "").strip()
                if st:
                    style_candidates.append(st)
            except Exception:
                pass
            try:
                cls = str(parent.winfo_class() or "").strip()
                if cls:
                    style_candidates.append(cls)
            except Exception:
                pass
            style_candidates.extend(["TFrame", "."])
            for name in style_candidates:
                try:
                    bg = style.lookup(name, "background")
                except Exception:
                    bg = ""
                if bg:
                    return bg
        except Exception:
            pass
        return fallback

    def _current_theme(self):
        theme = _get_effective_theme(_is_dark_mode_active())
        parent_bg = self._resolve_parent_bg(theme["bg"])
        return theme, parent_bg, parent_bg

    def _apply_cell_visual(self, cell):
        theme, _parent_bg, _grid_bg = self._current_theme()
        if cell.revealed:
            base = CELL_COLORS["empty"]
            relief = tk.SUNKEN
            state = tk.DISABLED
        elif cell.flagged:
            base = CELL_COLORS["flagged"]
            relief = tk.RAISED
            state = tk.NORMAL
        else:
            base = CELL_COLORS["default"]
            relief = tk.RAISED
            state = tk.NORMAL

        try:
            cell.btn.config(
                bg=base,
                activebackground=base,
                fg=theme["fg"],
                activeforeground=theme["fg"],
                disabledforeground=theme["fg"],
                highlightthickness=0,
                highlightbackground=base,
                highlightcolor=base,
                bd=2,
                borderwidth=2,
                relief=relief,
                state=state,
            )
        except Exception:
            pass

    def apply_theme(self):
        _theme, parent_bg, _grid_bg = self._current_theme()
        try:
            self.root.config(bg=parent_bg)
        except Exception:
            pass
        try:
            self.title_label.config(bg=parent_bg)
        except Exception:
            pass
        try:
            self.frame.config(bg=parent_bg)
        except Exception:
            pass
        try:
            for row in self.cells:
                for cell in row:
                    self._apply_cell_visual(cell)
        except Exception:
            pass

    def update_title(self):
        if self.data["has_gold"] and self.data["has_silver"] and self.data["has_bronze"]:
            text, color = LEVELS[3]["title"], LEVEL_COLORS[3]
        elif self.data["has_silver"] and self.data["has_bronze"]:
            text, color = LEVELS[2]["title"], LEVEL_COLORS[2]
        elif self.data["has_bronze"]:
            text, color = LEVELS[1]["title"], LEVEL_COLORS[1]
        else:
            text, color = "", "black"
        self.data["title"] = text
        self.title_label.config(text=text, fg=color)
        # Persist updated title so config stays in sync
        try:
            save_progress(self.data)
        except Exception:
            pass

    def start_level(self):
        self.size, self.mines = LEVELS[self.level]["size"], LEVELS[self.level]["mines"]
        self.first_click = True
        self.update_title()

        for widget in self.frame.winfo_children():
            widget.destroy()

        theme = _get_effective_theme(_is_dark_mode_active())
        try:
            self.frame.config(bg=self._resolve_parent_bg(theme["bg"]))
        except Exception:
            pass
        self.cells, self.mine_locations = [], set()
        for r in range(self.size):
            row = []
            for c in range(self.size):
                btn = tk.Button(
                    self.frame, width=2, height=1, font=("Arial", 12),
                    bg=CELL_COLORS["default"], activebackground=CELL_COLORS["default"],
                    fg=theme["fg"], activeforeground=theme["fg"],
                    disabledforeground=theme["fg"],
                    bd=2, borderwidth=2, relief=tk.RAISED, highlightthickness=0,
                    highlightbackground=CELL_COLORS["default"],
                    highlightcolor=CELL_COLORS["default"],
                    takefocus=0,
                    command=lambda r=r, c=c: self.reveal(r, c)
                )
                # Cross-platform right-click support
                btn.bind("<Button-3>", lambda e, r=r, c=c: self.toggle_flag(r, c))
                btn.bind("<Button-2>", lambda e, r=r, c=c: self.toggle_flag(r, c))
                btn.grid(row=r, column=c)
                row.append(Cell(r, c, btn))
            self.cells.append(row)
        self.apply_theme()

    def place_mines(self, safe_r, safe_c):
        exclude = {(safe_r + dr, safe_c + dc) for dr in (-1, 0, 1) for dc in (-1, 0, 1)}
        available = [(r, c) for r in range(self.size) for c in range(self.size) if (r, c) not in exclude]
        if len(available) < self.mines:
            raise ValueError("Not enough space to place mines!")
        chosen = random.sample(available, self.mines)
        for r, c in chosen:
            self.cells[r][c].has_mine = True
            self.mine_locations.add((r, c))

    def reveal(self, r, c):
        cell = self.cells[r][c]
        if cell.flagged or cell.revealed:
            return
        if self.first_click:
            self.place_mines(r, c)
            self.first_click = False
        if cell.has_mine:
            show_info("Boom!", "You hit a mine! Restarting level...")
            return self.start_level()

        self._reveal_recursive(r, c)
        if self.check_win():
            self.win_level()

    def _reveal_recursive(self, r, c):
        if not (0 <= r < self.size and 0 <= c < self.size): return
        cell = self.cells[r][c]
        if cell.revealed or cell.flagged: return

        cell.revealed = True
        self._apply_cell_visual(cell)
        count = self.adjacent_mines(r, c)
        if count: cell.btn.config(text=str(count))
        else:
            for dr in (-1, 0, 1):
                for dc in (-1, 0, 1):
                    if dr or dc: self._reveal_recursive(r+dr, c+dc)

    def toggle_flag(self, r, c):
        cell = self.cells[r][c]
        if cell.revealed: return
        cell.flagged = not cell.flagged
        if cell.flagged:
            cell.btn.config(text=EMOJI_FLAG)
        else:
            cell.btn.config(text="")
        self._apply_cell_visual(cell)

    def adjacent_mines(self, r, c):
        return sum(
            1 for dr in (-1, 0, 1) for dc in (-1, 0, 1)
            if (dr or dc) and 0 <= r+dr < self.size and 0 <= c+dc < self.size
            and self.cells[r+dr][c+dc].has_mine
        )

    def check_win(self):
        return all(cell.revealed or cell.has_mine for row in self.cells for cell in row)

    def win_level(self):
        if self.level == 1:
            self.data["has_bronze"] = True
            self.level = 2
        elif self.level == 2:
            self.data["has_silver"] = True
            self.level = 3
        elif self.level == 3:
            self.data["has_gold"] = True
            # After gold, reset to level 1 for replay
            self.level = 1
        self.data["level"] = self.level
        save_progress(self.data)
        self.start_level()
MINESWEEPER_AVAILABLE = True

# -----------------------------------------------------------------------------
# END SECTION: Minesweeper Mini-Game (Settings tab)
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Binary Utilities (Fog Tool)
# Used In: Fog Tool tab -> FogToolApp (fog file encoding)
# =============================================================================
class BitWriter:
    def __init__(self):
        self.cur = 0
        self.bitpos = 0
        self.bytes = bytearray()

    def write_bit(self, b):
        if b:
            self.cur |= (1 << self.bitpos)
        self.bitpos += 1
        if self.bitpos == 8:
            self.bytes.append(self.cur)
            self.cur = 0
            self.bitpos = 0

    def write_bits(self, val, n):
        for i in range(n):
            self.write_bit((val >> i) & 1)

    def align_byte(self):
        while self.bitpos != 0:
            self.write_bit(0)

    def get_bytes(self):
        if self.bitpos != 0:
            self.bytes.append(self.cur)
            self.cur = 0
            self.bitpos = 0
        return bytes(self.bytes)

# -----------------------------------------------------------------------------
# END SECTION: Binary Utilities (Fog Tool)
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Save-Path Discovery (Fog Tool + Save File tab)
# Used In: FogToolApp and launch_gui startup
# =============================================================================
def load_editor_last_path():
    """Load last used save path from config and return the folder."""
    try:
        full_path = load_last_path()
        if full_path:
            return os.path.dirname(full_path)
    except Exception:
        pass
    return None

def load_initial_path():
    """Priority:
      1) config last_save_path (if exists and points to existing folder)
      2) config fogtool_last_dir (if exists)
      3) legacy last_dir.txt (in tool folder)
      3) os.getcwd()
    """
    # 1) SnowRunner editor path first (config-based)
    editor_path = load_editor_last_path()
    if editor_path and os.path.isdir(editor_path):
        return editor_path

    # 2) FogTool last dir from config
    try:
        cfg = _load_config_safe()
        ld = cfg.get("fogtool_last_dir", "")
        if ld and os.path.isdir(ld):
            return ld
    except Exception:
        pass

    # 3) Legacy last_dir.txt (migrate if possible)
    last_dir_file = resource_path("last_dir.txt")
    if os.path.exists(last_dir_file):
        try:
            with open(last_dir_file, "r", encoding="utf-8") as f:
                ld = f.read().strip()
            if ld and os.path.isdir(ld):
                _update_config_values({"fogtool_last_dir": ld})
                try:
                    os.remove(last_dir_file)
                except Exception:
                    pass
                return ld
        except Exception:
            pass

    # 4) Fallback
    return os.getcwd()

# -----------------------------------------------------------------------------
# END SECTION: Save-Path Discovery (Fog Tool + Save File tab)
# -----------------------------------------------------------------------------
# =============================================================================
# SECTION: Fog Tool (Editor + Automation UI)
# Used In: Fog Tool tab -> FogToolFrame
# =============================================================================
class FogToolApp(ttk.Frame):
    def __init__(self, master=None, initial_save_dir=None):
        # Resolve initial path according to priority
        if not initial_save_dir:
            initial_save_dir = load_initial_path()

        # save_dir: the folder where fog files live
        self.save_dir = initial_save_dir
        # last_dir: used for file dialogs; keep in sync with save_dir
        self.last_dir = initial_save_dir
        # file to persist FogTool's last dir
        self.last_dir_file = resource_path("last_dir.txt")

        super().__init__(master)

        # Editor state
        self.cfg_path = None
        self.file_ext = None
        self.decomp_bytes = None
        self.current_image_L = None  # bytearray grayscale pixels (editor orientation)
        self.current_image_size = (0, 0)  # (width, height)
        self.footer = b""
        self.scale = 1.0
        self.offset_x = 0
        self.offset_y = 0
        self.brush_gray = 1
        self.brush_size = 4
        self._brush_mask_cache = {}
        self.drawing = False
        self.last_x = None
        self.last_y = None

        # Overlay state (RGBA)
        self.overlay_img = None  # {"size": (w, h), "rgba": bytearray}
        self.overlay_scale = 1.0
        self.overlay_offset = (0, 0)   # in fog-image pixels (editor orientation)
        self.dragging_overlay = False
        self.last_drag = (0, 0)

        # Preview cache/throttle state (keeps drag/zoom responsive)
        self._preview_after_id = None
        self._base_preview_rgb = None
        self._base_preview_key = None
        self._base_preview_dirty = True

        # Automation state
        self.slot_var = None
        self.auto_status_var = None
        self.per_season_var = None
        self.season_checks = {}
        self.extra_season_var = None

        # Notebook with Editor + Automation
        self.notebook = ttk.Notebook(self)
        # Clicking tabs sometimes gives them keyboard focus which some themes draw as a dotted ring.
        # Prefer a non-destructive approach: explicitly tell this notebook instance not to take focus,
        # and bind a focus-return handler once the editor frame exists.
        try:
            # Explicitly configure the notebook instance (option_add may not affect existing widgets)
            try:
                self.notebook.configure(takefocus=0)
            except Exception:
                pass

            # Use ButtonRelease + after_idle later (after editor_frame exists) to return focus to the content.
            # We'll (re)bind after the editor_frame is added below.
            def _return_focus_after_click(e):
                try:
                    self.notebook.after_idle(lambda: (self.editor_frame.focus_set() if hasattr(self, 'editor_frame') else self.focus_set()))
                except Exception:
                    try:
                        (self.editor_frame.focus_set() if hasattr(self, 'editor_frame') else self.focus_set())
                    except Exception:
                        pass

            # temporary bind now (safe even if editor_frame isn't present yet)
            try:
                self.notebook.bind('<ButtonRelease-1>', _return_focus_after_click, add='+')
            except Exception:
                pass
        except Exception:
            pass
        self.notebook.pack(fill="both", expand=True)

        self.editor_frame = ttk.Frame(self.notebook)
        self._build_editor_ui(self.editor_frame)
        self.notebook.add(self.editor_frame, text="Editor")
        # Re-bind Notebook release to focus editor_frame explicitly now that it exists.
        try:
            self.notebook.bind('<ButtonRelease-1>', lambda e: self.notebook.after_idle(self.editor_frame.focus_set), add='+')
        except Exception:
            pass

        self.automation_frame = ttk.Frame(self.notebook)
        self._build_automation_ui(self.automation_frame)
        self.notebook.add(self.automation_frame, text="Automation")

    # ---------- Helpers for saving paths ----------
    def _update_last_paths(self, folder_path):
        """Persist FogTool last directory and editor save path into config."""
        try:
            # write a representative path to CompleteSave.cfg inside the folder
            example_savefile = os.path.join(folder_path, "CompleteSave.cfg")
            _update_config_values({
                "fogtool_last_dir": folder_path,
                "last_save_path": example_savefile
            })
        except Exception:
            pass

    # ---------------- UI BUILD ----------------
    def _build_editor_ui(self, parent):
        top = ttk.Frame(parent)
        top.pack(fill="x")
        ttk.Button(top, text="Open .cfg/.dat", command=self.open_cfg).pack(side="left", padx=4)
        ttk.Button(top, text="Save", command=lambda: (make_backup_if_enabled(self.cfg_path) if self.cfg_path else None, self.save_back())).pack(side="left", padx=4)
        ttk.Label(top, text="Brush:").pack(side="left", padx=6)
        ttk.Button(top, text="Black", command=lambda: self.set_color_hex("#000101")).pack(side="left")
        ttk.Button(top, text="Gray", command=lambda: self.set_color_hex("#808080")).pack(side="left")
        ttk.Button(top, text="White", command=lambda: self.set_color_hex("#FFFFFF")).pack(side="left")
        ttk.Label(top, text="Size:").pack(side="left", padx=6)
        self.size_var = tk.IntVar(value=4)
        cb = ttk.Combobox(top, textvariable=self.size_var, values=[2,4,8,16,32,64,128], state="readonly", width=5)
        cb.pack(side="left")
        cb.bind("<<ComboboxSelected>>", lambda e: self.set_brush_size(self.size_var.get()))
        # overlay controls
        ttk.Button(top, text="Load Overlay Image", command=self.load_overlay).pack(side="left", padx=6)
        ttk.Button(top, text="Apply Overlay", command=self.apply_overlay).pack(side="left", padx=2)
        ttk.Button(top, text="Clear Overlay", command=self.clear_overlay).pack(side="left", padx=2)
        ttk.Button(top, text="Tutorial / Info", command=self.show_info).pack(side="right", padx=6)

        # status + canvas
        self.status = tk.StringVar(value="Ready")
        ttk.Label(parent, textvariable=self.status).pack(fill="x")
        fog_bg = _get_effective_theme().get("fog_bg", _theme_color_literal("#d4bf98", role="bg"))
        self.canvas = tk.Canvas(parent, bg=fog_bg)
        try:
            self.canvas._theme_bg_key = "fog_bg"
        except Exception:
            pass
        self.canvas.pack(fill="both", expand=True)
        self.canvas.bind("<Configure>", lambda e: self._schedule_preview_render(base_dirty=True))

        # painting (left mouse)
        self.canvas.bind("<ButtonPress-1>", self.start_draw)
        self.canvas.bind("<B1-Motion>", self.draw)
        self.canvas.bind("<ButtonRelease-1>", self.stop_draw)

        # overlay drag with right mouse
        self.canvas.bind("<ButtonPress-3>", self.start_overlay_drag)
        self.canvas.bind("<B3-Motion>", self.do_overlay_drag)
        self.canvas.bind("<ButtonRelease-3>", self.stop_overlay_drag)
        # macOS often reports secondary click as Button-2
        self.canvas.bind("<ButtonPress-2>", self.start_overlay_drag)
        self.canvas.bind("<B2-Motion>", self.do_overlay_drag)
        self.canvas.bind("<ButtonRelease-2>", self.stop_overlay_drag)

        # cross-platform mouse wheel zoom for overlay
        self.canvas.bind("<MouseWheel>", self.overlay_zoom)  # Windows & macOS (delta)
        # Linux and some macOS systems:
        self.canvas.bind("<Button-4>", lambda e: self.overlay_zoom(type("E", (), {"delta": 120})()))
        self.canvas.bind("<Button-5>", lambda e: self.overlay_zoom(type("E", (), {"delta": -120})()))

    def _build_automation_ui(self, parent):
        top = ttk.Frame(parent)
        top.pack(fill="x", pady=6)
        ttk.Button(top, text="Select Save Folder", command=self.automation_select_folder).pack(side="left", padx=4)
        ttk.Label(top, text="Save Slot:").pack(side="left", padx=6)
        self.slot_var = tk.StringVar(value="1")
        slot_cb = ttk.Combobox(top, textvariable=self.slot_var, values=["1","2","3","4"], state="readonly", width=5)
        slot_cb.pack(side="left")
        ttk.Button(top, text="Cover All", command=lambda: self.automation_apply("cover")).pack(side="left", padx=10)
        ttk.Button(top, text="Uncover All", command=lambda: self.automation_apply("uncover")).pack(side="left", padx=4)

        self.per_season_var = tk.IntVar(value=0)
        per_season_chk = ttk.Checkbutton(top, text="Automation per season", variable=self.per_season_var, command=self._toggle_season_checks)
        per_season_chk.pack(side="left", padx=12)

        self.season_frame = ttk.Frame(parent)
        seasons = ALL_REGION_CODE_LABELS
        for code, name in seasons:
            v = tk.IntVar(value=0)
            ttk.Checkbutton(self.season_frame, text=name, variable=v).pack(anchor="w")
            self.season_checks[code] = v

        ttk.Label(self.season_frame, text="Other Season number (e.g., 18, 19, 20):").pack(anchor="w")
        self.extra_season_var = tk.StringVar()
        ttk.Entry(self.season_frame, textvariable=self.extra_season_var).pack(anchor="w", fill="x")

        # Show the currently chosen save folder (derived at startup or selected later)
        self.auto_status_var = tk.StringVar(value=f"Save folder (auto): {self.save_dir}")
        ttk.Label(parent, textvariable=self.auto_status_var).pack(fill="x", pady=6)

    # ---------------- Info popup ----------------
    def show_info(self):
        season_map_lines = [f"- {code} → {name}  " for code, name in ALL_REGION_CODE_LABELS]
        season_map_text = "\n".join(season_map_lines)

        info_text = f"""Fog Image Tool — Tutorial

Sorry for the wall of text — but this guide should answer most questions :)

Overview
---------
The Fog Image Tool lets you edit SnowRunner fog maps directly from your save files.  
It has two main parts:
- Editor Tab → Fine-tune each fog map manually or create artistic custom maps.  
- Automation Tab → Quickly cover or uncover entire maps, regions, or seasons.
- Fog maps are automatically aligned with the camera’s default position on the map, so what you create in the editor is exactly what you’ll see in-game

Where to find files
--------------------
- Fog files are stored in your save folder.  
- File names look like: `fog_level_*.cfg` (Steam) or `fog_level_*.dat` (Epic).  

Save slot meaning:
- `fog_level...`   → Save Slot 1  
- `1_fog_level...` → Save Slot 2  
- `2_fog_level...` → Save Slot 3  
- `3_fog_level...` → Save Slot 4  

Map IDs:
- The part after `fog_level_` tells you which map it belongs to.  
- Example: `_us_01_01` → US region, first map of region 01.  

Note about missing fog maps:
- Some fog maps only exist after you visit the map in-game.  
- If a map hasn’t been visited, its fog file won’t appear until you drive there.  
- Usually, the first map(s) of a season are present by default; others may require visiting first.  

Editor Tab
-----------
Step 1: Open a fog file 
- Click Open .cfg/.dat and select the fog map you want to edit.  

Step 2: Choose a brush  
- Black → Makes that part of the map hidden.  
- Gray → Revealed but grayed-out (semi-hidden).  
- White → Fully revealed in color.  

Step 3: Brush size & painting  
- Pick a brush size and hold Left Mouse Button to paint.  

Step 4: Overlay an image (optional)  
- Click Load Overlay Image to place an image over the fog map.  
- Supported formats: PNG, GIF, PPM, PGM.  
- Any resolution/proportion works (square, rectangle, etc.).
          -Big PNGs will lag it 
- Colors are automatically reduced to black, gray, and white:  
  - good for simple few colors images.  
  - worse for many close colored images - may blur into blobs.
          - Tip: Run the image through ChatGPT to redraw it in 3 colors before importing.  

Overlay controls:
- Right-Click + drag → Move overlay.  
- Scroll Wheel → Zoom overlay.  
- Apply Overlay → Burn the PNG onto the fog map.  
- Clear Overlay → Remove the overlay without applying.  

Step 5: Save your work  
- Click Save to update the fog file with your edits.  

Automation Tab
---------------
The Automation Tab is for fast bulk edits without painting manually.

Step 1: Select save folder  
- Auto-detected if you’ve used the Main Editor.  
- If not, point it to your save’s remote folder (where all fog files are stored).

Note:  
Both the Editor and Automation tabs share paths. Once you set the save folder in one, the other will use it automatically. 

Step 2: Pick save slot  
- Choose which save slot to modify (1–4).  

Step 3: Choose action 
- Cover All → Makes all maps hidden (black).  
- Uncover All → Makes all maps fully revealed (colored).  
- Per Season/Region → Shows checkboxes so you can pick only certain seasons/regions to affect.  

Season / Map Reference
-----------------------
{season_map_text}
"""
        win = _create_themed_toplevel(self)
        win.title("Tutorial / Info")
        win.geometry("700x600")
        text = tk.Text(win, wrap="word")
        text.insert("1.0", info_text)
        text.config(state="disabled")
        text.pack(fill="both", expand=True)
        scroll = ttk.Scrollbar(win, orient="vertical", command=text.yview)
        text.config(yscrollcommand=scroll.set)
        scroll.pack(side="right", fill="y")

    # ---------------- Helpers ----------------
    def log(self, s):
        self.status.set(s)
        self.update_idletasks()

    def set_color_hex(self, hx):
        mapping = {"#000101": 1, "#808080": 128, "#FFFFFF": 255}
        self.brush_gray = mapping.get(hx.upper(), self.hex_to_gray(hx))
        self.log(f"Brush color {self.brush_gray}")

    def set_brush_size(self, s):
        self.brush_size = int(s)
        self.log(f"Brush size {s}")

    def hex_to_gray(self, hx):
        hx = hx.lstrip("#")
        r = int(hx[0:2], 16); g = int(hx[2:4], 16); b = int(hx[4:6], 16)
        return int(round((r + g + b) / 3))

    def _flip_vertical_gray(self, pix: bytes | bytearray, w: int, h: int) -> bytearray:
        """Return a vertically flipped grayscale buffer."""
        out = bytearray(len(pix))
        row = w
        for y in range(h):
            src = (h - 1 - y) * row
            dst = y * row
            out[dst:dst + row] = pix[src:src + row]
        return out

    def _get_brush_offsets(self, size: int):
        radius = max(1, int(size // 2))
        cached = self._brush_mask_cache.get(radius)
        if cached is not None:
            return cached
        r2 = radius * radius
        offsets = []
        for dy in range(-radius, radius + 1):
            for dx in range(-radius, radius + 1):
                if dx * dx + dy * dy <= r2:
                    offsets.append((dx, dy))
        self._brush_mask_cache[radius] = offsets
        return offsets

    def _invalidate_base_preview(self):
        self._base_preview_dirty = True
        self._base_preview_key = None
        self._base_preview_rgb = None

    def _schedule_preview_render(self, base_dirty: bool = False, immediate: bool = False):
        if base_dirty:
            self._invalidate_base_preview()
        if immediate:
            if self._preview_after_id is not None:
                try:
                    self.after_cancel(self._preview_after_id)
                except Exception:
                    pass
                self._preview_after_id = None
            self.show_preview()
            return
        if self._preview_after_id is None:
            try:
                self._preview_after_id = self.after(16, self._flush_scheduled_preview)
            except Exception:
                self._preview_after_id = None

    def _flush_scheduled_preview(self):
        self._preview_after_id = None
        self.show_preview()

    def _tk_color_to_rgb(self, color):
        if isinstance(color, (tuple, list)) and len(color) >= 3:
            try:
                return int(color[0]), int(color[1]), int(color[2])
            except Exception:
                pass
        if isinstance(color, str):
            c = color.strip()
            if c.startswith("#") and len(c) == 7:
                try:
                    return int(c[1:3], 16), int(c[3:5], 16), int(c[5:7], 16)
                except Exception:
                    pass
            if c.startswith("#") and len(c) == 4:
                try:
                    return int(c[1] * 2, 16), int(c[2] * 2, 16), int(c[3] * 2, 16)
                except Exception:
                    pass
            try:
                r16, g16, b16 = self.winfo_rgb(c)
                return r16 // 257, g16 // 257, b16 // 257
            except Exception:
                pass
        return 0, 0, 0

    def _parse_p6_ppm_rgb(self, raw: bytes):
        """Parse binary PPM (P6) bytes and return (w, h, rgb_bytes)."""
        n = len(raw)
        i = 0
        tokens = []
        while len(tokens) < 4 and i < n:
            while i < n and raw[i] in b" \t\r\n":
                i += 1
            if i >= n:
                break
            if raw[i] == 35:  # '#'
                while i < n and raw[i] not in b"\r\n":
                    i += 1
                continue
            j = i
            while j < n and raw[j] not in b" \t\r\n":
                j += 1
            tokens.append(raw[i:j])
            i = j
        if len(tokens) < 4:
            raise ValueError("Invalid PPM header")
        if tokens[0] != b"P6":
            raise ValueError("Unsupported PPM format (expected P6)")
        w = int(tokens[1])
        h = int(tokens[2])
        maxv = int(tokens[3])
        if w <= 0 or h <= 0 or maxv <= 0 or maxv > 255:
            raise ValueError("Invalid PPM dimensions or max value")
        while i < n and raw[i] in b" \t\r\n":
            i += 1
        need = w * h * 3
        rgb = raw[i:i + need]
        if len(rgb) < need:
            raise ValueError("PPM payload is truncated")
        return w, h, bytes(rgb)

    def _load_overlay_rgba(self, path):
        img = PhotoImage(file=path)
        w = int(img.width())
        h = int(img.height())
        if w <= 0 or h <= 0:
            raise ValueError("Overlay has invalid dimensions")

        rgba = None
        # Fast path: export via Tk in one shot, parse PPM payload, then expand to RGBA.
        # This avoids millions of per-pixel Tcl roundtrips from PhotoImage.get().
        tmp_path = None
        try:
            with tempfile.NamedTemporaryFile(delete=False, suffix=".ppm") as tmp:
                tmp_path = tmp.name
            img.write(tmp_path, format="ppm")
            with open(tmp_path, "rb") as f:
                raw_ppm = f.read()
            pw, ph, rgb = self._parse_p6_ppm_rgb(raw_ppm)
            if pw != w or ph != h:
                w, h = pw, ph
            px_count = w * h
            rgba = bytearray(px_count * 4)
            rgba[0::4] = rgb[0::3]
            rgba[1::4] = rgb[1::3]
            rgba[2::4] = rgb[2::3]
            rgba[3::4] = b"\xFF" * px_count
        except Exception:
            rgba = None
        finally:
            if tmp_path and os.path.exists(tmp_path):
                try:
                    os.remove(tmp_path)
                except Exception:
                    pass

        # Safe fallback for unusual Tk builds/formats.
        if rgba is None:
            rgba = bytearray(w * h * 4)
            for y in range(h):
                for x in range(w):
                    r, g, b = self._tk_color_to_rgb(img.get(x, y))
                    idx = (y * w + x) * 4
                    rgba[idx] = r
                    rgba[idx + 1] = g
                    rgba[idx + 2] = b
                    rgba[idx + 3] = 255

        # Optional binary transparency mask on smaller images.
        # For large overlays this scan is intentionally skipped for responsiveness.
        px_count = w * h
        if hasattr(img, "transparency_get") and px_count <= 350000:
            try:
                for y in range(h):
                    row = y * w
                    for x in range(w):
                        if img.transparency_get(x, y):
                            rgba[(row + x) * 4 + 3] = 0
            except Exception:
                pass

        return {"size": (w, h), "rgba": rgba}

    def _render_base_preview_rgb(self, sw: int, sh: int, scale: float) -> bytearray:
        iw, ih = self.current_image_size
        src = self.current_image_L
        x_map = [min(iw - 1, int(x / scale)) for x in range(sw)]
        y_map = [min(ih - 1, int(y / scale)) for y in range(sh)]
        rgb = bytearray(sw * sh * 3)

        di = 0
        for sy in y_map:
            row = sy * iw
            for sx in x_map:
                gray = src[row + sx]
                rgb[di] = gray
                rgb[di + 1] = gray
                rgb[di + 2] = gray
                di += 3
        return rgb

    def _blend_overlay_into_rgb(self, rgb: bytearray, sw: int, sh: int, scale: float):
        overlay = self.overlay_img if isinstance(self.overlay_img, dict) else None
        if not overlay:
            return
        ow, oh = overlay.get("size", (0, 0))
        opix = overlay.get("rgba", b"")
        if ow <= 0 or oh <= 0 or not opix:
            return

        oscale = max(0.0001, float(self.overlay_scale))
        ox, oy = self.overlay_offset

        left = max(0, int(math.floor(ox * scale)))
        top = max(0, int(math.floor(oy * scale)))
        right = min(sw, int(math.ceil((ox + ow * oscale) * scale)))
        bottom = min(sh, int(math.ceil((oy + oh * oscale) * scale)))
        if left >= right or top >= bottom:
            return

        area = (right - left) * (bottom - top)
        bilinear = (not self.dragging_overlay) and area <= 1200000
        inv_scale = 1.0 / scale
        inv_oscale = 1.0 / oscale

        if bilinear:
            x_meta = []
            for px in range(left, right):
                fx = (((px + 0.5) * inv_scale) - ox) * inv_oscale - 0.5
                x0 = int(math.floor(fx))
                tx = fx - x0
                if x0 < 0:
                    x0 = 0
                    x1 = 0
                    tx = 0.0
                elif x0 >= ow - 1:
                    x0 = ow - 1
                    x1 = x0
                    tx = 0.0
                else:
                    x1 = x0 + 1
                x_meta.append((x0, x1, tx))

            for py in range(top, bottom):
                fy = (((py + 0.5) * inv_scale) - oy) * inv_oscale - 0.5
                y0 = int(math.floor(fy))
                ty = fy - y0
                if y0 < 0:
                    y0 = 0
                    y1 = 0
                    ty = 0.0
                elif y0 >= oh - 1:
                    y0 = oh - 1
                    y1 = y0
                    ty = 0.0
                else:
                    y1 = y0 + 1

                row00 = y0 * ow * 4
                row10 = y1 * ow * 4
                out_i = (py * sw + left) * 3
                for x0, x1, tx in x_meta:
                    i00 = row00 + x0 * 4
                    i01 = row00 + x1 * 4
                    i10 = row10 + x0 * 4
                    i11 = row10 + x1 * 4

                    w00 = (1.0 - tx) * (1.0 - ty)
                    w01 = tx * (1.0 - ty)
                    w10 = (1.0 - tx) * ty
                    w11 = tx * ty

                    a = int(
                        opix[i00 + 3] * w00
                        + opix[i01 + 3] * w01
                        + opix[i10 + 3] * w10
                        + opix[i11 + 3] * w11
                    )
                    if a > 0:
                        r = int(opix[i00] * w00 + opix[i01] * w01 + opix[i10] * w10 + opix[i11] * w11)
                        g = int(opix[i00 + 1] * w00 + opix[i01 + 1] * w01 + opix[i10 + 1] * w10 + opix[i11 + 1] * w11)
                        b = int(opix[i00 + 2] * w00 + opix[i01 + 2] * w01 + opix[i10 + 2] * w10 + opix[i11 + 2] * w11)
                        if a >= 255:
                            rgb[out_i] = r
                            rgb[out_i + 1] = g
                            rgb[out_i + 2] = b
                        else:
                            inv = 255 - a
                            rgb[out_i] = (r * a + rgb[out_i] * inv) // 255
                            rgb[out_i + 1] = (g * a + rgb[out_i + 1] * inv) // 255
                            rgb[out_i + 2] = (b * a + rgb[out_i + 2] * inv) // 255
                    out_i += 3
            return

        x_src = []
        for px in range(left, right):
            sx = int((((px + 0.5) * inv_scale) - ox) * inv_oscale)
            if 0 <= sx < ow:
                x_src.append(sx)
            else:
                x_src.append(-1)

        for py in range(top, bottom):
            sy = int((((py + 0.5) * inv_scale) - oy) * inv_oscale)
            if sy < 0 or sy >= oh:
                continue
            src_row = sy * ow * 4
            out_i = (py * sw + left) * 3
            for sx in x_src:
                if sx >= 0:
                    si = src_row + sx * 4
                    a = opix[si + 3]
                    if a:
                        if a >= 255:
                            rgb[out_i] = opix[si]
                            rgb[out_i + 1] = opix[si + 1]
                            rgb[out_i + 2] = opix[si + 2]
                        else:
                            inv = 255 - a
                            rgb[out_i] = (opix[si] * a + rgb[out_i] * inv) // 255
                            rgb[out_i + 1] = (opix[si + 1] * a + rgb[out_i + 1] * inv) // 255
                            rgb[out_i + 2] = (opix[si + 2] * a + rgb[out_i + 2] * inv) // 255
                out_i += 3

    def _photo_from_rgb(self, rgb: bytes | bytearray, w: int, h: int):
        header = f"P6 {w} {h} 255\n".encode("ascii")
        return PhotoImage(data=header + bytes(rgb), format="PPM")

    # ---------------- Editor functions ----------------
    def open_cfg(self):
        # Use last_dir for the file dialog
        startdir = self.last_dir if self.last_dir and os.path.isdir(self.last_dir) else os.getcwd()
        path = filedialog.askopenfilename(initialdir=startdir, filetypes=[("CFG/DAT files", "*.cfg *.dat"), ("All", "*.*")])
        if not path:
            return

        # persist last dir & sync both files
        self.last_dir = os.path.dirname(path)
        self.save_dir = self.last_dir
        self._update_last_paths(self.last_dir)
        try:
            self.auto_status_var.set(f"Save folder (auto): {self.save_dir}")
        except:
            pass

        self.cfg_path = path
        _, ext = os.path.splitext(path)
        self.file_ext = ext.lower()
        data = open(path, "rb").read()

        # find zlib stream candidate(s)
        candidates = [i for i, b in enumerate(data) if b == 0x78]
        found = False
        dec = None
        for z_off in candidates:
            try:
                dobj = zlib.decompressobj()
                dec_local = dobj.decompress(data[z_off:])
                # require minimum length (8 bytes for width+height)
                if dec_local is not None and len(dec_local) >= 8:
                    comp_raw = data[z_off: z_off + len(data[z_off:]) - len(dobj.unused_data)]
                    if len(comp_raw) >= 6:
                        dec = dec_local
                        found = True
                        break
            except:
                continue
        if not found:
            messagebox.showerror("Error", "Could not find zlib stream in file")
            return

        try:
            self.decomp_bytes = bytearray(dec)
            w = struct.unpack_from("<I", self.decomp_bytes, 0)[0]
            h = struct.unpack_from("<I", self.decomp_bytes, 4)[0]
            expected = 8 + w * h
            if w <= 0 or h <= 0 or len(self.decomp_bytes) < expected:
                raise ValueError(f"Invalid dimensions {w}x{h}")
            pix = bytes(self.decomp_bytes[8:8 + w * h])
            self.footer = bytes(self.decomp_bytes[8 + w * h:])
            # vertical flip in editor to match in-game orientation
            self.current_image_L = self._flip_vertical_gray(pix, w, h)
            self.current_image_size = (w, h)

            # If overlay is loaded, center it by default on load
            if self.overlay_img:
                iw, ih = self.current_image_size
                ow, oh = self.overlay_img.get("size", (0, 0))
                # center overlay in image coordinates
                self.overlay_offset = (max(0, (iw - int(ow * self.overlay_scale)) // 2),
                                       max(0, (ih - int(oh * self.overlay_scale)) // 2))

            self.log(f"Loaded {os.path.basename(path)} — {w}x{h}")
            self._schedule_preview_render(base_dirty=True, immediate=True)
        except Exception as e:
            with open(self.cfg_path + ".decode_debug.log", "a", encoding="utf-8") as f:
                f.write("Open parse error:\n")
                f.write(repr(e) + "\n")
                f.write(traceback.format_exc() + "\n")
            messagebox.showerror("Error parsing payload", str(e))

    def show_preview(self):
        if not self.current_image_L:
            return
        cw = self.canvas.winfo_width(); ch = self.canvas.winfo_height()
        iw, ih = self.current_image_size
        if cw <= 0 or ch <= 0:
            return
        scale = min(cw / iw, ch / ih)
        self.scale = scale
        self.offset_x = (cw - iw * scale) / 2
        self.offset_y = (ch - ih * scale) / 2

        sw = max(1, int(iw * scale))
        sh = max(1, int(ih * scale))
        base_key = (iw, ih, sw, sh, round(scale, 6))
        if self._base_preview_dirty or self._base_preview_rgb is None or self._base_preview_key != base_key:
            self._base_preview_rgb = self._render_base_preview_rgb(sw, sh, scale)
            self._base_preview_key = base_key
            self._base_preview_dirty = False

        if self.overlay_img:
            preview_rgb = bytearray(self._base_preview_rgb)
            self._blend_overlay_into_rgb(preview_rgb, sw, sh, scale)
        else:
            preview_rgb = self._base_preview_rgb
        self.tk_preview = self._photo_from_rgb(preview_rgb, sw, sh)
        self.canvas.delete("all")
        fog_bg = _get_effective_theme().get("fog_bg", _theme_color_literal("#d4bf98", role="bg"))
        self.canvas.create_rectangle(0, 0, cw, ch, fill=fog_bg, outline="")
        self.canvas.create_image(self.offset_x, self.offset_y, anchor="nw", image=self.tk_preview)

    def img_coords(self, x, y):
        # convert canvas coords to image (editor) coords
        return int((x - self.offset_x) / self.scale), int((y - self.offset_y) / self.scale)

    def start_draw(self, e):
        if not self.current_image_L:
            return
        self.drawing = True
        self.last_x, self.last_y = self.img_coords(e.x, e.y)

    def draw(self, e):
        if not self.drawing or not self.current_image_L:
            return
        x, y = self.img_coords(e.x, e.y)
        iw, ih = self.current_image_size
        x = max(0, min(iw - 1, x)); y = max(0, min(ih - 1, y))
        pix = self.current_image_L
        brush_offsets = self._get_brush_offsets(self.brush_size)
        x0, y0 = self.last_x, self.last_y
        dx, dy = x - x0, y - y0
        dist = max(1, int((dx * dx + dy * dy) ** 0.5))
        for i in range(dist + 1):
            xi = int(round(x0 + dx * (i / dist))); yi = int(round(y0 + dy * (i / dist)))
            for ox, oy in brush_offsets:
                tx = xi + ox
                ty = yi + oy
                if 0 <= tx < iw and 0 <= ty < ih:
                    pix[ty * iw + tx] = self.brush_gray
        self.last_x, self.last_y = x, y
        self._schedule_preview_render(base_dirty=True)

    def stop_draw(self, e):
        self.drawing = False
        self.last_x = self.last_y = None

    def save_back(self):
        if not self.cfg_path or not self.current_image_L:
            messagebox.showerror("Error", "Open a .cfg or .dat first")
            return

        # flip back vertically before saving (reverse of editor flip)
        w, h = self.current_image_size
        pix = bytes(self._flip_vertical_gray(self.current_image_L, w, h))
        payload = bytearray(struct.pack("<II", w, h) + pix + (self.footer or b""))

        try:
            self._write_stored_block_file(self.cfg_path, payload)
            self.log(f"Saved: {self.cfg_path}")
            show_info("Saved", f"Patched file:\n{self.cfg_path}")
            # Update stored last-paths to reflect successful save location
            if self.save_dir and os.path.isdir(self.save_dir):
                self._update_last_paths(self.save_dir)
        except Exception as e:
            with open(self.cfg_path + ".decode_debug.log", "a", encoding="utf-8") as f:
                f.write("Save error:\n"); f.write(repr(e) + "\n"); f.write(traceback.format_exc() + "\n")
            messagebox.showerror("Save error", str(e))

    def _write_stored_block_file(self, out_path, payload: bytes):
        """
        Replaces the zlib-wrapped deflate stream in out_path with a zlib stream
        that contains stored (uncompressed) deflate blocks so we preserve
        file sections outside the zlib stream.
        """
        data = open(out_path, "rb").read()
        candidates = [i for i, b in enumerate(data) if b == 0x78]
        z_off = None; zlib_header = None; unused = b""
        for cand in candidates:
            try:
                dobj = zlib.decompressobj()
                dec = dobj.decompress(data[cand:])
                comp_raw = data[cand: cand + len(data[cand:]) - len(dobj.unused_data)]
                if len(comp_raw) >= 6:
                    z_off = cand
                    zlib_header = comp_raw[:2]
                    unused = dobj.unused_data
                    break
            except:
                continue
        if z_off is None:
            raise RuntimeError("Zlib header not found while saving")

        # Build stored (uncompressed) deflate blocks
        max_chunk = 0xFFFF
        out_deflate = bytearray()
        writer = BitWriter()
        written = 0
        while written < len(payload):
            chunk = payload[written:written + max_chunk]
            written += len(chunk)
            bfinal = 1 if written >= len(payload) else 0
            writer.write_bits(bfinal, 1)
            writer.write_bits(0, 2)  # btype = 00 (stored)
            writer.align_byte()
            out_deflate.extend(writer.get_bytes())
            out_deflate.extend(struct.pack("<H", len(chunk)))
            out_deflate.extend(struct.pack("<H", 0xFFFF ^ len(chunk)))
            out_deflate.extend(chunk)
            writer = BitWriter()
        out_deflate.extend(writer.get_bytes())

        # new zlib (header preserved from original stream) + adler32
        new_adler = zlib.adler32(payload) & 0xffffffff
        final_zlib = bytearray(zlib_header) + out_deflate + struct.pack(">I", new_adler)

        with open(out_path, "wb") as f:
            f.write(data[:z_off] + final_zlib + unused)

    # ---------------- Automation functions ----------------
    def automation_select_folder(self):
        startdir = self.last_dir if self.last_dir and os.path.isdir(self.last_dir) else os.getcwd()
        folder = filedialog.askdirectory(initialdir=startdir)
        if not folder:
            return
        self.save_dir = folder
        self.last_dir = folder
        # update both persisted files
        self._update_last_paths(folder)
        self.auto_status_var.set(f"Save folder: {folder}")

    def _toggle_season_checks(self):
        if self.per_season_var.get():
            self.season_frame.pack(fill="x", pady=6)
        else:
            self.season_frame.pack_forget()

    def automation_apply(self, mode):
        """
        mode: "cover" -> black (1), "uncover" -> white (255)
        """
        if not self.save_dir or not os.path.isdir(self.save_dir):
            messagebox.showerror("Error", "Select a folder first")
            return
        slot = self.slot_var.get()
        prefix = "" if slot == "1" else f"{int(slot)-1}_"
        files = [f for f in os.listdir(self.save_dir)
                 if f.lower().endswith((".cfg", ".dat")) and f.lower().startswith((prefix + "fog_level").lower())]
        if not files:
            messagebox.showerror("Error", "No fog files found for this save slot")
            return

        # per-season filtering
        if self.per_season_var.get():
            selected_codes = [code for code, var in self.season_checks.items() if var.get() == 1]
            extras_text = (self.extra_season_var.get() or "")
            extras = [s.strip() for s in extras_text.split(",") if s.strip().isdigit()]
            def match(fname):
                lname = fname.lower()
                for code in selected_codes:
                    if ("_" + code.lower() + "_") in lname:
                        return True
                for num in extras:
                    if ("_" + num + "_") in lname:
                        return True
                return False
            files = [f for f in files if match(f)]
            if not files:
                show_info("No files", "No files matched the selected seasons/maps.")
                return

        self.auto_status_var.set(f"Processing {len(files)} files...")
        self.update_idletasks()
        color = 1 if mode == "cover" else 255
        processed = 0
        for fname in files:
            fpath = os.path.join(self.save_dir, fname)
            try:
                data = open(fpath, "rb").read()
                cands = [i for i, b in enumerate(data) if b == 0x78]
                dec = None
                for z_off in cands:
                    try:
                        dobj = zlib.decompressobj()
                        dec_local = dobj.decompress(data[z_off:])
                        if dec_local is not None and len(dec_local) >= 8:
                            dec = dec_local
                            break
                    except:
                        continue
                if dec is None:
                    continue
                w = struct.unpack_from("<I", dec, 0)[0]
                h = struct.unpack_from("<I", dec, 4)[0]
                if w <= 0 or h <= 0:
                    continue
                newpix = bytes([color]) * (w * h)
                footer = dec[8 + w * h:] if len(dec) >= 8 + w * h else b""
                payload = bytearray(struct.pack("<II", w, h) + newpix + footer)
                self._write_stored_block_file(fpath, payload)
                processed += 1
            except Exception as e:
                try:
                    open(fpath + ".decode_debug.log", "a", encoding="utf-8").write("Automation error:\n" + repr(e) + "\n" + traceback.format_exc() + "\n")
                except:
                    pass
                continue
        self.auto_status_var.set(f"Automation done: {mode} applied to {processed} files.")

    # ---------------- Overlay functions ----------------
    def load_overlay(self):
        startdir = self.last_dir if self.last_dir and os.path.isdir(self.last_dir) else os.getcwd()
        path = filedialog.askopenfilename(
            initialdir=startdir,
            filetypes=[("Image files", "*.png;*.gif;*.ppm;*.pgm"), ("All", "*.*")]
        )
        if not path:
            return
        try:
            img = self._load_overlay_rgba(path)
            self.overlay_img = img
            # center overlay on current fog image if available
            if self.current_image_L:
                iw, ih = self.current_image_size
                ow, oh = img.get("size", (0, 0))
                self.overlay_scale = 1.0
                self.overlay_offset = (max(0, (iw - ow) // 2), max(0, (ih - oh) // 2))
            else:
                self.overlay_scale = 1.0
                self.overlay_offset = (0, 0)
            self._schedule_preview_render(immediate=True)
            self.log(f"Overlay loaded: {os.path.basename(path)} (drag with right mouse, scroll to zoom)")
        except Exception as e:
            messagebox.showerror("Overlay error", str(e))

    def clear_overlay(self):
        self.overlay_img = None
        self._schedule_preview_render(immediate=True)

    def apply_overlay(self):
        """
        Rasterizes the overlay onto the fog map (self.current_image_L).
        Any overlay pixel with alpha < 128 is ignored.
        Color mapping: nearest of 0->1, 128->128, 255->255
        """
        if not self.overlay_img or not self.current_image_L:
            return
        base = bytearray(self.current_image_L)
        bw, bh = self.current_image_size
        ow, oh = self.overlay_img.get("size", (0, 0))
        opix = self.overlay_img.get("rgba", b"")
        if ow <= 0 or oh <= 0 or not opix:
            return
        oscale = max(0.0001, float(self.overlay_scale))
        new_w = max(1, int(ow * self.overlay_scale))
        new_h = max(1, int(oh * self.overlay_scale))
        ox, oy = self.overlay_offset
        for y in range(new_h):
            ty = y + oy
            if ty < 0 or ty >= bh:
                continue
            sy = min(oh - 1, int(y / oscale))
            for x in range(new_w):
                tx = x + ox
                if tx < 0 or tx >= bw:
                    continue
                sx = min(ow - 1, int(x / oscale))
                si = (sy * ow + sx) * 4
                r, g, b, a = opix[si], opix[si + 1], opix[si + 2], opix[si + 3]
                if a < 128:
                    continue
                brightness = (r + g + b) // 3
                choices = [(1, abs(brightness - 0)), (128, abs(brightness - 128)), (255, abs(brightness - 255))]
                closest_val = min(choices, key=lambda v: v[1])[0]
                base[ty * bw + tx] = closest_val
        self.current_image_L = base
        self.overlay_img = None
        self._schedule_preview_render(base_dirty=True, immediate=True)
        self.log("Overlay applied")

    def start_overlay_drag(self, e):
        if not self.overlay_img:
            return
        self.dragging_overlay = True
        self.last_drag = (e.x, e.y)

    def do_overlay_drag(self, e):
        if not self.dragging_overlay:
            return
        dx = (e.x - self.last_drag[0]) / self.scale
        dy = (e.y - self.last_drag[1]) / self.scale
        ox, oy = self.overlay_offset
        self.overlay_offset = (ox + int(dx), oy + int(dy))
        self.last_drag = (e.x, e.y)
        self._schedule_preview_render()

    def stop_overlay_drag(self, e):
        self.dragging_overlay = False
        # Render one high-quality frame after drag ends.
        self._schedule_preview_render(immediate=True)

    def overlay_zoom(self, e):
        """
        Zoom overlay. Accepts event objects with attribute `delta`.
        On Linux we synthesize an object with delta = +/-120.
        """
        if not self.overlay_img:
            return
        delta = getattr(e, "delta", 0)
        factor = 1.1 if delta > 0 else 0.9
        self.overlay_scale *= factor
        # clamp scale to reasonable values
        self.overlay_scale = max(0.05, min(20.0, self.overlay_scale))
        self._schedule_preview_render()

# -----------------------------------------------------------------------------
# END SECTION: Fog Tool (Editor + Automation UI)
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Fog Tool Frame Wrapper
# Used In: Fog Tool tab -> embeds FogToolApp into a ttk.Frame
# =============================================================================
class FogToolFrame(ttk.Frame):
    def __init__(self, parent, initial_save_dir=None):
        super().__init__(parent)
        self.app = FogToolApp(self, initial_save_dir=initial_save_dir)
        self.app.pack(fill="both", expand=True)

# -----------------------------------------------------------------------------
# END SECTION: Fog Tool Frame Wrapper
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Desktop Path + App Config Helpers
# Used In: Settings tab (shortcuts + config persistence)
# =============================================================================
def get_desktop_path():
    if platform.system() == "Windows":
        # --- existing Windows logic ---
        class GUID(ctypes.Structure):
            _fields_ = [
                ('Data1', wintypes.DWORD),
                ('Data2', wintypes.WORD),
                ('Data3', wintypes.WORD),
                ('Data4', wintypes.BYTE * 8)
            ]

        import uuid
        def guid_from_string(guid_str):
            u = uuid.UUID(guid_str)
            return GUID(
                u.time_low,
                u.time_mid,
                u.time_hi_version,
                (wintypes.BYTE * 8).from_buffer_copy(u.bytes[8:])
            )

        SHGetKnownFolderPath = ctypes.windll.shell32.SHGetKnownFolderPath
        SHGetKnownFolderPath.argtypes = [
            ctypes.POINTER(GUID), wintypes.DWORD, wintypes.HANDLE,
            ctypes.POINTER(ctypes.c_wchar_p)
        ]
        SHGetKnownFolderPath.restype = wintypes.HRESULT

        desktop_id = guid_from_string('{B4BFCC3A-DB2C-424C-B029-7FE99A87C641}')
        out_path = ctypes.c_wchar_p()
        result = SHGetKnownFolderPath(ctypes.byref(desktop_id), 0, 0, ctypes.byref(out_path))
        if result != 0:
            raise ctypes.WinError(result)
        return out_path.value
    else:
        # Linux / macOS → just point to ~/Desktop (safe fallback)
        return os.path.join(os.path.expanduser("~"), "Desktop")

LEGACY_SAVE_PATH_FILE = os.path.join(os.path.expanduser("~"), ".snowrunner_save_path.txt")  # legacy
SAVE_PATH_FILE = LEGACY_SAVE_PATH_FILE  # read-only migration source
LEGACY_CONFIG_FILE = os.path.join(os.path.expanduser("~"), ".snowrunner_editor_config.json")
CONFIG_FILE = os.path.join(get_editor_data_dir(), "snowrunner_editor_config.json")


def _migrate_legacy_config_if_needed():
    if os.path.exists(CONFIG_FILE):
        return
    if not os.path.exists(LEGACY_CONFIG_FILE):
        return
    try:
        with open(LEGACY_CONFIG_FILE, "r", encoding="utf-8") as f:
            legacy_data = json.load(f)
        if isinstance(legacy_data, dict):
            save_config(legacy_data)
    except Exception:
        pass


def load_config():
    _migrate_legacy_config_if_needed()
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            pass
    return {}
def save_config(data):
    try:
        os.makedirs(os.path.dirname(CONFIG_FILE) or ".", exist_ok=True)
        with open(CONFIG_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f)
    except Exception as e:
        print("Failed to save config:", e)

def _load_config_safe():
    try:
        return load_config() or {}
    except Exception:
        return {}

def _save_config_safe(cfg):
    try:
        save_config(cfg)
        return True
    except Exception:
        return False

def _update_config_values(values: dict):
    cfg = _load_config_safe()
    try:
        cfg.update(values)
        _save_config_safe(cfg)
        return True
    except Exception:
        return False

def _delete_config_keys(keys):
    cfg = _load_config_safe()
    changed = False
    for k in keys:
        if k in cfg:
            cfg.pop(k, None)
            changed = True
    if changed:
        _save_config_safe(cfg)
    return changed


def _remove_var_traces(var, fallback_modes=("write", "w")):
    """
    Remove all traces from a tkinter Variable.
    Uses trace_remove() first (Tcl 8.6+ / Tcl 9-safe), with trace_vdelete()
    only as a legacy fallback.
    """
    if var is None:
        return
    try:
        traces = var.trace_info() or []
    except Exception:
        traces = []

    for t in traces:
        mode = None
        cbname = None
        try:
            if isinstance(t, (list, tuple)):
                if len(t) >= 2:
                    mode, cbname = t[0], t[1]
                elif len(t) == 1:
                    cbname = t[0]
            else:
                cbname = t
        except Exception:
            mode = None
            cbname = None

        if not cbname:
            continue

        removed = False

        # Preferred API (no Tcl9 deprecation warning).
        if mode is not None:
            try:
                var.trace_remove(mode, cbname)
                removed = True
            except Exception:
                pass
        if not removed:
            for m in fallback_modes:
                try:
                    var.trace_remove(m, cbname)
                    removed = True
                    break
                except Exception:
                    pass

        # Legacy fallback for very old tkinter.
        if removed:
            continue
        if mode is not None:
            try:
                var.trace_vdelete(mode, cbname)
                removed = True
            except Exception:
                pass
        if not removed:
            for m in fallback_modes:
                try:
                    var.trace_vdelete(m, cbname)
                    removed = True
                    break
                except Exception:
                    pass


def _cfg_bool(value, default=False):
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        v = value.strip().lower()
        if v in ("1", "true", "yes", "on"):
            return True
        if v in ("0", "false", "no", "off"):
            return False
        return bool(default)
    try:
        return bool(int(value))
    except Exception:
        return bool(default)


def _parse_nonnegative_int(value, default):
    try:
        parsed = int(str(value).strip())
        if parsed < 0:
            return int(default)
        return parsed
    except Exception:
        return int(default)


def _sanitize_autosave_poll_interval_seconds(value, default=60):
    try:
        parsed_default = int(default)
    except Exception:
        parsed_default = 60
    if parsed_default < 1:
        parsed_default = 60
    seconds = _parse_nonnegative_int(value, parsed_default)
    if seconds < 1:
        seconds = parsed_default
    if seconds < 1:
        seconds = 1
    if seconds > 86400:
        seconds = 86400
    return seconds


def _get_autosave_poll_interval_seconds(default=60):
    cfg = _load_config_safe()
    return _sanitize_autosave_poll_interval_seconds(
        cfg.get("autosave_poll_interval_seconds", default),
        default=default,
    )


def _sleep_with_stop_event(stop_event, seconds):
    total = _sanitize_autosave_poll_interval_seconds(seconds, default=1)
    for _ in range(total):
        if stop_event.is_set():
            break
        time.sleep(1)


def _read_backup_limits_from_config(default_backups=20, default_autobackups=50):
    cfg = _load_config_safe()
    max_backups = _parse_nonnegative_int(cfg.get("max_backups", default_backups), default_backups)
    max_autobackups = _parse_nonnegative_int(cfg.get("max_autobackups", default_autobackups), default_autobackups)
    return max_backups, max_autobackups


def _cleanup_backup_history(backup_dir, max_backups=20, max_autobackups=50):
    if not backup_dir or not os.path.isdir(backup_dir):
        return

    try:
        all_entries = sorted(os.listdir(backup_dir))
    except Exception:
        return

    normal_backups = [n for n in all_entries if n.startswith("backup-")]
    auto_backups = [n for n in all_entries if n.startswith("autobackup-")]

    if max_backups > 0 and len(normal_backups) > max_backups:
        to_delete = normal_backups[:len(normal_backups) - max_backups]
        for old in to_delete:
            old_path = os.path.join(backup_dir, old)
            try:
                if os.path.isdir(old_path):
                    shutil.rmtree(old_path)
                else:
                    os.remove(old_path)
            except Exception:
                pass
        print(f"[Backup] Removed {len(to_delete)} old normal backup(s)")

    if max_autobackups > 0 and len(auto_backups) > max_autobackups:
        to_delete = auto_backups[:len(auto_backups) - max_autobackups]
        for old in to_delete:
            old_path = os.path.join(backup_dir, old)
            try:
                if os.path.isdir(old_path):
                    shutil.rmtree(old_path)
                else:
                    os.remove(old_path)
            except Exception:
                pass
        print(f"[Autosave] Removed {len(to_delete)} old autobackup(s)")


def _create_timestamped_full_backup(save_dir, prefix="backup"):
    """
    Create a timestamped full backup folder under <save_dir>/backup.
    Returns (backup_dir, full_dir, copied_count).
    """
    if not save_dir or not os.path.isdir(save_dir):
        raise ValueError("save directory is missing or invalid")

    timestamp = datetime.now().strftime(f"{prefix}-%d.%m.%Y %H-%M-%S")
    backup_dir = os.path.join(save_dir, "backup")
    os.makedirs(backup_dir, exist_ok=True)

    full_dir = os.path.join(backup_dir, timestamp + "_full")
    os.makedirs(full_dir, exist_ok=True)

    copied = 0
    backup_dir_abs = os.path.abspath(backup_dir)
    for root, _, files in os.walk(save_dir):
        if os.path.abspath(root).startswith(backup_dir_abs):
            continue
        for file in files:
            if not file.lower().endswith((".cfg", ".dat")):
                continue
            src_path = os.path.join(root, file)
            rel_path = os.path.relpath(src_path, save_dir)
            dst_path = os.path.join(full_dir, rel_path)
            os.makedirs(os.path.dirname(dst_path), exist_ok=True)
            shutil.copy2(src_path, dst_path)
            copied += 1

    return backup_dir, full_dir, copied


def _run_powershell_command(ps_command):
    """
    Execute a PowerShell command using either powershell or pwsh.
    Raises RuntimeError when execution fails on all supported shells.
    """
    last_error = ""
    for exe in ("powershell", "pwsh"):
        try:
            result = subprocess.run(
                [exe, "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", ps_command],
                capture_output=True,
                text=True,
            )
        except FileNotFoundError:
            last_error = f"{exe} not found"
            continue
        if result.returncode == 0:
            return True
        last_error = (result.stderr or result.stdout or "").strip()

    raise RuntimeError(last_error or "PowerShell command failed")


def _ps_quote(value):
    return "'" + str(value).replace("'", "''") + "'"


def _is_windows_startup_supported():
    return platform.system() == "Windows"


def _windows_startup_shortcut_path():
    appdata = os.environ.get("APPDATA", "")
    if not appdata:
        return ""
    startup_dir = os.path.join(appdata, "Microsoft", "Windows", "Start Menu", "Programs", "Startup")
    return os.path.join(startup_dir, "SnowRunner Editor.lnk")


def _startup_launch_target_and_args():
    if getattr(sys, "frozen", False):
        target = os.path.abspath(sys.executable)
        args = ""
        workdir = os.path.dirname(target)
    else:
        target = os.path.abspath(sys.executable)
        script = os.path.abspath(sys.argv[0])
        args = f"\"{script}\"".strip()
        workdir = os.path.dirname(script)
    return target, args, workdir


def _startup_registration_metadata():
    target, args, workdir = _startup_launch_target_and_args()
    return {
        "start_with_windows_registered_version": int(APP_VERSION),
        "start_with_windows_registered_target": str(target),
        "start_with_windows_registered_args": str(args),
        "start_with_windows_registered_workdir": str(workdir),
    }


def _norm_path_compare(value):
    txt = str(value or "").strip()
    if not txt:
        return ""
    try:
        return os.path.normcase(os.path.normpath(txt))
    except Exception:
        return txt


def _sync_windows_startup_registration_if_needed():
    """
    Keep startup shortcut pinned to the currently running build when startup is enabled.
    This lets users update from v100 -> v101 and have startup move to v101 after first launch.
    """
    if not _is_windows_startup_supported():
        return

    cfg = _load_config_safe()
    if not _cfg_bool(cfg.get("start_with_windows", False), default=False):
        return

    expected = _startup_registration_metadata()
    shortcut_path = _windows_startup_shortcut_path()
    shortcut_exists = bool(shortcut_path and os.path.exists(shortcut_path))

    registered_version = _parse_nonnegative_int(cfg.get("start_with_windows_registered_version", 0), 0)
    registered_target = _norm_path_compare(cfg.get("start_with_windows_registered_target", ""))
    registered_args = str(cfg.get("start_with_windows_registered_args", "") or "").strip()
    registered_workdir = _norm_path_compare(cfg.get("start_with_windows_registered_workdir", ""))

    expected_version = int(expected["start_with_windows_registered_version"])
    expected_target = _norm_path_compare(expected["start_with_windows_registered_target"])
    expected_args = str(expected["start_with_windows_registered_args"] or "").strip()
    expected_workdir = _norm_path_compare(expected["start_with_windows_registered_workdir"])

    needs_refresh = (
        (not shortcut_exists)
        or (registered_version != expected_version)
        or (registered_target != expected_target)
        or (registered_args != expected_args)
        or (registered_workdir != expected_workdir)
    )
    if not needs_refresh:
        return

    ok, msg = _apply_startup_mode(True)
    if not ok:
        print(f"[Startup] auto-refresh failed: {msg}")
        return

    _update_config_values(expected)
    print(
        "[Startup] startup shortcut refreshed to current build "
        f"(v{expected_version}, target='{expected['start_with_windows_registered_target']}')."
    )


def _set_windows_startup_enabled(enabled):
    """
    Enable or disable startup shortcut registration on Windows.
    """
    if not _is_windows_startup_supported():
        raise RuntimeError("Windows startup registration is only supported on Windows.")

    enabled = bool(enabled)

    shortcut_path = _windows_startup_shortcut_path()
    if not shortcut_path:
        raise RuntimeError("Could not resolve Windows Startup folder.")

    startup_dir = os.path.dirname(shortcut_path)
    os.makedirs(startup_dir, exist_ok=True)

    if not enabled:
        try:
            if os.path.exists(shortcut_path):
                os.remove(shortcut_path)
        except Exception as e:
            raise RuntimeError(f"Failed to remove startup shortcut: {e}") from e
        return "Startup launch disabled."

    target, args, workdir = _startup_launch_target_and_args()
    ps = (
        "$W = New-Object -ComObject WScript.Shell; "
        f"$S = $W.CreateShortcut({_ps_quote(shortcut_path)}); "
        f"$S.TargetPath = {_ps_quote(target)}; "
        f"$S.Arguments = {_ps_quote(args)}; "
        f"$S.WorkingDirectory = {_ps_quote(workdir)}; "
        f"$S.IconLocation = {_ps_quote(target)}; "
        "$S.Save()"
    )
    _run_powershell_command(ps)
    return "Startup launch enabled."


def _apply_startup_mode(enabled):
    """
    Apply startup mode on this OS. Non-Windows platforms keep config only.
    Returns (ok: bool, message: str).
    """
    if not _is_windows_startup_supported():
        return False, "Startup launch integration is currently only available on Windows."
    try:
        msg = _set_windows_startup_enabled(enabled)
        return True, msg
    except Exception as e:
        return False, str(e)


# Theme palettes and color remapping for runtime dark/light switching.
_LIGHT_THEME = {
    "bg": "#f0f0f0",
    "fg": "black",
    "warning_fg": "red",
    "warning_btn_bg": "#c62828",
    "warning_btn_active_bg": "#b71c1c",
    "warning_btn_fg": "white",
    "field_bg": "#ffffff",
    "button_bg": "#e9e9e9",
    "button_active_bg": "#e6e6e6",
    "disabled_fg": "#7a7a7a",
    "border": "#c8c8c8",
    "accent": "#2f7dff",
    "accent_fg": "white",
    "row_a": "#e0e0e0",
    "row_b": "#f8f8f8",
    "mine_closed_bg": "#bdbdbd",
    "fog_bg": "#d4bf98",
    "notebook_bg": "#d7d7d7",
    "tab_bg": "#ebebeb",
    "tab_active_bg": "#f4f4f4",
}

_DARK_THEME = {
    "bg": "#1f1f1f",
    "fg": "#f0f0f0",
    "warning_fg": "#ffb347",
    "warning_btn_bg": "#a96c20",
    "warning_btn_active_bg": "#945c16",
    "warning_btn_fg": "white",
    "field_bg": "#2a2a2a",
    "button_bg": "#333333",
    "button_active_bg": "#3f3f3f",
    "disabled_fg": "#9a9a9a",
    "border": "#505050",
    "accent": "#355778",
    "accent_fg": "#f0f0f0",
    "row_a": "#2a2a2a",
    "row_b": "#1f1f1f",
    "mine_closed_bg": "#444444",
    "fog_bg": "#3a3325",
    "notebook_bg": "#2a2a2a",
    "tab_bg": "#333333",
    "tab_active_bg": "#3f3f3f",
}

_BUILTIN_THEME_PRESETS = {
    "Metrix": {
        "mode": "dark",
        "colors": {
            "bg": "#0b120b",
            "fg": "#64ff64",
            "warning_fg": "#ccff33",
            "warning_btn_bg": "#3a6a16",
            "warning_btn_active_bg": "#4d8a1d",
            "warning_btn_fg": "#f2fff2",
            "field_bg": "#081008",
            "button_bg": "#102010",
            "button_active_bg": "#183318",
            "disabled_fg": "#5ca05c",
            "border": "#2f6b2f",
            "accent": "#00a63b",
            "accent_fg": "#f2fff2",
            "row_a": "#0f180f",
            "row_b": "#0a120a",
            "fog_bg": "#132113",
            "notebook_bg": "#101a10",
            "tab_bg": "#152615",
            "tab_active_bg": "#1e381e",
        },
    },
    "Eco": {
        "mode": "dark",
        "colors": {
            "bg": "#1c241f",
            "fg": "#b8ffcb",
            "warning_fg": "#ffd58d",
            "warning_btn_bg": "#7b5a2a",
            "warning_btn_active_bg": "#9a7034",
            "warning_btn_fg": "#f7f3e8",
            "field_bg": "#243128",
            "button_bg": "#2e3e33",
            "button_active_bg": "#3b5042",
            "disabled_fg": "#86a394",
            "border": "#4b6b57",
            "accent": "#6bc27c",
            "accent_fg": "#102016",
            "row_a": "#253227",
            "row_b": "#1f2b22",
            "fog_bg": "#334233",
            "notebook_bg": "#26342a",
            "tab_bg": "#2d3e32",
            "tab_active_bg": "#385141",
        },
    },
    "Midnight": {
        "mode": "dark",
        "colors": {
            "bg": "#111624",
            "fg": "#dbe7ff",
            "warning_fg": "#ffbe7a",
            "warning_btn_bg": "#7f5125",
            "warning_btn_active_bg": "#9a6530",
            "warning_btn_fg": "#fff5e9",
            "field_bg": "#1a2336",
            "button_bg": "#25304a",
            "button_active_bg": "#314063",
            "disabled_fg": "#8a96b3",
            "border": "#43557f",
            "accent": "#4f7dff",
            "accent_fg": "#f2f6ff",
            "row_a": "#182034",
            "row_b": "#131a2b",
            "fog_bg": "#1d2640",
            "notebook_bg": "#182035",
            "tab_bg": "#202a43",
            "tab_active_bg": "#2a3657",
        },
    },
    "Ember": {
        "mode": "dark",
        "colors": {
            "bg": "#221712",
            "fg": "#ffd8c4",
            "warning_fg": "#ffb07f",
            "warning_btn_bg": "#8c3f24",
            "warning_btn_active_bg": "#aa4f2e",
            "warning_btn_fg": "#fff1e8",
            "field_bg": "#2e2019",
            "button_bg": "#3b2a22",
            "button_active_bg": "#4a352b",
            "disabled_fg": "#9f7f70",
            "border": "#6c4b3f",
            "accent": "#ff7e42",
            "accent_fg": "#20120d",
            "row_a": "#31221b",
            "row_b": "#261b15",
            "fog_bg": "#3d2b22",
            "notebook_bg": "#2d211b",
            "tab_bg": "#3a2a22",
            "tab_active_bg": "#4b362b",
        },
    },
}
_BUILTIN_THEME_ALIASES = {
    "matrix": "Metrix",
}
_BUILTIN_THEME_ORDER = ["Light", "Dark", "Metrix", "Eco", "Midnight", "Ember", "Random"]

if not isinstance(_ACTIVE_THEME, dict):
    _ACTIVE_THEME = dict(_LIGHT_THEME)

_THEME_CUSTOMIZER_BASIC_FIELDS = (
    ("bg", "Window Background"),
    ("fg", "Text Color"),
    ("field_bg", "Input Background"),
    ("button_bg", "Button Background"),
    ("button_active_bg", "Button Active"),
    ("border", "Borders"),
    ("accent", "Accent / Selection"),
    ("accent_fg", "Accent Text"),
    ("row_a", "Row 1 (Objectives+/Backups)"),
    ("row_b", "Row 2 (Objectives+/Backups)"),
    ("mine_closed_bg", "Minesweeper Closed Cell"),
    ("fog_bg", "Fog Tool Background"),
    ("notebook_bg", "Tab Row Background"),
    ("tab_bg", "Tab Background"),
    ("tab_active_bg", "Tab Active"),
    ("warning_color", "Warning Color"),
    ("warning_btn_fg", "Warning Button Text"),
    ("disabled_fg", "Disabled Text"),
)

_THEME_CUSTOMIZER_ADVANCED_FIELDS = (
    ("bg", "Window Background"),
    ("fg", "Text Color"),
    ("field_bg", "Input Background"),
    ("button_bg", "Button Background"),
    ("button_active_bg", "Button Active"),
    ("border", "Borders"),
    ("accent", "Accent / Selection"),
    ("accent_fg", "Accent Text"),
    ("row_a", "Row 1 (Objectives+/Backups)"),
    ("row_b", "Row 2 (Objectives+/Backups)"),
    ("mine_closed_bg", "Minesweeper Closed Cell"),
    ("fog_bg", "Fog Tool Background"),
    ("notebook_bg", "Tab Row Background"),
    ("tab_bg", "Tab Background"),
    ("tab_active_bg", "Tab Active"),
    ("warning_fg", "Warning Text"),
    ("warning_btn_bg", "Warning Button"),
    ("warning_btn_active_bg", "Warning Button Active"),
    ("warning_btn_fg", "Warning Button Text"),
    ("disabled_fg", "Disabled Text"),
)


def _normalize_theme_mode(mode):
    token = str(mode or "").strip().lower()
    return "dark" if token == "dark" else "light"


def _reserved_theme_names():
    names = {"light", "dark", "random"}
    try:
        names.update(str(k).strip().lower() for k in _BUILTIN_THEME_PRESETS.keys() if str(k).strip())
    except Exception:
        pass
    try:
        names.update(str(k).strip().lower() for k in _BUILTIN_THEME_ALIASES.keys() if str(k).strip())
    except Exception:
        pass
    return names


def _resolve_builtin_theme_name(name):
    token = str(name or "").strip()
    if not token:
        return None
    lower = token.lower()
    if lower == "light":
        return "Light"
    if lower == "dark":
        return "Dark"
    if lower == "random":
        return "Random"
    for preset_name in _BUILTIN_THEME_PRESETS.keys():
        if isinstance(preset_name, str) and preset_name.lower() == lower:
            return preset_name
    alias = _BUILTIN_THEME_ALIASES.get(lower)
    if isinstance(alias, str) and alias:
        return alias
    return None


def _rand_hex_color():
    return f"#{random.randint(0, 255):02x}{random.randint(0, 255):02x}{random.randint(0, 255):02x}"


def _hex_luma(color_hex):
    token = _normalize_color_token(color_hex)
    if not token or not isinstance(token, str) or not re.fullmatch(r"#[0-9a-f]{6}", token):
        return 0.0
    r = int(token[1:3], 16) / 255.0
    g = int(token[3:5], 16) / 255.0
    b = int(token[5:7], 16) / 255.0
    return (0.2126 * r) + (0.7152 * g) + (0.0722 * b)


def _contrast_text_for(bg, light="#f0f0f0", dark="#101010"):
    return dark if _hex_luma(bg) > 0.55 else light


def _generate_random_theme(mode="dark"):
    mode = _normalize_theme_mode(mode)
    defaults = _theme_defaults_for_mode(mode)
    colors = {}
    for key in defaults.keys():
        colors[key] = _rand_hex_color()

    # Keep primary text readable.
    colors["fg"] = _contrast_text_for(colors["bg"])
    colors["accent_fg"] = _contrast_text_for(colors["accent"])
    colors["warning_btn_fg"] = _contrast_text_for(colors["warning_btn_bg"])
    colors["disabled_fg"] = "#9a9a9a" if _hex_luma(colors["bg"]) < 0.55 else "#5a5a5a"
    return _sanitize_theme_colors(colors, mode)


def _theme_defaults_for_mode(mode):
    mode = _normalize_theme_mode(mode)
    return dict(_DARK_THEME if mode == "dark" else _LIGHT_THEME)


def _sanitize_theme_colors(colors, mode):
    defaults = _theme_defaults_for_mode(mode)
    clean = {}
    for key, fallback in defaults.items():
        value = fallback
        if isinstance(colors, dict):
            raw = colors.get(key, fallback)
            if isinstance(raw, str) and raw.strip():
                value = raw.strip()
        clean[key] = value
    return clean


def _serialize_theme_presets():
    exported = {}
    for name, payload in (_THEME_CUSTOM_PRESETS or {}).items():
        if not isinstance(name, str):
            continue
        clean_name = name.strip()
        if not clean_name or clean_name.lower() in _reserved_theme_names():
            continue
        if not isinstance(payload, dict):
            continue
        mode = _normalize_theme_mode(payload.get("mode", "light"))
        colors = _sanitize_theme_colors(payload.get("colors", {}), mode)
        exported[clean_name] = {"mode": mode, "colors": colors}
    return exported


def _load_theme_presets_from_config(cfg):
    presets = {}
    if not isinstance(cfg, dict):
        return presets

    raw = cfg.get("theme_presets", {})
    if not isinstance(raw, dict):
        return presets

    for name, payload in raw.items():
        if not isinstance(name, str):
            continue
        clean_name = name.strip()
        if not clean_name or clean_name.lower() in _reserved_theme_names():
            continue

        mode = "light"
        colors_payload = payload
        if isinstance(payload, dict):
            if "colors" in payload:
                mode = _normalize_theme_mode(payload.get("mode", "light"))
                colors_payload = payload.get("colors", {})
            else:
                mode = _normalize_theme_mode(payload.get("mode", "light"))
                colors_payload = payload

        presets[clean_name] = {
            "mode": mode,
            "colors": _sanitize_theme_colors(colors_payload, mode),
        }
    return presets


def _get_theme_preset_names():
    names = list(_BUILTIN_THEME_ORDER)
    lowered = {n.lower() for n in names}
    for name in (_THEME_CUSTOM_PRESETS or {}).keys():
        if not isinstance(name, str):
            continue
        if name.lower() in lowered:
            continue
        if name not in names:
            names.append(name)
            lowered.add(name.lower())
    return names


def _resolve_theme_preset(name):
    label = str(name or "").strip()
    if not label:
        label = "Dark" if _is_dark_mode_active() else "Light"

    builtin = _resolve_builtin_theme_name(label)
    if builtin == "Dark":
        return {"name": "Dark", "mode": "dark", "colors": _theme_defaults_for_mode("dark")}
    if builtin == "Light":
        return {"name": "Light", "mode": "light", "colors": _theme_defaults_for_mode("light")}
    if builtin == "Random":
        mode = "dark"
        return {"name": "Random", "mode": mode, "colors": _generate_random_theme(mode)}
    if isinstance(builtin, str) and builtin in _BUILTIN_THEME_PRESETS:
        payload = _BUILTIN_THEME_PRESETS.get(builtin, {})
        mode = _normalize_theme_mode(payload.get("mode", "dark"))
        colors = _sanitize_theme_colors(payload.get("colors", {}), mode)
        return {"name": builtin, "mode": mode, "colors": colors}

    payload = (_THEME_CUSTOM_PRESETS or {}).get(label)
    if payload is None:
        for existing_name in (_THEME_CUSTOM_PRESETS or {}).keys():
            if isinstance(existing_name, str) and existing_name.lower() == label.lower():
                payload = _THEME_CUSTOM_PRESETS.get(existing_name)
                label = existing_name
                break

    if isinstance(payload, dict):
        mode = _normalize_theme_mode(payload.get("mode", "light"))
        colors = _sanitize_theme_colors(payload.get("colors", {}), mode)
        return {"name": label, "mode": mode, "colors": colors}

    fallback_dark = _is_dark_mode_active()
    if fallback_dark:
        return {"name": "Dark", "mode": "dark", "colors": _theme_defaults_for_mode("dark")}
    return {"name": "Light", "mode": "light", "colors": _theme_defaults_for_mode("light")}


def _get_effective_theme(dark_mode=None):
    if dark_mode is None:
        dark_mode = _is_dark_mode_active()
    mode = "dark" if bool(dark_mode) else "light"

    palette = _theme_defaults_for_mode(mode)
    if isinstance(_ACTIVE_THEME, dict):
        for key, value in _ACTIVE_THEME.items():
            if key in palette and isinstance(value, str) and value.strip():
                palette[key] = value.strip()
    return palette


def _persist_theme_selection(preset_name=None, dark_mode=None):
    selected = str(preset_name or _ACTIVE_THEME_NAME or "").strip()
    if not selected:
        selected = "Dark" if bool(dark_mode) else "Light"
    if dark_mode is None:
        dark_mode = _normalize_theme_mode(_ACTIVE_THEME_MODE) == "dark"
        try:
            if "dark_mode_var" in globals() and dark_mode_var is not None:
                dark_mode = bool(dark_mode_var.get())
        except Exception:
            pass

    _update_config_values(
        {
            "theme_preset": selected,
            "theme_presets": _serialize_theme_presets(),
            "dark_mode": bool(dark_mode),
        }
    )


def _set_active_theme_preset(name, persist=False):
    global _ACTIVE_THEME, _ACTIVE_THEME_NAME, _ACTIVE_THEME_MODE

    resolved = _resolve_theme_preset(name)
    _ACTIVE_THEME_NAME = resolved["name"]
    _ACTIVE_THEME_MODE = _normalize_theme_mode(resolved["mode"])
    _ACTIVE_THEME = dict(resolved["colors"])

    dark = _ACTIVE_THEME_MODE == "dark"
    try:
        if "dark_mode_var" in globals() and dark_mode_var is not None:
            dark_mode_var.set(bool(dark))
    except Exception:
        pass

    if persist:
        _persist_theme_selection(_ACTIVE_THEME_NAME, dark_mode=dark)

    return dark

_THEME_BG_TO_DARK = {
    "systembuttonface": "#1f1f1f",
    "systemwindow": "#1f1f1f",
    "system3dface": "#1f1f1f",
    "#f0f0f0": "#1f1f1f",
    "#d9d9d9": "#1f1f1f",
    "#f8f8f8": "#1f1f1f",
    "#e0e0e0": "#2a2a2a",
    "#bdbdbd": "#444444",
    "#ffffff": "#1f1f1f",
    "white": "#1f1f1f",
    "#d4bf98": "#3a3325",
    "#fefecd": "#3a3523",
    "#cfe8ff": "#355778",
    "#2f7dff": "#355778",
    "#c62828": "#a96c20",
    "#b71c1c": "#945c16",
}

_THEME_BG_TO_LIGHT = {
    "#1f1f1f": "#f8f8f8",
    "#2a2a2a": "#e0e0e0",
    "#333333": "#e0e0e0",
    "#3f3f3f": "#f0f0f0",
    "#444444": "#bdbdbd",
    "#3a3325": "#d4bf98",
    "#3a3523": "#fefecd",
    "#355778": "#2f7dff",
    "#cfe8ff": "#2f7dff",
    "#a96c20": "#c62828",
    "#945c16": "#b71c1c",
}

_THEME_FG_TO_DARK = {
    "black": "#f0f0f0",
    "#000000": "#f0f0f0",
    "systemwindowtext": "#f0f0f0",
    "systembuttontext": "#f0f0f0",
    "red": "#ffb347",
    "#ff0000": "#ffb347",
    "darkred": "#ffb347",
    "#c62828": "#ffb347",
}

_THEME_FG_TO_LIGHT = {
    "#f0f0f0": "black",
    "#efefef": "black",
    "#ffb347": "red",
}

_THEME_BG_OPTIONS = (
    "background", "bg", "fieldbackground", "readonlybackground",
    "activebackground", "disabledbackground", "highlightbackground",
    "highlightcolor", "selectbackground", "troughcolor", "bordercolor",
    "lightcolor", "darkcolor", "selectcolor",
)

_THEME_FG_OPTIONS = (
    "foreground", "fg", "insertbackground", "insertcolor",
    "activeforeground", "disabledforeground", "selectforeground",
    "arrowcolor",
)


def _normalize_color_token(value):
    if not isinstance(value, str):
        return None
    token = value.strip()
    if not token:
        return None
    if re.fullmatch(r"#[0-9A-Fa-f]{3}", token):
        token = "#" + "".join(ch * 2 for ch in token[1:])
    if re.fullmatch(r"#[0-9A-Fa-f]{6}", token):
        return token.lower()
    return token.lower()


def _is_dark_mode_active():
    try:
        if "dark_mode_var" in globals() and dark_mode_var is not None:
            return bool(dark_mode_var.get())
    except Exception:
        pass
    try:
        cfg = load_config() or {}
        return bool(cfg.get("dark_mode", False))
    except Exception:
        return False


def _use_native_light_notebook_tabs(dark_mode=None):
    """
    Use native platform ttk notebook tabs only for the built-in Light preset.
    All other presets keep the themed/custom notebook tab style.
    """
    if dark_mode is None:
        dark_mode = _is_dark_mode_active()
    if bool(dark_mode):
        return False
    try:
        active_name = str(globals().get("_ACTIVE_THEME_NAME") or "").strip()
        if not active_name:
            return True
        return _resolve_builtin_theme_name(active_name) == "Light"
    except Exception:
        return True


def _set_runtime_theme_constants(dark_mode):
    global STRIPE_A, STRIPE_B, CELL_COLORS
    mode = "dark" if bool(dark_mode) else "light"
    defaults = _theme_defaults_for_mode(mode)
    palette = _get_effective_theme(bool(dark_mode))

    STRIPE_A = str(palette.get("row_a") or defaults.get("row_a") or defaults["bg"])
    STRIPE_B = str(palette.get("row_b") or defaults.get("row_b") or defaults["field_bg"])
    cell_closed = str(palette.get("mine_closed_bg") or defaults.get("mine_closed_bg") or ("#444444" if bool(dark_mode) else "#bdbdbd"))

    if bool(dark_mode):
        CELL_COLORS = {
            "default": cell_closed,
            "empty": str(palette.get("bg") or defaults["bg"]),
            "flagged": str(palette.get("row_a") or defaults.get("row_a") or defaults["bg"]),
        }
    else:
        CELL_COLORS = {
            "default": cell_closed,
            "empty": str(palette.get("bg") or defaults["bg"]),
            "flagged": str(palette.get("row_a") or defaults.get("row_a") or defaults["bg"]),
        }


def _theme_mapped_color(value, *, dark_mode, role):
    key = _normalize_color_token(value)
    if not key:
        return None
    if role == "fg":
        table = _THEME_FG_TO_DARK if dark_mode else _THEME_FG_TO_LIGHT
    else:
        table = _THEME_BG_TO_DARK if dark_mode else _THEME_BG_TO_LIGHT
    mapped = table.get(key)
    if mapped:
        return mapped

    palette = _get_effective_theme(dark_mode)
    dynamic = {}

    if role == "fg":
        for theme_key in ("fg", "accent_fg", "warning_fg", "warning_btn_fg", "disabled_fg"):
            target = palette.get(theme_key)
            if not isinstance(target, str) or not target:
                continue
            for source in (_LIGHT_THEME.get(theme_key), _DARK_THEME.get(theme_key)):
                source_key = _normalize_color_token(source)
                if source_key:
                    dynamic[source_key] = target
        dynamic["black"] = palette.get("fg", "black")
        dynamic["systemwindowtext"] = palette.get("fg", "black")
        dynamic["systembuttontext"] = palette.get("fg", "black")
        dynamic["red"] = palette.get("warning_fg", "red")
    else:
        for theme_key in (
            "bg",
            "field_bg",
            "button_bg",
            "button_active_bg",
            "border",
            "accent",
            "row_a",
            "row_b",
            "mine_closed_bg",
            "fog_bg",
            "notebook_bg",
            "tab_bg",
            "tab_active_bg",
            "warning_btn_bg",
            "warning_btn_active_bg",
        ):
            target = palette.get(theme_key)
            if not isinstance(target, str) or not target:
                continue
            for source in (_LIGHT_THEME.get(theme_key), _DARK_THEME.get(theme_key)):
                source_key = _normalize_color_token(source)
                if source_key:
                    dynamic[source_key] = target
        dynamic["systembuttonface"] = palette.get("bg", "#f0f0f0")
        dynamic["systemwindow"] = palette.get("bg", "#f0f0f0")
        dynamic["system3dface"] = palette.get("bg", "#f0f0f0")

    return dynamic.get(key)


def _theme_color_literal(value, role="bg", dark_mode=None):
    if dark_mode is None:
        dark_mode = _is_dark_mode_active()
    mapped = _theme_mapped_color(value, dark_mode=dark_mode, role=role)
    return mapped if mapped else value


def _to_colorref(value):
    """Convert a color token to a Windows COLORREF (0x00bbggrr)."""
    token = _normalize_color_token(value)
    if token == "black":
        token = "#000000"
    elif token == "white":
        token = "#ffffff"
    if not token or not isinstance(token, str) or not re.fullmatch(r"#[0-9a-f]{6}", token):
        return None
    r = int(token[1:3], 16)
    g = int(token[3:5], 16)
    b = int(token[5:7], 16)
    return (r | (g << 8) | (b << 16))


def _apply_windows_titlebar_theme(root, dark_mode=None):
    """
    Apply native Windows title-bar dark/light styling.
    Affects only the OS title bar (non-client area), not ttk tabs.
    """
    if platform.system() != "Windows":
        return
    if dark_mode is None:
        dark_mode = _is_dark_mode_active()
    dark_mode = bool(dark_mode)

    ct = globals().get("ctypes")
    if ct is None:
        return

    try:
        hwnd = int(root.winfo_id())
    except Exception:
        return
    if not hwnd:
        return

    try:
        user32 = ct.windll.user32
        try:
            user32.GetAncestor.argtypes = [wintypes.HWND, ct.c_uint]
            user32.GetAncestor.restype = wintypes.HWND
        except Exception:
            pass
        # Ensure we target the real top-level window handle.
        GA_ROOT = 2
        top = user32.GetAncestor(wintypes.HWND(hwnd), GA_ROOT)
        if top:
            hwnd = int(top)
    except Exception:
        pass

    try:
        set_attr = ct.windll.dwmapi.DwmSetWindowAttribute
        try:
            set_attr.argtypes = [wintypes.HWND, ct.c_uint, ct.c_void_p, ct.c_uint]
            set_attr.restype = wintypes.HRESULT
        except Exception:
            pass
    except Exception:
        return

    # Toggle native dark title bar on supported Windows builds.
    try:
        use_dark = ct.c_int(1 if dark_mode else 0)
        for attr in (20, 19):  # DWMWA_USE_IMMERSIVE_DARK_MODE, legacy fallback
            try:
                set_attr(wintypes.HWND(hwnd), attr, ct.byref(use_dark), ct.sizeof(use_dark))
            except Exception:
                pass
    except Exception:
        pass

    # Optional fine-grained color control (supported on newer Windows versions).
    palette = _get_effective_theme(dark_mode)
    for attr, token in (
        (35, palette.get("bg")),      # DWMWA_CAPTION_COLOR
        (36, palette.get("fg")),      # DWMWA_TEXT_COLOR
        (34, palette.get("border")),  # DWMWA_BORDER_COLOR
    ):
        color = _to_colorref(token)
        if color is None:
            continue
        try:
            cval = ct.c_uint(color)
            set_attr(wintypes.HWND(hwnd), attr, ct.byref(cval), ct.sizeof(cval))
        except Exception:
            pass

    # Force a non-client redraw so title-bar changes apply immediately.
    try:
        SWP_NOMOVE = 0x0002
        SWP_NOSIZE = 0x0001
        SWP_NOZORDER = 0x0004
        SWP_FRAMECHANGED = 0x0020
        user32.SetWindowPos(
            wintypes.HWND(hwnd),
            wintypes.HWND(0),
            0, 0, 0, 0,
            SWP_NOMOVE | SWP_NOSIZE | SWP_NOZORDER | SWP_FRAMECHANGED
        )
    except Exception:
        pass


def _register_themed_toplevel(win):
    try:
        bucket = globals().setdefault("_THEMED_TOPLEVELS", [])
        if win not in bucket:
            bucket.append(win)
    except Exception:
        pass


def _retheme_registered_toplevels(dark_mode=None):
    if dark_mode is None:
        dark_mode = _is_dark_mode_active()
    try:
        bucket = globals().get("_THEMED_TOPLEVELS", [])
    except Exception:
        bucket = []
    keep = []
    for win in bucket:
        try:
            if win is None or not bool(win.winfo_exists()):
                continue
            _apply_editor_theme(win, dark_mode=dark_mode, walk_children=True)
            keep.append(win)
        except Exception:
            continue
    try:
        globals()["_THEMED_TOPLEVELS"] = keep
    except Exception:
        pass


def _create_themed_toplevel(parent=None):
    win = tk.Toplevel(parent) if parent else tk.Toplevel()
    try:
        _register_themed_toplevel(win)
        _apply_editor_theme(win, dark_mode=_is_dark_mode_active(), walk_children=False)
        win.after_idle(lambda w=win: _apply_editor_theme(w, dark_mode=_is_dark_mode_active(), walk_children=True))
    except Exception:
        pass
    return win


def _resolve_message_parent(parent=None):
    try:
        if parent is not None and bool(parent.winfo_exists()):
            return parent
    except Exception:
        pass
    try:
        root = getattr(tk, "_default_root", None)
        if root is not None and bool(root.winfo_exists()):
            return root
    except Exception:
        pass
    return None


def _show_themed_message(kind, title=None, message="", **options):
    """Theme-aware replacement for messagebox.showinfo/showwarning/showerror."""
    native_map = {
        "info": _NATIVE_SHOWINFO,
        "warning": _NATIVE_SHOWWARNING,
        "error": _NATIVE_SHOWERROR,
    }
    native_fn = native_map.get(kind, _NATIVE_SHOWINFO)

    # Tk dialogs must be created on main thread; otherwise use native fallback.
    if threading.current_thread() is not threading.main_thread():
        return native_fn(title, message, **options)

    parent = _resolve_message_parent(options.get("parent"))
    if parent is None:
        return native_fn(title, message, **options)

    msg = "" if message is None else str(message)
    detail = options.get("detail")
    if detail:
        msg = f"{msg}\n\n{detail}"

    try:
        win = _create_themed_toplevel(parent)
        win.title("" if title is None else str(title))
        win.transient(parent)
        win.resizable(False, False)

        body = ttk.Frame(win, padding=12)
        body.pack(fill="both", expand=True)

        icon_text = {"info": "i", "warning": "!", "error": "x"}.get(kind, "i")
        icon_style = "Warning.TLabel" if kind in ("warning", "error") else "TLabel"
        ttk.Label(body, text=icon_text, style=icon_style, font=("TkDefaultFont", 14, "bold")).pack(anchor="w")

        ttk.Label(body, text=msg, wraplength=560, justify="left").pack(fill="both", expand=True, pady=(6, 10))

        btn_frame = ttk.Frame(body)
        btn_frame.pack(fill="x")
        ttk.Button(btn_frame, text="OK", command=win.destroy).pack(side="right")

        win.bind("<Return>", lambda e: win.destroy())
        win.bind("<Escape>", lambda e: win.destroy())

        # Place near parent center.
        try:
            parent.update_idletasks()
            win.update_idletasks()
            px, py = parent.winfo_rootx(), parent.winfo_rooty()
            pw, ph = parent.winfo_width(), parent.winfo_height()
            ww, wh = win.winfo_reqwidth(), win.winfo_reqheight()
            x = px + max(0, (pw - ww) // 2)
            y = py + max(0, (ph - wh) // 2)
            win.geometry(f"+{x}+{y}")
        except Exception:
            pass

        win.grab_set()
        parent.wait_window(win)
        return "ok"
    except Exception:
        return native_fn(title, message, **options)


def _install_themed_messagebox_hooks():
    try:
        if getattr(messagebox, "_themed_hooks_installed", False):
            return
    except Exception:
        pass

    def _info(title=None, message=None, **options):
        return _show_themed_message("info", title, message, **options)

    def _warning(title=None, message=None, **options):
        return _show_themed_message("warning", title, message, **options)

    def _error(title=None, message=None, **options):
        return _show_themed_message("error", title, message, **options)

    try:
        messagebox.showinfo = _info
        messagebox.showwarning = _warning
        messagebox.showerror = _error
        messagebox._themed_hooks_installed = True
    except Exception:
        pass


def _retint_combobox_popdown(widget, palette):
    """Force ttk.Combobox dropdown (popdown Listbox) colors to match current theme."""
    try:
        if not isinstance(widget, ttk.Combobox):
            return
    except Exception:
        return

    try:
        cb_path = str(widget)
        popdown = widget.tk.call("ttk::combobox::PopdownWindow", cb_path)
        if not popdown:
            return

        try:
            if not int(widget.tk.call("winfo", "exists", popdown)):
                return
        except Exception:
            return

        # Popdown container widgets (best-effort, direct Tcl calls).
        for path in (popdown, f"{popdown}.f"):
            try:
                if int(widget.tk.call("winfo", "exists", path)):
                    try:
                        widget.tk.call(path, "configure", "-background", palette["bg"])
                    except Exception:
                        pass
                    try:
                        widget.tk.call(path, "configure", "-highlightbackground", palette["border"])
                    except Exception:
                        pass
                    try:
                        widget.tk.call(path, "configure", "-highlightcolor", palette["border"])
                    except Exception:
                        pass
            except Exception:
                pass

        # Actual dropdown list.
        listbox_path = f"{popdown}.f.l"
        try:
            if int(widget.tk.call("winfo", "exists", listbox_path)):
                widget.tk.call(
                    listbox_path,
                    "configure",
                    "-background", palette["field_bg"],
                    "-foreground", palette["fg"],
                    "-selectbackground", palette["accent"],
                    "-selectforeground", palette["accent_fg"],
                    "-highlightthickness", 0,
                    "-borderwidth", 0,
                )
        except Exception:
            pass

        # Popdown scrollbar (platform/theme dependent).
        sb_path = f"{popdown}.f.sb"
        try:
            if int(widget.tk.call("winfo", "exists", sb_path)):
                try:
                    widget.tk.call(sb_path, "configure", "-background", palette["button_bg"])
                except Exception:
                    pass
                try:
                    widget.tk.call(sb_path, "configure", "-activebackground", palette["button_active_bg"])
                except Exception:
                    pass
                try:
                    widget.tk.call(sb_path, "configure", "-troughcolor", palette["field_bg"])
                except Exception:
                    pass
        except Exception:
            pass
    except Exception:
        pass


def _install_combobox_popdown_refresh_bindings(root):
    """Ensure combobox dropdown lists are retinted each time they are opened."""
    try:
        if bool(getattr(root, "_combobox_popdown_theme_hooks_installed", False)):
            return
    except Exception:
        pass

    def _retint_after_open(event):
        try:
            cb = event.widget
            if not isinstance(cb, ttk.Combobox):
                return

            def _apply():
                _retint_combobox_popdown(cb, _get_effective_theme())

            try:
                cb.after_idle(_apply)
                cb.after(20, _apply)
                cb.after(80, _apply)
            except Exception:
                _apply()
        except Exception:
            pass

    try:
        root.bind_class("TCombobox", "<Button-1>", _retint_after_open, add="+")
        root.bind_class("TCombobox", "<KeyPress-Down>", _retint_after_open, add="+")
        root.bind_class("TCombobox", "<Alt-Down>", _retint_after_open, add="+")
    except Exception:
        pass

    try:
        root._combobox_popdown_theme_hooks_installed = True
    except Exception:
        pass


def _retint_widget(widget, dark_mode):
    try:
        if bool(getattr(widget, "_skip_theme_retint", False)):
            return
    except Exception:
        pass

    palette = _get_effective_theme(dark_mode)
    try:
        role_key = getattr(widget, "_theme_bg_key", None)
        if isinstance(role_key, str) and role_key in palette:
            direct_bg = palette.get(role_key)
            if isinstance(direct_bg, str) and direct_bg:
                try:
                    if "bg" in widget.keys():
                        widget.configure(bg=direct_bg)
                except Exception:
                    pass
                try:
                    if "background" in widget.keys():
                        widget.configure(background=direct_bg)
                except Exception:
                    pass
    except Exception:
        pass

    for option in _THEME_BG_OPTIONS:
        try:
            if option not in widget.keys():
                continue
            current = widget.cget(option)
            updated = _theme_mapped_color(current, dark_mode=dark_mode, role="bg")
            if updated and updated != current:
                widget.configure(**{option: updated})
        except Exception:
            pass

    for option in _THEME_FG_OPTIONS:
        try:
            if option not in widget.keys():
                continue
            current = widget.cget(option)
            updated = _theme_mapped_color(current, dark_mode=dark_mode, role="fg")
            if updated and updated != current:
                widget.configure(**{option: updated})
        except Exception:
            pass

    try:
        if isinstance(widget, ttk.Treeview):
            widget.tag_configure("even", background=STRIPE_B)
            widget.tag_configure("odd", background=STRIPE_A)
    except Exception:
        pass

    try:
        if isinstance(widget, ttk.Combobox):
            try:
                widget.configure(style="TCombobox")
            except Exception:
                pass
            _retint_combobox_popdown(widget, palette)
    except Exception:
        pass

    try:
        if isinstance(widget, ttk.Notebook):
            nb_style = "TNotebook" if _use_native_light_notebook_tabs(dark_mode) else "Editor.TNotebook"
            try:
                widget.configure(style=nb_style)
            except Exception:
                pass
    except Exception:
        pass

    try:
        if callable(getattr(widget, "show_preview", None)):
            widget.after_idle(widget.show_preview)
    except Exception:
        pass


def _apply_editor_theme(root, dark_mode=None, walk_children=True):
    if dark_mode is None:
        dark_mode = _is_dark_mode_active()
    dark_mode = bool(dark_mode)
    palette = _get_effective_theme(dark_mode)

    _set_runtime_theme_constants(dark_mode)

    try:
        root.configure(background=palette["bg"])
    except Exception:
        pass

    try:
        root.option_add("*Label.background", palette["bg"])
        root.option_add("*Label.foreground", palette["fg"])
        root.option_add("*Button.background", palette["button_bg"])
        root.option_add("*Button.foreground", palette["fg"])
        root.option_add("*Button.activeBackground", palette["button_active_bg"])
        root.option_add("*Button.activeForeground", palette["fg"])
        root.option_add("*Checkbutton.background", palette["bg"])
        root.option_add("*Checkbutton.foreground", palette["fg"])
        root.option_add("*Checkbutton.selectColor", palette["field_bg"])
        root.option_add("*Radiobutton.background", palette["bg"])
        root.option_add("*Radiobutton.foreground", palette["fg"])
        root.option_add("*Radiobutton.selectColor", palette["field_bg"])
        root.option_add("*Entry.background", palette["field_bg"])
        root.option_add("*Entry.foreground", palette["fg"])
        root.option_add("*Entry.insertBackground", palette["fg"])
        root.option_add("*Text.background", palette["field_bg"])
        root.option_add("*Text.foreground", palette["fg"])
        root.option_add("*Text.insertBackground", palette["fg"])
        root.option_add("*Listbox.background", palette["field_bg"])
        root.option_add("*Listbox.foreground", palette["fg"])
        root.option_add("*Canvas.background", palette["bg"])
        root.option_add("*TCombobox*Listbox.background", palette["field_bg"])
        root.option_add("*TCombobox*Listbox.foreground", palette["fg"])
        root.option_add("*TCombobox*Listbox.selectBackground", palette["accent"])
        root.option_add("*TCombobox*Listbox.selectForeground", palette["accent_fg"])
        root.option_add("*selectBackground", palette["accent"])
        root.option_add("*selectForeground", palette["accent_fg"])
    except Exception:
        pass

    try:
        root.configure(highlightthickness=0, highlightbackground=palette["bg"], highlightcolor=palette["bg"])
    except Exception:
        pass

    try:
        _install_combobox_popdown_refresh_bindings(root)
    except Exception:
        pass

    try:
        global _BASE_TTK_THEME
        style = ttk.Style(root)
        use_native_tabs = _use_native_light_notebook_tabs(dark_mode)
        try:
            if _BASE_TTK_THEME is None:
                _BASE_TTK_THEME = style.theme_use()
        except Exception:
            pass

        # Use a theme that respects full color overrides in dark mode.
        try:
            names = tuple(style.theme_names() or ())
        except Exception:
            names = ()
        try:
            current_theme = style.theme_use()
        except Exception:
            current_theme = ""

        try:
            if dark_mode:
                if "clam" in names and str(current_theme).lower() != "clam":
                    style.theme_use("clam")
            else:
                if _BASE_TTK_THEME and _BASE_TTK_THEME in names and str(current_theme) != str(_BASE_TTK_THEME):
                    style.theme_use(_BASE_TTK_THEME)
        except Exception:
            pass

        try:
            style.configure(
                ".",
                background=palette["bg"],
                foreground=palette["fg"],
                fieldbackground=palette["field_bg"],
                troughcolor=palette["field_bg"],
                bordercolor=palette["border"],
                lightcolor=palette["border"],
                darkcolor=palette["border"],
            )
        except Exception:
            pass
        try:
            style.configure("TLabel", background=palette["bg"], foreground=palette["fg"])
            style.map("TLabel", foreground=[("disabled", palette["disabled_fg"]), ("!disabled", palette["fg"])])
        except Exception:
            pass
        try:
            style.configure("Warning.TLabel", background=palette["bg"], foreground=palette["warning_fg"])
            style.map("Warning.TLabel", foreground=[("disabled", palette["disabled_fg"]), ("!disabled", palette["warning_fg"])])
            # Backward-compatible style name already used in parts of the UI.
            style.configure("RedWarning.TLabel", background=palette["bg"], foreground=palette["warning_fg"])
            style.map("RedWarning.TLabel", foreground=[("disabled", palette["disabled_fg"]), ("!disabled", palette["warning_fg"])])
        except Exception:
            pass
        try:
            status_bg = palette.get("notebook_bg", palette["bg"])
            status_panel_bg = palette.get("field_bg", palette["bg"])

            style.configure("StatusBar.TFrame", background=status_bg)
            style.configure(
                "StatusBarBadge.TLabel",
                background=palette["accent"],
                foreground=palette["accent_fg"],
                padding=(8, 2),
                font=("TkDefaultFont", 9, "bold"),
            )
            style.map(
                "StatusBarBadge.TLabel",
                foreground=[("disabled", palette["disabled_fg"]), ("!disabled", palette["accent_fg"])],
                background=[("disabled", status_bg), ("!disabled", palette["accent"])],
            )

            style.configure(
                "StatusBarText.TLabel",
                background=status_panel_bg,
                foreground=palette["fg"],
                padding=(10, 4),
                relief="solid",
                borderwidth=1,
                bordercolor=palette["border"],
                lightcolor=palette["border"],
                darkcolor=palette["border"],
            )
            style.map(
                "StatusBarText.TLabel",
                foreground=[("disabled", palette["disabled_fg"]), ("!disabled", palette["fg"])],
                background=[("!disabled", status_panel_bg)],
            )
        except Exception:
            pass
        try:
            style.configure("TFrame", background=palette["bg"])
        except Exception:
            pass
        try:
            style.configure("TLabelframe", background=palette["bg"], foreground=palette["fg"], bordercolor=palette["border"])
            style.configure("TLabelframe.Label", background=palette["bg"], foreground=palette["fg"])
        except Exception:
            pass
        try:
            style.configure("TButton", background=palette["button_bg"], foreground=palette["fg"], bordercolor=palette["border"])
            style.map(
                "TButton",
                background=[("pressed", palette["button_active_bg"]), ("active", palette["button_active_bg"]), ("!disabled", palette["button_bg"])],
                foreground=[("disabled", palette["disabled_fg"]), ("!disabled", palette["fg"])],
            )
        except Exception:
            pass
        try:
            style.configure(
                "Warning.TButton",
                background=palette["warning_btn_bg"],
                foreground=palette["warning_btn_fg"],
                bordercolor=palette["border"],
            )
            style.map(
                "Warning.TButton",
                background=[
                    ("pressed", palette["warning_btn_active_bg"]),
                    ("active", palette["warning_btn_active_bg"]),
                    ("!disabled", palette["warning_btn_bg"]),
                ],
                foreground=[("disabled", palette["disabled_fg"]), ("!disabled", palette["warning_btn_fg"])],
            )
        except Exception:
            pass
        try:
            style.configure("TCheckbutton", background=palette["bg"], foreground=palette["fg"])
            style.map(
                "TCheckbutton",
                background=[("active", palette["bg"]), ("selected", palette["bg"]), ("!disabled", palette["bg"])],
                foreground=[("disabled", palette["disabled_fg"]), ("!disabled", palette["fg"])],
            )
            # Clam/alt expose indicator color options; use them so the checkbox glyph
            # stays readable in dark mode instead of the default light indicator.
            try:
                style.configure(
                    "TCheckbutton",
                    indicatorbackground=palette["field_bg"],
                    indicatorforeground=palette["fg"],
                    upperbordercolor=palette["border"],
                    lowerbordercolor=palette["border"],
                )
                style.map(
                    "TCheckbutton",
                    indicatorbackground=[
                        ("selected", palette["accent"]),
                        ("active", palette["button_active_bg"]),
                        ("!selected", palette["field_bg"]),
                    ],
                    indicatorforeground=[
                        ("selected", palette["accent_fg"]),
                        ("!selected", palette["fg"]),
                    ],
                )
            except Exception:
                pass
        except Exception:
            pass
        try:
            style.configure("TRadiobutton", background=palette["bg"], foreground=palette["fg"])
            style.map(
                "TRadiobutton",
                background=[("active", palette["bg"]), ("selected", palette["bg"]), ("!disabled", palette["bg"])],
                foreground=[("disabled", palette["disabled_fg"]), ("!disabled", palette["fg"])],
            )
        except Exception:
            pass
        try:
            style.configure(
                "TEntry",
                fieldbackground=palette["field_bg"],
                foreground=palette["fg"],
                background=palette["field_bg"],
                insertcolor=palette["fg"],
                bordercolor=palette["border"],
            )
            style.map(
                "TEntry",
                fieldbackground=[("readonly", palette["field_bg"]), ("disabled", palette["field_bg"]), ("!disabled", palette["field_bg"])],
                foreground=[("disabled", palette["disabled_fg"]), ("!disabled", palette["fg"])],
            )
        except Exception:
            pass
        try:
            style.configure(
                "TCombobox",
                fieldbackground=palette["field_bg"],
                background=palette["button_bg"],
                foreground=palette["fg"],
                arrowcolor=palette["fg"],
            )
            style.map(
                "TCombobox",
                fieldbackground=[("readonly", palette["field_bg"]), ("!disabled", palette["field_bg"])],
                foreground=[("readonly", palette["fg"]), ("!disabled", palette["fg"])],
                selectbackground=[("readonly", palette["field_bg"]), ("!disabled", palette["accent"])],
                selectforeground=[("readonly", palette["fg"]), ("!disabled", palette["accent_fg"])],
                background=[("readonly", palette["field_bg"]), ("active", palette["button_active_bg"]), ("!disabled", palette["button_bg"])],
            )
        except Exception:
            pass
        try:
            style.configure(
                "TSpinbox",
                fieldbackground=palette["field_bg"],
                foreground=palette["fg"],
                background=palette["button_bg"],
                arrowcolor=palette["fg"],
            )
            style.map("TSpinbox", fieldbackground=[("!disabled", palette["field_bg"])], foreground=[("!disabled", palette["fg"])])
        except Exception:
            pass
        try:
            style.configure("TScrollbar", background=palette["button_bg"], troughcolor=palette["field_bg"], bordercolor=palette["border"], arrowcolor=palette["fg"])
            style.map("TScrollbar", background=[("active", palette["button_active_bg"])])
        except Exception:
            pass
        try:
            style.configure("Treeview", background=palette["field_bg"], fieldbackground=palette["field_bg"], foreground=palette["fg"])
            style.map("Treeview", background=[("selected", palette["accent"])], foreground=[("selected", palette["accent_fg"])])
            style.configure("Treeview.Heading", background=palette["button_bg"], foreground=palette["fg"])
            style.map("Treeview.Heading", background=[("active", palette["button_active_bg"])])
        except Exception:
            pass
        try:
            if use_native_tabs:
                try:
                    # Remove custom maps from themed style in case user switched from non-light.
                    style.map(
                        "Editor.TNotebook.Tab",
                        foreground=[],
                        background=[],
                        lightcolor=[],
                        darkcolor=[],
                        bordercolor=[],
                    )
                except Exception:
                    pass
            else:
                style.configure("Editor.TNotebook", background=palette["notebook_bg"], bordercolor=palette["border"])
                style.configure(
                    "Editor.TNotebook.Tab",
                    background=palette["tab_bg"],
                    foreground=palette["fg"],
                    padding=(10, 4),
                    bordercolor=palette["border"],
                    lightcolor=palette["border"],
                    darkcolor=palette["border"],
                )
                style.map(
                    "Editor.TNotebook.Tab",
                    foreground=[("disabled", palette["disabled_fg"]), ("selected", palette["fg"]), ("!disabled", palette["fg"])],
                    background=[("disabled", palette["notebook_bg"]), ("selected", palette["bg"]), ("active", palette["tab_active_bg"]), ("!disabled", palette["tab_bg"])],
                    lightcolor=[("!disabled", palette["border"])],
                    darkcolor=[("!disabled", palette["border"])],
                    bordercolor=[("!disabled", palette["border"])],
                )
        except Exception:
            pass

        try:
            style.configure("RowA.TCheckbutton", background=STRIPE_A, foreground=palette["fg"])
            style.map("RowA.TCheckbutton", background=[("active", STRIPE_A), ("selected", STRIPE_A)])
            style.configure("RowB.TCheckbutton", background=STRIPE_B, foreground=palette["fg"])
            style.map("RowB.TCheckbutton", background=[("active", STRIPE_B), ("selected", STRIPE_B)])
        except Exception:
            pass

        try:
            style.configure(
                "Backups.Treeview",
                background=STRIPE_B,
                fieldbackground=STRIPE_B,
                bordercolor=STRIPE_B,
                foreground=palette["fg"],
                rowheight=30,
                font=("TkDefaultFont", 10),
            )
            style.configure(
                "Backups.Treeview.Heading",
                background=STRIPE_B,
                foreground=palette["fg"],
                font=("TkDefaultFont", 10, "bold"),
            )
            style.map("Backups.Treeview", background=[("selected", palette["accent"])], foreground=[("selected", palette["accent_fg"])])
        except Exception:
            pass
    except Exception:
        pass

    if walk_children:
        stack = [root]
        while stack:
            widget = stack.pop()
            _retint_widget(widget, dark_mode=dark_mode)
            try:
                stack.extend(widget.winfo_children())
            except Exception:
                pass

    try:
        _apply_focus_outline_fix(root)
    except Exception:
        pass
    try:
        _apply_windows_titlebar_theme(root, dark_mode=dark_mode)
    except Exception:
        pass
    try:
        if isinstance(root, tk.Tk):
            _retheme_registered_toplevels(dark_mode=dark_mode)
    except Exception:
        pass

# -----------------------------------------------------------------------------
# END SECTION: Desktop Path + App Config Helpers
# -----------------------------------------------------------------------------
# =============================================================================
# SECTION: Gameplay Constants + Rules Placeholders
# Used In: Money & Rank tab, Rules tab, sync_all_rules
# =============================================================================
RANK_XP_REQUIREMENTS = {
    1: 0, 2: 700, 3: 1700, 4: 2900, 5: 4100, 6: 5400, 7: 6900,
    8: 8500, 9: 10100, 10: 11800, 11: 13700, 12: 15700, 13: 17800,
    14: 20100, 15: 22500, 16: 25000, 17: 27500, 18: 30100,
    19: 32700, 20: 35500, 21: 38300, 22: 41300, 23: 44300,
    24: 47500, 25: 50700, 26: 54100, 27: 57500, 28: 61100,
    29: 64900, 30: 69000
}
# Rules-related configuration removed — rules UI has been stripped per request.
# Keep empty placeholders so other modules referencing these names won't crash.
external_addon_map = {}
FACTOR_RULE_DEFINITIONS = []
FACTOR_RULE_VARS = []

# -----------------------------------------------------------------------------
# END SECTION: Gameplay Constants + Rules Placeholders
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Process Detection + Autosave/Backup Utilities
# Used In: Settings tab, Backups tab, autosave monitor
# =============================================================================
def _is_snowrunner_running():
    """
    Cross-platform check: returns True if any running process name/command line contains 'snowrunner' (case-insensitive).
    Uses tasklist on Windows and pgrep/ps on Unix. Defensive and avoids extra dependencies.
    """
    try:
        system = platform.system()
        if system == "Windows":
            si = subprocess.STARTUPINFO()
            si.dwFlags |= subprocess.STARTF_USESHOWWINDOW

            CREATE_NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0x08000000)

            out = subprocess.check_output(
                ["tasklist"],
                stderr=subprocess.DEVNULL,
                text=True,
                encoding="utf-8",
                errors="ignore",
                startupinfo=si,
                creationflags=CREATE_NO_WINDOW,
            )
            return "snowrunner" in out.lower()
        else:
            # try pgrep for efficiency
            try:
                out = subprocess.check_output(
                    ["pgrep", "-af", "snowrunner"],
                    stderr=subprocess.DEVNULL,
                    text=True,
                    encoding="utf-8",
                    errors="ignore",
                )
                return bool(out.strip())
            except Exception:
                # fallback to ps aux
                out = subprocess.check_output(
                    ["ps", "aux"],
                    stderr=subprocess.DEVNULL,
                    text=True,
                    encoding="utf-8",
                    errors="ignore",
                )
                return "snowrunner" in out.lower()
    except Exception:
        # if detection fails for any reason, return False (safe fallback)
        return False


def _set_autosave_runtime_state(enabled=None, full_backup=None, save_path=None):
    """Store autosave state in plain Python globals for background-thread use."""
    global _AUTOSAVE_ENABLED, _AUTOSAVE_FULL_BACKUP, _AUTOSAVE_SAVE_PATH
    with _AUTOSAVE_STATE_LOCK:
        if enabled is not None:
            _AUTOSAVE_ENABLED = bool(enabled)
        if full_backup is not None:
            _AUTOSAVE_FULL_BACKUP = bool(full_backup)
        if save_path is not None:
            _AUTOSAVE_SAVE_PATH = str(save_path or "")


def _get_autosave_runtime_state():
    """Read autosave state snapshot without touching tkinter variables."""
    with _AUTOSAVE_STATE_LOCK:
        return _AUTOSAVE_ENABLED, _AUTOSAVE_FULL_BACKUP, _AUTOSAVE_SAVE_PATH


def _refresh_autosave_runtime_state_from_vars():
    """Refresh runtime autosave state from tkinter vars (must run on main thread)."""
    enabled = False
    full_mode = False
    current_path = ""

    try:
        if autosave_var is not None:
            enabled = bool(autosave_var.get())
    except Exception:
        enabled = False

    try:
        if full_backup_var is not None:
            full_mode = bool(full_backup_var.get())
    except Exception:
        full_mode = False

    try:
        if save_path_var is not None:
            current_path = str(save_path_var.get() or "")
    except Exception:
        current_path = ""

    _set_autosave_runtime_state(enabled=enabled, full_backup=full_mode, save_path=current_path)


def _bind_autosave_runtime_state_traces():
    """Bind Tk variable traces once so worker threads never query Tk directly."""
    global _AUTOSAVE_STATE_TRACES_BOUND
    if _AUTOSAVE_STATE_TRACES_BOUND:
        _refresh_autosave_runtime_state_from_vars()
        return

    def _sync(*_):
        _refresh_autosave_runtime_state_from_vars()

    for var in (autosave_var, full_backup_var, save_path_var):
        if var is None:
            continue
        try:
            var.trace_add("write", _sync)
            continue
        except Exception:
            pass
        try:
            var.trace("w", _sync)
        except Exception:
            pass

    _AUTOSAVE_STATE_TRACES_BOUND = True
    _refresh_autosave_runtime_state_from_vars()



def _create_autobackup(save_dir, full_backup_mode=None):
    """
    Copy all .cfg/.dat files from save_dir into backup/autobackup-<timestamp>[_full] preserving subpaths.
    Uses the same skip logic as make_backup_if_enabled (skips the backup folder itself).
    """
    try:
        if not save_dir or not os.path.isdir(save_dir):
            print("[Autosave] Save dir missing or invalid:", save_dir)
            return
        if full_backup_mode is None:
            _, full_backup_mode, _ = _get_autosave_runtime_state()
        timestamp = datetime.now().strftime("autobackup-%d.%m.%Y %H-%M-%S")
        backup_dir = os.path.join(save_dir, "backup")
        os.makedirs(backup_dir, exist_ok=True)
        folder_name = timestamp + ("_full" if full_backup_mode else "")
        full_dir = os.path.join(backup_dir, folder_name)
        os.makedirs(full_dir, exist_ok=True)

        for root, _, files in os.walk(save_dir):
            # skip backups-of-backups
            if os.path.abspath(root).startswith(os.path.abspath(backup_dir)):
                continue
            for file in files:
                if file.lower().endswith((".cfg", ".dat")):
                    src_path = os.path.join(root, file)
                    rel_path = os.path.relpath(src_path, save_dir)
                    dst_path = os.path.join(full_dir, rel_path)
                    os.makedirs(os.path.dirname(dst_path), exist_ok=True)
                    try:
                        shutil.copy2(src_path, dst_path)
                    except Exception as e:
                        print(f"[Autosave] copy failed {src_path} -> {dst_path}: {e}")
        print(f"[Autosave] Created autobackup at: {full_dir}")
        set_app_status(f"Autosave backup created: {os.path.basename(full_dir)}", timeout_ms=5000)
        try:
            max_backups, max_autobackups = _read_backup_limits_from_config()
            _cleanup_backup_history(backup_dir, max_backups=max_backups, max_autobackups=max_autobackups)
        except Exception:
            pass
    except Exception as e:
        print("[Autosave] Failed:", e, flush=True)
        set_app_status(f"Autosave backup failed: {e}", timeout_ms=9000)


def _scan_folder_mtimes(save_dir):
    """Return dict {relative_path: mtime} for .cfg/.dat files in save_dir (non-recursive for file-list consistency)."""
    mt = {}
    if not save_dir or not os.path.isdir(save_dir):
        return mt
    for root, _, files in os.walk(save_dir):
        # skip backup folder
        if os.path.abspath(root).startswith(os.path.abspath(os.path.join(save_dir, "backup"))):
            continue
        for f in files:
            if f.lower().endswith((".cfg", ".dat")):
                full = os.path.join(root, f)
                try:
                    mt[os.path.relpath(full, save_dir)] = os.path.getmtime(full)
                except Exception:
                    pass
    return mt

def _autosave_monitor_loop(stop_event, poll_interval=60):
    """
    Monitor loop (configurable cadence):
      - If autosave disabled -> sleep poll_interval between checks.
      - If save folder invalid -> sleep poll_interval and re-check.
      - If game not running -> reset baseline and sleep poll_interval.
      - Optional: when game transitions from running -> not running, create one final full backup.
      - If game running -> check folder mtimes every poll_interval seconds and create autobackup on change.
    """
    last_seen_mtimes = {}
    was_running = False
    while not stop_event.is_set():
        try:
            enabled, full_backup_mode, cached_save_path = _get_autosave_runtime_state()
            cfg = _load_config_safe()
            backup_on_game_exit = _cfg_bool(cfg.get("autosave_backup_on_game_exit", False), default=False)
            poll_interval = _sanitize_autosave_poll_interval_seconds(
                cfg.get("autosave_poll_interval_seconds", poll_interval),
                default=poll_interval,
            )

            # Respect the poll interval consistently
            if not enabled:
                print(f"[Autosave] disabled - will re-check every {poll_interval}s.", flush=True)
                was_running = False
                _sleep_with_stop_event(stop_event, poll_interval)
                continue

            # Read cached path mirrored from Tk variables on the main thread.
            # Avoid touching tkinter variables in this worker thread.
            full_path = str(cached_save_path or "")

            # Resolve folder to watch
            if not full_path:
                lastp = ""
                try:
                    lastp = load_last_path()
                except Exception:
                    lastp = ""
                if lastp:
                    save_dir = lastp if os.path.isdir(lastp) else os.path.dirname(lastp)
                else:
                    save_dir = ""
            else:
                save_dir = os.path.dirname(full_path)

            print(f"[Autosave] checking. save_dir='{save_dir}'", flush=True)

            if not save_dir or not os.path.isdir(save_dir):
                print(f"[Autosave] save dir missing or invalid: '{save_dir}'. Will retry in {poll_interval}s.", flush=True)
                was_running = False
                _sleep_with_stop_event(stop_event, poll_interval)
                continue

            # Check whether SnowRunner is running (once per interval)
            running = _is_snowrunner_running()
            print(f"[Autosave] process running: {running}", flush=True)

            # If not running -> reset baseline and wait one interval before checking again
            if not running:
                if was_running and backup_on_game_exit:
                    try:
                        backup_dir, full_dir, copied = _create_timestamped_full_backup(save_dir, prefix="backup")
                        print(f"[Autosave] game exit detected -> final full backup: {full_dir} ({copied} files)", flush=True)
                        set_app_status(
                            f"Game closed: full backup created ({os.path.basename(full_dir)}).",
                            timeout_ms=7000,
                        )
                        max_backups, max_autobackups = _read_backup_limits_from_config()
                        _cleanup_backup_history(backup_dir, max_backups=max_backups, max_autobackups=max_autobackups)
                    except Exception as e:
                        print(f"[Autosave] failed to create game-exit backup: {e}", flush=True)
                        set_app_status(f"Game-exit backup failed: {e}", timeout_ms=9000)

                was_running = False
                last_seen_mtimes = _scan_folder_mtimes(save_dir)
                if last_seen_mtimes:
                    most_recent_file, mt = max(last_seen_mtimes.items(), key=lambda it: it[1])
                    try:
                        most_recent = datetime.fromtimestamp(mt).strftime("%d.%m.%Y %H:%M:%S")
                    except Exception:
                        most_recent = str(mt)
                    print(f"[Autosave] baseline set (not running). most recent file: {most_recent_file} @ {most_recent}", flush=True)
                else:
                    print("[Autosave] baseline set (not running). no files found.", flush=True)
                _sleep_with_stop_event(stop_event, poll_interval)
                continue

            if not was_running:
                print("[Autosave] game session detected (process became running).", flush=True)
            was_running = True

            # Game is running — scan folder mtimes now
            current_mtimes = _scan_folder_mtimes(save_dir)
            if current_mtimes:
                most_recent_file, most_recent_m = max(current_mtimes.items(), key=lambda it: it[1])
                try:
                    most_recent_human = datetime.fromtimestamp(most_recent_m).strftime("%d.%m.%Y %H:%M:%S")
                except Exception:
                    most_recent_human = str(most_recent_m)
                print(f"[Autosave] most recent file: {most_recent_file} @ {most_recent_human}", flush=True)
            else:
                print("[Autosave] no .cfg/.dat files found in save folder.", flush=True)

            # If first time seeing the folder while running, initialise baseline and wait one interval
            if not last_seen_mtimes:
                last_seen_mtimes = current_mtimes
                print("[Autosave] initialized baseline while running; re-checking immediately.", flush=True)
                continue

            # detect changes: new file, removed file, or modified mtime
            changed_files = []
            for f, m in current_mtimes.items():
                if f not in last_seen_mtimes or last_seen_mtimes.get(f) != m:
                    changed_files.append(f)
            for f in list(last_seen_mtimes.keys()):
                if f not in current_mtimes:
                    changed_files.append(f + " (deleted)")

            if changed_files:
                print(f"[Autosave] changes detected: {len(changed_files)} -> {changed_files}", flush=True)
                try:
                    _create_autobackup(save_dir, full_backup_mode=full_backup_mode)
                except Exception as e:
                    print("[Autosave] failed to create autobackup:", e, flush=True)
                last_seen_mtimes = current_mtimes
            else:
                print("[Autosave] no changes detected.", flush=True)

            # Wait exactly poll_interval seconds (split into 1s steps so stop_event wakes quickly)
            _sleep_with_stop_event(stop_event, poll_interval)

        except Exception as e:
            print("[Autosave] monitor exception:", e, flush=True)
            # On error, sleep one interval before retrying
            _sleep_with_stop_event(stop_event, poll_interval)

    print("[Autosave] monitor exiting", flush=True)


def start_autosave_monitor():
    global _AUTOSAVE_THREAD, _AUTOSAVE_STOP_EVENT
    if _AUTOSAVE_THREAD and _AUTOSAVE_THREAD.is_alive():
        return
    current_poll = _get_autosave_poll_interval_seconds(default=60)
    _AUTOSAVE_STOP_EVENT = threading.Event()
    _AUTOSAVE_THREAD = threading.Thread(
        target=_autosave_monitor_loop,
        args=(_AUTOSAVE_STOP_EVENT, current_poll),
        daemon=True,
    )
    _AUTOSAVE_THREAD.start()
    print(f"[Autosave] monitor started (interval {current_poll}s)")


def stop_autosave_monitor():
    global _AUTOSAVE_THREAD, _AUTOSAVE_STOP_EVENT
    try:
        if _AUTOSAVE_STOP_EVENT:
            _AUTOSAVE_STOP_EVENT.set()
        if _AUTOSAVE_THREAD:
            _AUTOSAVE_THREAD.join(timeout=2)
    except Exception:
        pass
    _AUTOSAVE_THREAD = None
    _AUTOSAVE_STOP_EVENT = None
    print("[Autosave] monitor stopped")


def make_backup_if_enabled(path, force_full=False):
    try:
        if not os.path.exists(path):
            print("[Backup] Skipped (path invalid).")
            set_app_status("Backup skipped: save path is invalid.", timeout_ms=5000)
            return

        save_dir = os.path.dirname(path)
        timestamp = datetime.now().strftime("backup-%d.%m.%Y %H-%M-%S")
        backup_dir = os.path.join(save_dir, "backup")
        os.makedirs(backup_dir, exist_ok=True)

        full_mode_selected = bool(force_full)
        if not full_mode_selected:
            try:
                full_mode_selected = bool(full_backup_var.get())
            except Exception:
                full_mode_selected = False

        # FULL BACKUP: copy all .cfg/.dat files (skip backup folder itself)
        if full_mode_selected:
            backup_dir, full_dir, copied = _create_timestamped_full_backup(save_dir, prefix="backup")
            print(f"[Backup] Full backup created at: {full_dir} ({copied} files)")
            set_app_status(f"Full backup created: {os.path.basename(full_dir)}", timeout_ms=5000)

        # SINGLE BACKUP: only current save
        elif bool(make_backup_var.get() if make_backup_var is not None else False):
            single_dir = os.path.join(backup_dir, timestamp)
            os.makedirs(single_dir, exist_ok=True)
            backup_file_path = os.path.join(single_dir, os.path.basename(path))
            shutil.copy2(path, backup_file_path)
            print(f"[Backup] Backup created at: {backup_file_path}")
            set_app_status(f"Backup created: {os.path.basename(backup_file_path)}", timeout_ms=5000)
        else:
            print("[Backup] Skipped (disabled).")
            set_app_status("Backup skipped: backup is disabled.", timeout_ms=3500)

        # --- Auto cleanup old backups ---
        try:
            max_backups = int(max_backups_var.get())
        except Exception:
            max_backups = 20
        try:
            max_autobackups = int(max_autobackups_var.get())
        except Exception:
            max_autobackups = 50

        _cleanup_backup_history(backup_dir, max_backups=max_backups, max_autobackups=max_autobackups)

    except Exception as e:
        print(f"[Backup Error] Failed to create backup: {e}")
        set_app_status(f"Backup failed: {e}", timeout_ms=9000)
        
# -----------------------------------------------------------------------------
# END SECTION: Process Detection + Autosave/Backup Utilities
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Save-File IO + Version Safety
# Used In: Save File tab and startup auto-load
# =============================================================================
def load_last_path():
    cfg = _load_config_safe()
    p = cfg.get("last_save_path", "")
    if p:
        return p
    # Legacy migration from .snowrunner_save_path.txt
    try:
        if os.path.exists(SAVE_PATH_FILE):
            with open(SAVE_PATH_FILE, "r", encoding="utf-8") as f:
                legacy = f.read().strip()
            if legacy:
                cfg["last_save_path"] = legacy
                _save_config_safe(cfg)
                try:
                    os.remove(SAVE_PATH_FILE)
                except Exception:
                    pass
                return legacy
    except Exception:
        pass
    return ""
def safe_load_save(path):
    """Try to load a save file, return content or None with popup error."""
    if not os.path.exists(path):
        messagebox.showerror(
            "Save File Missing",
            f"Could not load save file:\n{path}\n\nThe file does not exist."
        )
        return None
    try:
        with open(path, "r", encoding="utf-8") as f:
            return f.read()
    except Exception:
        messagebox.showerror(
            "Save File Corrupted",
            f"Could not load save file:\n{path}\n\nThe file appears to be corrupted or incomplete."
        )
        return None
    
# --- HELPER ---
def _read_int_key_from_text(content: str, key: str):
    """Return the largest int value for all occurrences of '"key": <int>' or None if not present/parsable."""
    try:
        matches = re.findall(rf'"{re.escape(key)}"\s*:\s*(-?\d+)', content, flags=re.IGNORECASE)
        if not matches:
            return None
        vals = []
        for m in matches:
            try:
                vals.append(int(m))
            except Exception:
                # skip unparsable entry
                continue
        if not vals:
            return None
        return max(vals)
    except Exception:
        return None

def prompt_save_version_mismatch_and_choose(path, modal=True):
    """
    Checks a save file for objVersion/birthVersion/cfg_version and if any values
    differ from expected OR any key is missing shows a dialog.

    If modal=True (default) the function blocks and returns (action, path).
    If modal=False the dialog is non-blocking: it returns immediately and the
    dialog's buttons perform the accept/replace logic themselves (they persist
    the new path and refresh UI).
    """
    try:
        content = safe_load_save(path)
    except Exception:
        return ("error", None)

    if content is None:
        return ("error", None)

    expected = {"objVersion": 9, "birthVersion": 9, "cfg_version": 1}
    diffs = []

    for key, exp in expected.items():
        m = re.search(rf'"{re.escape(key)}"\s*:\s*(-?\d+)', content)
        if not m:
            diffs.append(f'{key}: MISSING (expected {exp})')
        else:
            try:
                val = int(m.group(1))
            except Exception:
                diffs.append(f'{key}: UNREADABLE (expected {exp})')
                continue
            if val != exp:
                diffs.append(f'{key}: {val} (expected {exp})')

    # No differences → nothing to show
    if not diffs:
        return ("ok", None) if modal else None

    # Build the dialog
    top = _create_themed_toplevel()
    top.title("Save file version mismatch")
    top.transient()  # keep above other windows
    # do NOT call grab_set() if non-modal - that would block interactions
    if modal:
        top.grab_set()

    # Icon setup removed

    msg = (
        "The selected save file appears to have version differences or missing keys\n"
        "which may cause unexpected issues in the tool. Differences found:\n\n"
        + "\n".join(diffs)
        + "\n\nSelect \"Select different file\" to choose another save file,\n"
        "or choose \"Ignore\" to continue anyway."
    )
    lbl = tk.Label(top, text=msg, justify="left", wraplength=700)
    lbl.pack(padx=12, pady=(12, 8), fill="both", expand=True)

    # Buttons frame
    btn_frame = ttk.Frame(top)
    btn_frame.pack(padx=12, pady=(0, 12), anchor="e")

    # result capture for modal mode
    result = {"action": None, "path": None}

    def _validate_and_apply_new_path(new_path):
        """
        Validate new_path contents and, on success, persist it and refresh UI.
        Returns True on success, False otherwise.
        """
        try:
            with open(new_path, "r", encoding="utf-8") as f:
                new_content = f.read()
            # reuse the parser you already have
            m, r, xp, d, t, s, day, night, tp = get_file_info(new_content)
            try:
                _sync_time_ui(day=day, night=night, skip_time=s)
            except Exception as e:
                print("[WATCH] Failed to refresh Time tab:", e)

            if day is None or night is None:
                raise ValueError("Missing time settings")

            # persist the new path (so autoload works on next launch)
            try:
                save_path(new_path)
            except Exception:
                # non-fatal: warn in console
                print("Warning: failed to persist save path to config")
            # refresh all GUI values if helper exists
            try:
                if "_refresh_all_tabs_from_save" in globals():
                    globals()["_refresh_all_tabs_from_save"](new_path)
                elif "sync_all_rules" in globals():
                    globals()["sync_all_rules"](new_path)
            except Exception:
                pass

            return True
        except Exception as e:
            messagebox.showerror(
                "Save File Corrupted",
                f"Could not load save file:\n{new_path}\n\nThe file appears to be corrupted or incomplete."
            )
            return False

    # --- modal handlers ---
    def _handle_select_modal():
        new = filedialog.askopenfilename(filetypes=[("SnowRunner Save", "*.cfg *.dat")])
        if new:
            # validate first
            if _validate_and_apply_new_path(new):
                result["action"] = "select"
                result["path"] = new
                top.destroy()
            else:
                # keep dialog open if validation failed
                return
        else:
            # user cancelled file dialog: keep the version dialog open
            return

    def _handle_ignore_modal():
        result["action"] = "ok"
        top.destroy()

    # --- non-modal handlers (buttons do their own work) ---
    def _handle_select_nonmodal():
        new = filedialog.askopenfilename(
            initialdir=os.path.dirname(path) if os.path.isdir(os.path.dirname(path)) else None,
            filetypes=[("SnowRunner Save", "*.cfg *.dat")]
        )
        if not new:
            return  # user cancelled; leave non-modal dialog open

        # validate and apply immediately
        if _validate_and_apply_new_path(new):
            # close the dialog after successful selection
            top.destroy()
            # Non-modal flow doesn't return; it applied new path itself.
        else:
            # validation failed — keep dialog open
            return

    def _handle_ignore_nonmodal():
        top.destroy()

    # Add buttons (use the appropriate handlers depending on modal flag)
    if modal:
        ttk.Button(btn_frame, text="Select different file", command=_handle_select_modal).pack(side="right", padx=(6, 0))
        ttk.Button(btn_frame, text="Ignore", command=_handle_ignore_modal).pack(side="right")
        # block until window is closed (modal)
        top.wait_window()
        return (result["action"], result["path"])
    else:
        ttk.Button(btn_frame, text="Select different file", command=_handle_select_nonmodal).pack(side="right", padx=(6, 0))
        ttk.Button(btn_frame, text="Ignore", command=_handle_ignore_nonmodal).pack(side="right")
        # non-blocking: return immediately (dialog handles its own actions)
        return None

# --- end replacement helper ---

def try_autoload_last_save(save_path_var):
    last_path = load_last_path()
    if not last_path:
        return

    if not os.path.exists(last_path):
        messagebox.showerror(
            "Save File Missing",
            f"Could not load save file:\n{last_path}\n\nThe file does not exist."
        )
        save_path_var.set("")
        return

    try:
        with open(last_path, "r", encoding="utf-8") as f:
            content = f.read()

        # Try parsing the save — if anything fails, it’s corrupted
        money, rank, xp, difficulty, truck_avail, skip_time, day, night, truck_price = get_file_info(content)

        # If day or night is None → treat as corruption
        if day is None or night is None:
            raise ValueError("Missing time settings")

        # DO NOT prompt immediately here — accept the path now so GUI can finish loading.
        save_path_var.set(last_path)

        # (The delayed, non-blocking version-check will run separately after startup)
    except Exception:
        messagebox.showerror(
            "Save File Corrupted",
            f"Could not load save file:\n{last_path}\n\nThe file appears to be corrupted or incomplete."
        )
        save_path_var.set("")


def save_path(path):
    if "dont_remember_path_var" in globals() and dont_remember_path_var.get():
        return
    _update_config_values({"last_save_path": path})


# =============================================================================
# SECTION: Optional Improve Upload Helpers
# Used In: Save File tab ("Make editor better" checkbox)
# =============================================================================
def get_improve_upload_endpoint():
    return str(IMPROVE_UPLOAD_ENDPOINT or "").strip()


def is_improve_upload_endpoint_configured(endpoint_override=None):
    endpoint = str(endpoint_override or get_improve_upload_endpoint()).strip()
    if not re.match(r"^https://[^ ]+$", endpoint, flags=re.IGNORECASE):
        return False
    if re.search(r"your-worker\.workers\.dev|example\.workers\.dev", endpoint, flags=re.IGNORECASE):
        return False
    return True


def collect_improve_share_entries(folder_path: str):
    """Collect top-level save files from folder matching allowed prefixes."""
    if not folder_path or not os.path.isdir(folder_path):
        return []

    entries = []
    allowed_prefixes = ("commonsslsave", "completesave")

    try:
        names = sorted(os.listdir(folder_path), key=lambda n: str(n).lower())
    except Exception:
        return []

    for name in names:
        name_lower = str(name).lower()
        if not name_lower.startswith(allowed_prefixes):
            continue
        abs_path = os.path.join(folder_path, name)
        if not os.path.isfile(abs_path):
            continue

        try:
            size = int(os.path.getsize(abs_path))
        except Exception:
            continue

        entries.append(
            {
                "name": str(name),
                "path": abs_path,
                "size": size,
            }
        )

    return entries


def get_improve_share_signature(folder_path: str, entries):
    if not entries:
        return ""
    parts = []
    for entry in entries:
        try:
            name = str(entry.get("name", "")).lower()
            size = int(entry.get("size", 0))
            parts.append(f"{name}:{size}")
        except Exception:
            continue
    parts.sort()
    base = os.path.abspath(str(folder_path or "")).lower()
    payload = f"{base}|{'|'.join(parts)}"
    return hashlib.sha1(payload.encode("utf-8", errors="ignore")).hexdigest()


def _encode_multipart_form_data(fields, files):
    boundary = "----SnowRunnerEditorBoundary" + uuid.uuid4().hex
    body = bytearray()

    for key, value in (fields or {}).items():
        body.extend(f"--{boundary}\r\n".encode("utf-8"))
        body.extend(f'Content-Disposition: form-data; name="{key}"\r\n\r\n'.encode("utf-8"))
        body.extend(str(value).encode("utf-8"))
        body.extend(b"\r\n")

    for item in files or []:
        field_name = str(item.get("field", "files"))
        filename = str(item.get("filename", "file.bin")).replace('"', "")
        content_type = str(item.get("content_type", "application/octet-stream"))
        data = item.get("data", b"")
        if not isinstance(data, (bytes, bytearray)):
            data = bytes(data)

        body.extend(f"--{boundary}\r\n".encode("utf-8"))
        body.extend(
            f'Content-Disposition: form-data; name="{field_name}"; filename="{filename}"\r\n'.encode("utf-8")
        )
        body.extend(f"Content-Type: {content_type}\r\n\r\n".encode("utf-8"))
        body.extend(data)
        body.extend(b"\r\n")

    body.extend(f"--{boundary}--\r\n".encode("utf-8"))
    content_type_header = f"multipart/form-data; boundary={boundary}"
    return bytes(body), content_type_header


def upload_improve_samples_from_entries(entries, endpoint=None, source="snowrunner-save-editor-desktop", folder_root=""):
    target = str(endpoint or get_improve_upload_endpoint()).strip()
    if not is_improve_upload_endpoint_configured(target):
        raise RuntimeError("Worker URL is not configured.")

    valid_entries = []

    for entry in entries or []:
        if not isinstance(entry, dict):
            continue
        name = str(entry.get("name", "")).strip()
        path = str(entry.get("path", "")).strip()
        if not name or not path or not os.path.isfile(path):
            continue
        valid_entries.append({"name": name, "path": path})

    if not valid_entries:
        raise RuntimeError("No readable top-level files were available for upload.")

    try:
        max_files_per_request = max(1, int(IMPROVE_UPLOAD_MAX_FILES_PER_REQUEST))
    except Exception:
        max_files_per_request = 6
    try:
        chunk_pause_seconds = max(0.0, float(IMPROVE_UPLOAD_BETWEEN_CHUNKS_MS) / 1000.0)
    except Exception:
        chunk_pause_seconds = 0.0
    timeout_seconds = max(1.0, float(IMPROVE_UPLOAD_TIMEOUT_MS) / 1000.0)

    base_headers = {
        "User-Agent": "SnowRunnerEditor/1.0",
        "Accept": "application/json",
    }
    origin_header = str(IMPROVE_UPLOAD_ORIGIN_HEADER or "").strip()
    referer_header = str(IMPROVE_UPLOAD_REFERER_HEADER or "").strip()
    if origin_header:
        base_headers["Origin"] = origin_header
    if referer_header:
        base_headers["Referer"] = referer_header

    def _post_worker_chunk(body_bytes, content_type_header, chunk_label):
        headers = dict(base_headers)
        headers["Content-Type"] = content_type_header
        req = urllib.request.Request(
            target,
            data=body_bytes,
            headers=headers,
            method="POST",
        )
        raw_body = ""
        status = 0

        try:
            with urllib.request.urlopen(req, timeout=timeout_seconds) as resp:
                status = int(getattr(resp, "status", 0) or resp.getcode() or 0)
                raw_body = resp.read().decode("utf-8", errors="replace")
        except urllib.error.HTTPError as http_err:
            http_body = ""
            try:
                http_body = http_err.read().decode("utf-8", errors="replace")
            except Exception:
                pass

            payload = None
            if http_body:
                try:
                    payload = json.loads(http_body)
                except Exception:
                    payload = None

            if isinstance(payload, dict) and payload.get("error"):
                raise RuntimeError(f"{chunk_label}: {payload.get('error')}")
            if http_body:
                raise RuntimeError(f"{chunk_label}: {http_body}")
            raise RuntimeError(f"{chunk_label}: HTTP {getattr(http_err, 'code', 'error')}")
        except Exception as err:
            message = str(err or "Unknown error")
            if "timed out" in message.lower():
                raise RuntimeError(f"{chunk_label}: Request timed out.")
            raise RuntimeError(message)

        payload = None
        if raw_body:
            try:
                payload = json.loads(raw_body)
            except Exception:
                payload = None

        if status < 200 or status >= 300:
            if isinstance(payload, dict) and payload.get("error"):
                raise RuntimeError(f"{chunk_label}: {payload.get('error')}")
            if raw_body:
                raise RuntimeError(f"{chunk_label}: {raw_body}")
            raise RuntimeError(f"{chunk_label}: HTTP {status}")

        if not isinstance(payload, dict):
            raise RuntimeError(f"{chunk_label}: Worker did not return JSON.")

        return payload

    total = len(valid_entries)
    total_chunks = max(1, (total + max_files_per_request - 1) // max_files_per_request)
    batch_id = "desktop-" + uuid.uuid4().hex
    uploaded = []
    ignored = []
    failed = []
    uploaded_count = 0
    ignored_count = 0
    failed_count = 0

    for chunk_index in range(total_chunks):
        start = chunk_index * max_files_per_request
        end = min(start + max_files_per_request, total)
        chunk_entries = valid_entries[start:end]
        chunk_label = f"Upload chunk {chunk_index + 1}/{total_chunks}"

        file_parts = []
        for entry in chunk_entries:
            name = str(entry.get("name", "")).strip()
            path = str(entry.get("path", "")).strip()
            if not name or not path or not os.path.isfile(path):
                continue
            try:
                with open(path, "rb") as fh:
                    data = fh.read()
            except Exception:
                continue

            file_parts.append(
                {
                    "field": "files",
                    "filename": name,
                    "content_type": "application/octet-stream",
                    "data": data,
                }
            )

        if not file_parts:
            continue

        fields = {
            "source": str(source or "snowrunner-save-editor-desktop"),
            "folderRoot": str(folder_root or ""),
            "uploadedAt": datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z"),
            "batchId": batch_id,
            "chunkIndex": str(chunk_index + 1),
            "chunkTotal": str(total_chunks),
        }
        body, content_type_header = _encode_multipart_form_data(fields, file_parts)
        try:
            payload = _post_worker_chunk(body, content_type_header, chunk_label)
        except Exception as err:
            failed.append(
                {
                    "name": f"[chunk {chunk_index + 1}]",
                    "reason": str(err or "Chunk upload error"),
                }
            )
            failed_count += 1
            if (chunk_index + 1) < total_chunks and chunk_pause_seconds > 0:
                time.sleep(chunk_pause_seconds)
            continue

        returned_batch_id = str(payload.get("batchId") or payload.get("id") or "").strip()
        if returned_batch_id:
            batch_id = returned_batch_id

        chunk_uploaded = payload.get("uploaded")
        chunk_ignored = payload.get("ignored")
        chunk_failed = payload.get("failed")
        if isinstance(chunk_uploaded, list):
            uploaded.extend(chunk_uploaded)
        if isinstance(chunk_ignored, list):
            ignored.extend(chunk_ignored)
        if isinstance(chunk_failed, list):
            failed.extend(chunk_failed)

        try:
            uploaded_count += int(payload.get("uploadedCount", 0))
        except Exception:
            uploaded_count += len(chunk_uploaded) if isinstance(chunk_uploaded, list) else 0
        try:
            ignored_count += int(payload.get("ignoredCount", 0))
        except Exception:
            ignored_count += len(chunk_ignored) if isinstance(chunk_ignored, list) else 0
        try:
            failed_count += int(payload.get("failedCount", 0))
        except Exception:
            failed_count += len(chunk_failed) if isinstance(chunk_failed, list) else 0

        if (chunk_index + 1) < total_chunks and chunk_pause_seconds > 0:
            time.sleep(chunk_pause_seconds)

    if uploaded_count <= 0 and not uploaded:
        first_error = ""
        if failed and isinstance(failed[0], dict):
            first_error = str(failed[0].get("reason") or "").strip()
        if first_error:
            raise RuntimeError(f"No files were uploaded. First error: {first_error}")
        raise RuntimeError("No files were uploaded.")

    if uploaded_count <= 0:
        uploaded_count = len(uploaded)
    if ignored_count < len(ignored):
        ignored_count = len(ignored)
    if failed_count < len(failed):
        failed_count = len(failed)

    first_error = ""
    if failed and isinstance(failed[0], dict):
        first_error = str(failed[0].get("reason") or "").strip()

    return {
        "success": uploaded_count > 0,
        "error": first_error,
        "id": batch_id,
        "batchId": batch_id,
        "uploadedCount": uploaded_count,
        "ignoredCount": ignored_count,
        "failedCount": failed_count,
        "uploaded": uploaded,
        "ignored": ignored,
        "failed": failed,
    }

# -----------------------------------------------------------------------------
# END SECTION: Save-File IO + Version Safety
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Save Parsing + Common Extractors
# Used In: sync_all_rules, Money & Rank tab, Time tab
# =============================================================================
def get_file_info(content):
    truck_price = int(re.search(r'"truckPricingFactor"\s*:\s*(\d+)', content).group(1)) if re.search(r'"truckPricingFactor"\s*:\s*(\d+)', content) else 1

    def search_num(key):
        match = re.search(rf'"{key}"\s*:\s*(-?\d+(\.\d+)?(e[-+]?\d+)?)', content)
        return float(match.group(1)) if match else None

    # helper: return the maximum integer value for all occurrences of the given key, or None
    def read_max_int(key):
        matches = re.findall(rf'"{re.escape(key)}"\s*:\s*(-?\d+)', content, flags=re.IGNORECASE)
        if not matches:
            return None
        vals = []
        for m in matches:
            try:
                vals.append(int(m))
            except Exception:
                continue
        return max(vals) if vals else None

    money_val = read_max_int("money")   # read_max_int is already defined in get_file_info
    money = int(money_val) if money_val is not None else 0
    
    # prefer the largest value found in the file (some saves have duplicates)
    rank_val = read_max_int("rank")
    rank = int(rank_val) if rank_val is not None else 0

    xp_val = read_max_int("experience")
    xp = int(xp_val) if xp_val is not None else 0

    difficulty = int(re.search(r'"gameDifficultyMode"\s*:\s*(\d+)', content).group(1)) if re.search(r'"gameDifficultyMode"\s*:\s*(\d+)', content) else 0
    truck_avail = int(re.search(r'"truckAvailability"\s*:\s*(\d+)', content).group(1)) if re.search(r'"truckAvailability"\s*:\s*(\d+)', content) else 0

    skip_match = re.search(r'"isAbleToSkipTime"\s*:\s*(true|false)', content, flags=re.IGNORECASE)
    skip_time = skip_match.group(1).lower() == 'true' if skip_match else False

    day = search_num("timeSettingsDay")
    night = search_num("timeSettingsNight")
    return money, rank, xp, difficulty, truck_avail, skip_time, day, night, truck_price

# -----------------------------------------------------------------------------
# END SECTION: Save Parsing + Common Extractors
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Time UI Sync Helpers
# Used In: sync_all_rules, time preset selection, save reloads
# =============================================================================
def _sync_time_ui(day=None, night=None, skip_time=None, preset_name=None):
    """Update time-related tkinter vars safely without recursion."""
    global _TIME_SYNC_GUARD
    _TIME_SYNC_GUARD = True
    try:
        # Day/night sliders + entries
        if "custom_day_var" in globals() and custom_day_var is not None:
            try:
                if day is None:
                    custom_day_var.set(1.0)
                else:
                    custom_day_var.set(round(float(day), 2))
            except Exception:
                custom_day_var.set(1.0)

        if "custom_night_var" in globals() and custom_night_var is not None:
            try:
                if night is None:
                    custom_night_var.set(1.0)
                else:
                    custom_night_var.set(round(float(night), 2))
            except Exception:
                custom_night_var.set(1.0)

        # Keep raw stringvars in sync too (if used elsewhere)
        if "time_day_var" in globals() and time_day_var is not None:
            try:
                if day is not None:
                    time_day_var.set(str(day))
            except Exception:
                pass
        if "time_night_var" in globals() and time_night_var is not None:
            try:
                if night is not None:
                    time_night_var.set(str(night))
            except Exception:
                pass

        # Skip-time checkbox
        if "skip_time_var" in globals() and skip_time_var is not None and skip_time is not None:
            try:
                skip_time_var.set(bool(skip_time))
            except Exception:
                pass

        # Preset combobox
        if "time_preset_var" in globals() and time_preset_var is not None:
            preset_to_set = preset_name
            if preset_to_set is None and day is not None and night is not None:
                preset_to_set = "Custom"
                try:
                    for preset_name_it, (p_day, p_night) in time_presets.items():
                        if (
                            abs(float(day) - float(p_day)) < 0.01
                            and abs(float(night) - float(p_night)) < 0.01
                        ):
                            preset_to_set = preset_name_it
                            break
                except Exception:
                    preset_to_set = "Custom"
            if preset_to_set is not None:
                try:
                    time_preset_var.set(preset_to_set)
                except Exception:
                    pass
    finally:
        _TIME_SYNC_GUARD = False

# -----------------------------------------------------------------------------
# END SECTION: Time UI Sync Helpers
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Time Settings (Time tab)
# Used In: Time tab -> Apply Time Settings
# =============================================================================
def modify_time(file_path, time_day, time_night, skip_time):
    with open(file_path, 'r', encoding='utf-8') as file:
        content = file.read()
    content = re.sub(r'("timeSettingsDay"\s*:\s*)-?\d+(\.\d+)?(e[-+]?\d+)?', lambda m: f'{m.group(1)}{time_day}', content)
    content = re.sub(r'("timeSettingsNight"\s*:\s*)-?\d+(\.\d+)?(e[-+]?\d+)?', lambda m: f'{m.group(1)}{time_night}', content)
    content = re.sub(r'("isAbleToSkipTime"\s*:\s*)(true|false)', lambda m: f'{m.group(1)}{"true" if skip_time else "false"}', content)
    with open(file_path, 'w', encoding='utf-8') as out_file:
        out_file.write(content)
    show_info("Success", "Time updated.")

# -----------------------------------------------------------------------------
# END SECTION: Time Settings (Time tab)
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Missions Completion (Missions tab)
# Used In: Missions tab -> Complete Selected Missions
# =============================================================================
def complete_seasons_and_maps(file_path, selected_seasons, selected_maps):
    with open(file_path, 'r', encoding='utf-8') as file:
        content = file.read()

    start = content.find('"objectiveStates"')
    if start == -1:
        messagebox.showerror("Error", "'objectiveStates' not found in save file.")
        return

    block_str, block_start, block_end = extract_brace_block(content, start)
    obj_states = json.loads(block_str)
    modified = False

    for key in obj_states:
        for season in selected_seasons:
            map_id = SEASON_ID_MAP.get(season)
            if map_id and map_id in key:
                obj_states[key]["isFinished"] = True
                obj_states[key]["wasCompletedAtLeastOnce"] = True
                modified = True
            elif f"_{season:02}_" in key:
                obj_states[key]["isFinished"] = True
                obj_states[key]["wasCompletedAtLeastOnce"] = True
                modified = True

        for map_id in selected_maps:
            if map_id in key:
                obj_states[key]["isFinished"] = True
                obj_states[key]["wasCompletedAtLeastOnce"] = True
                modified = True

    if not modified:
        show_info("Notice", "No matching missions found.")
        return

    new_block_str = json.dumps(obj_states, separators=(",", ":"))
    content = content[:block_start] + new_block_str + content[block_end:]
    with open(file_path, 'w', encoding='utf-8') as out_file:
        out_file.write(content)

    show_info("Success", "Selected missions marked complete.")

# -----------------------------------------------------------------------------
# END SECTION: Missions Completion (Missions tab)
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Rules Tab Sync Stubs
# Used In: Rules tab is currently disabled; kept for compatibility
# =============================================================================
def sync_rule_dropdowns(path):
    """Stub: rule dropdown sync disabled because rules tab was removed."""
    return
def sync_factor_rule_dropdowns(file_path):
    """Stub: factor rule sync disabled because rules tab was removed."""
    return

# -----------------------------------------------------------------------------
# END SECTION: Rules Tab Sync Stubs
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: JSON Block Parsing + Contest/Mission Helpers
# Used In: Contests tab, Objectives tab
# =============================================================================
def extract_brace_block(s, start_index):
    open_braces = 0
    in_string = False
    escape = False
    block_start = None
    for i in range(start_index, len(s)):
        char = s[i]
        if char == '"' and not escape:
            in_string = not in_string
        if not in_string:
            if char == '{':
                if open_braces == 0:
                    block_start = i
                open_braces += 1
            elif char == '}':
                open_braces -= 1
                if open_braces == 0 and block_start is not None:
                    return s[block_start:i+1], block_start, i+1
        escape = (char == '\\' and not escape)
    raise ValueError("Matching closing brace not found.")

def extract_bracket_block(s, start_index):
    open_brackets = 0
    in_string = False
    escape = False
    block_start = None
    for i in range(start_index, len(s)):
        char = s[i]
        if char == '"' and not escape:
            in_string = not in_string
        if not in_string:
            if char == '[':
                if open_brackets == 0:
                    block_start = i
                open_brackets += 1
            elif char == ']':
                open_brackets -= 1
                if open_brackets == 0 and block_start is not None:
                    return s[block_start:i+1], block_start, i+1
        escape = (char == '\\' and not escape)
    raise ValueError("Matching closing bracket not found.")
def update_all_contest_times_blocks(content, new_entries):
    matches = list(re.finditer(r'"contestTimes"\s*:\s*{', content))
    updated_content = content
    for match in reversed(matches):  # process backwards so offsets remain valid
        json_block, block_start, block_end = extract_brace_block(updated_content, match.end() - 1)
        try:
            parsed = json.loads(json_block)
        except Exception:
            # If parsing fails, skip this block
            continue
        changed = False
        for key, val in new_entries.items():
            if key not in parsed:
                parsed[key] = val
                changed = True
        if changed:
            new_block_str = json.dumps(parsed, separators=(",", ":"))
            updated_content = updated_content[:block_start] + new_block_str + updated_content[block_end:]
    return updated_content
def mark_discovered_contests_complete(save_path, selected_seasons, selected_maps, debug=False):
    """
    save_path: path to save file
    selected_seasons: list of ints (season numbers)
    selected_maps: list of map code strings (e.g. "US_01")
    debug: if True, prints debug info to stdout
    """
    make_backup_if_enabled(save_path)
    if not os.path.exists(save_path):
        messagebox.showerror("Error", "Save file not found.")
        return

    if debug:
        print(f"[DEBUG] mark_discovered_contests_complete called with seasons={selected_seasons} maps={selected_maps}")

    try:
        with open(save_path, "r", encoding="utf-8") as f:
            content = f.read()

        # Prepare mapping from seasons to canonical region codes
        selected_region_codes = [SEASON_ID_MAP[s] for s in selected_seasons if s in SEASON_ID_MAP]

        # We'll collect the union of contestTimes entries added while processing save blocks
        global_contest_times_new_entries = {}

        total_added = 0
        processed_blocks = 0

        # Find all CompleteSave* occurrences and process each
        for match in re.finditer(r'"(CompleteSave\d*)"\s*:\s*{', content):
            save_key = match.group(1)
            # extract the value block (the { ... } after the key:)
            value_block_str, val_block_start, val_block_end = extract_brace_block(content, match.end() - 1)
            # value_block_str is the JSON string for the value of the CompleteSave key
            try:
                value_data = json.loads(value_block_str)
            except Exception as e:
                # skip malformed blocks
                if debug:
                    print(f"[DEBUG] Skipping CompleteSave block {save_key} due to JSON parse error: {e}")
                continue

            # The SslValue might be directly inside value_data, or sometimes wrapped differently.
            ssl_value = value_data.get("SslValue") or value_data.get(save_key, {}).get("SslValue") or {}

            # discoveredObjectives can be a dict or a list; normalize an iterator over keys
            discovered_raw = ssl_value.get("discoveredObjectives", {})
            if isinstance(discovered_raw, dict):
                discovered_iter = list(discovered_raw.keys())
            elif isinstance(discovered_raw, list):
                discovered_iter = list(discovered_raw)
            else:
                discovered_iter = []

            # finishedObjs may be dict or list; keep original shape info
            orig_finished = ssl_value.get("finishedObjs", [])
            finished_is_dict = isinstance(orig_finished, dict)
            if isinstance(orig_finished, dict):
                finished_set = set(orig_finished.keys())
            elif isinstance(orig_finished, list):
                finished_set = set(orig_finished)
            else:
                finished_set = set()

            # contestTimes ensure dict
            contest_times = ssl_value.get("contestTimes", {})
            if not isinstance(contest_times, dict):
                contest_times = {}

            added_keys = []

            # For matching keys we'll:
            # - mark matches that contain selected region codes OR selected maps
            # - OR match by season token like _NN_ (two-digit season) if user selected that season
            season_tokens = [f"_{s:02}_" for s in selected_seasons]

            for key in discovered_iter:
                # key could be a non-string - skip if so
                if not isinstance(key, str):
                    continue

                # Basic heuristic: contest keys often include uppercase letters (A..Z) + map code / season tokens
                # We'll check for season token OR selected_region_codes OR selected_maps appearance in key
                matched = False
                # check season token (e.g. _01_)
                for token in season_tokens:
                    if token in key:
                        matched = True
                        break
                # check region codes and map ids
                if not matched:
                    for code in selected_region_codes + list(selected_maps):
                        if code and code in key:
                            matched = True
                            break

                if matched:
                    if key not in finished_set:
                        finished_set.add(key)
                        added_keys.append(key)
                    if key not in contest_times:
                        contest_times[key] = 1
                        global_contest_times_new_entries[key] = 1

            if added_keys:
                # update finishedObjs in same shape as original
                if finished_is_dict:
                    ssl_value["finishedObjs"] = {k: True for k in finished_set}
                else:
                    ssl_value["finishedObjs"] = list(finished_set)

                ssl_value["contestTimes"] = contest_times

                # remove these keys from viewedUnactivatedObjectives if that list exists
                viewed = ssl_value.get("viewedUnactivatedObjectives", [])
                if isinstance(viewed, list):
                    ssl_value["viewedUnactivatedObjectives"] = [v for v in viewed if v not in added_keys]

                # put SslValue back and serialize the value block back to JSON
                value_data["SslValue"] = ssl_value
                new_value_block_str = json.dumps(value_data, separators=(",", ":"))

                # replace this block in the file content
                content = content[:val_block_start] + new_value_block_str + content[val_block_end:]

                # Advance subsequent match positions: since we replaced content, regex matches computed earlier may be off.
                # To keep things simple we will restart scanning from the beginning after a replacement.
                processed_blocks += 1
                total_added += len(added_keys)

                if debug:
                    print(f"[DEBUG] For {save_key}: added {len(added_keys)} keys")
                # restart scanning regardless (we will re-run the outer regex on the modified content)
                # break out of the for-loop so outer loop can restart
                break

        else:
            # executed if the for loop completed normally (no break)
            # nothing changed; proceed
            pass

        # If we made at least one replacement, re-run the processing loop until no more replacements occur.
        # This ensures we properly update multiple CompleteSave blocks even after earlier replacements changed offsets.
        # We limit the number of iterations to avoid infinite loops.
        max_iterations = 6
        it = 0
        while it < max_iterations:
            it += 1
            made_any = False
            for match in re.finditer(r'"(CompleteSave\d*)"\s*:\s*{', content):
                save_key = match.group(1)
                value_block_str, val_block_start, val_block_end = extract_brace_block(content, match.end() - 1)
                try:
                    value_data = json.loads(value_block_str)
                except Exception:
                    continue
                ssl_value = value_data.get("SslValue") or value_data.get(save_key, {}).get("SslValue") or {}
                discovered_raw = ssl_value.get("discoveredObjectives", {})
                if isinstance(discovered_raw, dict):
                    discovered_iter = list(discovered_raw.keys())
                elif isinstance(discovered_raw, list):
                    discovered_iter = list(discovered_raw)
                else:
                    discovered_iter = []

                orig_finished = ssl_value.get("finishedObjs", [])
                finished_is_dict = isinstance(orig_finished, dict)
                if isinstance(orig_finished, dict):
                    finished_set = set(orig_finished.keys())
                elif isinstance(orig_finished, list):
                    finished_set = set(orig_finished)
                else:
                    finished_set = set()

                contest_times = ssl_value.get("contestTimes", {})
                if not isinstance(contest_times, dict):
                    contest_times = {}

                added_keys = []
                season_tokens = [f"_{s:02}_" for s in selected_seasons]
                for key in discovered_iter:
                    if not isinstance(key, str):
                        continue
                    matched = False
                    for token in season_tokens:
                        if token in key:
                            matched = True
                            break
                    if not matched:
                        for code in selected_region_codes + list(selected_maps):
                            if code and code in key:
                                matched = True
                                break
                    if matched:
                        if key not in finished_set:
                            finished_set.add(key)
                            added_keys.append(key)
                        if key not in contest_times:
                            contest_times[key] = 1
                            global_contest_times_new_entries[key] = 1

                if added_keys:
                    if finished_is_dict:
                        ssl_value["finishedObjs"] = {k: True for k in finished_set}
                    else:
                        ssl_value["finishedObjs"] = list(finished_set)
                    ssl_value["contestTimes"] = contest_times
                    viewed = ssl_value.get("viewedUnactivatedObjectives", [])
                    if isinstance(viewed, list):
                        ssl_value["viewedUnactivatedObjectives"] = [v for v in viewed if v not in added_keys]
                    value_data["SslValue"] = ssl_value
                    new_value_block_str = json.dumps(value_data, separators=(",", ":"))
                    content = content[:val_block_start] + new_value_block_str + content[val_block_end:]
                    made_any = True
                    total_added += len(added_keys)
                    if debug:
                        print(f"[DEBUG] (iter {it}) For {save_key}: added {len(added_keys)} keys")
                    # break to restart scanning from beginning
                    break
            if not made_any:
                break

        # After processing CompleteSave blocks, merge contestTimes into other contestTimes blocks
        if global_contest_times_new_entries:
            content = update_all_contest_times_blocks(content, global_contest_times_new_entries)

        # Final write
        with open(save_path, "w", encoding="utf-8") as f:
            f.write(content)

        if total_added == 0:
            show_info("Info", "No new contests were modified.")
        else:
            show_info("Success", f"{total_added} contests marked as completed.")

    except Exception as e:
        messagebox.showerror("Error", repr(e))

# -----------------------------------------------------------------------------
# END SECTION: JSON Block Parsing + Contest/Mission Helpers
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Upgrades + Watchtowers Data & Helpers
# Used In: Upgrades tab, Watchtowers tab
# =============================================================================
# Canonical watchtower/upgrade lists (used to fill missing entries safely)
_UPGRADES_GIVER_UNLOCKS_JSON = """{
  "level_us_03_02": {
    "US_03_02_G_SCOUT_FINETUNE": 2,
    "US_03_02_BOAR_45318_SUS_HI": 2,
    "US_03_02_PAYSTAR_5600_TS": 2,
    "US_03_02_G_SPECIAL_FINETUNE": 2
  },
  "test_zone_color_summer": {
    "COLORTEST_UPGRADE": 0
  },
  "level_ru_08_02": {
    "RU_08_02_UPGRADE_GIVER": 2
  },
  "test_zone_color_winter": {
    "test_zone_upgrade": 0
  },
  "level_us_04_02": {
    "US_04_02_UPG_G": 2,
    "US_04_02_UPG_ANK": 2,
    "US_04_02_UPG_KOLOB": 2
  },
  "level_ru_03_01": {
    "RU_03_01_UPGRADE_01": 2,
    "RU_03_01_UPGRADE_03": 2,
    "RU_03_01_UPGRADE_05": 2,
    "RU_03_01_UPGRADE_02": 2,
    "RU_03_01_UPGRADE_04": 2
  },
  "level_us_16_02": {
    "US_16_02_UPG_01": 2,
    "US_16_02_UPG_02": 2
  },
  "level_us_02_03_new": {
    "US_02_03_UPG_01": 2,
    "US_02_03_UPG_02": 2,
    "US_02_03_UPG_05": 2,
    "US_02_03_UPG_04": 2,
    "US_02_03_UPG_06": 2,
    "US_02_03_UPG_07": 2
  },
  "level_us_01_02": {
    "US_01_02_UPGRADE_INTERN_SCOUT_SUSP_HIGH": 2,
    "US_01_02_UPGRADE_TRUCK_ENG": 2,
    "US_01_02_UPGRADE_CHEVY_DIFF_LOCK": 2,
    "US_01_02_UPGRADE_GMC_DIFF_LOCK": 2,
    "US_01_02_UPGRADE_WHITE_ALLWHEELS": 2,
    "US_01_02_UPGRADE_WHITE_SUSP_HIGH": 2,
    "US_01_02_UPGRADE_TRUCK_ENG_4070": 2,
    "US_01_02_UPGRADE_G_SCOUT_HIGHWAY": 2
  },
  "level_ru_13_01": {
    "RU_13_01_UPGRADE_04": 2,
    "RU_13_01_UPGRADE_07": 2,
    "RU_13_01_UPGRADE_05": 2,
    "RU_13_01_UPGRADE_01": 2,
    "RU_13_01_UPGRADE_02": 2,
    "RU_13_01_UPGRADE_03": 2,
    "RU_13_01_UPGRADE_06": 2
  },
  "level_ru_08_01": {
    "RU_08_01_UPG": 2
  },
  "level_ru_08_03": {
    "RU_08_03_UPGRADE_GIVER_01": 2,
    "RU_08_03_UPGRADE_GIVER_02": 2
  },
  "level_us_12_02": {
    "US_12_02_UPG_02": 2,
    "US_12_02_UPG_01": 2
  },
  "level_us_02_01": {
    "US_02_01_UPG_06": 2,
    "US_02_01_UPG_02": 2,
    "US_02_01_UPG_01": 2,
    "US_02_01_UPG_04": 2,
    "US_02_01_UPG_08": 2,
    "US_02_01_UPG_05": 2,
    "US_02_01_UPG_09": 2,
    "US_02_01_UPG_07": 2
  },
  "level_us_06_01": {
    "US_06_01_UPG_01": 2
  },
  "level_us_01_03": {
    "US_01_03_UPG_3": 2,
    "US_01_03_UPG_2": 2,
    "US_01_03_UPG_6": 2,
    "US_01_03_UPG_4": 2
  },
  "level_us_15_02": {
    "US_15_02_UPG_01": 2,
    "US_15_02_UPG_02": 2
  },
  "level_us_12_03": {
    "US_12_03_UPGRADE_02": 2,
    "US_12_03_UPGRADE_01": 2
  },
  "level_us_14_01": {
    "US_14_01_UPG_02": 2,
    "US_14_01_UPG_01": 2
  },
  "level_us_01_01": {
    "US_01_01_UPGRADE_FLEESTAR_SUSP_HIGHT": 2,
    "US_01_01_UPGRADE_SCOUT_OLD_ENGINE": 2,
    "US_01_01_UPGRADE_FLEESTAR_ALLWHEELS": 2,
    "US_01_01_UPGRADE_TRUCK_OLD_ENGINE": 2,
    "US_01_01_UPGRADE_GMC_SUSP_HIGHT": 2,
    "US_01_01_UPGRADE_CK_SUSPENSION": 2,
    "US_01_01_UPGRADE_G_SCOUT_OFFROAD": 2
  },
  "level_ru_03_02": {
    "RU_03_02_UPG_2": 2,
    "RU_03_02_UPG_DETECTOR": 2,
    "RU_03_02_UPG_4": 2,
    "RU_03_02_UPG_5": 2,
    "RU_03_02_UPG_3": 2
  },
  "level_us_09_02": {
    "US_09_02_UPG_01": 2,
    "US_09_02_UPG_02": 2
  },
  "level_ru_05_01": {
    "RU_05_02_UPGRADE_03": 2
  },
  "level_ru_02_01_crop": {
    "RU_02_01_UPGRADE_02": 2,
    "RU_02_01_UPGRADE_04": 2,
    "RU_02_01_UPGRADE_07": 2,
    "RU_02_01_UPGRADE_01": 2,
    "RU_02_01_UPGRADE_08": 2,
    "RU_02_01_UPGRADE_06": 2,
    "RU_02_01_UPGRADE_03": 2
  },
  "level_us_03_01": {
    "US_03_01_UPG_01": 2,
    "US_03_01_UPG_03": 2,
    "US_03_01_UPG_02": 2,
    "US_03_01_UPG_04": 2
  },
  "level_us_16_03": {
    "US_16_03_UPG_01": 2,
    "US_16_03_UPG_02": 2
  },
  "level_ru_08_04": {
    "RU_08_04_UPGRADE_02": 2
  },
  "level_ru_17_01": {
    "RU_17_01_UPG_02": 2,
    "RU_17_01_UPG_01": 2
  },
  "level_us_14_02": {
    "US_14_02_UPG_02": 2,
    "US_14_02_UPG_01": 2
  },
  "level_us_01_04_new": {
    "US_01_04_UPG_1": 2,
    "US_01_04_UPG_3": 2
  },
  "level_us_04_01": {
    "US_04_01_UPG_03": 2,
    "US_04_01_UPG_01": 2,
    "US_04_01_UPG_02": 2
  },
  "level_us_12_04": {
    "US_12_04_UPG_02": 2,
    "US_12_04_UPG_01": 2
  },
  "level_us_16_01": {
    "US_16_01_UPG_01": 2,
    "US_16_01_UPG_02": 2
  },
  "level_us_10_02": {
    "US_10_02_UPG_01": 2
  },
  "level_ru_05_02": {
    "RU_05_02_UPGRADE_01": 2
  },
  "level_ru_17_02": {
    "RU_17_02_UPGRADE_01": 2,
    "RU_17_02_UPGRADE_02": 2
  },
  "level_us_06_02": {
    "US_06_02_UPG_01": 2,
    "US_06_02_UPG_03": 2,
    "US_06_02_UPG_02": 2,
    "US_06_02_UPG_04": 2
  },
  "level_us_02_04_new": {
    "US_02_04_UPG_3": 2,
    "US_02_04_UPG_2": 2,
    "US_02_04_UPG_1": 2,
    "US_02_04_UPG_5": 2
  },
  "level_us_10_01": {
    "US_10_01_UPG_02": 2,
    "US_10_01_UPG_01": 2
  },
  "level_us_02_02_new": {
    "US_02_02_UPG_01": 2,
    "US_02_02_UPG_05": 2,
    "US_02_02_UPG_06": 2,
    "US_02_02_UPG_02": 2,
    "US_02_02_UPG_04": 2
  },
  "level_ru_04_03": {
    "RU_04_03_UPGRADE_01": 2
  },
  "level_ru_02_02": {
    "RU_02_02_UPGRADE_06": 2,
    "RU_02_02_UPGRADE_09": 2,
    "RU_02_02_UPGRADE_01": 2,
    "RU_02_02_UPGRADE_04": 2,
    "RU_02_02_UPGRADE_05": 2,
    "RU_02_02_UPGRADE_03": 2,
    "RU_02_02_UPGRADE_02": 2,
    "RU_02_02_UPGRADE_08": 2
  },
  "level_ru_04_01": {
    "RU_04_01_KHAN_UPG": 2
  },
  "level_us_15_01": {
    "US_15_01_UPG_02": 2,
    "US_15_01_UPG_01": 2
  },
  "level_ru_02_03": {
    "RU_02_03_UPGRADE8": 2,
    "RU_02_03_UPGRADE1": 2,
    "RU_02_03_UPGRADE7": 2,
    "RU_02_03_UPGRADE4": 2,
    "RU_02_03_UPGRADE6": 2,
    "RU_02_03_UPGRADE5": 2
  },
  "level_ru_04_02": {
    "RU_04_02_UPGRADE_01": 2
  },
  "level_ru_02_04": {
    "RU_02_04_UPGRADE_03": 2,
    "RU_02_04_UPGRADE_01": 2,
    "RU_02_04_UPGRADE_02": 2
  },
  "level_us_11_01": {
    "US_11_01_UPG_01": 2
  },
  "level_us_07_01": {
    "US_07_01_UPGRADE_02": 2,
    "US_07_01_UPGRADE_04": 2,
    "US_07_01_UPGRADE_01": 2,
    "US_07_01_UPGRADE_03": 2
  },
  "level_ru_04_04": {
    "RU_04_04_UPG_01": 2,
    "RU_04_04_UPG_02": 2
  },
  "level_us_11_02": {
    "US_11_02_ADDON": 2
  },
  "level_us_12_01": {
    "US_12_01_UPGRADE": 2
  },
  "level_us_09_01": {
    "US_09_01_UPG_02": 2,
    "US_09_01_UPG_01": 2
  }
}"""
UPGRADES_GIVER_UNLOCKS = json.loads(_UPGRADES_GIVER_UNLOCKS_JSON)

_WATCHPOINTS_UNLOCKS_JSON = """{
  "level_ru_03_01": {
    "RU_03_01_WATCHPOINT_0": true,
    "RU_03_01_WATCHPOINT_1": true,
    "RU_03_01_WATCHPOINT_2": true
  },
  "level_us_16_02": {
    "US_16_02_WATCHPOINT_04": true,
    "US_16_02_WATCHPOINT_03": true,
    "US_16_02_WATCHPOINT_01": true,
    "US_16_02_WATCHPOINT_02": true
  },
  "level_us_02_03_new": {
    "US_02_03_WP_03": true,
    "US_02_03_WP_01": true,
    "US_02_03_WP_05": true,
    "US_02_03_WP_04": true,
    "US_02_03_WP_02": true
  },
  "level_us_01_02": {
    "US_01_02_W7": true,
    "US_01_02_W1": true,
    "US_01_02_W4": true,
    "US_01_02_W2": true,
    "US_01_02_W3": true,
    "US_01_02_W5": true
  },
  "level_ru_13_01": {
    "RU_13_01_WATCHPOINT_01": true,
    "RU_13_01_WATCHPOINT_02": true,
    "RU_13_01_WATCHPOINT_04": true,
    "RU_13_01_WATCHPOINT_03": true
  },
  "level_ru_08_01": {
    "RU_08_01_WATCHPOINT_1": true,
    "RU_08_01_WATCHPOINT_2": true,
    "RU_08_01_WATCHPOINT_3": true,
    "RU_08_01_WATCHPOINT_4": true
  },
  "level_ru_08_03": {
    "WATCHPOINT_01": true,
    "WATCHPOINT_02": true
  },
  "level_us_12_02": {
    "US_12_02_WATCHPOINT_02": true,
    "US_12_02_WATCHPOINT_03": true,
    "US_12_02_WATCHPOINT_01": true,
    "US_12_02_WATCHPOINT_04": true,
    "US_12_02_WATCHPOINT_05": true
  },
  "level_us_02_01": {
    "US_02_01_WP_04": true,
    "US_02_01_WP_03": true,
    "US_02_01_WP_01": true,
    "US_02_01_WP_02": true
  },
  "level_us_06_01": {
    "US_06_01_WT_02": true,
    "US_06_01_WT_04": true,
    "US_06_01_WT_01": true,
    "US_06_01_WT_03": true
  },
  "level_us_01_03": {
    "US_01_03_W6": true,
    "US_01_03_W5": true,
    "US_01_03_W8": true,
    "US_01_03_W3": true,
    "US_01_03_W1": true,
    "US_01_03_W2": true,
    "US_01_03_W7": true,
    "US_01_03_W4": true
  },
  "level_ru_05_01": {
    "RU_05_01_TOWER": true,
    "WATCHPOINT": true
  },
  "level_ru_02_01_crop": {
    "WATCHPOINT_HILL_EAST": true,
    "WATCHPOINT_CHURCH_NORTH": true,
    "WATCHPOINT_HILL_SOUTH": true,
    "WATCHPOINT_SWAMP_EAST": true,
    "WATCHPOINT_HILL_SOUTHWEST": true,
    "WATCHPOINT_CLIFFSIDE_WEST": true
  },
  "level_ru_04_03": {
    "WATCHPOINT_SE": true,
    "WATCHPOINT_C": true,
    "WATCHPOINT_W": true
  },
  "level_ru_02_02": {
    "RU_02_02_W1": true,
    "RU_02_02_W3": true,
    "RU_02_02_W2": true
  },
  "level_us_15_02": {
    "US_15_02_WATCHPOINT_03": true,
    "US_15_02_WATCHPOINT_01": true,
    "US_15_02_WATCHPOINT_02": true,
    "US_15_02_WATCHPOINT_04": true
  },
  "level_us_12_03": {
    "US_12_03_WATCHPOINT_02": true,
    "US_12_03_WATCHPOINT_03": true,
    "US_12_03_WATCHPOINT_01": true
  },
  "level_us_14_01": {
    "US_14_01_WATCHPOINT_03": true,
    "US_14_01_WATCHPOINT_02": true,
    "US_14_01_WATCHPOINT_01": true,
    "US_14_01_WATCHPOINT_04": true
  },
  "level_us_01_01": {
    "US_01_01_W5": true,
    "US_01_01_W1": true,
    "US_01_01_W6": true,
    "US_01_01_W3": true,
    "US_01_01_W7": true,
    "US_01_01_W9": true,
    "US_01_01_W4": true,
    "US_01_01_W8": true
  },
  "level_ru_03_02": {
    "RU_03_02_WATCHTOWER_1": true,
    "RU_03_02_WATCHTOWER_2": true,
    "RU_03_02_WATCHTOWER_4": true
  },
  "level_us_09_02": {
    "US_09_02_WATCHPOINT_03": true,
    "US_09_02_WATCHPOINT_02": true,
    "US_09_02_WATCHPOINT_01": true
  },
  "level_us_03_01": {
    "US_03_01_WP_01": true,
    "US_03_01_WP_03": true,
    "US_03_01_WP_02": true
  },
  "level_us_16_03": {
    "US_16_03_WATCHPOINT_03": true,
    "US_16_03_WATCHPOINT_02": true,
    "US_16_03_WATCHPOINT_01": true,
    "US_16_03_WATCHPOINT_04": true
  },
  "level_ru_08_04": {
    "WATCHPOINT_01": true,
    "WATCHPOINT_02": true,
    "WATCHPOINT_03": true
  },
  "level_ru_17_01": {
    "RU_17_01_WATCHTOWER_05": true,
    "RU_17_01_WATCHTOWER_04": true,
    "RU_17_01_WATCHTOWER_03": true,
    "RU_17_01_WATCHTOWER_02": true,
    "RU_17_01_WATCHTOWER_01": true
  },
  "level_us_14_02": {
    "US_14_02_WATCHPOINT_01": true,
    "US_14_02_WATCHPOINT_03": true,
    "US_14_02_WATCHPOINT_02": true
  },
  "level_us_01_04_new": {
    "US_01_04_W3": true,
    "US_01_04_W1": true,
    "US_01_04_W2": true,
    "US_01_04_W4": true
  },
  "level_us_04_01": {
    "US_04_01_WT_04": true,
    "US_04_01_WT_01": true,
    "US_04_01_WT_03": true,
    "US_04_01_WT_02": true
  },
  "level_us_12_04": {
    "US_12_04_WATCHPOINT_04": true,
    "US_12_04_WATCHPOINT_03": true,
    "US_12_04_WATCHPOINT_02": true,
    "US_12_04_WATCHPOINT_01": true
  },
  "level_us_16_01": {
    "US_16_01_WATCHTOWER_01": true,
    "US_16_01_WATCHTOWER_05": true,
    "US_16_01_WATCHTOWER_04": true,
    "US_16_01_WATCHTOWER_03": true,
    "US_16_01_WATCHTOWER_02": true
  },
  "level_us_10_02": {
    "US_10_02_WP_07": true,
    "US_10_02_WP_01": true,
    "US_10_02_WP_02": true,
    "US_10_02_WP_06": true,
    "US_10_02_WP_05": true,
    "US_10_02_WP_04": true,
    "US_10_02_WP_03": true
  },
  "level_ru_05_02": {
    "WATCHPOINT": true
  },
  "level_ru_17_02": {
    "RU_17_02_WATCHPOINT_05": true,
    "RU_17_02_WATCHPOINT_04": true,
    "RU_17_02_WATCHPOINT_03": true,
    "RU_17_02_WATCHPOINT_02": true,
    "RU_17_02_WATCHPOINT_01": true
  },
  "level_ru_08_02": {
    "WATCHPOINT_01": true,
    "WATCHPOINT_02": true,
    "WATCHPOINT_03": true
  },
  "level_us_04_02": {
    "US_04_02_W1": true,
    "US_04_02_W4": true,
    "US_04_02_W3": true,
    "US_04_02_W5": true,
    "US_04_02_W7": true,
    "US_04_02_W2": true,
    "US_04_02_W6": true
  },
  "level_us_06_02": {
    "US_06_02_W2": true,
    "US_06_02_W3": true,
    "US_06_02_BIG_WATCHTOWER": true
  },
  "level_us_02_04_new": {
    "US_02_04_W3": true,
    "US_02_04_W1": true,
    "US_02_04_W2": true,
    "US_02_04_W4": true
  },
  "level_us_10_01": {
    "US_10_01_WP_03": true,
    "US_10_01_WP_06": true,
    "US_10_01_WP_08": true,
    "US_10_01_WP_04": true,
    "US_10_01_WP_15": true,
    "US_10_01_WP_14": true,
    "US_10_01_WP_02": true,
    "US_10_01_WP_11": true,
    "US_10_01_WP_07": true,
    "US_10_01_WP_13": true,
    "US_10_01_WP_05": true,
    "US_10_01_WP_12": true,
    "US_10_01_WP_01": true,
    "US_10_01_WP_10": true,
    "US_10_01_WP_09": true
  },
  "level_us_02_02_new": {
    "US_02_02_WP_03": true,
    "US_02_02_WP_02": true,
    "US_02_02_WP_01": true
  },
  "level_ru_04_01": {
    "RU_04_01_WT_04": true,
    "RU_04_01_WT_03": true,
    "RU_04_01_WT_02": true,
    "RU_04_01_WT_01": true
  },
  "level_us_15_01": {
    "US_15_01_WATCHTOWER_02": true,
    "US_15_01_WATCHTOWER_04": true,
    "US_15_01_WATCHTOWER_01": true,
    "US_15_01_WATCHTOWER_03": true
  },
  "level_ru_02_03": {
    "RU_02_03_WATCHPOINT_3": true,
    "RU_02_03_WATCHPOINT_1": true,
    "RU_02_03_WATCHPOINT_2": true
  },
  "level_ru_04_02": {
    "RU_04_02_WATCHTOWER_05": true,
    "RU_04_02_WATCHTOWER_04": true,
    "RU_04_02_WATCHTOWER_03": true,
    "RU_04_02_WATCHTOWER_02": true,
    "RU_04_02_WATCHTOWER_01": true
  },
  "level_us_03_02": {
    "US_03_02_W5": true,
    "US_03_02_W1": true,
    "US_03_02_W3": true,
    "US_03_02_W2": true,
    "US_03_02_W4": true
  },
  "level_ru_02_04": {
    "WATCHPOINT_SHORE_SOUTH": true,
    "WATCHPOINT_MINES_NORTH": true,
    "WATCHPOINT_FARM_NORTH": true,
    "WATCHPOINT_MOUNTAIN_SOUTH": true
  },
  "level_us_11_01": {
    "US_11_01_WATCHPOINT_04": true,
    "US_11_01_WATCHPOINT_01": true,
    "US_11_01_WATCHPOINT_02": true,
    "US_11_01_WATCHPOINT_03": true
  },
  "level_us_07_01": {
    "US_07_01_WATCHTOWER_01": true,
    "US_07_01_WATCHTOWER_02": true,
    "US_07_01_WATCHTOWER_04": true,
    "US_07_01_WATCHTOWER_03": true
  },
  "level_ru_04_04": {
    "RU_04_04_WTR_01": true,
    "RU_04_04_WTR_04": true,
    "RU_04_04_WTR_03": true,
    "RU_04_04_WTR_02": true
  },
  "level_us_11_02": {
    "US_11_02_WATCHTOWER_01_RECOVERY": true,
    "US_11_02_WATCHTOWER_03": true,
    "US_11_02_WATCHTOWER_02_RECOVERY": true
  },
  "level_us_12_01": {
    "US_12_01_WATCHPOINT_04": true,
    "US_12_01_WATCHPOINT_03": true,
    "US_12_01_WATCHPOINT_02": true,
    "US_12_01_WATCHPOINT_01": true
  },
  "level_us_09_01": {
    "US_09_01_WATCHPOINT_02": true,
    "US_09_01_WATCHPOINT_01": true,
    "US_09_01_WATCHPOINT_03": true
  }
}"""
WATCHPOINTS_UNLOCKS = json.loads(_WATCHPOINTS_UNLOCKS_JSON)

# Canonical discovered trucks list (used to fill missing entries safely)
_DISCOVERED_TRUCKS_DEFAULTS_JSON = """{
  "test_zone_color_summer": {"current": 0, "all": 0},
  "level_ru_08_02": {"current": 0, "all": 1},
  "level_us_16_02": {"current": 0, "all": 0},
  "level_ru_02_02": {"current": 0, "all": 0},
  "level_trial_04_02": {"current": 0, "all": 1},
  "test_programmers_sandbox": {"current": 0, "all": 0},
  "level_trial_03_02": {"current": 0, "all": 3},
  "level_trial_03_01": {"current": 0, "all": 2},
  "test_farming": {"current": 0, "all": 0},
  "level_ru_03_01": {"current": 0, "all": 1},
  "level_ru_08_03": {"current": 0, "all": 0},
  "level_us_01_02": {"current": 0, "all": 2},
  "us_11_test_objectives": {"current": 0, "all": 0},
  "level_trial_03_03": {"current": 0, "all": 2},
  "level_us_12_02": {"current": 0, "all": 0},
  "level_us_test_polygon": {"current": 0, "all": 2},
  "level_ru_05_02": {"current": 0, "all": 0},
  "level_us_04_01": {"current": 0, "all": 1},
  "level_us_02_01": {"current": 0, "all": 1},
  "level_us_02_04_new": {"current": 0, "all": 1},
  "level_us_07_01": {"current": 0, "all": 0},
  "level_us_14_02": {"current": 0, "all": 0},
  "test_zone_color_winter": {"current": 0, "all": 0},
  "level_trial_02_02": {"current": 0, "all": 1},
  "level_us_14_01": {"current": 0, "all": 0},
  "level_ru_02_03": {"current": 0, "all": 1},
  "level_ru_17_01": {"current": 0, "all": 0},
  "level_us_10_01": {"current": 0, "all": 1},
  "level_us_09_02": {"current": 0, "all": 3},
  "level_ru_05_01": {"current": 0, "all": 0},
  "level_trial_04_01": {"current": 0, "all": 1},
  "level_tutorial_objectives": {"current": 0, "all": 0},
  "level_us_11_01": {"current": 0, "all": 0},
  "level_trial_01_01": {"current": 0, "all": 1},
  "level_us_15_01": {"current": 0, "all": 0},
  "level_ru_02_01_crop": {"current": 0, "all": 0},
  "level_ru_04_04": {"current": 0, "all": 0},
  "level_tutorial_upgrades": {"current": 0, "all": 0},
  "level_trial_02_01": {"current": 0, "all": 5},
  "level_ru_03_02": {"current": 0, "all": 1},
  "level_ru_08_04": {"current": 0, "all": 0},
  "level_us_02_03_new": {"current": 0, "all": 0},
  "level_us_03_01": {"current": 0, "all": 1},
  "level_trial_01_02": {"current": 0, "all": 4},
  "level_us_01_03": {"current": 0, "all": 0},
  "level_us_12_03": {"current": 0, "all": 0},
  "level_us_16_01": {"current": 0, "all": 0},
  "level_us_12_01": {"current": 0, "all": 1},
  "level_us_12_04": {"current": 0, "all": 0},
  "level_us_10_02": {"current": 0, "all": 1},
  "level_ru_17_02": {"current": 0, "all": 0},
  "level_ru_02_04": {"current": 0, "all": 0},
  "level_us_01_01": {"current": 0, "all": 5},
  "level_us_04_02": {"current": 0, "all": 1},
  "level_us_06_01": {"current": 0, "all": 0},
  "level_us_03_02": {"current": 0, "all": 1},
  "level_us_02_02_new": {"current": 0, "all": 0},
  "level_tutorial_track": {"current": 0, "all": 0},
  "level_us_06_02": {"current": 0, "all": 0},
  "level_us_16_03": {"current": 0, "all": 0},
  "level_ru_04_01": {"current": 0, "all": 0},
  "level_ru_04_02": {"current": 0, "all": 0},
  "level_ru_04_03": {"current": 0, "all": 0},
  "level_us_15_02": {"current": 0, "all": 0},
  "level_trial_05_01": {"current": 0, "all": 6},
  "level_ru_08_01": {"current": 0, "all": 3},
  "level_ru_test_polygon": {"current": 0, "all": 2},
  "level_us_01_04_new": {"current": 0, "all": 1},
  "level_ru_13_01": {"current": 0, "all": 0},
  "level_us_11_02": {"current": 0, "all": 1},
  "level_us_09_01": {"current": 0, "all": 1}
}"""
DISCOVERED_TRUCKS_DEFAULTS = json.loads(_DISCOVERED_TRUCKS_DEFAULTS_JSON)

# Known regions + visited levels defaults
KNOWN_REGIONS_DEFAULTS = [
    "us_01","us_02","ru_02","us_14","ru_13","us_12","us_11","us_10","us_09","ru_08",
    "us_07","us_06","ru_05","ru_04","us_03","us_04","ru_03","ru_17","us_16","us_15"
]

VISITED_LEVELS_DEFAULTS = [
    "level_ru_02_01_crop","level_ru_02_02","level_ru_02_03","level_ru_02_04",
    "level_ru_03_01","level_ru_03_02","level_ru_04_01","level_ru_04_02",
    "level_ru_04_03","level_ru_04_04","level_ru_05_01","level_ru_05_02",
    "level_ru_08_01","level_ru_08_02","level_ru_08_03","level_ru_08_04",
    "level_ru_13_01","level_ru_17_01","level_ru_17_02",
    "level_us_01_01","level_us_01_02","level_us_01_03","level_us_01_04_new",
    "level_us_02_01","level_us_02_02_new","level_us_02_03_new","level_us_02_04_new",
    "level_us_03_01","level_us_03_02","level_us_04_01","level_us_04_02",
    "level_us_06_01","level_us_06_02","level_us_07_01",
    "level_us_09_01","level_us_09_02","level_us_10_01","level_us_10_02",
    "level_us_11_01","level_us_11_02","level_us_12_01","level_us_12_02",
    "level_us_12_03","level_us_12_04","level_us_14_01","level_us_14_02",
    "level_us_15_01","level_us_15_02","level_us_16_01","level_us_16_02","level_us_16_03"
]

# Garage status defaults (0=no garage, 1=garage locked, 2=garage unlocked)
LEVEL_GARAGE_STATUSES_DEFAULTS = {
    "level_us_12_02": 1,
    "level_ru_03_01": 2,
    "level_ru_04_01": 2,
    "level_ru_08_03": 1,
    "level_us_04_01": 2,
    "level_us_03_01": 2,
    "level_ru_05_01": 2,
    "level_us_02_01": 2,
    "level_ru_02_04": 0,
    "level_us_01_02": 1,
    "level_us_11_02": 0,
    "level_us_14_01": 2,
    "level_ru_03_02": 1,
    "level_us_09_02": 0,
    "level_ru_02_01_crop": 0,
    "level_ru_02_02": 2,
    "level_ru_17_01": 2,
    "level_us_01_01": 2,
    "level_ru_08_04": 1,
    "level_us_15_01": 2,
    "level_us_02_03_new": 1,
    "level_us_01_03": 0,
    "level_us_12_03": 1,
    "level_us_14_02": 0,
    "level_us_16_01": 0,
    "level_ru_08_02": 0,
    "level_us_16_03": 0,
    "level_ru_05_02": 0,
    "level_us_12_04": 0,
    "level_us_10_01": 2,
    "level_ru_17_02": 0,
    "level_us_06_01": 2,
    "level_us_02_02_new": 0,
    "level_us_04_02": 1,
    "level_us_16_02": 2,
    "level_us_10_02": 1,
    "level_us_01_04_new": 0,
    "level_us_06_02": 0,
    "level_ru_04_04": 1,
    "level_us_02_04_new": 0,
    "level_ru_02_03": 1,
    "level_ru_04_02": 1,
    "level_us_03_02": 1,
    "level_us_15_02": 0,
    "level_us_11_01": 2,
    "level_ru_04_03": 0,
    "level_ru_08_01": 2,
    "level_us_07_01": 2,
    "level_ru_13_01": 2,
    "level_us_12_01": 2,
    "level_us_09_01": 2
}

REGION_LEVELS = {}
for _lvl in VISITED_LEVELS_DEFAULTS:
    try:
        m = re.match(r'^level_([a-z]{2}_\d{2})', _lvl)
        if m:
            code = m.group(1).upper()
            REGION_LEVELS.setdefault(code, []).append(_lvl)
    except Exception:
        pass

def _ensure_upgrades_defaults(upgrades_data):
    added = 0
    for map_key, upgrades in UPGRADES_GIVER_UNLOCKS.items():
        existing = upgrades_data.get(map_key)
        if not isinstance(existing, dict):
            try:
                existing = dict(existing) if existing is not None else {}
            except Exception:
                existing = {}
            upgrades_data[map_key] = existing
        for upgrade_key in upgrades.keys():
            if upgrade_key not in existing:
                existing[upgrade_key] = 0
                added += 1
    return added

def _ensure_watchpoints_defaults(wp_data):
    added = 0
    data = wp_data.get("data")
    if not isinstance(data, dict):
        data = {}
        wp_data["data"] = data
    for map_key, towers in WATCHPOINTS_UNLOCKS.items():
        existing = data.get(map_key)
        if not isinstance(existing, dict):
            try:
                existing = dict(existing) if existing is not None else {}
            except Exception:
                existing = {}
            data[map_key] = existing
        for tower_key in towers.keys():
            if tower_key not in existing:
                existing[tower_key] = False
                added += 1
    return added

def _ensure_discovered_trucks_defaults(dt_data):
    added = 0
    if not isinstance(dt_data, dict):
        dt_data = {}
    for map_key, vals in DISCOVERED_TRUCKS_DEFAULTS.items():
        existing = dt_data.get(map_key)
        if not isinstance(existing, dict):
            dt_data[map_key] = {"current": vals.get("current", 0), "all": vals.get("all", 0)}
            added += 1
            continue
        if "current" not in existing:
            existing["current"] = vals.get("current", 0)
            added += 1
        if "all" not in existing:
            existing["all"] = vals.get("all", 0)
            added += 1
    return added, dt_data

def _set_current_to_all(entry):
    try:
        all_val = entry.get("all", 0)
        if isinstance(all_val, bool):
            all_val = int(all_val)
        elif not isinstance(all_val, (int, float)):
            try:
                all_val = int(str(all_val).strip())
            except Exception:
                all_val = 0
    except Exception:
        all_val = 0
    entry["all"] = all_val
    entry["current"] = all_val

def _ensure_level_garage_statuses_defaults(lg_data):
    added = 0
    if not isinstance(lg_data, dict):
        lg_data = {}
    for level_id, status in LEVEL_GARAGE_STATUSES_DEFAULTS.items():
        if level_id not in lg_data:
            lg_data[level_id] = status
            added += 1
    return added, lg_data

def _build_garage_data_entry():
    return {
        "slotsDatas": {
            "garage_interior_slot_1": {
                "garageSlotZoneId": "garage_interior_slot_1",
                "truckDesc": None
            },
            "garage_interior_slot_2": {
                "garageSlotZoneId": "garage_interior_slot_2",
                "truckDesc": None
            },
            "garage_interior_slot_3": {
                "garageSlotZoneId": "garage_interior_slot_3",
                "truckDesc": None
            },
            "garage_interior_slot_4": {
                "garageSlotZoneId": "garage_interior_slot_4",
                "truckDesc": None
            },
            "garage_interior_slot_5": {
                "garageSlotZoneId": "garage_interior_slot_5",
                "truckDesc": None
            },
            "garage_interior_slot_6": {
                "garageSlotZoneId": "garage_interior_slot_6",
                "truckDesc": None
            }
        },
        "selectedSlot": "garage_interior_slot_1"
    }

def _make_upgradable_garage_key(level_id: str) -> str:
    try:
        suffix = level_id.replace("level_", "").upper()
    except Exception:
        suffix = str(level_id).upper()
    return f"{level_id} || {suffix}_GARAGE_ENTRANCE"

def _normalize_feature_states(entry):
    fs = entry.get("featureStates")
    if not isinstance(fs, list):
        fs = []
    # ensure at least 4 entries; keep any extra entries intact
    fs = list(fs)
    while len(fs) < 4:
        fs.append(False)
    # ensure bools
    fs = [bool(x) for x in fs]
    entry["featureStates"] = fs
    if "isUpgradable" not in entry:
        entry["isUpgradable"] = True
    return entry

def unlock_watchtowers(save_path, selected_regions):
    make_backup_if_enabled(save_path)
    try:
        with open(save_path, "r", encoding="utf-8") as f:
            content = f.read()

        match = re.search(r'"watchPointsData"\s*:\s*{', content)
        if not match:
            return messagebox.showerror("Error", "No watchPointsData found in file.")

        block, start, end = extract_brace_block(content, match.end() - 1)
        wp_data = json.loads(block)
        added = _ensure_watchpoints_defaults(wp_data)
        updated = 0

        data = wp_data.get("data", {})
        if not isinstance(data, dict):
            data = {}

        for map_key, towers in data.items():
            if not isinstance(towers, dict):
                continue
            for code in selected_regions:
                if f"level_{code.lower()}" in map_key.lower():
                    for tower_key, val in towers.items():
                        if val is False:
                            towers[tower_key] = True
                            updated += 1
                    break

        new_block = json.dumps(wp_data, separators=(",", ":"))
        content = content[:start] + new_block + content[end:]
        with open(save_path, "w", encoding="utf-8") as f:
            f.write(content)

        msg = f"Unlocked {updated} watchtowers."
        if added:
            msg += f" Added {added} missing entries."
        show_info("Success", msg)
    except Exception as e:
        messagebox.showerror("Error", str(e))

def unlock_garages(save_path, selected_regions, upgrade_all=False):
    make_backup_if_enabled(save_path)
    try:
        with open(save_path, "r", encoding="utf-8") as f:
            content = f.read()

        # Locate SslValue block (main save data)
        ssl_match = re.search(r'"SslValue"\s*:\s*{', content)
        if not ssl_match:
            return messagebox.showerror("Error", "SslValue block not found in save file.")

        ssl_block, ssl_start, ssl_end = extract_brace_block(content, ssl_match.end() - 1)
        try:
            ssl_data = json.loads(ssl_block)
        except Exception as e:
            return messagebox.showerror("Error", f"Failed to parse SslValue:\n{e}")

        # levelGarageStatuses
        lg_data = ssl_data.get("levelGarageStatuses", {})
        added_defaults, lg_data = _ensure_level_garage_statuses_defaults(lg_data)

        # determine selected levels from region codes
        selected_levels = []
        for code in selected_regions:
            for lvl in REGION_LEVELS.get(code, []):
                selected_levels.append(lvl)

        updated = 0
        for lvl in selected_levels:
            if lvl in lg_data and lg_data.get(lvl) == 1:
                lg_data[lvl] = 2
                updated += 1

        ssl_data["levelGarageStatuses"] = lg_data

        # garagesData
        gd_data = ssl_data.get("garagesData", {})
        if not isinstance(gd_data, dict):
            gd_data = {}

        added_garage_data = 0
        for lvl in selected_levels:
            if lg_data.get(lvl) == 2 and lvl not in gd_data:
                gd_data[lvl] = _build_garage_data_entry()
                added_garage_data += 1

        ssl_data["garagesData"] = gd_data

        # upgradableGarages (optional)
        upgraded_entries = 0
        added_upgradable = 0
        if upgrade_all:
            ug_data = ssl_data.get("upgradableGarages", {})
            if not isinstance(ug_data, dict):
                ug_data = {}
            for lvl in selected_levels:
                if lg_data.get(lvl) != 2:
                    continue
                # find existing entry for this level
                found_key = None
                for k, v in ug_data.items():
                    try:
                        if isinstance(k, str) and lvl.lower() in k.lower():
                            found_key = k
                            break
                        if isinstance(v, dict):
                            zg = v.get("zoneGlobalId")
                            if isinstance(zg, str) and lvl.lower() in zg.lower():
                                found_key = k
                                break
                    except Exception:
                        continue
                key = found_key or _make_upgradable_garage_key(lvl)
                entry = ug_data.get(key)
                if not isinstance(entry, dict):
                    entry = {"zoneGlobalId": key, "featureStates": [False, False, False, False], "isUpgradable": True}
                    ug_data[key] = entry
                    if found_key is None:
                        added_upgradable += 1
                if not entry.get("zoneGlobalId"):
                    entry["zoneGlobalId"] = key
                entry = _normalize_feature_states(entry)
                # flip all to true (preserve any extra length)
                fs = entry.get("featureStates") if isinstance(entry.get("featureStates"), list) else []
                entry["featureStates"] = [True for _ in fs]
                entry["isUpgradable"] = True
                ug_data[key] = entry
                upgraded_entries += 1
            ssl_data["upgradableGarages"] = ug_data

        new_block = json.dumps(ssl_data, separators=(",", ":"))
        content = content[:ssl_start] + new_block + content[ssl_end:]

        with open(save_path, "w", encoding="utf-8") as f:
            f.write(content)

        msg = f"Unlocked {updated} garages."
        if added_defaults:
            msg += f" Added {added_defaults} missing levelGarageStatuses entries."
        if added_garage_data:
            msg += f" Added {added_garage_data} garage data entries."
        if upgrade_all:
            msg += f" Upgraded {upgraded_entries} garages."
            if added_upgradable:
                msg += f" Added {added_upgradable} upgradable garage entries."
        show_info("Success", msg)
    except Exception as e:
        messagebox.showerror("Error", str(e))

def unlock_discoveries(save_path, selected_regions):
    make_backup_if_enabled(save_path)
    try:
        with open(save_path, "r", encoding="utf-8") as f:
            content = f.read()

        # Only modify discoveredTrucks under persistentProfileData
        pp_match = re.search(r'"persistentProfileData"\s*:\s*{', content)
        if not pp_match:
            return messagebox.showerror("Error", "persistentProfileData not found in save file.")

        pp_block, pp_start, pp_end = extract_brace_block(content, pp_match.end() - 1)

        dt_match = re.search(r'"discoveredTrucks"\s*:\s*{', pp_block)
        if dt_match:
            dt_block, dt_start, dt_end = extract_brace_block(pp_block, dt_match.end() - 1)
            try:
                dt_data = json.loads(dt_block)
            except Exception:
                dt_data = {}
        else:
            dt_data = {}
            dt_start = dt_end = None

        added, dt_data = _ensure_discovered_trucks_defaults(dt_data)
        updated = 0

        if not isinstance(dt_data, dict):
            dt_data = {}

        for map_key, entry in dt_data.items():
            if not isinstance(entry, dict):
                entry = {"current": 0, "all": 0}
                dt_data[map_key] = entry
            map_key_low = map_key.lower()
            for code in selected_regions:
                if code.lower() in map_key_low:
                    _set_current_to_all(entry)
                    updated += 1
                    break

        new_block = json.dumps(dt_data, separators=(",", ":"))
        if dt_start is not None and dt_end is not None:
            pp_block = pp_block[:dt_start] + new_block + pp_block[dt_end:]
        else:
            # Insert discoveredTrucks inside persistentProfileData
            pp_block = _set_key_in_text(pp_block, "discoveredTrucks", new_block)

        content = content[:pp_start] + pp_block + content[pp_end:]

        with open(save_path, "w", encoding="utf-8") as f:
            f.write(content)

        msg = f"Updated {updated} discovery entries."
        if added:
            msg += f" Added {added} missing entries."
        show_info("Success", msg)
    except Exception as e:
        messagebox.showerror("Error", str(e))

def unlock_levels(save_path, selected_regions):
    make_backup_if_enabled(save_path)
    try:
        with open(save_path, "r", encoding="utf-8") as f:
            content = f.read()

        # --- persistentProfileData.knownRegions (only this block) ---
        pp_match = re.search(r'"persistentProfileData"\s*:\s*{', content)
        if not pp_match:
            return messagebox.showerror("Error", "persistentProfileData not found in save file.")

        pp_block, pp_start, pp_end = extract_brace_block(content, pp_match.end() - 1)
        kr_match = re.search(r'"knownRegions"\s*:\s*\[', pp_block)
        if kr_match:
            kr_block, kr_start, kr_end = extract_bracket_block(pp_block, kr_match.end() - 1)
            try:
                known_regions = json.loads(kr_block)
            except Exception:
                known_regions = []
        else:
            known_regions = []
            kr_start = kr_end = None

        added_selected_kr = 0
        for code in selected_regions:
            key = code.lower()
            if key not in known_regions:
                known_regions.append(key)
                added_selected_kr += 1

        new_known = json.dumps(known_regions, separators=(",", ":"))
        if kr_start is not None and kr_end is not None:
            pp_block = pp_block[:kr_start] + new_known + pp_block[kr_end:]
        else:
            pp_block = _set_key_in_text(pp_block, "knownRegions", new_known)

        content = content[:pp_start] + pp_block + content[pp_end:]

        # --- visitedLevels (top-level, only one) ---
        vl_match = re.search(r'"visitedLevels"\s*:\s*\[', content)
        if vl_match:
            vl_block, vl_start, vl_end = extract_bracket_block(content, vl_match.end() - 1)
            try:
                visited_levels = json.loads(vl_block)
            except Exception:
                visited_levels = []
        else:
            visited_levels = []
            vl_start = vl_end = None

        added_selected_vl = 0
        for code in selected_regions:
            for lvl in REGION_LEVELS.get(code, []):
                if lvl not in visited_levels:
                    visited_levels.append(lvl)
                    added_selected_vl += 1

        new_visited = json.dumps(visited_levels, separators=(",", ":"))
        if vl_start is not None and vl_end is not None:
            content = content[:vl_start] + new_visited + content[vl_end:]
        else:
            content = _set_key_in_text(content, "visitedLevels", new_visited)

        with open(save_path, "w", encoding="utf-8") as f:
            f.write(content)

        msg = (
            f"Known regions added: {added_selected_kr}. "
            f"Visited levels added: {added_selected_vl}."
        )
        show_info("Success", msg)
    except Exception as e:
        messagebox.showerror("Error", str(e))

# -----------------------------------------------------------------------------
# END SECTION: Upgrades + Watchtowers Data & Helpers
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Objectives+ Data, Logging, and Virtualized UI
# Used In: Objectives+ tab (large datasets + virtualized list rendering)
# =============================================================================
_pd = None  # placeholder for pandas when loaded
DEBUG: bool = True
# Reduce log spam from high-frequency Objectives+ scrolling unless explicitly enabled.
DEBUG_OBJECTIVES_SCROLL: bool = False
_APP_START: Optional[float] = None


def _objectives_prefetch_snapshot() -> Dict[str, Any]:
    with _OBJECTIVES_PREFETCH_LOCK:
        return dict(_OBJECTIVES_PREFETCH_STATE)


def _set_objectives_prefetch_state(**updates):
    with _OBJECTIVES_PREFETCH_LOCK:
        _OBJECTIVES_PREFETCH_STATE.update(updates)


def start_objectives_prefetch_background(force: bool = False) -> bool:
    """
    Start Objectives+ latest-data refresh in background at app startup.
    Returns True when a new worker thread is started.
    """
    state = _objectives_prefetch_snapshot()
    if state.get("inflight"):
        return False
    if state.get("completed") and (not force):
        return False

    _set_objectives_prefetch_state(
        started=True,
        inflight=True,
        completed=False,
        built=False,
        error="",
    )

    def _worker():
        cache_csv = _objectives_cache_csv_path()
        built = False
        err = ""
        try:
            built = _mr_build_csv(cache_csv)
        except Exception as e:
            built = False
            err = str(e)

        _set_objectives_prefetch_state(
            inflight=False,
            completed=True,
            built=bool(built),
            error=str(err or ""),
            last_completed_ts=float(time.time()),
        )

        if built:
            set_app_status("Objectives+ latest data cached in background.", timeout_ms=4500)
        else:
            # Keep this informational (non-fatal); cached/bundled data is still usable.
            set_app_status("Objectives+ background refresh failed; cached data will be used.", timeout_ms=5000)

    threading.Thread(target=_worker, daemon=True).start()
    return True


def _now_ms() -> float:
    global _APP_START
    if _APP_START is None:
        _APP_START = time.perf_counter()
    return (time.perf_counter() - _APP_START) * 1000.0
STRIPE_A = "#e0e0e0"
STRIPE_B = "#f8f8f8"
# Always keep Objectives+ virtualized (pool) to avoid huge widget trees.
OBJECTIVES_VIRTUAL_THRESHOLD: int = 0
def log(msg: str) -> None:
    if not DEBUG:
        return
    elapsed = _now_ms()
    t = time.strftime('%H:%M:%S')
    try:
        print(f"[{t} +{elapsed:.0f}ms] {msg}")
    except Exception:
        try:
            print(msg)
        except Exception:
            pass
def default_parquet_path() -> str:
    try:
        base = get_editor_data_dir()
    except Exception:
        base = os.path.dirname(resource_path(""))
    return os.path.join(base, "maprunner_data.parquet")
def extract_json_block_by_key(s: str, key: str):
    m = re.search(rf'"{re.escape(key)}"\s*:\s*{{', s)
    if not m:
        raise ValueError("Key not found")
    return extract_brace_block(s, m.end() - 1)
def _read_finished_contests(path: str) -> Set[str]:
    try:
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
    except Exception:
        return set()

    m = re.search(r'"(CompleteSave[^"]*)"\s*:\s*{', content)
    if not m:
        return set()

    save_key = m.group(1)
    try:
        json_block, _, _ = extract_json_block_by_key(content, save_key)
        data = json.loads(json_block)
    except Exception:
        return set()

    save_obj = data.get(save_key, data)
    ssl = save_obj.get("SslValue", {})
    finished = ssl.get("finishedObjs", {})

    if isinstance(finished, dict):
        return {k for k, v in finished.items() if v}
    elif isinstance(finished, list):
        return set(finished)
    return set()
def _read_finished_missions(save_path: str) -> Set[str]:
    try:
        with open(save_path, "r", encoding="utf-8") as f:
            content = f.read()
        start = content.find('"objectiveStates"')
        if start == -1:
            return set()
        block, bs, be = extract_brace_block(content, start)
        obj_states = json.loads(block)
        return {k for k, v in obj_states.items() if isinstance(v, dict) and v.get("isFinished")}
    except Exception:
        return set()
#----------csv loader------------   
class SimpleFrame:
    """Tiny DataFrame-like adapter for a list-of-dicts (rows)."""
    def __init__(self, rows: List[Dict[str, Any]]):
        self._rows = rows
        self.columns = list(rows[0].keys()) if rows else []
        self.shape = (len(self._rows), len(self.columns))

    def __len__(self):
        return len(self._rows)

    def iterrows(self) -> Iterator:
        for i, r in enumerate(self._rows):
            yield i, r

    def to_dict(self, orient="records"):
        if orient != "records":
            raise ValueError("SimpleFrame only supports orient='records'")
        return self._rows

    # convenience: get column as list
    def get_column(self, col: str) -> List[Any]:
        return [r.get(col) for r in self._rows]

# =============================================================================
# SECTION: Objectives+ CSV Builder (Maprunner)
# Used In: Objectives+ loader (auto-refresh CSV when online)
# =============================================================================
_MR_URL = "https://www.maprunner.info/michigan/black-river?loc=_CL_1"
_MR_TIMEOUT_SECONDS = 20
_MR_CANONICAL_NAMES = {"data": "data.js", "desc": "desc.js"}
_MR_IN_MEM_FILES: Dict[str, bytes] = {}
_MR_IN_MEM_META: Dict[str, Dict[str, Any]] = {}
_MR_CHUNK_MAX = 220
_MR_ENGLISH_TARGET = 20000
_MR_DATA_SIGNATURE = "const _=JSON.parse('[{\"name\":\"RU_02_01_SERVHUB_GAS\""
_MR_DESC_SIGNATURE = "const t={UI_TRUCK_TYPE_HEAVY_DUTY:{t:0,b:{t:2,i:[{t:3}],s:\"HEAVY DUTY\""
_MR_DEBUG = False
_MR_SAFE_FALLBACK_URLS = [
    "https://raw.githubusercontent.com/MrBoxik/SnowRunner-Save-Editor/main/app/objectives/CKSuO70b.js",
    "https://raw.githubusercontent.com/MrBoxik/SnowRunner-Save-Editor/main/app/objectives/ChUX6nGL.js",
]
_MR_SAFE_FALLBACK_ERROR = ""

# Language preference helpers (favor English when multiple locales exist)
_MR_ENGLISH_WORDS = {
    "the", "and", "to", "of", "in", "on", "for", "with", "from", "at", "by",
    "you", "your", "we", "our", "deliver", "find", "task", "contract", "contest",
    "lost", "trailer", "truck", "cargo", "repair", "bridge", "road", "house",
    "watchtower", "explore", "exploration", "mission"
}
_MR_DIACRITICS = set("ąćęłńóśźżĄĆĘŁŃÓŚŹŻàáâäãåæçèéêëìíîïñòóôöõøùúûüýÿßčďěňřšťůž")
_MR_ENGLISH_SAMPLE_MAX = 240
# Avg English score threshold for localization files (higher = stricter)
_MR_ENGLISH_AVG_MIN = 2.5
# Minimum distinct English hits required in localization sample
_MR_ENGLISH_HITS_MIN = 12
# Allow near-top localization files within this score delta of the best
_MR_ENGLISH_AVG_DELTA = 0.5
# If we already have a strong English localization of this size, stop scanning more
_MR_ENGLISH_MIN_ENTRIES = 12000
# Max JS files to parse when auto-detecting localization language
_MR_LOCALIZATION_CANDIDATE_MAX = 40
# Tracks which localization files were selected (used to filter lazy lookups)
_MR_LAST_LOCALIZATION_FILES: List[str] = []
_MR_LAST_LOCALIZATION_BLOCKED = False
# Minimum localization size required to proceed with CSV build.
_MR_MIN_LOCALIZATION_ENTRIES = 2000
# Heuristics to exclude non-English localization files
_MR_FORBIDDEN_LANG_WORDS = {
    "palivo", "verlassene", "naturelle", "opuszczone", "privacidad",
    "perduto", "deslizamento",
    # Common Polish stems/words seen in MapRunner objectives
    "zatopion", "ciezarowk", "pojazd", "narzedz", "rolnicz", "zniw",
    "odbudow", "zagubion", "garaz", "wieza", "cysterna", "przyczep",
    "utkn", "zaginion", "blokada", "naprawa", "osuwisk", "osusz",
    "wzgorz", "rozrywka", "swierk",
}
_MR_CYRILLIC_RE = re.compile(r"[\u0400-\u04FF]")
_MR_NON_ASCII_RATIO_MAX = 0.03
_MR_VALUE_ENGLISH_MIN_SCORE = 0.6

# Objectives+ safe fallback mode (thread-safe, config-backed)
_OBJECTIVES_SAFE_FALLBACK_MODE = False
_OBJECTIVES_SAFE_FALLBACK_MODE_LOCK = threading.Lock()
_OBJECTIVES_SAFE_FALLBACK_MODE_SET = False

def _set_objectives_safe_fallback_mode(enabled: bool) -> None:
    global _OBJECTIVES_SAFE_FALLBACK_MODE, _OBJECTIVES_SAFE_FALLBACK_MODE_SET
    try:
        with _OBJECTIVES_SAFE_FALLBACK_MODE_LOCK:
            _OBJECTIVES_SAFE_FALLBACK_MODE = bool(enabled)
            _OBJECTIVES_SAFE_FALLBACK_MODE_SET = True
    except Exception:
        _OBJECTIVES_SAFE_FALLBACK_MODE = bool(enabled)
        _OBJECTIVES_SAFE_FALLBACK_MODE_SET = True

def _get_objectives_safe_fallback_mode() -> bool:
    global _OBJECTIVES_SAFE_FALLBACK_MODE, _OBJECTIVES_SAFE_FALLBACK_MODE_SET
    try:
        with _OBJECTIVES_SAFE_FALLBACK_MODE_LOCK:
            if not _OBJECTIVES_SAFE_FALLBACK_MODE_SET:
                try:
                    cfg = load_config() or {}
                    val = cfg.get("objectives_use_safe_fallback", None)
                    if val is None:
                        # Backward compatibility with older backup setting
                        val = cfg.get("objectives_use_backup", False)
                    _OBJECTIVES_SAFE_FALLBACK_MODE = bool(val)
                except Exception:
                    _OBJECTIVES_SAFE_FALLBACK_MODE = False
                _OBJECTIVES_SAFE_FALLBACK_MODE_SET = True
            return bool(_OBJECTIVES_SAFE_FALLBACK_MODE)
    except Exception:
        return bool(_OBJECTIVES_SAFE_FALLBACK_MODE)

# Language detection helpers (best-effort / heuristic)
_MR_LANG_DIACRITICS = {
    "Polish": set("ąćęłńóśźżĄĆĘŁŃÓŚŹŻ"),
    "Czech/Slovak": set("áčďéěíňóřšťúůýžÁČĎÉĚÍŇÓŘŠŤÚŮÝŽ"),
    "German": set("äöüßÄÖÜ"),
    "French": set("àâäçéèêëîïôöùûüÿœæÀÂÄÇÉÈÊËÎÏÔÖÙÛÜŸŒÆ"),
    "Spanish": set("áéíñóúüÁÉÍÑÓÚÜ"),
    "Portuguese": set("áàâãçéêíóôõúüÁÀÂÃÇÉÊÍÓÔÕÚÜ"),
    "Italian": set("àèéìíîòóùúÀÈÉÌÍÎÒÓÙÚ"),
    "Turkish": set("çğıöşüÇĞİÖŞÜ"),
    "Romanian": set("ăâîșşțţĂÂÎȘŞȚŢ"),
}
_MR_LANG_STOPWORDS = {
    "English": ["the", "and", "of", "to", "in", "for", "with", "from", "on"],
    "Polish": ["i", "oraz", "na", "do", "z", "w", "jest", "nie", "się"],
    "Czech/Slovak": ["a", "na", "je", "se", "pro", "kter", "nen", "neni"],
    "German": ["und", "der", "die", "das", "nicht", "mit", "für", "von", "auf", "zu"],
    "French": ["et", "le", "la", "les", "des", "de", "pour", "avec", "dans"],
    "Spanish": ["el", "la", "los", "las", "de", "que", "y", "para", "con", "en"],
    "Portuguese": ["de", "e", "que", "para", "com", "em", "nao", "uma", "um"],
    "Italian": ["il", "la", "e", "che", "per", "con", "del", "della"],
    "Turkish": ["ve", "bir", "ile", "icin", "de", "da", "bu"],
    "Romanian": ["si", "in", "de", "la", "cu", "pentru", "este"],
    "Russian": ["и", "в", "на", "что", "с", "для", "по", "из"],
}

def _mr_guess_language_from_values(values: List[str], english_avg: Optional[float] = None) -> str:
    try:
        if english_avg is not None and english_avg >= _MR_ENGLISH_AVG_MIN:
            return "English"
    except Exception:
        pass
    if not values:
        return "Unknown"
    sample = " ".join(values[:120])
    if not sample:
        return "Unknown"
    # Script detection
    try:
        if re.search(r"[\u0400-\u04FF]", sample):
            return "Russian"
        if re.search(r"[\u4E00-\u9FFF]", sample):
            return "Chinese"
        if re.search(r"[\u3040-\u30FF]", sample):
            return "Japanese"
        if re.search(r"[\uAC00-\uD7AF]", sample):
            return "Korean"
    except Exception:
        pass

    scores: Dict[str, float] = {}
    for lang, chars in _MR_LANG_DIACRITICS.items():
        try:
            count = sum(sample.count(ch) for ch in chars)
        except Exception:
            count = 0
        if count:
            scores[lang] = scores.get(lang, 0.0) + float(count) * 2.0

    lower = sample.lower()
    # normalize to spaces
    try:
        lower_norm = re.sub(r"[^a-z\u00c0-\u017f\u0400-\u04ff]+", " ", lower)
    except Exception:
        lower_norm = lower
    lower_norm = f" {lower_norm} "
    for lang, words in _MR_LANG_STOPWORDS.items():
        for w in words:
            try:
                if f" {w} " in lower_norm:
                    scores[lang] = scores.get(lang, 0.0) + 1.0
            except Exception:
                continue

    if scores:
        best_lang = max(scores, key=scores.get)
        if scores.get(best_lang, 0.0) >= 3.0:
            return best_lang

    try:
        if english_avg is not None and english_avg >= 1.0:
            return "Mixed"
    except Exception:
        pass
    return "Unknown"

def _mr_text_english_score(s: Any) -> float:
    try:
        if s is None:
            return -999.0
        if not isinstance(s, str):
            s = str(s)
    except Exception:
        return -999.0
    if not s:
        return -999.0
    score = 0.0
    # Penalize typical mojibake markers
    bad_markers = ("Ã", "Â", "�")
    for bm in bad_markers:
        if bm in s:
            score -= 4.0 * s.count(bm)
    # Prefer mostly-ASCII letters (English tends to be ASCII)
    letters = sum(ch.isalpha() for ch in s)
    ascii_letters = sum((ch.isascii() and ch.isalpha()) for ch in s)
    if letters:
        score += (ascii_letters / letters) * 4.0
    # Penalize diacritics commonly used in non-English locales
    diac = sum(1 for ch in s if ch in _MR_DIACRITICS)
    score -= diac * 0.4
    # Common English word boosts
    lower = s.lower()
    for w in _MR_ENGLISH_WORDS:
        if w in lower:
            score += 0.6
    # Hard penalties for known non-English markers
    for w in _MR_FORBIDDEN_LANG_WORDS:
        if w in lower:
            score -= 6.0
    if _MR_CYRILLIC_RE.search(s):
        score -= 8.0
    # Penalize ID-like strings
    if re.fullmatch(r"[A-Z0-9_]+", s):
        score -= 2.0
    return score

def _mr_sample_values(values: List[str], max_samples: int = _MR_ENGLISH_SAMPLE_MAX) -> List[str]:
    if not values:
        return []
    n = len(values)
    if n <= max_samples:
        return values
    step = max(1, n // max_samples)
    out: List[str] = []
    for i in range(0, n, step):
        out.append(values[i])
        if len(out) >= max_samples:
            break
    return out

def _mr_localization_avg_score(loc: Dict[str, str]) -> float:
    if not loc:
        return -999.0
    try:
        values = list(loc.values())
    except Exception:
        return -999.0
    sample = _mr_sample_values(values, _MR_ENGLISH_SAMPLE_MAX)
    if not sample:
        return -999.0
    total = 0.0
    for v in sample:
        total += _mr_text_english_score(v)
    return total / max(1, len(sample))

def _mr_localization_sample_flags(values: List[str]) -> Dict[str, Any]:
    if not values:
        return {
            "has_cyrillic": False,
            "forbidden_hits": [],
            "non_ascii_ratio": 0.0,
            "non_ascii_heavy": False,
            "english_hits": 0,
        }

    # Scan full list for forbidden words / cyrillic (early-exit when found).
    has_cyrillic = False
    forbidden_hits = set()
    for v in values:
        if not v:
            continue
        try:
            s = v if isinstance(v, str) else str(v)
        except Exception:
            s = ""
        if not s:
            continue
        if not has_cyrillic and _MR_CYRILLIC_RE.search(s):
            has_cyrillic = True
        if not forbidden_hits:
            low = s.lower()
            for w in _MR_FORBIDDEN_LANG_WORDS:
                if w in low:
                    forbidden_hits.add(w)
                    break
        if has_cyrillic or forbidden_hits:
            break

    # Use a bounded sample for non-ASCII ratio to keep cost low.
    sample_vals = _mr_sample_values(values, _MR_ENGLISH_SAMPLE_MAX)
    sample = " ".join(sample_vals or [])
    letters = sum(1 for ch in sample if ch.isalpha())
    non_ascii_letters = sum(1 for ch in sample if ch.isalpha() and not ch.isascii())
    non_ascii_ratio = (non_ascii_letters / letters) if letters else 0.0
    non_ascii_heavy = bool(letters >= 80 and non_ascii_ratio > _MR_NON_ASCII_RATIO_MAX)
    english_hits = 0
    try:
        lower = sample.lower()
        lower_norm = re.sub(r"[^a-z0-9]+", " ", lower)
        lower_norm = f" {lower_norm} "
        for w in _MR_LANG_STOPWORDS.get("English", []):
            if f" {w} " in lower_norm:
                english_hits += 1
        for w in _MR_ENGLISH_WORDS:
            if f" {w} " in lower_norm:
                english_hits += 1
    except Exception:
        english_hits = 0
    return {
        "has_cyrillic": has_cyrillic,
        "forbidden_hits": sorted(list(forbidden_hits)),
        "non_ascii_ratio": non_ascii_ratio,
        "non_ascii_heavy": non_ascii_heavy,
        "english_hits": english_hits,
    }

def _mr_strings_look_non_english(values: List[str]) -> bool:
    if not values:
        return False
    try:
        sample_vals = _mr_sample_values(values, 200)
    except Exception:
        sample_vals = values[:200]
    flags = _mr_localization_sample_flags(sample_vals)
    if flags.get("has_cyrillic") or flags.get("forbidden_hits"):
        return True
    if flags.get("non_ascii_heavy"):
        return True
    return False

def _mr_localization_looks_english(avg: float, flags: Optional[Dict[str, Any]] = None) -> bool:
    try:
        if avg < _MR_ENGLISH_AVG_MIN:
            return False
    except Exception:
        return False
    if flags:
        if flags.get("has_cyrillic") or flags.get("forbidden_hits") or flags.get("non_ascii_heavy"):
            return False
        if flags.get("english_hits", 0) < _MR_ENGLISH_HITS_MIN:
            return False
    return True

def _mr_desc_bytes_look_english(bs: Optional[bytes]) -> bool:
    try:
        txt = _mr_decode_bytes_to_text(bs) or ""
    except Exception:
        txt = ""
    if not txt:
        return False
    parsed = _mr_parse_localization_from_desc_text(txt)
    if not parsed or len(parsed) < _MR_MIN_LOCALIZATION_ENTRIES:
        return False
    avg = _mr_localization_avg_score(parsed)
    try:
        sample_vals = _mr_sample_values(list(parsed.values()), _MR_ENGLISH_SAMPLE_MAX)
    except Exception:
        sample_vals = []
    flags = _mr_localization_sample_flags(sample_vals)
    return _mr_localization_looks_english(avg, flags)

def _mr_value_allowed(val: Any) -> bool:
    if val is None:
        return False
    try:
        s = val if isinstance(val, str) else str(val)
    except Exception:
        return False
    if not s:
        return False
    low = s.lower()
    for w in _MR_FORBIDDEN_LANG_WORDS:
        if w in low:
            return False
    if _MR_CYRILLIC_RE.search(s):
        return False
    return True

def _mr_normalize_mojibake_text(value: Any) -> str:
    """
    Normalize common mojibake/escaped text artifacts from remote MapRunner sources.
    """
    if value is None:
        return ""
    if isinstance(value, bytes):
        try:
            s = value.decode("utf-8", errors="replace")
        except Exception:
            s = str(value)
    else:
        s = str(value)
    if not s:
        return ""

    if "\\x" in s:
        try:
            s = codecs.decode(s, "unicode_escape")
        except Exception:
            pass

    candidates: List[str] = []

    def _push(v: Any) -> None:
        if v is None:
            return
        if isinstance(v, bytes):
            try:
                t = v.decode("utf-8", errors="replace")
            except Exception:
                t = str(v)
        else:
            t = str(v)
        if t and t not in candidates:
            candidates.append(t)

    _push(s)

    if "\\" in s:
        try:
            _push(codecs.decode(s, "unicode_escape"))
        except Exception:
            pass
        try:
            ue = codecs.decode(s, "unicode_escape")
            _push(ue.encode("latin-1", errors="replace").decode("utf-8", errors="replace"))
        except Exception:
            pass

    for base in list(candidates):
        try:
            _push(base.encode("latin-1", errors="replace").decode("utf-8", errors="replace"))
        except Exception:
            pass
        try:
            _push(base.encode("cp1252", errors="replace").decode("utf-8", errors="replace"))
        except Exception:
            pass

    def _polish(txt: str) -> str:
        t = str(txt or "")
        t = t.replace("â€”", " - ")
        t = t.replace("â€“", " - ")
        t = t.replace("\u00e2\u0080\u0094", " - ")
        t = t.replace("\u00e2\u0080\u0093", " - ")
        t = t.replace("—", " - ")
        t = t.replace("–", " - ")
        t = t.replace("â€˜", "'").replace("â€™", "'")
        t = t.replace("â€œ", "\"").replace("â€�", "\"")
        t = t.replace("Ã—", "x")
        # Some locales render the mojibake dash artifact as standalone "à".
        t = re.sub(r"(?<=[A-Za-z0-9])\s+à\s+(?=[A-Za-z0-9])", " - ", t)
        # Another common artifact is a literal '?' replacing a dash between words.
        t = re.sub(r"(?<=[A-Za-z0-9])\?(?=[A-Za-z0-9])", " - ", t)
        t = re.sub(r"\s+", " ", t).strip()
        return t

    polished = [_polish(c) for c in candidates if c]
    if not polished:
        return ""

    def _score(txt: str):
        bad = 0
        bad += txt.count("�") * 8
        bad += txt.count("\\x") * 3
        bad += txt.count("Ã") * 3
        bad += txt.count("Â") * 3
        bad += txt.count("â") * 2
        if re.search(r"(?<=[A-Za-z0-9])\s+à\s+(?=[A-Za-z0-9])", txt):
            bad += 4
        return (bad, len(txt))

    return min(polished, key=_score)

def _mr_log(msg: str) -> None:
    return

def _mr_log_exc(context: str) -> None:
    return

# Build region list from the editor's season config so it stays in sync.
_MR_REGION_LIST = BASE_MAPS + [(code, REGION_NAME_MAP.get(code, code)) for code, _ in SEASON_CODE_LABELS]
_MR_REGION_ORDER = [r for r, _ in _MR_REGION_LIST]
_MR_REGION_LOOKUP = dict(_MR_REGION_LIST)
_MR_CATEGORY_PRIORITY = ["_CONTRACTS", "_TASKS", "_CONTESTS"]
_MR_TYPE_PRIORITY = ["truckDelivery", "cargoDelivery", "exploration"]
_MR_ALLOWED_CATEGORIES = set(_MR_CATEGORY_PRIORITY)

def _mr_store_in_memory(name: str, data: bytes, url: Optional[str] = None) -> None:
    if not name or data is None:
        return
    _MR_IN_MEM_FILES[name] = data
    if url:
        _MR_IN_MEM_META[name] = {"url": url}

def _mr_get_file_bytes_or_mem(name: str) -> Optional[bytes]:
    if name in _MR_IN_MEM_FILES:
        return _MR_IN_MEM_FILES[name]
    try:
        if os.path.exists(name) and os.path.isfile(name):
            with open(name, "rb") as f:
                return f.read()
    except Exception:
        pass
    try:
        base = os.path.basename(name)
        if base in _MR_IN_MEM_FILES:
            return _MR_IN_MEM_FILES[base]
        if os.path.exists(base) and os.path.isfile(base):
            with open(base, "rb") as f:
                return f.read()
    except Exception:
        pass
    return None

def _mr_extract_js_string_literal(text: str, start_idx: int) -> Optional[str]:
    """Extract a JS string literal starting at the given quote index."""
    if start_idx >= len(text):
        return None
    quote = text[start_idx]
    if quote not in ("'", '"'):
        return None
    k = start_idx + 1
    escaped = False
    out = []
    while k < len(text):
        ch = text[k]
        if escaped:
            out.append(ch)
            escaped = False
            k += 1
            continue
        if ch == "\\":
            escaped = True
            k += 1
            continue
        if ch == quote:
            return "".join(out)
        out.append(ch)
        k += 1
    return None

def _mr_parse_localization_from_desc_text(txt: str) -> Dict[str, str]:
    """Parse localization entries from MapRunner desc.js text."""
    result: Dict[str, str] = {}
    if not txt:
        return result
    if not isinstance(txt, str):
        try:
            txt = _mr_decode_bytes_to_text(txt) or ""
        except Exception:
            try:
                txt = txt.decode("utf-8", errors="replace")
            except Exception:
                txt = str(txt)
    if not txt:
        return result

    # Fast-path: if there's no localization marker, skip heavy parsing.
    if ("s:\"" not in txt) and ("s:'" not in txt) and ("s :" not in txt):
        return result

    # Regex pass: capture KEY:{...s:"..."} with quoted or bare keys.
    pattern = re.compile(
        r'(?:\"([^\"]+)\"|([A-Za-z0-9_\\-]+))\s*:\s*\{.*?s\s*:\s*(?:\"((?:\\.|[^\"\\])*)\"|\'((?:\\.|[^\'\\])*)\')',
        re.DOTALL
    )
    for match in pattern.finditer(txt):
        key = match.group(1) or match.group(2)
        val = match.group(3) or match.group(4) or ""
        if not key:
            continue
        try:
            val = codecs.decode(val.replace(r"\/", "/"), "unicode_escape")
        except Exception:
            pass
        result[key] = (val or "").strip()

    # If regex didn't capture enough, fall back to a fast windowed scan.
    if len(result) < 200:
        key_re = re.compile(r'([A-Za-z0-9_\\-]+)\s*:\s*\{')
        for m in key_re.finditer(txt):
            key = m.group(1)
            if not key or key in result:
                continue
            start = m.end()
            window_end = min(len(txt), start + 600)
            segment = txt[start:window_end]
            sm = re.search(r's\s*:\s*(\"|\')', segment)
            if not sm:
                continue
            quote_idx = start + sm.start(1)
            val = _mr_extract_js_string_literal(txt, quote_idx)
            if val is None:
                continue
            try:
                val = codecs.decode(val.replace(r"\/", "/"), "unicode_escape")
            except Exception:
                pass
            result[key] = (val or "").strip()

    return result

def _mr_decode_bytes_to_text(bs: Optional[bytes]) -> Optional[str]:
    if bs is None:
        return None
    if isinstance(bs, str):
        return bs
    # Detect compressed payloads by magic bytes (in case headers are missing)
    try:
        if bs[:2] == b"\x1f\x8b":
            try:
                bs = gzip.decompress(bs)
            except Exception:
                pass
        elif bs[:2] in (b"\x78\x01", b"\x78\x9c", b"\x78\xda"):
            try:
                bs = zlib.decompress(bs)
            except Exception:
                pass
    except Exception:
        pass
    try:
        return bs.decode("utf-8")
    except Exception:
        pass
    try:
        import brotli  # type: ignore
        try:
            out = brotli.decompress(bs)
            return out.decode("utf-8", errors="replace")
        except Exception:
            pass
    except Exception:
        pass
    for enc in ("utf-8", "latin-1", "windows-1252", "iso-8859-1"):
        try:
            return bs.decode(enc, errors="replace")
        except Exception:
            continue
    try:
        return str(bs)
    except Exception:
        return None

def _mr_http_get(url: str, timeout: int = 15, range_bytes: Optional[tuple] = None):
    headers = {
        "User-Agent": "Mozilla/5.0",
        "Accept": "*/*",
        "Accept-Encoding": "identity",
        "Referer": "https://www.maprunner.info/",
        "Origin": "https://www.maprunner.info",
        "Accept-Language": "en-US,en;q=0.9",
    }
    if range_bytes is not None:
        try:
            start, end = range_bytes
            headers["Range"] = f"bytes={int(start)}-{int(end)}"
        except Exception:
            pass
    req = urllib.request.Request(url, headers=headers)
    def _open_with_ctx(ctx=None):
        if ctx is None:
            return urllib.request.urlopen(req, timeout=timeout)
        return urllib.request.urlopen(req, timeout=timeout, context=ctx)

    try:
        with _open_with_ctx() as resp:
            data = resp.read()
            headers = {k.lower(): v for k, v in resp.headers.items()}
        enc = (headers.get("content-encoding") or "").lower()
        if enc == "gzip":
            try:
                data = gzip.decompress(data)
            except Exception:
                pass
        elif enc == "deflate":
            try:
                data = zlib.decompress(data)
            except Exception:
                pass
        elif enc == "br":
            try:
                import brotli  # type: ignore
                data = brotli.decompress(data)
            except Exception:
                pass
        return data, headers
    except Exception as e:
        # Retry with unverified TLS only if certificate validation fails
        # (best-effort to avoid total feature failure in constrained setups).
        if isinstance(e, ssl.SSLCertVerificationError) or "CERTIFICATE_VERIFY_FAILED" in str(e):
            try:
                ctx = ssl.create_default_context()
                ctx.check_hostname = False
                ctx.verify_mode = ssl.CERT_NONE
                with _open_with_ctx(ctx) as resp:
                    data = resp.read()
                    headers = {k.lower(): v for k, v in resp.headers.items()}
                enc = (headers.get("content-encoding") or "").lower()
                if enc == "gzip":
                    try:
                        data = gzip.decompress(data)
                    except Exception:
                        pass
                elif enc == "deflate":
                    try:
                        data = zlib.decompress(data)
                    except Exception:
                        pass
                elif enc == "br":
                    try:
                        import brotli  # type: ignore
                        data = brotli.decompress(data)
                    except Exception:
                        pass
                return data, headers
            except Exception:
                pass
        if _MR_DEBUG:
            try:
                _mr_log(f"_mr_http_get failed for {url}: {e}")
            except Exception:
                pass
        raise

def _mr_looks_like_js_response(headers: Dict[str, str], url: str) -> bool:
    ctype = (headers.get("content-type") or "").lower()
    return ("javascript" in ctype) or ("/mr/" in url) or url.endswith(".js")

def _mr_probe_js_head(url: str, max_bytes: int = 16384) -> str:
    """Fetch a small prefix of a JS file to detect its signature."""
    try:
        data, headers = _mr_http_get(url, timeout=15, range_bytes=(0, max_bytes - 1))
        txt = _mr_decode_bytes_to_text(data) or ""
        return txt
    except Exception:
        return ""

def _mr_head_has_data_signature(head: str) -> bool:
    if not head:
        return False
    h = head.lstrip()
    if h.startswith(_MR_DATA_SIGNATURE):
        return True
    return ("const _=JSON.parse" in h) and ("RU_02_01_SERVHUB_GAS" in h)

def _mr_head_has_desc_signature(head: str) -> bool:
    if not head:
        return False
    h = head.lstrip()
    if h.startswith(_MR_DESC_SIGNATURE):
        return True
    return ("const t={" in h) and ("UI_TRUCK_TYPE_HEAVY_DUTY" in h) and ("HEAVY DUTY" in h)

def _mr_find_precise_js_from_urls(urls: List[str], head_bytes: int = 65536) -> Dict[str, bool]:
    """Scan URLs by head signature to find the data/desc JS regardless of filename."""
    found = {"data": False, "desc": False}
    for url in urls:
        head = _mr_probe_js_head(url, max_bytes=head_bytes)
        if not head:
            continue
        if (not found["data"]) and _mr_head_has_data_signature(head):
            try:
                data, headers = _mr_http_get(url, timeout=20)
                _mr_store_in_memory(_MR_CANONICAL_NAMES["data"], data, url)
                found["data"] = True
                if _MR_DEBUG:
                    _mr_log(f"precise_js: data={os.path.basename(urlparse(url).path)} url={url}")
            except Exception:
                pass
        if (not found["desc"]) and _mr_head_has_desc_signature(head):
            try:
                data, headers = _mr_http_get(url, timeout=20)
                _mr_store_in_memory(_MR_CANONICAL_NAMES["desc"], data, url)
                found["desc"] = True
                if _MR_DEBUG:
                    _mr_log(f"precise_js: desc={os.path.basename(urlparse(url).path)} url={url}")
            except Exception:
                pass
        if found["data"] and found["desc"]:
            break
    return found

def _mr_score_data_js(text: str) -> int:
    if not text:
        return 0
    tl = text.lower()
    if "json.parse" not in tl:
        return 0
    score = 0
    if '"category"' in tl:
        score += 10
    if '"objectives"' in tl:
        score += 8
    if '"rewards"' in tl:
        score += 8
    if '"key"' in tl:
        score += 10
    if "_contracts" in tl or "_tasks" in tl or "_contests" in tl:
        score += 12
    if '"truckdelivery"' in tl or '"cargodelivery"' in tl or '"exploration"' in tl:
        score += 6
    score += min(len(text) // 5000, 20)
    score += min(tl.count('"category"'), 30)
    score += min(tl.count('"key"'), 30)
    return score

def _mr_score_desc_js(text: str) -> int:
    if not text:
        return 0
    # Require localization-style entries (s:"...") to avoid false positives
    if not re.search(r'\bs\s*:\s*(?:"|\')', text):
        return 0
    score = 0
    if "UI_" in text:
        score += min(text.count("UI_"), 50)
    if re.search(r'\bs\s*:\s*(?:"|\')', text):
        score += 10
    if "_NAME" in text or "_DESC" in text:
        score += 6
    score += min(len(text) // 5000, 20)
    return score

def _mr_choose_best_js_roles() -> None:
    best_data = (0, None, False)
    best_desc = (0, None, False)
    for name, bs in _MR_IN_MEM_FILES.items():
        if not name.lower().endswith(".js"):
            continue
        text = _mr_decode_bytes_to_text(bs)
        if not text:
            continue
        data_score = _mr_score_data_js(text)
        desc_score = _mr_score_desc_js(text)
        meta_url = _MR_IN_MEM_META.get(name, {}).get("url", "")
        is_mr = ("maprunner.info" in meta_url) or ("/mr/" in meta_url)
        if is_mr:
            data_score += 3
            desc_score += 3
        else:
            # Strongly downrank non-MapRunner JS (ads, analytics)
            data_score = max(0, data_score - 50)
            desc_score = max(0, desc_score - 50)
        if data_score > best_data[0]:
            best_data = (data_score, name, is_mr)
        if desc_score > best_desc[0]:
            best_desc = (desc_score, name, is_mr)
    if best_data[1]:
        _mr_store_in_memory(_MR_CANONICAL_NAMES["data"], _MR_IN_MEM_FILES[best_data[1]])
        if _MR_DEBUG:
            try:
                _mr_log(f"choose_best: data={best_data[1]} score={best_data[0]} url={_MR_IN_MEM_META.get(best_data[1],{}).get('url','')}")
            except Exception:
                pass
    # Prefer desc from MapRunner domain; if not, fall back to the data file
    desc_name = None
    if best_desc[1] and best_desc[2]:
        desc_name = best_desc[1]
    elif best_data[1]:
        desc_name = best_data[1]
    if desc_name:
        _mr_store_in_memory(_MR_CANONICAL_NAMES["desc"], _MR_IN_MEM_FILES[desc_name])
        if _MR_DEBUG:
            try:
                _mr_log(f"choose_best: desc={desc_name} score={best_desc[0]} url={_MR_IN_MEM_META.get(desc_name,{}).get('url','')}")
            except Exception:
                pass

def _mr_expand_chunks_from_bundle() -> None:
    """
    If we only have the main bundle, try downloading its dynamic chunks directly
    (from the same CDN base) and rescore to find the data/desc JS.
    """
    if _MR_DEBUG:
        _mr_log("expand_chunks: start")
    # Pick a bundle that actually contains chunk references.
    primary = None
    primary_url = None
    primary_text = None
    chunk_names: List[str] = []
    max_chunks = 0
    try:
        for name, bs in _MR_IN_MEM_FILES.items():
            url = _MR_IN_MEM_META.get(name, {}).get("url", "")
            if "/mr/" not in url or not name.lower().endswith(".js"):
                continue
            try:
                text = _mr_decode_bytes_to_text(bs) or ""
            except Exception:
                continue
            names = sorted(set(re.findall(r'\./([A-Za-z0-9_-]+\.js)', text)))
            if len(names) > max_chunks:
                max_chunks = len(names)
                primary = name
                primary_url = url
                chunk_names = names
                primary_text = text
    except Exception:
        pass

    if not primary or not primary_url or not chunk_names:
        if _MR_DEBUG:
            _mr_log("expand_chunks: no chunk names found")
        return

    base_url = primary_url.rsplit("/", 1)[0] + "/"
    if _MR_DEBUG:
        _mr_log(f"expand_chunks: primary={primary} chunks={len(chunk_names)} base={base_url}")
        _mr_log(f"expand_chunks: first_chunks={chunk_names[:8]}")

    # First, try precise signature-based detection using chunk URLs.
    try:
        urls = [base_url + ch for ch in chunk_names]
        sig_found = _mr_find_precise_js_from_urls(urls, head_bytes=65536)
        if _MR_DEBUG:
            _mr_log(f"expand_chunks: precise_found data={sig_found.get('data')} desc={sig_found.get('desc')}")
    except Exception:
        sig_found = {"data": False, "desc": False}

    # Extract locale chunk mapping from the primary bundle to prioritize English locales.
    english_locale_chunks: List[str] = []
    if primary_text:
        try:
            pattern = re.compile(r'key:\"(locale_[^\"]+)\"[^\\n]*?import\\(\"\\.\\/([A-Za-z0-9_-]+\\.js)\"\\)')
            locale_items = pattern.findall(primary_text)
            if locale_items:
                english_locale_chunks = sorted({
                    chunk for key, chunk in locale_items
                    if key.startswith("locale_en_") or "english" in key
                })
        except Exception:
            english_locale_chunks = []

    # Probe all chunks lightly to find localization candidates.
    loc_candidates: List[tuple] = []
    data_candidates: List[str] = []
    desc_candidates: List[str] = []
    for ch in chunk_names:
        url = base_url + ch
        head = _mr_probe_js_head(url)
        if not head:
            continue
        if ("JSON.parse" in head) and ("const" in head):
            data_candidates.append(ch)
        if ("_DESC_DESC" in head) or ("_DESC\"" in head) or ("_DESC'" in head):
            desc_candidates.append(ch)
        if ("s:\"" in head) or ("s:'" in head) or ("const t=" in head) or ("const t={" in head):
            score = _mr_text_english_score(head)
            try:
                low = head.lower()
                for w in _MR_FORBIDDEN_LANG_WORDS:
                    if w in low:
                        score -= 5.0
                if _MR_CYRILLIC_RE.search(head):
                    score -= 8.0
            except Exception:
                pass
            loc_candidates.append((score, ch))
        # Limit probe list to a reasonable size
        if len(loc_candidates) >= 120 and len(data_candidates) >= 3:
            break

    # Download chunks; aim to capture enough English localization coverage.
    best_data_score = 0
    best_desc_score = 0
    english_entries = 0
    english_chunks = 0
    best_loc_name = None
    best_loc_avg = -999.0
    best_loc_count = 0
    downloaded = 0
    ok = 0
    fail = 0

    # Prioritize localization + description candidates (likely contain strings)
    try:
        loc_candidates_sorted = [c for _, c in sorted(loc_candidates, key=lambda x: x[0], reverse=True)]
    except Exception:
        loc_candidates_sorted = [c for _, c in loc_candidates]
    # Prioritize known English locale chunks, then desc/loc candidates, then the rest.
    download_queue = (
        english_locale_chunks
        + desc_candidates
        + loc_candidates_sorted
        + [ch for ch in chunk_names if ch not in loc_candidates_sorted and ch not in desc_candidates and ch not in english_locale_chunks]
    )
    for i, ch in enumerate(download_queue):
        if ch in _MR_IN_MEM_FILES:
            continue
        if _MR_CHUNK_MAX > 0 and downloaded >= _MR_CHUNK_MAX:
            break
        url = base_url + ch
        try:
            data, headers = _mr_http_get(url, timeout=20)
            _mr_store_in_memory(ch, data, url)
            ok += 1
            downloaded += 1
            # quick score to allow early exit
            txt = _mr_decode_bytes_to_text(data)
            if txt:
                ds = _mr_score_data_js(txt)
                cs = _mr_score_desc_js(txt)
                # Prefer MapRunner domain; URLs here are all /mr/
                best_data_score = max(best_data_score, ds)
                best_desc_score = max(best_desc_score, cs)
                if cs >= 10 and ("s:\"" in txt or "s:'" in txt):
                    try:
                        parsed = _mr_parse_localization_from_desc_text(txt)
                        if parsed:
                            try:
                                sample_vals = _mr_sample_values(list(parsed.values()), _MR_ENGLISH_SAMPLE_MAX)
                            except Exception:
                                sample_vals = list(parsed.values())[:120]
                            avg = _mr_localization_avg_score(parsed)
                            flags = _mr_localization_sample_flags(sample_vals)
                            looks_english = _mr_localization_looks_english(avg, flags)
                            if looks_english:
                                english_chunks += 1
                                english_entries += len(parsed)
                                if (avg > best_loc_avg) or (avg == best_loc_avg and len(parsed) > best_loc_count):
                                    best_loc_name = ch
                                    best_loc_avg = avg
                                    best_loc_count = len(parsed)
                                if _MR_DEBUG:
                                    _mr_log(f"expand_chunks: english_chunk={ch} entries={len(parsed)} avg={avg:.2f}")
                    except Exception:
                        pass
                if _MR_DEBUG and (ds >= 10 or cs >= 10):
                    _mr_log(f"expand_chunks: {ch} ds={ds} cs={cs}")
                have_data = (_MR_CANONICAL_NAMES.get("data") in _MR_IN_MEM_FILES) or (best_data_score >= 20)
                if best_loc_name and best_loc_count >= _MR_ENGLISH_MIN_ENTRIES and have_data:
                    break
        except Exception:
            fail += 1
            continue

    # Re-select best roles from the expanded set
    if _MR_DEBUG:
        _mr_log(f"expand_chunks: downloaded ok={ok} fail={fail} english_chunks={english_chunks} english_entries={english_entries}")
    _mr_choose_best_js_roles()
    # If we identified a strong English localization chunk, prefer it as desc.js.
    if best_loc_name and best_loc_name in _MR_IN_MEM_FILES:
        try:
            meta_url = _MR_IN_MEM_META.get(best_loc_name, {}).get("url")
            _mr_store_in_memory(_MR_CANONICAL_NAMES["desc"], _MR_IN_MEM_FILES[best_loc_name], meta_url)
            if _MR_DEBUG:
                _mr_log(f"expand_chunks: forced desc={best_loc_name} avg={best_loc_avg:.2f} entries={best_loc_count}")
        except Exception:
            pass

def _mr_identify_js_role(text: str) -> Optional[str]:
    if not text:
        return None
    data_score = _mr_score_data_js(text)
    desc_score = _mr_score_desc_js(text)
    if data_score >= 15 and data_score >= desc_score:
        return "data"
    if desc_score >= 10 and desc_score > data_score:
        return "desc"
    return None

def _mr_fallback_download_candidates_to_mem(page_url: str, html: str) -> List[str]:
    found_roles: List[str] = []
    candidates: List[str] = []
    for match in re.finditer(r'<script[^>]+src=["\']([^"\']+)["\']', html, flags=re.IGNORECASE):
        src = match.group(1)
        abs_url = urljoin(page_url, src)
        if "/mr/" in abs_url or abs_url.endswith(".js") or "cdn" in abs_url:
            candidates.append(abs_url)

    # Also include modulepreload/prefetch/preload links (Nuxt/Vite often use these for JS chunks)
    for match in re.finditer(r'<link[^>]+rel=["\'](?:modulepreload|prefetch|preload)["\'][^>]+href=["\']([^"\']+)["\']', html, flags=re.IGNORECASE):
        href = match.group(1)
        abs_url = urljoin(page_url, href)
        if "/mr/" in abs_url or abs_url.endswith(".js") or "cdn" in abs_url:
            candidates.append(abs_url)

    candidates = sorted(set(candidates), key=lambda u: ("/mr/" not in u, u))

    for abs_url in candidates:
        try:
            data, headers = _mr_http_get(abs_url, timeout=15)
            if not _mr_looks_like_js_response(headers, abs_url):
                continue
            txt = _mr_decode_bytes_to_text(data)
            role = _mr_identify_js_role(txt or "")
            filename = os.path.basename(urlparse(abs_url).path) or None
            if role:
                canon = _MR_CANONICAL_NAMES[role]
                if filename:
                    _mr_store_in_memory(filename, data, abs_url)
                _mr_store_in_memory(canon, data, abs_url)
                if canon not in found_roles:
                    found_roles.append(canon)
            else:
                if filename:
                    _mr_store_in_memory(filename, data, abs_url)
        except Exception:
            continue
    return found_roles

def _mr_try_direct_js_endpoints() -> bool:
    """
    Try known static JS endpoints directly (works without Playwright).
    Returns True if both data.js and desc.js were captured.
    """
    endpoints = [
        ("data", "https://www.maprunner.info/mr/data.js"),
        ("desc", "https://www.maprunner.info/mr/desc.js"),
    ]
    for role, url in endpoints:
        try:
            data, headers = _mr_http_get(url, timeout=15)
            if not _mr_looks_like_js_response(headers, url):
                continue
            txt = _mr_decode_bytes_to_text(data) or ""
            identified = _mr_identify_js_role(txt)
            if identified == role:
                _mr_store_in_memory(_MR_CANONICAL_NAMES[role], data, url)
        except Exception:
            continue
    return ("data.js" in _MR_IN_MEM_FILES) and ("desc.js" in _MR_IN_MEM_FILES)

def _mr_download_safe_fallback_js() -> bool:
    """
    Download known-good English JS files from the GitHub safe fallback.
    Returns True if both data.js and desc.js are available after loading.
    """
    global _MR_SAFE_FALLBACK_ERROR
    _MR_SAFE_FALLBACK_ERROR = ""
    _MR_IN_MEM_FILES.clear()
    _MR_IN_MEM_META.clear()
    ok = 0
    data_ok = False
    desc_ok = False
    for url in _MR_SAFE_FALLBACK_URLS:
        try:
            data, headers = _mr_http_get(url, timeout=20)
            filename = os.path.basename(urlparse(url).path) or None
            if filename:
                _mr_store_in_memory(filename, data, url)
            try:
                txt = _mr_decode_bytes_to_text(data) or ""
                if _mr_score_data_js(txt) > 0:
                    data_ok = True
                if _mr_score_desc_js(txt) > 0:
                    desc_ok = True
            except Exception:
                pass
            ok += 1
        except Exception:
            continue
    # Identify and promote canonical data/desc roles from downloaded files.
    _mr_choose_best_js_roles()
    has_data = ("data.js" in _MR_IN_MEM_FILES) and data_ok
    has_desc = ("desc.js" in _MR_IN_MEM_FILES) and desc_ok
    if not has_data or not has_desc:
        missing = []
        if not has_data:
            missing.append("data.js")
        if not has_desc:
            missing.append("desc.js")
        _MR_SAFE_FALLBACK_ERROR = (
            "Safe fallback failed: missing "
            + ", ".join(missing)
            + " in GitHub files."
        )
        return False
    return ok > 0

def _mr_download_js_step() -> None:
    _MR_IN_MEM_FILES.clear()
    _MR_IN_MEM_META.clear()
    found = set()

    # Safe fallback: load known-good GitHub files instead of MapRunner.
    try:
        if _get_objectives_safe_fallback_mode():
            if _mr_download_safe_fallback_js():
                _mr_persist_canonical_js_cache(allow_desc=True)
            else:
                _mr_load_cached_canonical_js_to_mem()
            return
    except Exception:
        pass

    # Fast-path: try known endpoints directly (no Playwright needed)
    try:
        if _MR_DEBUG:
            _mr_log("download_js_step: trying direct endpoints")
        if _mr_try_direct_js_endpoints():
            # Ensure the direct localization looks English; otherwise keep searching.
            try:
                desc_bs = _mr_get_file_bytes_or_mem(_MR_CANONICAL_NAMES["desc"])
            except Exception:
                desc_bs = None
            if _mr_desc_bytes_look_english(desc_bs):
                _mr_persist_canonical_js_cache(allow_desc=True)
                if _MR_DEBUG:
                    _mr_log("download_js_step: direct endpoints success")
                return
            if _MR_DEBUG:
                _mr_log("download_js_step: direct endpoints not English; continuing fallback")
    except Exception:
        if _MR_DEBUG:
            _mr_log_exc("download_js_step: direct endpoints failed")
        pass

    # Use HTML+urllib fallback (no Playwright dependency).
    try:
        data, _ = _mr_http_get(_MR_URL, timeout=15)
        html = _mr_decode_bytes_to_text(data) or ""
        _mr_fallback_download_candidates_to_mem(_MR_URL, html)
        _mr_choose_best_js_roles()
        _mr_expand_chunks_from_bundle()
        try:
            desc_ok = _mr_desc_bytes_look_english(_mr_get_file_bytes_or_mem(_MR_CANONICAL_NAMES["desc"]))
        except Exception:
            desc_ok = False
        _mr_persist_canonical_js_cache(allow_desc=bool(desc_ok))
        if _MR_DEBUG:
            _mr_log(f"download_js_step: fallback html ok; mem_files={list(_MR_IN_MEM_FILES.keys())[:6]}")
        return
    except Exception:
        _mr_load_cached_canonical_js_to_mem()
        if _MR_DEBUG:
            _mr_log_exc("download_js_step: fallback html failed")
        return

def _mr_choose_first_available(candidates: List[str]) -> Optional[str]:
    for name in candidates:
        if _mr_get_file_bytes_or_mem(name) is not None:
            return name
    return candidates[0] if candidates else None

def _mr_collect_localization(desc_js_file: Optional[str]) -> Dict[str, str]:
    """
    Build a localization dictionary by parsing one or more JS files that contain
    localization strings (s:"..."). This merges results across multiple chunks.
    """
    global _MR_LAST_LOCALIZATION_FILES, _MR_LAST_LOCALIZATION_BLOCKED
    merged: Dict[str, str] = {}
    seen_files: Set[str] = set()
    candidates: List[Dict[str, Any]] = []
    _MR_LAST_LOCALIZATION_FILES = []
    _MR_LAST_LOCALIZATION_BLOCKED = False

    def _merge_value(key: str, val: str) -> None:
        if not _mr_value_allowed(val):
            return
        if key not in merged:
            merged[key] = val
            return
        old = merged.get(key, "")
        # Prefer the value that looks more English / less mojibake
        new_score = _mr_text_english_score(val)
        old_score = _mr_text_english_score(old)
        if new_score > old_score + 0.2:
            merged[key] = val

    def _add_candidate(name: Optional[str], txt: Optional[str]) -> None:
        if not name or not txt:
            return
        # quick filter to avoid heavy parsing for unrelated files
        if ("s:\"") not in txt and ("s:'") not in txt and ("s :") not in txt:
            return
        parsed = _mr_parse_localization_from_desc_text(txt)
        if not parsed:
            return
        avg = _mr_localization_avg_score(parsed)
        try:
            all_vals = list(parsed.values())
        except Exception:
            all_vals = []
        try:
            sample_vals = _mr_sample_values(all_vals, _MR_ENGLISH_SAMPLE_MAX)
        except Exception:
            sample_vals = []
        flags = _mr_localization_sample_flags(sample_vals)
        lang_guess = _mr_guess_language_from_values(sample_vals, avg)
        candidates.append({
            "name": name,
            "loc": parsed,
            "avg": avg,
            "count": len(parsed),
            "lang": lang_guess,
            "flags": flags,
        })

    # First try the chosen desc file (if any)
    if desc_js_file:
        try:
            txt = _mr_decode_bytes_to_text(_mr_get_file_bytes_or_mem(desc_js_file))
            _add_candidate(desc_js_file, txt)
            if desc_js_file:
                seen_files.add(desc_js_file)
        except Exception:
            pass

    # Then scan other in-memory JS files likely to contain localization.
    other_files: List[tuple] = []
    for name, bs in list(_MR_IN_MEM_FILES.items()):
        if name in seen_files:
            continue
        if not name.lower().endswith(".js"):
            continue
        if name.lower() == _MR_CANONICAL_NAMES.get("data", "data.js"):
            continue
        other_files.append((name, bs))

    try:
        other_files.sort(
            key=lambda item: len(item[1]) if isinstance(item[1], (bytes, bytearray)) else 0,
            reverse=True,
        )
    except Exception:
        pass

    for name, bs in other_files:
        if _MR_LOCALIZATION_CANDIDATE_MAX > 0 and len(candidates) >= _MR_LOCALIZATION_CANDIDATE_MAX:
            break
        try:
            txt = _mr_decode_bytes_to_text(bs)
        except Exception:
            txt = None
        if not txt:
            continue
        if ("EXP_" not in txt) and ("_DESC_DESC" not in txt) and ("_NAME" not in txt and "_DESC" not in txt):
            # Skip chunks unlikely to contain localization
            continue
        _add_candidate(name, txt)
        seen_files.add(name)

    if not candidates:
        if _MR_DEBUG:
            try:
                _mr_log("collect_localization: no candidates found")
            except Exception:
                pass
        return merged

    # Per-value filters handle language exclusion; keep all candidates here.

    # Avoid tiny localization files (can be high-scoring but useless).
    best_count = max(c.get("count", 0) for c in candidates)
    min_count = max(200, int(best_count * 0.6))
    if best_count >= 2000:
        min_count = max(min_count, 2000)
    try:
        if any(c.get("count", 0) >= _MR_ENGLISH_MIN_ENTRIES for c in candidates):
            min_count = max(min_count, int(_MR_ENGLISH_MIN_ENTRIES))
    except Exception:
        pass
    pool = [c for c in candidates if c.get("count", 0) >= min_count]
    if pool:
        candidates = pool

    # If English-looking localization exists, only use those candidates.
    english_candidates = [
        c for c in candidates
        if _mr_localization_looks_english(float(c.get("avg", -999.0)), c.get("flags") or {})
    ]
    if english_candidates:
        candidates = english_candidates
    else:
        _MR_LAST_LOCALIZATION_BLOCKED = True
        if _MR_DEBUG:
            try:
                _mr_log("collect_localization: no English candidates found; blocking refresh")
            except Exception:
                pass
        return merged

    # Prefer English-looking localization files when multiple locales exist.
    candidates.sort(key=lambda c: (c.get("avg", -999.0), c.get("count", 0)), reverse=True)
    selected = candidates
    best = candidates[0]
    try:
        if best.get("avg", -999.0) >= _MR_ENGLISH_AVG_MIN:
            cutoff = max(_MR_ENGLISH_AVG_MIN, float(best.get("avg", 0.0)) - _MR_ENGLISH_AVG_DELTA)
            selected = [c for c in candidates if float(c.get("avg", -999.0)) >= cutoff]
            if not selected:
                selected = [best]
        else:
            best_lang = str(best.get("lang") or "").strip()
            if best_lang:
                selected = [c for c in candidates if str(c.get("lang") or "").strip() == best_lang]
                if not selected:
                    selected = [best]
            else:
                selected = [best]
    except Exception:
        selected = candidates

    # Merge selected candidates first.
    _MR_LAST_LOCALIZATION_FILES = []
    for cand in selected:
        loc = cand.get("loc") or {}
        for k, v in loc.items():
            _merge_value(k, v)
        if cand.get("name"):
            _MR_LAST_LOCALIZATION_FILES.append(str(cand.get("name")))
    # Preserve the best English localization file as canonical desc.js for caching.
    try:
        best_name = best.get("name")
        if best_name and best_name in _MR_IN_MEM_FILES:
            meta_url = _MR_IN_MEM_META.get(best_name, {}).get("url")
            _mr_store_in_memory(_MR_CANONICAL_NAMES["desc"], _MR_IN_MEM_FILES[best_name], meta_url)
    except Exception:
        pass

    # If still too small, expand with remaining unblocked candidates.
    if len(merged) < 2000 and len(candidates) > len(selected):
        for cand in candidates:
            if cand in selected:
                continue
            loc = cand.get("loc") or {}
            for k, v in loc.items():
                _merge_value(k, v)
            if cand.get("name"):
                _MR_LAST_LOCALIZATION_FILES.append(str(cand.get("name")))

    if _MR_DEBUG:
        try:
            _mr_log(
                f"collect_localization: files={len(_MR_LAST_LOCALIZATION_FILES)} "
                f"entries={len(merged)} best_avg={best.get('avg')}"
            )
        except Exception:
            pass
    return merged

def _write_csv_atomic(path: str, rows: List[Dict[str, Any]], fieldnames: List[str]) -> None:
    if not rows:
        return
    out_dir = os.path.dirname(path) or "."
    tmp_path = None
    try:
        os.makedirs(out_dir, exist_ok=True)
    except Exception:
        pass
    try:
        with tempfile.NamedTemporaryFile("w", delete=False, dir=out_dir, encoding="utf-8", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames, extrasaction="ignore")
            writer.writeheader()
            for row in rows:
                writer.writerow(row)
            tmp_path = f.name
        os.replace(tmp_path, path)
    finally:
        if tmp_path and os.path.exists(tmp_path):
            try:
                os.unlink(tmp_path)
            except Exception:
                pass

def _to_int(value, default=0) -> int:
    try:
        if value is None or value == "":
            return default
        return int(float(value))
    except Exception:
        return default

def _mr_build_csv(out_path: str) -> bool:
    """
    Attempt to download + parse MapRunner data and write a fresh CSV.
    Returns True on success, False on failure.
    """
    try:
        if _MR_DEBUG:
            _mr_log("build_csv: start")
        _mr_download_js_step()
        region_order = _MR_REGION_ORDER
        category_priority = _MR_CATEGORY_PRIORITY
        type_priority = _MR_TYPE_PRIORITY
        region_lookup = _MR_REGION_LOOKUP

        input_file = _mr_choose_first_available([_MR_CANONICAL_NAMES["data"], "data.js"])
        desc_js_file = _mr_choose_first_available([_MR_CANONICAL_NAMES["desc"], "desc.js"])
        if _MR_DEBUG:
            _mr_log(f"build_csv: input_file={input_file} desc_file={desc_js_file} mem_files={list(_MR_IN_MEM_FILES.keys())[:6]}")

        def clean_text(s):
            if s is None:
                return ""
            if not isinstance(s, str):
                try:
                    s = s.decode("utf-8", errors="replace")
                except Exception:
                    s = str(s)
            candidates = [s]
            # Only attempt unicode_escape if the string contains escapes
            if "\\" in s:
                try:
                    cand = bytes(s, "utf-8").decode("unicode_escape")
                    candidates.append(cand)
                except Exception:
                    pass
            try:
                candidates.append(s.encode("latin-1", errors="replace").decode("utf-8", errors="replace"))
            except Exception:
                pass
            try:
                candidates.append(s.encode("utf-8", errors="replace").decode("latin-1", errors="replace"))
            except Exception:
                pass
            try:
                if "\\" in s:
                    cand = bytes(s, "utf-8").decode("unicode_escape").encode("latin-1", errors="replace").decode("utf-8", errors="replace")
                    candidates.append(cand)
            except Exception:
                pass
            def score(x):
                if not x:
                    return 999999
                return x.count("�") + x.count("Ã") + x.count("Â") + x.count("\ufffd")
            best = min(candidates, key=score)
            return _mr_normalize_mojibake_text(best.strip())

        def _collect_desc_text_blobs(current_desc: Optional[str]) -> List[str]:
            blobs: List[str] = []
            seen: Set[str] = set()
            allowed = set(_MR_LAST_LOCALIZATION_FILES) if _MR_LAST_LOCALIZATION_FILES else None
            if current_desc and (allowed is None or current_desc in allowed):
                try:
                    txt = _mr_decode_bytes_to_text(_mr_get_file_bytes_or_mem(current_desc))
                    if txt:
                        blobs.append(txt)
                        seen.add(current_desc)
                except Exception:
                    pass
            for name, bs in list(_MR_IN_MEM_FILES.items()):
                if allowed is not None and name not in allowed:
                    continue
                if name in seen:
                    continue
                if not name.lower().endswith(".js"):
                    continue
                try:
                    txt = _mr_decode_bytes_to_text(bs)
                except Exception:
                    txt = None
                if not txt:
                    continue
                if ("EXP_" not in txt) and ("_DESC_DESC" not in txt) and ("_NAME" not in txt and "_DESC" not in txt):
                    continue
                if ("s:\"") not in txt and ("s:'") not in txt and ("s :") not in txt:
                    continue
                blobs.append(txt)
                seen.add(name)
                if len(blobs) >= 8:
                    break
            return blobs

        localization = _mr_collect_localization(desc_js_file)
        desc_text_blobs = _collect_desc_text_blobs(desc_js_file)

        # If localization is missing, try to expand chunks and re-select desc file.
        if (not localization or len(localization) < 200):
            try:
                _mr_expand_chunks_from_bundle()
                _mr_choose_best_js_roles()
                desc_js_file = _mr_choose_first_available([_MR_CANONICAL_NAMES["desc"], "desc.js"])
                localization = _mr_collect_localization(desc_js_file)
                desc_text_blobs = _collect_desc_text_blobs(desc_js_file)
            except Exception:
                pass
        if _MR_LAST_LOCALIZATION_BLOCKED:
            log("Maprunner localization blocked by language filters; using cached/bundled data.")
            return False
        if localization and len(localization) < _MR_MIN_LOCALIZATION_ENTRIES:
            log("Maprunner localization too small; using cached/bundled data.")
            return False
        if _MR_DEBUG:
            try:
                _mr_log(f"build_csv: localization size={len(localization) if localization else 0}")
            except Exception:
                pass

        _lazy_desc_cache: Dict[str, Optional[str]] = {}

        def lazy_desc_lookup(tok: str) -> Optional[str]:
            if not tok or not desc_text_blobs:
                return None
            if tok in _lazy_desc_cache:
                return _lazy_desc_cache[tok]
            # Try both bare and quoted keys across multiple blobs
            patterns = [f'{tok}:{{', f'"{tok}":{{', f"'{tok}':{{"]
            for blob in desc_text_blobs:
                idx = -1
                for pat in patterns:
                    idx = blob.find(pat)
                    if idx != -1:
                        break
                if idx == -1:
                    continue
                window = blob[idx: idx + 600]
                m = re.search(r's\\s*:\\s*(\"|\\\')', window)
                if not m:
                    continue
                quote_idx = idx + m.start(1)
                val = _mr_extract_js_string_literal(blob, quote_idx)
                if val is None:
                    continue
                try:
                    val = codecs.decode(val.replace(r"\\/", "/"), "unicode_escape")
                except Exception:
                    pass
                val = clean_text(val)
                _lazy_desc_cache[tok] = val
                return val
            _lazy_desc_cache[tok] = None
            return None

        def translate_token(tok):
            if not tok:
                return ""
            # Build lookup candidates (MapRunner often prefixes EXP_)
            candidates = [tok]
            if tok.startswith("EXP_"):
                candidates.append(tok[4:])
            else:
                candidates.append("EXP_" + tok)
            if tok.startswith("UI_") and not tok.startswith("EXP_UI_"):
                candidates.append("EXP_" + tok)
            for candidate in (tok, tok.upper(), tok.lower()):
                if candidate not in candidates:
                    candidates.append(candidate)
            if localization:
                for candidate in candidates:
                    if candidate in localization:
                        return clean_text(localization[candidate])
                stripped = tok.replace("UI_", "").replace("_NAME", "").replace("_DESC", "")
                if stripped in localization:
                    return clean_text(localization[stripped])
                if "EXP_" + stripped in localization:
                    return clean_text(localization["EXP_" + stripped])
            # If still not found, try lazy lookup across blobs
            for candidate in candidates:
                fallback = lazy_desc_lookup(candidate)
                if fallback:
                    return fallback
            return clean_text(tok)

        def collect_types(obj):
            types = set()
            if isinstance(obj, dict):
                t = obj.get("type")
                if isinstance(t, str) and t.strip():
                    types.add(t.strip())
                for v in obj.values():
                    types.update(collect_types(v))
            elif isinstance(obj, list):
                for item in obj:
                    types.update(collect_types(item))
            return types

        def pretty_cargo_name(raw_name):
            if not raw_name:
                return "Unknown"
            s = raw_name.replace("UI_CARGO_", "").replace("_NAME", "").replace("Cargo", "")
            s = s.replace("_", " ").strip()
            return " ".join([p.capitalize() for p in s.split()])

        def collect_cargo(obj):
            cargos = []
            if isinstance(obj, dict):
                if "cargo" in obj and isinstance(obj["cargo"], list):
                    for c in obj["cargo"]:
                        if isinstance(c, dict):
                            count = str(c.get("count", "") or "")
                            name = c.get("name") or c.get("key") or "Unknown"
                            name = pretty_cargo_name(name)
                            cargos.append(f"{count}× {name}" if count and count != "-1" else name)
                for v in obj.values():
                    cargos.extend(collect_cargo(v))
            elif isinstance(obj, list):
                for v in obj:
                    cargos.extend(collect_cargo(v))
            return cargos

        def humanize_key(k):
            parts = k.split("_")
            return " ".join([p.capitalize() for p in parts if p])

        def extract_js_parse_string(txt):
            idx = txt.find("JSON.parse")
            if idx == -1:
                return None
            i = txt.find("(", idx)
            if i == -1:
                return None
            j = i + 1
            while j < len(txt) and txt[j].isspace():
                j += 1
            if j >= len(txt) or txt[j] not in ("'", '"'):
                return None
            quote = txt[j]
            start = j + 1
            k = start
            escaped = False
            while k < len(txt):
                ch = txt[k]
                if escaped:
                    escaped = False
                    k += 1
                    continue
                if ch == "\\":
                    escaped = True
                    k += 1
                    continue
                if ch == quote:
                    return txt[start:k]
                k += 1
            return None

        def unescape_js_string(s):
            if s is None:
                return ""
            try:
                normalized = s.replace(r'\/', '/')
                return codecs.decode(normalized, "unicode_escape")
            except Exception:
                return s

        def load_embedded_json(filename):
            def _extract_js_string_literal(txt, start_idx):
                if start_idx >= len(txt):
                    return None
                quote = txt[start_idx]
                if quote not in ("'", '"', "`"):
                    return None
                k = start_idx + 1
                escaped = False
                out = []
                while k < len(txt):
                    ch = txt[k]
                    if escaped:
                        out.append(ch)
                        escaped = False
                        k += 1
                        continue
                    if ch == "\\":
                        escaped = True
                        k += 1
                        continue
                    if quote == "`" and ch == "$" and k + 1 < len(txt) and txt[k + 1] == "{":
                        # Template literal with interpolation not supported
                        return None
                    if ch == quote:
                        return "".join(out)
                    out.append(ch)
                    k += 1
                return None

            def _extract_largest_string(txt, min_len=100000):
                best = None
                best_len = 0
                i = 0
                n = len(txt)
                while i < n:
                    ch = txt[i]
                    if ch not in ("'", '"', "`"):
                        i += 1
                        continue
                    quote = ch
                    i += 1
                    escaped = False
                    start = i
                    has_interp = False
                    while i < n:
                        c = txt[i]
                        if escaped:
                            escaped = False
                            i += 1
                            continue
                        if c == "\\":
                            escaped = True
                            i += 1
                            continue
                        if quote == "`" and c == "$" and i + 1 < n and txt[i + 1] == "{":
                            has_interp = True
                        if c == quote:
                            s = txt[start:i]
                            if not has_interp:
                                slen = len(s)
                                if slen > best_len and slen >= min_len:
                                    best_len = slen
                                    best = s
                            i += 1
                            break
                        i += 1
                    else:
                        break
                return best

            def _find_json_parse_payload(txt):
                pos = 0
                while True:
                    idx = txt.find("JSON.parse", pos)
                    if idx == -1:
                        return None
                    i = txt.find("(", idx)
                    if i == -1:
                        return None
                    j = i + 1
                    while j < len(txt) and txt[j].isspace():
                        j += 1
                    if j >= len(txt):
                        return None
                    # JSON.parse(VAR_NAME) -> resolve variable
                    m = re.match(r'([A-Za-z_$][\\w$]*)', txt[j:])
                    if m:
                        varname = m.group(1)
                        # look for const/let/var assignment
                        assign_patterns = [
                            rf'(?:const|let|var)\\s+{re.escape(varname)}\\s*=\\s*',
                            rf'{re.escape(varname)}\\s*=\\s*',
                        ]
                        for pat in assign_patterns:
                            am = re.search(pat, txt)
                            if am:
                                k = am.end()
                                while k < len(txt) and txt[k].isspace():
                                    k += 1
                                if k < len(txt):
                                    if txt.startswith("atob", k):
                                        j2 = txt.find("(", k)
                                        if j2 != -1:
                                            j3 = j2 + 1
                                            while j3 < len(txt) and txt[j3].isspace():
                                                j3 += 1
                                            s = _extract_js_string_literal(txt, j3)
                                            if s is not None:
                                                try:
                                                    import base64
                                                    raw = base64.b64decode(s)
                                                    decoded = _mr_decode_bytes_to_text(raw) or ""
                                                    return decoded
                                                except Exception:
                                                    pass
                                    if txt[k] in ("'", '"', "`"):
                                        s = _extract_js_string_literal(txt, k)
                                        if s is not None:
                                            return s
                        pos = idx + 10
                        continue
                    # JSON.parse(atob("..."))
                    if txt.startswith("atob", j):
                        j2 = txt.find("(", j)
                        if j2 == -1:
                            pos = idx + 10
                            continue
                        j3 = j2 + 1
                        while j3 < len(txt) and txt[j3].isspace():
                            j3 += 1
                        s = _extract_js_string_literal(txt, j3)
                        if s is None:
                            pos = idx + 10
                            continue
                        try:
                            import base64
                            raw = base64.b64decode(s)
                            decoded = _mr_decode_bytes_to_text(raw) or ""
                            return decoded
                        except Exception:
                            pos = idx + 10
                            continue
                    # JSON.parse("...") / JSON.parse('...') / JSON.parse(`...`)
                    if txt[j] in ("'", '"', "`"):
                        s = _extract_js_string_literal(txt, j)
                        if s is not None:
                            return s
                    pos = idx + 10

            bs = _mr_get_file_bytes_or_mem(filename)
            if bs is None:
                return None
            txt = _mr_decode_bytes_to_text(bs)
            if _MR_DEBUG:
                try:
                    head = bs[:8]
                    head_hex = "".join([f"{b:02x}" for b in head])
                    _mr_log(f"load_embedded_json: {filename} bytes={len(bs)} head={head_hex} has_JSON_parse={bool(txt and ('JSON.parse' in txt))}")
                except Exception:
                    pass
            if not txt:
                return None
            embedded = _find_json_parse_payload(txt)
            if embedded is None:
                embedded = extract_js_parse_string(txt)
            if embedded is None:
                # Fallback: try largest string literal in the file
                try:
                    candidate = _extract_largest_string(txt)
                    if candidate:
                        if _MR_DEBUG:
                            _mr_log(f"load_embedded_json: largest string len={len(candidate)}")
                        embedded = candidate
                except Exception:
                    pass
            if embedded is None:
                return None
            json_text = unescape_js_string(embedded)
            try:
                return json.loads(json_text)
            except Exception:
                try:
                    repaired = clean_text(json_text)
                    return json.loads(repaired)
                except Exception:
                    try:
                        embedded_bytes = embedded.encode("utf-8", errors="replace")
                        candidate = embedded_bytes.decode("latin-1", errors="replace")
                        candidate = unescape_js_string(candidate)
                        return json.loads(candidate)
                    except Exception:
                        return None

        # Try multiple candidates if the primary data file fails
        data = load_embedded_json(input_file) if input_file else None
        if not data:
            if _MR_DEBUG:
                _mr_log("build_csv: primary load_embedded_json failed; trying candidates")
            # Rank candidates by data score
            candidates = []
            try:
                for name, bs in _MR_IN_MEM_FILES.items():
                    if not name.lower().endswith(".js"):
                        continue
                    txt = _mr_decode_bytes_to_text(bs) or ""
                    ds = _mr_score_data_js(txt)
                    if ds > 0:
                        candidates.append((ds, name))
                candidates.sort(reverse=True)
            except Exception:
                candidates = []
            for _, name in candidates:
                if name == input_file:
                    continue
                data = load_embedded_json(name)
                if data:
                    if _MR_DEBUG:
                        _mr_log(f"build_csv: data loaded from candidate {name}")
                    break
        if not data:
            if _MR_DEBUG:
                _mr_log("build_csv: load_embedded_json failed (no data)")
            return False

        rows = []
        wanted_columns = [
            "key", "displayName", "category", "region", "region_name", "type",
            "cargo_needed", "experience", "money", "descriptionText", "Source"
        ]

        def walk(o):
            if isinstance(o, dict):
                if "category" in o and "key" in o:
                    key = o["key"].upper()
                    region = "_".join(key.split("_")[:2]) if "_" in key else ""
                    if o.get("category") in _MR_ALLOWED_CATEGORIES and region in region_lookup:
                        exp = money = None
                        if isinstance(o.get("rewards"), list):
                            for r in o["rewards"]:
                                if isinstance(r, dict):
                                    exp = r.get("experience", exp)
                                    money = r.get("money", money)
                        types = collect_types(o.get("objectives", []))
                        cargos = collect_cargo(o.get("objectives", []))
                        if "truckDelivery" in types:
                            type_str = "truckDelivery"
                        elif cargos:
                            type_str = "cargoDelivery"
                        else:
                            type_str = "exploration"
                        cargo_str = "; ".join(cargos) if cargos else None

                        name_field = o.get("name") or ""
                        if name_field and not name_field.startswith("UI_"):
                            display = translate_token(name_field) if localization else clean_text(name_field)
                        else:
                            if localization and name_field:
                                display = translate_token(name_field)
                            elif localization:
                                display = translate_token(key)
                            else:
                                display = clean_text(humanize_key(key))

                        raw_desc = o.get("subtitle") or o.get("description") or o.get("descriptionText") or ""
                        description_text = translate_token(raw_desc) if raw_desc else ""
                        description_text = clean_text(description_text)

                        source = (o.get("category") or "").lstrip("_")

                        rows.append({
                            "key": key,
                            "displayName": clean_text(display),
                            "category": o.get("category"),
                            "region": region,
                            "region_name": region_lookup.get(region, ""),
                            "type": type_str,
                            "cargo_needed": cargo_str,
                            "experience": exp,
                            "money": money,
                            "descriptionText": description_text,
                            "Source": source,
                        })
            for v in (o.values() if isinstance(o, dict) else (o if isinstance(o, list) else [])):
                walk(v)

        walk(data)
        if not rows:
            if _MR_DEBUG:
                _mr_log("build_csv: no rows produced")
            return False

        seen = set()
        unique_rows = []
        for row in rows:
            k = row.get("key")
            if not k or k in seen:
                continue
            seen.add(k)
            unique_rows.append(row)

        region_map = {r: i for i, r in enumerate(region_order)}
        category_map = {cat: i for i, cat in enumerate(category_priority)}
        type_map = {t: i for i, t in enumerate(type_priority)}

        num_re = re.compile(r'(\d+)')
        def numeric_groups_from_key(k, max_groups=4):
            nums = num_re.findall(k)
            nums = [int(x) for x in nums]
            pad = [99999] * max_groups
            return (nums + pad)[:max_groups]

        def sort_key(r):
            nums = numeric_groups_from_key(r.get("key", ""))
            money_num = _to_int(r.get("money"))
            exp_num = _to_int(r.get("experience"))
            return (
                region_map.get(r.get("region"), 9999),
                nums[0], nums[1], nums[2], nums[3],
                category_map.get(r.get("category"), 9999),
                type_map.get(r.get("type"), 9999),
                -money_num,
                -exp_num,
                r.get("displayName") or "",
            )

        rows_sorted = sorted(unique_rows, key=sort_key)
        _write_csv_atomic(out_path, rows_sorted, wanted_columns)
        if _MR_DEBUG:
            try:
                if rows_sorted:
                    r0 = rows_sorted[0]
                    _mr_log(f"build_csv: sample0 key={r0.get('key')} displayName={r0.get('displayName')} region={r0.get('region')}")
                # Log a known key if present
                needle = "US_01_02_LOST_TRAILER_TSK"
                for r in rows_sorted:
                    if r.get("key") == needle:
                        _mr_log(f"build_csv: sample {needle} displayName={r.get('displayName')} desc={str(r.get('descriptionText'))[:80]}")
                        break
            except Exception:
                pass
        if _MR_DEBUG:
            _mr_log(f"build_csv: success rows={len(rows_sorted)} out={out_path}")
        return True
    except Exception as e:
        log(f"Maprunner CSV build failed: {e}")
        _mr_log_exc("build_csv: exception")
        return False

def _objectives_cache_csv_path() -> str:
    try:
        cfg_dir = os.path.dirname(CONFIG_FILE)
    except Exception:
        try:
            cfg_dir = os.path.expanduser("~")
        except Exception:
            cfg_dir = ""
    if not cfg_dir:
        cfg_dir = os.getcwd()
    return os.path.join(cfg_dir, ".snowrunner_editor_maprunner_data.csv")

def _objectives_cache_js_path(role: str) -> str:
    try:
        cfg_dir = os.path.dirname(CONFIG_FILE)
    except Exception:
        try:
            cfg_dir = os.path.expanduser("~")
        except Exception:
            cfg_dir = ""
    if not cfg_dir:
        cfg_dir = os.getcwd()
    role_key = str(role or "").strip().lower()
    if role_key == "desc":
        name = ".snowrunner_editor_maprunner_desc.js"
    else:
        name = ".snowrunner_editor_maprunner_data.js"
    return os.path.join(cfg_dir, name)

def _mr_persist_canonical_js_cache(allow_desc: bool = True) -> None:
    for role, canon in _MR_CANONICAL_NAMES.items():
        if role == "desc" and not allow_desc:
            continue
        bs = _MR_IN_MEM_FILES.get(canon)
        if not isinstance(bs, (bytes, bytearray)) or not bs:
            continue
        out_path = _objectives_cache_js_path(role)
        tmp_path = out_path + ".tmp"
        try:
            os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
        except Exception:
            pass
        try:
            with open(tmp_path, "wb") as f:
                f.write(bytes(bs))
            os.replace(tmp_path, out_path)
        except Exception:
            try:
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
            except Exception:
                pass

def _mr_load_cached_canonical_js_to_mem() -> Dict[str, str]:
    loaded: Dict[str, str] = {}
    for role, canon in _MR_CANONICAL_NAMES.items():
        if canon in _MR_IN_MEM_FILES:
            continue
        path = _objectives_cache_js_path(role)
        if not os.path.exists(path):
            continue
        try:
            with open(path, "rb") as f:
                data = f.read()
            if data:
                _mr_store_in_memory(canon, data, f"cache:{path}")
                loaded[role] = path
        except Exception:
            continue
    return loaded

def _load_csv_to_simpleframe(csv_path: str, skip_non_english: bool = False) -> Optional[SimpleFrame]:
    if not csv_path:
        return None
    log(f"Starting CSV load: {csv_path}")
    if not os.path.exists(csv_path):
        log(f"CSV file not found: {csv_path}")
        return None
    try:
        rows: List[Dict[str, Any]] = []
        with open(csv_path, "r", encoding="utf-8", newline="") as fh:
            reader = csv.DictReader(fh)
            for r in reader:
                normalized = {str(k).strip().lower(): (v if v != "" else None) for k, v in r.items()}
                rows.append(normalized)
        # Optionally skip cached CSVs that are clearly non-English.
        if skip_non_english:
            try:
                if _mr_strings_look_non_english([r.get("displayname") for r in rows if isinstance(r, dict)]):
                    log("CSV appears non-English; skipping this candidate.")
                    return None
            except Exception:
                pass
        log(f"CSV read complete: {len(rows)} rows")
        return SimpleFrame(rows)
    except Exception as e:
        log(f"Failed to read CSV: {e}")
        return None

def _load_parquet_safe(parquet_path: Optional[str] = None, allow_build: bool = True):
    """
    CSV loader with fallback chain.
    Order:
      1) If allow_build, attempt to build fresh CSV into cache (online).
      2) Load cached CSV from last successful build.
      3) Load bundled CSV next to the app (if present).
      4) If none work, return None (no crash).
    """
    if parquet_path is None:
        try:
            parquet_path = default_parquet_path()
        except Exception:
            parquet_path = resource_path("maprunner_data.parquet")

    cache_csv = _objectives_cache_csv_path()
    bundled_csv = resource_path("maprunner_data.csv")
    inferred_csv = os.path.splitext(parquet_path)[0] + ".csv"

    # Attempt online refresh into cache (best-effort)
    if allow_build:
        try:
            built = _mr_build_csv(cache_csv)
            if built:
                log(f"Fresh Objectives+ CSV built: {cache_csv}")
        except Exception:
            pass

    # Fallback chain (cache -> inferred -> bundled)
    candidates = []
    for p in (cache_csv, inferred_csv, bundled_csv):
        if p and p not in candidates:
            candidates.append(p)

    bundled_exists = bool(bundled_csv and os.path.exists(bundled_csv))
    for path in candidates:
        skip_non_english = bool(bundled_exists and path != bundled_csv)
        df = _load_csv_to_simpleframe(path, skip_non_english=skip_non_english)
        if df is not None:
            return df

    # Last resort: use cached CSV even if it is non-English when no bundled fallback exists.
    try:
        if cache_csv and os.path.exists(cache_csv):
            df = _load_csv_to_simpleframe(cache_csv, skip_non_english=False)
            if df is not None:
                log("Using cached CSV despite language filter (no English fallback found).")
                return df
    except Exception:
        pass

    log("Objectives+ CSV load failed: no usable CSV found.")
    return None

# ---------------------------------------------------------------------------
# END SECTION: Objectives+ CSV Builder (Maprunner)
# ---------------------------------------------------------------------------
# --- end CSV-only loader ---


class VirtualObjectivesFast:
    def __init__(self, parent, save_path_var):
        globals()['tk'] = tk
        globals()['ttk'] = ttk
        globals()['messagebox'] = messagebox
        globals()['filedialog'] = filedialog

        # Save parent and variable
        self.parent = parent
        self.save_var = save_path_var
        self._last_save_path = None
        # watcher will be started after the object is fully initialized

        # Basic UI placeholders (actual widgets created in build_ui)
        self.frame = None
        self.topbar = None
        self.canvas = None
        self.canvas_width = 0
        self.canvas_height = 0

        # Data
        self.items: List[Dict[str, Any]] = []
        self.filtered: List[int] = []
        self.original_checked: Set[str] = set()
        self.session_locked: Set[str] = set()
        self.selected_changes: Dict[str, bool] = {}

        # Virtualization config
        self.row_height = 30
        # extra rows reduce redraw artifacts during fast scroll
        self.buffer_rows = 4
        self.pool = []
        self.pool_size = 0
        self.pool_initialized = False
        self._virtualize = True
        # Full-list (non-virtual) UI state
        self._full_frame = None
        self._full_window_id = None
        self._full_rows = []
        # Scroll optimization
        self._scrolling = False
        self._scroll_idle_after = None
        self._needs_full_refresh = False

        # UI state variables (create after tkinter import)
        self.search_var = tk.StringVar()
        self.type_var = tk.StringVar()
        self.region_var = tk.StringVar()
        self.category_var = tk.StringVar()
        # Objectives+ data source controls
        try:
            self.safe_fallback_var = (
                objectives_safe_fallback_var
                if objectives_safe_fallback_var is not None
                else tk.BooleanVar(value=False)
            )
        except Exception:
            self.safe_fallback_var = tk.BooleanVar(value=False)
        self.safe_fallback_cb = None

        # Status / refresh UI
        self.status_var = tk.StringVar(value="")
        self.status_label = None
        self._loading_anim_id = None
        self._loading_phase = 0
        self._loading_base = ""
        self._loading_active = False
        self._status_clear_after = None
        self._refresh_inflight = False

        # Tooltip placeholders
        self._tip = None
        self._tip_label = None
        self._tooltip_after_id = None
        self._tooltip_pending_item = None

        # Lock for thread-safety
        self._lock = threading.Lock()

        # last visible index for logging scroll changes
        self._last_first_visible = -1

        # guard to prevent programmatic checkbox updates from firing change handlers
        self._suppress_trace = False

        # type map
        self._type_label_to_internal = {"": "", "Task": "TASK", "Contract": "CONTRACT", "Contest": "CONTEST"}

        # Style: create when GUI exists (but safe here since tkinter imported inside __init__)
        try:
            self.style = ttk.Style()
            # Configure stripes; if a theme ignores these, it's fine.
            try:
                self.style.configure("RowA.TCheckbutton", background=STRIPE_A)
                self.style.map("RowA.TCheckbutton", background=[("active", STRIPE_A)])
                self.style.configure("RowB.TCheckbutton", background=STRIPE_B)
                self.style.map("RowB.TCheckbutton", background=[("active", STRIPE_B)])
            except Exception:
                pass
        except Exception:
            # Some environments may not allow style configuration before a real root — ignore.
            self.style = None

        # start watching save_var only after the object is fully initialized
        try:
            self._watch_save_var()
        except Exception:
            pass
    def tk_var_get(self, var, default=None):
        """
        Thread-safe getter for tkinter Variable-like objects.
        If called from a background thread, schedules a read on the main
        thread via `self.parent.after` and waits for the result.
        If `var` has no `get` method, returns it directly.
        """
        if not hasattr(var, "get"):
            return var
        try:
            # Fast path: if we're already on the main thread, read directly
            if threading.current_thread() is threading.main_thread():
                return var.get()
        except Exception:
            pass

        ev = threading.Event()
        result = {}

        def _read():
            try:
                result['v'] = var.get()
            except Exception:
                result['v'] = default
            finally:
                try:
                    ev.set()
                except Exception:
                    pass

        try:
            # schedule on mainloop; fall back to direct get if scheduling fails
            if hasattr(self, 'parent') and hasattr(self.parent, 'after'):
                self.parent.after(0, _read)
            else:
                return var.get()
        except Exception:
            try:
                return var.get()
            except Exception:
                return default

        # wait for the mainloop to perform the read
        ev.wait()
        return result.get('v', default)

    def _event_in_objectives(self, event) -> bool:
        """Return True if the mousewheel event originated inside this Objectives+ frame."""
        try:
            if self.frame is None or not self.frame.winfo_ismapped():
                return False
        except Exception:
            # if mapping info isn't available, fall back to widget ancestry check
            pass
        try:
            w = getattr(event, "widget", None)
        except Exception:
            w = None
        while w is not None:
            if w == self.frame:
                return True
            try:
                w = w.master
            except Exception:
                break
        return False

    def _set_cb_var(self, pool_entry, value: bool):
        """Set checkbox variable without triggering trace callbacks."""
        try:
            self._suppress_trace = True
            pool_entry["cb_var"].set(bool(value))
        finally:
            self._suppress_trace = False

    def _init_full_list_ui(self):
        if self._full_frame is not None:
            return
        try:
            self._full_frame = tk.Frame(self.canvas, bg=STRIPE_B)
            self._full_window_id = self.canvas.create_window(
                (0, 0), window=self._full_frame, anchor="nw"
            )
            # keep scrollregion in sync with content size
            self._full_frame.bind(
                "<Configure>",
                lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all"))
            )
        except Exception:
            self._full_frame = None
            self._full_window_id = None

    def _tooltip_text_for_item(self, item: Dict[str, Any]) -> str:
        category_type = item.get("categoryType") or item.get("category") or ""
        cargo_info = item.get("cargo", "")
        tip = (
            f"Name: {item.get('displayName','')}\n"
            f"Type: {item.get('type','').title()}\n"
            f"Category: {category_type}\n"
            f"Region: {REGION_NAME_MAP.get(item.get('region'), item.get('region_name') or item.get('region') or '')}\n"
            f"Money: {item.get('money','')}\nXP: {item.get('xp','')}\n"
        )
        if category_type == "cargoDelivery":
            tip += f"Cargo: {cargo_info}\n"
        desc = item.get("desc", "")
        if desc:
            tip += f"\n{desc}"
        return tip

    def _show_tooltip_for_item(self, item: Dict[str, Any], event):
        tip = self._tooltip_text_for_item(item)
        if self._tip is None or not tk.Toplevel.winfo_exists(self._tip):
            self._tip = tk.Toplevel(self.parent)
            self._tip.wm_overrideredirect(True)
            try:
                self._tip.withdraw()
            except Exception:
                pass
            self._tip_label = tk.Label(
                self._tip,
                text=tip,
                justify="left",
                background=_theme_color_literal("#fefecd", role="bg"),
                relief="solid",
                borderwidth=1,
                wraplength=400
            )
            self._tip_label.pack(ipadx=4, ipady=3)
        else:
            self._tip_label.config(text=tip)
        try:
            x = event.x_root + 10
            y = event.y_root + 10
            self._tip.wm_geometry(f"+{x}+{y}")
            self._tip.deiconify()
        except Exception:
            pass

    def _cancel_tooltip_schedule(self):
        after_id = getattr(self, "_tooltip_after_id", None)
        if after_id is not None and hasattr(self.parent, "after_cancel"):
            try:
                self.parent.after_cancel(after_id)
            except Exception:
                pass
        self._tooltip_after_id = None
        self._tooltip_pending_item = None

    def _schedule_tooltip_for_item(self, item: Dict[str, Any], event=None, delay_ms: int = 260):
        self._cancel_tooltip_schedule()
        self._tooltip_pending_item = item

        def _show_later():
            self._tooltip_after_id = None
            pending = self._tooltip_pending_item
            self._tooltip_pending_item = None
            if pending is None:
                return
            try:
                x_root, y_root = self.parent.winfo_pointerxy()
            except Exception:
                x_root, y_root = (
                    int(getattr(event, "x_root", 0) if event is not None else 0),
                    int(getattr(event, "y_root", 0) if event is not None else 0),
                )
            ev = type("TooltipEvent", (), {"x_root": x_root, "y_root": y_root})()
            self._show_tooltip_for_item(pending, ev)

        try:
            self._tooltip_after_id = self.parent.after(max(50, int(delay_ms)), _show_later)
        except Exception:
            self._tooltip_after_id = None
            self._tooltip_pending_item = None
            try:
                self._show_tooltip_for_item(item, event)
            except Exception:
                pass

    def _clear_full_rows(self):
        for r in self._full_rows:
            try:
                r["frame"].destroy()
            except Exception:
                pass
        self._full_rows = []

    def _render_full_list(self):
        if self._full_frame is None:
            self._init_full_list_ui()
        if self._full_frame is None:
            return
        self._clear_full_rows()

        for row_idx, real_idx in enumerate(self.filtered):
            item = self.items[real_idx]
            item_id = item.get("id")
            color = STRIPE_A if (row_idx % 2 == 0) else STRIPE_B

            f = tk.Frame(self._full_frame, height=self.row_height, bg=color, bd=0, highlightthickness=0)
            f.pack(fill="x")
            f.pack_propagate(False)

            with self._lock:
                if item_id in self.selected_changes and item_id not in self.session_locked:
                    val = bool(self.selected_changes[item_id])
                else:
                    val = bool(item_id in self.original_checked)

            cb_var = tk.BooleanVar(value=val)
            style_name = "RowA.TCheckbutton" if color == STRIPE_A else "RowB.TCheckbutton"
            cb = ttk.Checkbutton(f, variable=cb_var, style=style_name)
            cb.pack(side="left", padx=6)

            lbl = tk.Label(f, text=item.get("displayName", ""), anchor="w", bg=color, bd=0, highlightthickness=0)
            lbl.pack(side="left", fill="x", expand=True, padx=(6, 6))

            info = tk.Label(f, text="i", width=2, relief="ridge", bg=color, bd=1, highlightthickness=0)
            info.pack(side="right", padx=6)

            def _on_toggle(iid=item_id, var=cb_var):
                with self._lock:
                    self.selected_changes[iid] = bool(var.get())
                log(f"Toggle -> id={iid} checked={self.selected_changes[iid]}")

            if item_id in getattr(self, "session_locked", set()):
                try:
                    cb.configure(state="disabled")
                except Exception:
                    pass
            else:
                try:
                    cb.configure(command=_on_toggle)
                except Exception:
                    pass

            info.bind("<Enter>", lambda e, it=item: self._schedule_tooltip_for_item(it, e))
            info.bind("<Leave>", lambda e: self._hide_tooltip())

            self._full_rows.append({"frame": f, "cb": cb, "cb_var": cb_var, "item_id": item_id})

        # ensure scrollregion is updated
        try:
            self.canvas.configure(scrollregion=self.canvas.bbox("all"))
        except Exception:
            pass

    # ---------------- status / refresh helpers ----------------
    def _set_status(self, text: str) -> None:
        try:
            self.status_var.set(text)
        except Exception:
            pass

    def _set_status_temp(self, text: str, ms: int = 2000) -> None:
        self._set_status(text)
        try:
            if self._status_clear_after is not None and hasattr(self.parent, "after_cancel"):
                try:
                    self.parent.after_cancel(self._status_clear_after)
                except Exception:
                    pass
            if hasattr(self.parent, "after"):
                self._status_clear_after = self.parent.after(ms, lambda: self._set_status(""))
        except Exception:
            pass

    def _set_loading_base(self, base_text: str) -> None:
        self._loading_base = base_text
        if self._loading_active:
            dots = "." * (self._loading_phase % 4)
            self._set_status(f"{self._loading_base}{dots}")

    def _start_loading_animation(self, base_text: str) -> None:
        self._loading_active = True
        self._loading_phase = 0
        self._loading_base = base_text
        try:
            if self._loading_anim_id is not None and hasattr(self.parent, "after_cancel"):
                try:
                    self.parent.after_cancel(self._loading_anim_id)
                except Exception:
                    pass
        except Exception:
            pass
        self._tick_loading()

    def _tick_loading(self) -> None:
        if not self._loading_active:
            return
        dots = "." * (self._loading_phase % 4)
        self._set_status(f"{self._loading_base}{dots}")
        self._loading_phase += 1
        try:
            if hasattr(self.parent, "after"):
                self._loading_anim_id = self.parent.after(400, self._tick_loading)
        except Exception:
            pass

    def _stop_loading_animation(self, final_text: Optional[str] = None) -> None:
        self._loading_active = False
        try:
            if self._loading_anim_id is not None and hasattr(self.parent, "after_cancel"):
                try:
                    self.parent.after_cancel(self._loading_anim_id)
                except Exception:
                    pass
        except Exception:
            pass
        self._loading_anim_id = None
        if final_text is not None:
            self._set_status(final_text)

    def refresh_data_async(self) -> None:
        if self._refresh_inflight:
            return
        self._refresh_inflight = True
        base_text = "Fetching newer data" if self.items else "Fetching data"
        try:
            if _get_objectives_safe_fallback_mode():
                base_text = "Fetching safe fallback data"
        except Exception:
            pass
        self._start_loading_animation(base_text)
        cache_csv = _objectives_cache_csv_path()

        def worker():
            built = False
            try:
                built = _mr_build_csv(cache_csv)
            except Exception:
                built = False

            def finish():
                self._refresh_inflight = False
                self._stop_loading_animation()
                if built or not self.items:
                    # reload from cache/bundled without blocking
                    self.load_data_thread(allow_build=False, preserve_changes=True, keep_existing_items=True, show_loading=False)
                if built:
                    self._set_status_temp("Updated to latest data", 2000)
                else:
                    if self.items:
                        self._set_status_temp("Update failed — using cached data", 3000)
                    else:
                        try:
                            if _get_objectives_safe_fallback_mode() and _MR_SAFE_FALLBACK_ERROR:
                                self._set_status_temp(_MR_SAFE_FALLBACK_ERROR, 5000)
                                return
                        except Exception:
                            pass
                        self._set_status_temp("No data available (offline)", 3000)

            try:
                if hasattr(self.parent, "after"):
                    self.parent.after(0, finish)
                else:
                    finish()
            except Exception:
                finish()

        threading.Thread(target=worker, daemon=True).start()

    def _on_safe_fallback_toggle(self) -> None:
        try:
            enabled = bool(self.safe_fallback_var.get())
        except Exception:
            enabled = False
        _set_objectives_safe_fallback_mode(enabled)
        _update_config_values({"objectives_use_safe_fallback": bool(enabled)})
        try:
            if enabled:
                self._set_status_temp("Safe fallback enabled — using GitHub data", 4000)
            else:
                self._set_status_temp("Safe fallback disabled — refresh to update", 3000)
        except Exception:
            pass

    # ---------------- UI builder ----------------
    def build_ui(self):
        # Build the actual UI. This must be called from main thread and after this object is instantiated.
        self.frame = ttk.Frame(self.parent)
        self.topbar = ttk.Frame(self.frame)
        self.frame.pack(fill="both", expand=True)
        self.topbar.pack(side="top", fill="x", padx=6, pady=6)

        ttk.Label(self.topbar, text="Search:").pack(side="left")
        se = ttk.Entry(self.topbar, textvariable=self.search_var, width=30)
        se.pack(side="left", padx=(4, 8))
        se.bind("<KeyRelease>", lambda e: self.apply_filters())

        ttk.Label(self.topbar, text="Type:").pack(side="left")
        cb1 = ttk.Combobox(self.topbar, textvariable=self.type_var, values=["", "Task", "Contract", "Contest"], width=12, state="readonly")
        cb1.pack(side="left", padx=(4, 8))
        cb1.bind("<<ComboboxSelected>>", lambda e: self.apply_filters())

        ttk.Label(self.topbar, text="Region:").pack(side="left")
        cb2 = ttk.Combobox(self.topbar, textvariable=self.region_var, values=[""], width=20, state="readonly")
        cb2.pack(side="left", padx=(4, 8))
        cb2.bind("<<ComboboxSelected>>", lambda e: self.apply_filters())

        ttk.Label(self.topbar, text="Category:").pack(side="left")
        cb3 = ttk.Combobox(self.topbar, textvariable=self.category_var, values=["", "Truck Delivery", "Cargo Delivery", "Exploration"], width=16, state="readonly")
        cb3.pack(side="left", padx=(4, 8))
        cb3.bind("<<ComboboxSelected>>", lambda e: self.apply_filters())

        ttk.Button(self.topbar, text="Reload Save", command=self.reload_checked_from_save).pack(side="right", padx=4)
        self.safe_fallback_cb = ttk.Checkbutton(
            self.topbar,
            text="Use safe fallback (English)",
            variable=self.safe_fallback_var,
            command=self._on_safe_fallback_toggle,
        )
        self.safe_fallback_cb.pack(side="right", padx=(6, 10))

        holder = tk.Frame(self.frame, bg=STRIPE_B)
        holder.pack(fill="both", expand=True, padx=6, pady=(0,6))

        self.canvas = tk.Canvas(holder, highlightthickness=0, bg=STRIPE_B, bd=0)
        vsb = ttk.Scrollbar(holder, orient="vertical", command=self._on_scrollbar)
        self.canvas.configure(yscrollcommand=vsb.set)
        vsb.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)

        # capture sizes
        self.canvas.bind("<Configure>", self._on_canvas_configure)

        # Mousewheel: bind globally but ignore events outside this tab
        try:
            self.canvas.bind_all("<MouseWheel>", self._on_mousewheel, add="+")
            # Linux/X11 wheel events
            self.canvas.bind_all("<Button-4>", self._on_mousewheel, add="+")
            self.canvas.bind_all("<Button-5>", self._on_mousewheel, add="+")
        except Exception:
            try:
                self.canvas.bind_all("<MouseWheel>", self._on_mousewheel)
            except Exception:
                pass
        
        bottom = ttk.Frame(self.frame)
        bottom.pack(side="bottom", fill="x", padx=6, pady=6)

        def _show_objectives_warning():
            msg = (
                "Warning — persistent save edits:\n\n"
                "1) Once you exit the editor with applied changes you can't un-complete those objectives without restoring a backup.\n\n"
                "2) You will not receive in-game rewards for objectives you mark as completed through this editor.\n\n"
                "3) Marking contracts that are locked behind other contracts will break the game until you also mark the prerequisite contracts — check in-game prerequisites before using this tool.\n\n"
            )
            try:
                messagebox.showwarning("Objectives+ — Important", msg)
            except Exception:
                pass

        warn_label = ttk.Label(
            bottom,
            text="⚠️",
            style="Warning.TLabel",
            font=("TkDefaultFont", 9, "bold"),
            wraplength=500,
            justify="left"
        )
        warn_label.pack(side="left", padx=(0, 8))

        warning_palette = _get_effective_theme(_is_dark_mode_active())
        read_btn = tk.Button(
            bottom,
            text="Read warning",
            command=_show_objectives_warning,
            bg=warning_palette.get("warning_btn_bg", "#c62828"),
            fg=warning_palette.get("warning_btn_fg", "white"),
            activebackground=warning_palette.get("warning_btn_active_bg", "#b71c1c"),
            activeforeground=warning_palette.get("warning_btn_fg", "white"),
            highlightthickness=1,
            highlightbackground=warning_palette.get("border", "#c8c8c8"),
            highlightcolor=warning_palette.get("border", "#c8c8c8"),
            bd=1,
            relief=tk.RAISED,
            padx=8,
            pady=2,
            takefocus=0,
        )
        read_btn.pack(side="left", padx=(0, 8))

        # Status centered between left warning and right action buttons
        self.status_label = ttk.Label(
            bottom,
            textvariable=self.status_var,
            style="Warning.TLabel",
            width=36,
            anchor="center",
            justify="center",
            font=("TkFixedFont", 9)
        )
        self.status_label.pack(side="left", padx=(8, 8), expand=True, fill="x")

        ttk.Button(bottom, text="Check filtered", command=self.check_filtered).pack(side="right", padx=4)
        ttk.Button(bottom, text="Uncheck filtered", command=self.uncheck_filtered).pack(side="right", padx=4)
        ttk.Button(bottom, text="Apply Changes", command=self.apply_changes_thread).pack(side="right")
        ttk.Button(bottom, text="Accept Tasks", command=self.accept_tasks_thread).pack(side="right", padx=(0, 4))

    # ---------------- canvas & virtual pool management ----------------
    def _on_canvas_configure(self, event):
        changed = False
        if event.width != self.canvas_width:
            self.canvas_width = event.width
            changed = True
        if event.height != self.canvas_height:
            self.canvas_height = event.height
            changed = True
        if changed and self.items:
            if DEBUG and DEBUG_OBJECTIVES_SCROLL:
                log(f"Canvas resized -> width={self.canvas_width}, height={self.canvas_height}")
            if self._virtualize:
                self._ensure_pool()
            else:
                try:
                    if self._full_window_id is not None:
                        self.canvas.itemconfig(self._full_window_id, width=self.canvas_width)
                except Exception:
                    pass

    def _on_mousewheel(self, event):
        # Ignore wheel events that aren't over this Objectives+ tab
        if not self._event_in_objectives(event):
            return
        try:
            delta = 0
            if hasattr(event, "delta") and event.delta:
                # Windows / MacOS
                delta = int(-1 * (event.delta / 120))
                if delta == 0:
                    delta = -1 if event.delta < 0 else 1
            elif hasattr(event, "num"):
                # Linux / X11
                if event.num == 4:
                    delta = -1
                elif event.num == 5:
                    delta = 1
            if delta == 0:
                return
            self.canvas.yview_scroll(delta, "units")
            self._schedule_scroll_update()
        except Exception:
            # fail silently on unexpected event shapes
            return

    def _on_scrollbar(self, *args):
        self.canvas.yview(*args)
        self._schedule_scroll_update()

    def _schedule_scroll_update(self):
        """Lightweight updates while scrolling; full refresh after idle."""
        # Light update immediately
        try:
            self._scrolling = True
            self._update_visible_rows(light=True)
        except Exception:
            pass
        # Debounce full refresh
        try:
            if self._scroll_idle_after is not None and hasattr(self.parent, "after_cancel"):
                try:
                    self.parent.after_cancel(self._scroll_idle_after)
                except Exception:
                    pass
            if hasattr(self.parent, "after"):
                self._scroll_idle_after = self.parent.after(80, self._on_scroll_idle)
        except Exception:
            pass

    def _on_scroll_idle(self):
        self._scrolling = False
        try:
            # Force a full refresh to sync checkbox states and commands
            self._update_visible_rows(light=False, force_full=True)
            self._refresh_visible_checkbox_vars(force=True)
            self._needs_full_refresh = False
        except Exception:
            pass

    def _watch_save_var(self):
        try:
            current = self.tk_var_get(self.save_var)
            if current != getattr(self, "_last_save_path", None):
                self._last_save_path = current
                if current and os.path.exists(current):
                    log(f"[WATCH] Save path changed -> {current}")
                    self.reload_checked_from_save()
        except Exception as e:
            log(f"[WATCH ERROR] {e}")
        # Recheck every second
        try:
            # parent might not have .after if not yet in mainloop; guard it
            if hasattr(self, "parent") and hasattr(self.parent, "after"):
                self.parent.after(1000, self._watch_save_var)
        except Exception:
            pass

    def _ensure_pool(self):
        if not self._virtualize:
            return
        visible_rows = max(1, int(self.canvas_height / self.row_height))
        desired_pool = min(len(self.filtered), visible_rows + self.buffer_rows)
        if desired_pool == 0:
            desired_pool = min(10, max(1, visible_rows + self.buffer_rows))

        if not self.pool_initialized or desired_pool != self.pool_size:
            if DEBUG and DEBUG_OBJECTIVES_SCROLL:
                log(f"Creating/resizing pool: old={self.pool_size}, new={desired_pool} (filtered={len(self.filtered)})")
            for p in self.pool:
                try:
                    self.canvas.delete(p["window_id"])
                except Exception:
                    pass
            self.pool.clear()

            self.pool_size = desired_pool
            for i in range(self.pool_size):
                f = tk.Frame(self.canvas, height=self.row_height, bg=STRIPE_A, bd=0, highlightthickness=0, relief="flat")
                f.pack_propagate(False)

                cb_var = tk.BooleanVar(value=False)
                cb = ttk.Checkbutton(f, variable=cb_var, style="RowA.TCheckbutton")
                cb.pack(side="left", padx=6)

                lbl = tk.Label(f, text="", anchor="w", bg=STRIPE_A, bd=0, highlightthickness=0)
                lbl.pack(side="left", fill="x", expand=True, padx=(6,6))
                info = tk.Label(f, text="i", width=2, relief="ridge", bg=STRIPE_A, bd=1, highlightthickness=0)
                info.pack(side="right", padx=6)

                def enter(e, pool_index=i):
                    self._schedule_tooltip_for_pool(pool_index, e)
                def leave(e):
                    self._hide_tooltip()

                info.bind("<Enter>", enter)
                info.bind("<Leave>", leave)

                window_id = self.canvas.create_window(
                    (0, 0),
                    window=f,
                    anchor="nw",
                    width=self.canvas_width,
                    height=self.row_height
                )

                p = {
                    "frame": f,
                    "cb_var": cb_var,
                    "cb": cb,
                    "label": lbl,
                    "info": info,
                    "window_id": window_id,
                    "item_index": None
                }
                self.pool.append(p)

            self.pool_initialized = True

        total_h = len(self.filtered) * self.row_height
        self.canvas.configure(scrollregion=(0, 0, self.canvas_width, max(total_h, self.canvas_height)))
        self._update_visible_rows()

    def _update_visible_rows(self, light: bool = False, force_full: bool = False):
        if not self._virtualize:
            return
        if not self.pool_initialized or not self.filtered:
            if self.pool_initialized:
                for p in self.pool:
                    try:
                        self.canvas.itemconfigure(p["window_id"], state="hidden")
                    except Exception:
                        pass
            return

        y0 = self.canvas.canvasy(0)
        first_visible = int(max(0, y0 // self.row_height))
        visible_rows_count = max(1, int(self.canvas_height / self.row_height))
        if first_visible != self._last_first_visible:
            self._last_first_visible = first_visible
            if DEBUG and DEBUG_OBJECTIVES_SCROLL:
                log(f"Viewport first_visible={first_visible} visible_rows={visible_rows_count} (filtered_total={len(self.filtered)})")

        for pool_pos, p in enumerate(self.pool):
            item_idx = first_visible + pool_pos
            if item_idx >= len(self.filtered):
                try:
                    self.canvas.itemconfigure(p["window_id"], state="hidden")
                except Exception:
                    pass
                p["item_index"] = None
                if not light:
                    try:
                        if "_trace_ids" in p:
                            for tid in p["_trace_ids"]:
                                try:
                                    p["cb_var"].trace_remove("write", tid)
                                except Exception:
                                    pass
                            p["_trace_ids"] = []
                        if p.get("cb"):
                            try:
                                p["cb"].configure(command=lambda: None)
                            except Exception:
                                pass
                    except Exception:
                        pass
                continue

            try:
                self.canvas.itemconfigure(p["window_id"], state="normal")
            except Exception:
                pass

            y = item_idx * self.row_height
            try:
                self.canvas.coords(p["window_id"], 0, y)
                self.canvas.itemconfig(p["window_id"], width=self.canvas_width, height=self.row_height)
            except Exception:
                pass

            if force_full or p.get("item_index") != item_idx:
                real_idx = self.filtered[item_idx]
                item = self.items[real_idx]
                item_id = item.get("id")

                try:
                    p["label"].config(text=item.get("displayName", ""))
                except Exception:
                    pass

                # Only update checkbox state/handlers when not in light (scrolling) mode
                if not light:
                    with self._lock:
                        if item_id in self.selected_changes and item_id not in getattr(self, "session_locked", set()):
                            val = bool(self.selected_changes[item_id])
                        else:
                            val = bool(item_id in self.original_checked)

                    try:
                        if "_trace_ids" in p:
                            for tid in p["_trace_ids"]:
                                try:
                                    p["cb_var"].trace_remove("write", tid)
                                except Exception:
                                    pass
                            p["_trace_ids"] = []
                        try:
                            p["cb"].configure(command=lambda: None)
                        except Exception:
                            pass
                    except Exception:
                        pass
                    try:
                        self._set_cb_var(p, val)
                    except Exception:
                        pass

                    try:
                        cb_widget = p.get("cb")
                        if item_id in getattr(self, "session_locked", set()):
                            try:
                                if hasattr(cb_widget, "state"):
                                    cb_widget.state(("disabled",))
                                else:
                                    cb_widget.configure(state="disabled")
                            except Exception:
                                try:
                                    cb_widget.configure(state="disabled")
                                except Exception:
                                    pass
                            try:
                                cb_widget.configure(command=lambda: None)
                            except Exception:
                                pass
                        else:
                            def on_toggle(iid=item_id, var=p["cb_var"]):
                                with self._lock:
                                    self.selected_changes[iid] = bool(var.get())
                                log(f"Toggle -> id={iid} checked={self.selected_changes[iid]}")
                            try:
                                cb_widget.configure(command=on_toggle)
                            except Exception:
                                try:
                                    def _trace(*a, var=p["cb_var"], iid=item_id):
                                        if getattr(self, "_suppress_trace", False):
                                            return
                                        with self._lock:
                                            self.selected_changes[iid] = bool(var.get())
                                        log(f"Toggle(trace) -> id={iid} checked={self.selected_changes[iid]}")
                                    tid = p["cb_var"].trace_add("write", _trace)
                                    if "_trace_ids" not in p:
                                        p["_trace_ids"] = []
                                    p["_trace_ids"].append(tid)
                                except Exception:
                                    pass
                            try:
                                if hasattr(cb_widget, "state"):
                                    cb_widget.state(("!disabled",))
                                else:
                                    cb_widget.configure(state="normal")
                            except Exception:
                                try:
                                    cb_widget.configure(state="normal")
                                except Exception:
                                    pass
                    except Exception:
                        pass

                p["item_index"] = item_idx
                p["frame"]._tip_payload = item

                color = STRIPE_A if (item_idx % 2 == 0) else STRIPE_B
                try:
                    p["frame"].config(bg=color)
                    p["label"].config(bg=color)
                    p["info"].config(bg=color)
                    # ttk or tk checkbutton: try both style and tk colors
                    style_name = "RowA.TCheckbutton" if color == STRIPE_A else "RowB.TCheckbutton"
                    try:
                        p["cb"].configure(style=style_name)
                    except Exception:
                        pass
                    try:
                        p["cb"].config(background=color, bg=color, activebackground=color, selectcolor=color)
                    except Exception:
                        pass
                except Exception:
                    pass

                if not light:
                    try:
                        cb_widget = p.get("cb")
                        if cb_widget:
                            if item_id in getattr(self, "session_locked", set()):
                                try:
                                    if hasattr(cb_widget, "state"):
                                        cb_widget.state(("disabled",))
                                    else:
                                        cb_widget.configure(state="disabled")
                                except Exception:
                                    try:
                                        cb_widget.configure(state="disabled")
                                    except Exception:
                                        pass
                            else:
                                try:
                                    if hasattr(cb_widget, "state"):
                                        cb_widget.state(("!disabled",))
                                    else:
                                        cb_widget.configure(state="normal")
                                except Exception:
                                    try:
                                        cb_widget.configure(state="normal")
                                    except Exception:
                                        pass
                            try:
                                cb_widget.update_idletasks()
                            except Exception:
                                pass
                    except Exception:
                        pass

                if DEBUG and DEBUG_OBJECTIVES_SCROLL:
                    log(f"Assigned pool_pos={pool_pos} -> item_idx={item_idx} (real_idx={real_idx}) id={item['id']} name={item.get('displayName')}")
                    if item_idx >= len(self.filtered) - (visible_rows_count + 2):
                        log(f"Near end of filtered list (pos {item_idx} / {len(self.filtered)})")

        if light:
            self._needs_full_refresh = True

    # ---------------- refresh visible checkbox vars ----------------
    def _refresh_visible_checkbox_vars(self, force=False):
        if not self._virtualize:
            # Update all rows in full list mode
            for r in self._full_rows:
                item_id = r.get("item_id")
                if not item_id:
                    continue
                with self._lock:
                    if item_id in self.selected_changes and item_id not in self.session_locked:
                        val = self.selected_changes[item_id]
                    else:
                        val = (item_id in self.original_checked)
                try:
                    r["cb_var"].set(bool(val))
                except Exception:
                    pass
                try:
                    cb_widget = r.get("cb")
                    if cb_widget:
                        if item_id in self.session_locked:
                            cb_widget.configure(state="disabled")
                        else:
                            cb_widget.configure(state="normal")
                except Exception:
                    pass
            return
        if not self.pool_initialized:
            return
        updated = 0
        with self._lock:
            for p in self.pool:
                item_idx = p.get("item_index")
                if item_idx is None:
                    continue
                if item_idx < 0 or item_idx >= len(self.filtered):
                    continue
                real_idx = self.filtered[item_idx]
                item = self.items[real_idx]
                item_id = item.get("id")

                if item_id in self.selected_changes and item_id not in self.session_locked:
                    val = self.selected_changes[item_id]
                else:
                    val = (item_id in self.original_checked)

                if force or bool(p["cb_var"].get()) != bool(val):
                    self._set_cb_var(p, bool(val))
                    updated += 1

                try:
                    cb_widget = p.get("cb")
                    if cb_widget:
                        if item_id in self.session_locked:
                            if hasattr(cb_widget, "state"):
                                try:
                                    cb_widget.state(("disabled",))
                                except Exception:
                                    cb_widget.configure(state="disabled")
                            else:
                                cb_widget.configure(state="disabled")
                        else:
                            if hasattr(cb_widget, "state"):
                                try:
                                    cb_widget.state(("!disabled",))
                                except Exception:
                                    cb_widget.configure(state="normal")
                            else:
                                cb_widget.configure(state="normal")
                except Exception:
                    pass

    # ---------------- tooltip reuse ----------------
    def _show_tooltip_for_pool(self, pool_index, event):
        if pool_index < 0 or pool_index >= len(self.pool):
            return
        p = self.pool[pool_index]
        item_idx = p.get("item_index")
        if item_idx is None:
            return
        real_idx = self.filtered[item_idx]
        item = self.items[real_idx]
        self._show_tooltip_for_item(item, event)

    def _schedule_tooltip_for_pool(self, pool_index, event):
        if pool_index < 0 or pool_index >= len(self.pool):
            return
        p = self.pool[pool_index]
        item_idx = p.get("item_index")
        if item_idx is None:
            return
        real_idx = self.filtered[item_idx]
        item = self.items[real_idx]
        self._schedule_tooltip_for_item(item, event)

    def _hide_tooltip(self):
        self._cancel_tooltip_schedule()
        if self._tip is not None and tk.Toplevel.winfo_exists(self._tip):
            try:
                self._tip.withdraw()
            except Exception:
                pass

    # ---------------- data loading & filtering ----------------
    def load_data_thread(
        self,
        allow_build: bool = True,
        preserve_changes: bool = False,
        keep_existing_items: bool = False,
        show_loading: bool = True,
    ):
        try:
            if _get_objectives_safe_fallback_mode():
                cache_csv = _objectives_cache_csv_path()
                if not cache_csv or not os.path.exists(cache_csv):
                    allow_build = True
        except Exception:
            pass
        started_loading = False
        try:
            if show_loading and not self._loading_active:
                base_text = "Loading data" if allow_build else "Loading cached data"
                self._start_loading_animation(base_text)
                started_loading = True
        except Exception:
            started_loading = False
        if not keep_existing_items:
            self.items = []
            self.filtered = []
            self.original_checked = set()
            self.session_locked = set()
        if not preserve_changes:
            self.selected_changes = {}

        def worker():
            log("Worker: starting data processing thread")
            tstart = time.perf_counter()
            df = _load_parquet_safe(allow_build=allow_build)
            if df is None or (hasattr(df, "empty") and df.empty):
                log("No data in parquet or failed to read.")
                return
            df.columns = [str(c).strip().lower() for c in df.columns]
            all_items = []
            for idx, row in df.iterrows():
                def g(k):
                    try:
                        v = row.get(k.lower(), "")
                    except Exception:
                        v = ""
                    if _pd is not None:
                        try:
                            if _pd.isna(v):
                                return ""
                        except Exception:
                            pass
                    return "" if v is None else str(v)
                key = g("key") or g("id") or g("name") or f"ITEM_{idx}"
                display = _mr_normalize_mojibake_text(g("displayname") or g("name") or key)
                if not display.strip() or display.startswith("---"):
                    continue
                excel_type = g("type")
                raw_source = (g("source") or "").upper().strip()
                category_val = g("category") or excel_type
                _source_map = {"CONTESTS": "CONTEST", "CONTEST": "CONTEST", "TASKS": "TASK", "TASK": "TASK", "CONTRACTS":"CONTRACT","CONTRACT":"CONTRACT"}
                norm_type = _source_map.get(raw_source)
                if not norm_type and raw_source:
                    norm_type = raw_source[:-1] if raw_source.endswith("S") else raw_source
                if not norm_type:
                    rt = excel_type.lower() if excel_type else ""
                    if "contest" in rt: norm_type = "CONTEST"
                    elif "task" in rt: norm_type = "TASK"
                    elif "contract" in rt: norm_type = "CONTRACT"
                    else: norm_type = ""
                item = {
                    "id": key,
                    "displayName": display,
                    "categoryType": excel_type,
                    "type": norm_type,
                    "region": g("region"),
                    "region_name": g("region_name"),
                    "category": category_val,
                    "money": g("money"),
                    "xp": g("experience"),
                    "cargo": g("cargo_needed"),
                    "desc": _mr_normalize_mojibake_text(g("descriptiontext") or ""),
                    "source": raw_source
                }
                all_items.append(item)
            tmid = (time.perf_counter() - tstart) * 1000.0
            log(f"Parsed items: {len(all_items)} (processing time {tmid:.0f}ms)")

            sp = self.tk_var_get(self.save_var)
            pre = set()
            if sp and os.path.exists(sp):
                try:
                    pre = _read_finished_contests(sp) | _read_finished_missions(sp)
                except Exception:
                    pre = set()

            def finish():
                self.items = all_items
                self.original_checked = pre
                self.session_locked = {
                    str(it.get("id", "")).strip()
                    for it in all_items
                    if str(it.get("id", "")).strip() in pre and (str(it.get("type", "")).upper() != "TASK")
                }
                if preserve_changes:
                    try:
                        valid_ids = {it.get("id") for it in all_items if it.get("id")}
                        with self._lock:
                            self.selected_changes = {k: v for k, v in self.selected_changes.items() if k in valid_ids}
                    except Exception:
                        pass
                else:
                    with self._lock:
                        self.selected_changes = {}
                # Decide whether to virtualize based on item count
                try:
                    self._virtualize = len(all_items) > OBJECTIVES_VIRTUAL_THRESHOLD
                except Exception:
                    self._virtualize = True
                if not self._virtualize:
                    self._init_full_list_ui()

                regs = sorted({
                    REGION_NAME_MAP.get(it.get("region"), it.get("region_name") or it.get("region") or "")
                    for it in all_items if (it.get("region") or it.get("region_name"))
                })
                for child in (self.topbar.winfo_children() if self.topbar else []):
                    if isinstance(child, ttk.Combobox) and child.cget("width") == 20:
                        child.config(values=[""] + [r for r in regs if r])
                try:
                    if self._loading_active and self.items:
                        if self._loading_base.lower().startswith("fetching data"):
                            self._set_loading_base("Fetching newer data")
                except Exception:
                    pass
                log(f"Scheduling finish: items={len(self.items)} original_checked={len(self.original_checked)})")
                self.apply_filters()
                if started_loading:
                    try:
                        self._stop_loading_animation(final_text="")
                    except Exception:
                        pass
            try:
                if hasattr(self.parent, "after"):
                    self.parent.after(10, finish)
            except Exception:
                pass

        threading.Thread(target=worker, daemon=True).start()

    def apply_filters(self):
        q = (self.search_var.get() or "").lower().strip()
        t_label = (self.type_var.get() or "").strip()
        t = self._type_label_to_internal.get(t_label, (t_label or "").upper()).strip()
        rsel = (self.region_var.get() or "").strip()
        csel = (self.category_var.get() or "").strip()

        log(f"Filtering: q='{q}' type='{t}' region='{rsel}' category='{csel}'")

        results = []
        for idx, it in enumerate(self.items):
            if q and q not in it.get("displayName", "").lower():
                continue
            if t and it.get("type", "").upper() != t:
                continue
            rn = REGION_NAME_MAP.get(it.get("region"), it.get("region_name") or it.get("region") or "")
            if rsel and rsel != rn:
                continue
            if csel:
                category_raw = (it.get("categoryType") or it.get("category") or "").strip()
                cat_map = {"Truck Delivery": "truckDelivery", "Cargo Delivery": "cargoDelivery", "Exploration": "exploration"}
                expected = cat_map.get(csel)
                if expected and category_raw != expected:
                    continue
            results.append(idx)
        self.filtered = results
        log(f"Filtering result count: {len(self.filtered)})")

        if self._virtualize:
            if self.pool_initialized:
                for p in self.pool:
                    p["item_index"] = None

            total_h = len(self.filtered) * self.row_height
            if self.canvas:
                try:
                    self.canvas.configure(scrollregion=(0, 0, self.canvas_width, max(total_h, self.canvas_height)))
                except Exception:
                    pass
            self._ensure_pool()
            self._refresh_visible_checkbox_vars()
        else:
            self._render_full_list()

    # ---------------- bulk check/uncheck ----------------
    def check_filtered(self):
        if not self.filtered:
            log("Check filtered: no filtered items")
            return
        cnt = 0
        with self._lock:
            for idx in self.filtered:
                iid = self.items[idx]["id"]
                if iid in self.session_locked:
                    continue
                self.selected_changes[iid] = True
                cnt += 1
        log(f"Check filtered: marked {cnt} items (matching current filters)")
        self._refresh_visible_checkbox_vars()

    def uncheck_filtered(self):
        if not self.filtered:
            log("Uncheck filtered: no filtered items")
            return
        cnt = 0
        with self._lock:
            for idx in self.filtered:
                iid = self.items[idx]["id"]
                if iid in self.session_locked:
                    continue
                self.selected_changes[iid] = False
                cnt += 1
        log(f"Uncheck filtered: marked {cnt} items (matching current filters)")
        self._refresh_visible_checkbox_vars()

    # ---------------- applying changes ----------------
    def apply_changes_thread(self):
        sp = self.tk_var_get(self.save_var)
        if not sp or not os.path.exists(sp):
            try:
                show_info("Info", "No valid save file provided; Apply Changes will only print actions to console.")
            except Exception:
                pass
            return

        # Create backup if host's make_backup_if_enabled exists
        try:
            if 'make_backup_if_enabled' in globals():
                make_backup_if_enabled(sp)
        except Exception:
            pass

        with self._lock:
            changes = dict(self.selected_changes)
            self.selected_changes.clear()
            original_checked_snapshot = set(self.original_checked)

        if not changes:
            log("ApplyChanges: nothing to do")
            return

        log(f"ApplyChanges: batch-applying {len(changes)} changes")

        def worker():
            mission_changes = {}
            contest_changes = {}
            task_reaccept_ids = []
            unexpected_uncheck_ids = []
            try:
                id_to_type = {it["id"]: (it.get("type") or "TASK").upper() for it in self.items}
                for oid, new_value in changes.items():
                    oid_s = str(oid)
                    old_checked = oid_s in original_checked_snapshot
                    now_checked = bool(new_value)
                    kind = id_to_type.get(oid_s, "TASK")

                    if (not old_checked) and now_checked:
                        if kind == "CONTEST":
                            contest_changes[oid_s] = True
                        else:
                            mission_changes[oid_s] = True
                    elif old_checked and (not now_checked):
                        if kind == "TASK":
                            task_reaccept_ids.append(oid_s)
                        else:
                            unexpected_uncheck_ids.append(oid_s)

                task_reaccept_ids = _experiments_dedupe_ids(task_reaccept_ids)

                if task_reaccept_ids:
                    try:
                        _experiments_load_js_objective_sources(force_reload=True)
                    except Exception:
                        pass
                    _experiments_reaccept_finished_tasks(
                        sp,
                        task_reaccept_ids,
                        add_discovered=True,
                        seed_states=True,
                        seed_stage_mode="placeholder",
                        reset_to_unfinished=True,
                        touch_existing_states=False,
                        remove_from_viewed=True,
                        track_first=False,
                        trust_ids_as_tasks=True,
                    )

                if sp and os.path.exists(sp) and (mission_changes or contest_changes):
                    with open(sp, "r", encoding="utf-8") as f:
                        content = f.read()

                    if mission_changes:
                        start = content.find('"objectiveStates"')
                        if start != -1:
                            try:
                                block, bs, be = extract_brace_block(content, start)
                                try:
                                    obj_states = json.loads(block)
                                except Exception:
                                    obj_states = {}
                                for kid in mission_changes.keys():
                                    cur = obj_states.get(kid)
                                    if not isinstance(cur, dict):
                                        cur = {}
                                    cur["isFinished"] = True
                                    obj_states[kid] = cur
                                new_block = json.dumps(obj_states, indent=4, ensure_ascii=False)
                                content = content[:bs] + new_block + content[be:]
                            except Exception as e:
                                log(f"[BATCH WRITE] failed to patch objectiveStates: {e}")
                        else:
                            log("[BATCH WRITE] objectiveStates block not found; mission changes skipped")

                    if contest_changes:
                        try:
                            global_contest_times_new = {}
                            added_total = 0
                            removed_total = 0

                            matches = list(re.finditer(r'"(CompleteSave\d*)"\s*:\s*{', content))
                            for match in reversed(matches):
                                save_key = match.group(1)
                                try:
                                    value_block_str, val_block_start, val_block_end = extract_brace_block(content, match.end() - 1)
                                    try:
                                        value_data = json.loads(value_block_str)
                                    except Exception:
                                        continue

                                    ssl = value_data.get("SslValue") or value_data.get(save_key, {}).get("SslValue") or {}

                                    orig_finished = ssl.get("finishedObjs", [])
                                    finished_is_dict = isinstance(orig_finished, dict)
                                    if isinstance(orig_finished, dict):
                                        finished_set = set(orig_finished.keys())
                                    elif isinstance(orig_finished, list):
                                        finished_set = set(orig_finished)
                                    else:
                                        finished_set = set()

                                    contest_times = ssl.get("contestTimes", {})
                                    if not isinstance(contest_times, dict):
                                        contest_times = {}

                                    added_here = []
                                    removed_here = []

                                    for k in contest_changes.keys():
                                        if k not in finished_set:
                                            finished_set.add(k)
                                            added_here.append(k)
                                        if k not in contest_times:
                                            contest_times[k] = 1
                                            global_contest_times_new[k] = 1

                                    if added_here or removed_here:
                                        if finished_is_dict:
                                            ssl["finishedObjs"] = {kk: True for kk in finished_set}
                                        else:
                                            ssl["finishedObjs"] = list(finished_set)

                                        ssl["contestTimes"] = contest_times

                                        viewed = ssl.get("viewedUnactivatedObjectives", [])
                                        if isinstance(viewed, list) and added_here:
                                            ssl["viewedUnactivatedObjectives"] = [v for v in viewed if v not in added_here]

                                        value_data["SslValue"] = ssl
                                        new_value_block_str = json.dumps(value_data, separators=(",", ":"))
                                        content = content[:val_block_start] + new_value_block_str + content[val_block_end:]

                                        added_total += len(added_here)
                                        removed_total += len(removed_here)
                                except Exception:
                                    continue

                            if global_contest_times_new and 'update_all_contest_times_blocks' in globals():
                                try:
                                    content = update_all_contest_times_blocks(content, global_contest_times_new)
                                except Exception:
                                    pass

                            log(f"[BATCH WRITE] Contests updated: +{added_total} / -{removed_total}")
                        except Exception as e:
                            log(f"[BATCH WRITE] Failed to patch CompleteSave blocks: {e}")

                    try:
                        with open(sp, "w", encoding="utf-8") as f:
                            f.write(content)
                        log(
                            f"[BATCH WRITE] applied complete={len(mission_changes) + len(contest_changes)} "
                            f"reaccept={len(task_reaccept_ids)} to {sp}"
                        )
                    except Exception as e:
                        log(f"[BATCH WRITE] write failed: {e}")
            except Exception as ex:
                log(f"[BATCH WRITE][ERROR] {ex}")

            try:
                new_checked = _read_finished_contests(sp) | _read_finished_missions(sp) if sp and os.path.exists(sp) else set()
            except Exception:
                new_checked = set()
            self.original_checked = new_checked
            self.session_locked = {
                str(it.get("id", "")).strip()
                for it in self.items
                if str(it.get("id", "")).strip() in new_checked and (str(it.get("type", "")).upper() != "TASK")
            }
            log(f"ApplyChanges: finished; original_checked now {len(self.original_checked)} items")

            self._refresh_visible_checkbox_vars()
            self._update_visible_rows()

            try:
                apply_complete = len(mission_changes) + len(contest_changes)
                apply_reaccept = len(task_reaccept_ids)
                apply_total = apply_complete + apply_reaccept
                if unexpected_uncheck_ids:
                    messagebox.showerror(
                        "Objectives+",
                        (
                            "Unexpected\n\n"
                            f"Non-task checked->unchecked transitions detected: {len(unexpected_uncheck_ids)}\n"
                            f"Applied completions: {apply_complete}\n"
                            f"Applied task re-accepts: {apply_reaccept}"
                        ),
                    )
                elif apply_total > 0:
                    show_info(
                        "Objectives+",
                        (
                            f"Successfully applied {apply_total} change(s) to your save file.\n\n"
                            f"Completions: {apply_complete}\n"
                            f"Task re-accepts: {apply_reaccept}"
                        ),
                    )
                else:
                    show_info(
                        "Objectives+",
                        "No changes were applied (nothing selected)."
                    )
            except Exception as e:
                log(f"[BATCH WRITE][POPUP ERROR] {e}")

        threading.Thread(target=worker, daemon=True).start()

    def accept_tasks_thread(self):
        sp = self.tk_var_get(self.save_var)
        if not sp or not os.path.exists(sp):
            try:
                show_info("Info", "No valid save file provided.")
            except Exception:
                pass
            return

        id_to_type = {it.get("id"): (it.get("type") or "").upper() for it in self.items}
        with self._lock:
            # Use Objectives+ current pending selections, but accept only checked TASK entries.
            task_ids = [
                oid
                for oid, should_apply in self.selected_changes.items()
                if bool(should_apply) and id_to_type.get(oid, "") == "TASK"
            ]
            # Keep non-task and uncheck edits untouched for regular "Apply Changes".
            for oid in task_ids:
                self.selected_changes.pop(oid, None)

        task_ids = _experiments_dedupe_ids(task_ids)
        if not task_ids:
            try:
                show_info("Objectives+", "No selected TASK entries to accept.")
            except Exception:
                pass
            return

        try:
            if "make_backup_if_enabled" in globals() and callable(make_backup_if_enabled):
                make_backup_if_enabled(sp)
        except Exception:
            pass

        def worker():
            try:
                try:
                    _experiments_load_js_objective_sources(force_reload=True)
                except Exception:
                    pass
                stats = _experiments_accept_objectives(
                    sp,
                    task_ids,
                    add_discovered=True,
                    seed_states=True,
                    seed_stage_mode="placeholder",
                    reset_to_unfinished=True,
                    touch_existing_states=False,
                    remove_from_finished=False,
                    remove_from_viewed=True,
                    track_first=False,
                    trust_ids_as_tasks=True,
                )
            except Exception as ex:
                stats = None
                log(f"[ACCEPT TASKS][ERROR] {ex}")

            try:
                new_checked = _read_finished_contests(sp) | _read_finished_missions(sp) if sp and os.path.exists(sp) else set()
            except Exception:
                new_checked = set()
            self.original_checked = new_checked
            self.session_locked = {
                str(it.get("id", "")).strip()
                for it in self.items
                if str(it.get("id", "")).strip() in new_checked and (str(it.get("type", "")).upper() != "TASK")
            }

            self._refresh_visible_checkbox_vars(force=True)
            self._update_visible_rows()

            try:
                if isinstance(stats, dict):
                    touched = int(stats.get("states_touched", 0))
                    seeded = int(stats.get("states_seeded", 0))
                    skipped_finished = int(stats.get("ids_skipped_finished", 0))
                    skipped_non_tasks = int(stats.get("ids_skipped_non_tasks", 0))
                    msg = (
                        f"Accept Tasks finished.\n\n"
                        f"Task IDs requested: {len(task_ids)}\n"
                        f"States touched: {touched}\n"
                        f"States seeded: {seeded}\n"
                        f"Skipped already finished: {skipped_finished}\n"
                        f"Skipped non-tasks: {skipped_non_tasks}"
                    )
                    show_info("Objectives+", msg)
                else:
                    show_info("Objectives+", "Accept Tasks finished.")
            except Exception as e:
                log(f"[ACCEPT TASKS][POPUP ERROR] {e}")

        threading.Thread(target=worker, daemon=True).start()

    def reload_checked_from_save(self):
        sp = self.tk_var_get(self.save_var)
        if not sp or not os.path.exists(sp):
            return
        try:
            new_checked = _read_finished_contests(sp) | _read_finished_missions(sp)
        except Exception:
            new_checked = set()

        self.original_checked = new_checked
        self.session_locked = {
            str(it.get("id", "")).strip()
            for it in self.items
            if str(it.get("id", "")).strip() in new_checked and (str(it.get("type", "")).upper() != "TASK")
        }
        self.selected_changes.clear()

        for item in self.items:
            item_id = item.get("id")
            item["checked"] = item_id in self.original_checked

        log(f"Reloaded save: original_checked={len(self.original_checked)}")
        self._refresh_visible_checkbox_vars(force=True)
        self._update_visible_rows()
        if not self._virtualize:
            # refresh full list to reflect locked/checked states
            try:
                self._render_full_list()
            except Exception:
                pass

# -----------------------------------------------------------------------------
# END SECTION: Objectives+ Data, Logging, and Virtualized UI
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Tab Builders (UI construction)
# Used In: launch_gui -> Notebook tabs
# =============================================================================
# TAB: Backups (launch_gui -> tab_backups)
def create_backups_tab(tab_backups, save_path_var):
    """
    Backups tab: lists backup folders -> clicking a folder lists CompleteSave*.cfg/.dat
    Columns: Name | Saved Time | Money | XP | Rank
    - Single-click selects (enables Recall Selected).
    - Double-click folder -> open (list files).
    - Double-click file -> recall that file (+ associated companion files).
    - Recall Selected: when a folder-row is selected -> restore entire backup folder.
                       when a file-row is selected   -> restore that file + companions.
    """
    container = ttk.Frame(tab_backups)
    container.pack(fill="both", expand=True, padx=8, pady=8)

    top_row = ttk.Frame(container)
    top_row.pack(fill="x", pady=(0,6))

    title = ttk.Label(top_row, text="Backups", font=("TkDefaultFont", 11, "bold"))
    title.pack(side="left", anchor="w")

        # add this near the top_row button definitions (after refresh/back/recall buttons)
    settings_btn = ttk.Button(top_row, text="Settings")
    settings_btn.pack(side="right", padx=(6,0))

    def open_backup_settings():
        """
        Robust Backup Settings popup with autosave/backup settings and startup integration.
        """
        # Determine parent safely
        try:
            parent = tab_backups.winfo_toplevel() if 'tab_backups' in globals() and hasattr(tab_backups, 'winfo_toplevel') else (tk._default_root if getattr(tk, "_default_root", None) is not None else None)
        except Exception:
            parent = None

        win = _create_themed_toplevel(parent)
        win.title("Backup Settings")
        win.geometry("580x500")
        win.resizable(False, False)
        try:
            if parent:
                try:
                    win.transient(parent)
                except Exception:
                    pass
        except Exception:
            pass

        # Load config safely
        try:
            cfg = load_config() or {}
        except Exception:
            cfg = {}

        # Ensure globals references
        global make_backup_var, full_backup_var, max_backups_var, max_autobackups_var, autosave_var, save_path_var

        # Local fallbacks if globals missing (UI-bound vars for the popup)
        if 'make_backup_var' not in globals() or make_backup_var is None:
            make_backup_var_local = tk.BooleanVar(win, value=bool(cfg.get("make_backup", True)))
        else:
            make_backup_var_local = make_backup_var

        if 'full_backup_var' not in globals() or full_backup_var is None:
            full_backup_var_local = tk.BooleanVar(win, value=bool(cfg.get("full_backup", False)))
        else:
            full_backup_var_local = full_backup_var

        if 'max_backups_var' not in globals() or max_backups_var is None:
            max_backups_var_local = tk.StringVar(win, value=str(cfg.get("max_backups", "20")))
        else:
            max_backups_var_local = max_backups_var

        if 'max_autobackups_var' not in globals() or max_autobackups_var is None:
            max_autobackups_var_local = tk.StringVar(win, value=str(cfg.get("max_autobackups", "50")))
        else:
            max_autobackups_var_local = max_autobackups_var

        # Force the app-global autosave_var to exist and use it (so popup toggles affect the app immediately)
        try:
            if 'autosave_var' not in globals() or autosave_var is None:
                autosave_var = tk.BooleanVar(win, value=bool(cfg.get("autosave", False)))
        except Exception:
            autosave_var = tk.BooleanVar(win, value=bool(cfg.get("autosave", False)))

        autosave_backup_on_game_exit_var = tk.BooleanVar(
            win,
            value=_cfg_bool(cfg.get("autosave_backup_on_game_exit", False), default=False),
        )
        autosave_poll_interval_var = tk.StringVar(
            win,
            value=str(_sanitize_autosave_poll_interval_seconds(cfg.get("autosave_poll_interval_seconds", 60), default=60)),
        )
        startup_with_windows_var = tk.BooleanVar(
            win,
            value=_cfg_bool(cfg.get("start_with_windows", False), default=False),
        )

        startup_supported = _is_windows_startup_supported()

        def _autosave_toggled(*_):
            """Start/stop autosave monitor when checkbox changes."""
            try:
                _refresh_autosave_runtime_state_from_vars()
            except Exception:
                pass
            try:
                if autosave_var.get():
                    start_autosave_monitor()
                else:
                    stop_autosave_monitor()
            except Exception as e:
                print("[Autosave] toggle error:", e)

        def _on_startup_normal_toggle():
            # checkbox state is already the desired final state
            return

        def _attach_hover_tooltip(anchor_widget, tooltip_text):
            tip_state = {"win": None, "job": None}

            def _cancel_job():
                job = tip_state.get("job")
                if job is not None:
                    try:
                        anchor_widget.after_cancel(job)
                    except Exception:
                        pass
                    tip_state["job"] = None

            def _hide(_event=None):
                _cancel_job()
                tip = tip_state.get("win")
                if tip is not None:
                    try:
                        tip.destroy()
                    except Exception:
                        pass
                    tip_state["win"] = None

            def _show_now():
                _hide()
                try:
                    tip = tk.Toplevel(anchor_widget)
                    tip.wm_overrideredirect(True)
                    try:
                        tip.withdraw()
                    except Exception:
                        pass
                    try:
                        tip.attributes("-topmost", True)
                    except Exception:
                        pass
                    x = int(anchor_widget.winfo_rootx() + anchor_widget.winfo_width() + 8)
                    y = int(anchor_widget.winfo_rooty() + anchor_widget.winfo_height() + 6)
                    tip.geometry(f"+{x}+{y}")
                    tk.Label(
                        tip,
                        text=str(tooltip_text or ""),
                        justify="left",
                        wraplength=500,
                        bg="#fffbe6",
                        fg="black",
                        relief="solid",
                        bd=1,
                        padx=8,
                        pady=6,
                    ).pack()
                    tip_state["win"] = tip
                    try:
                        tip.deiconify()
                    except Exception:
                        pass
                except Exception:
                    _hide()

            def _schedule_show(_event=None):
                _cancel_job()
                try:
                    tip_state["job"] = anchor_widget.after(260, _show_now)
                except Exception:
                    _show_now()

            anchor_widget.bind("<Enter>", _schedule_show, add="+")
            anchor_widget.bind("<Leave>", _hide, add="+")
            anchor_widget.bind("<ButtonPress>", _hide, add="+")
            anchor_widget.bind("<FocusOut>", _hide, add="+")

        # Build UI
        frm = ttk.Frame(win, padding=10)
        frm.pack(fill="both", expand=True)

        ttk.Label(frm, text="Backup options", font=("TkDefaultFont", 11, "bold")).pack(anchor="w", pady=(0,8))

        # Checkbuttons
        try:
            ttk.Checkbutton(frm, text="Small Backup (only the main save file)", variable=make_backup_var_local).pack(anchor="w", pady=(2,4))
        except Exception:
            ttk.Checkbutton(frm, text="Small Backup (only the main save file)").pack(anchor="w", pady=(2,4))

        try:
            ttk.Checkbutton(frm, text="Full Backup (entire save folder) Recommended", variable=full_backup_var_local).pack(anchor="w", pady=(0,8))
        except Exception:
            ttk.Checkbutton(frm, text="Full Backup (entire save folder) Recommended").pack(anchor="w", pady=(0,8))

        # Autosave checkbox bound to the global var so it affects the monitor immediately
        ttk.Checkbutton(
            frm,
            text="Enable Autosave (create autobackup when game autosaves)",
            variable=autosave_var,
            command=_autosave_toggled,
        ).pack(anchor="w", pady=(0,6))
        ttk.Checkbutton(
            frm,
            text="When SnowRunner closes, create one final full backup",
            variable=autosave_backup_on_game_exit_var,
        ).pack(anchor="w", pady=(0,8))

        scan_row = ttk.Frame(frm)
        scan_row.pack(fill="x", pady=(2, 8))
        ttk.Label(scan_row, text="Scan for SnowRunner every").pack(side="left")
        ttk.Entry(scan_row, textvariable=autosave_poll_interval_var, width=8).pack(side="left", padx=(6, 6))
        ttk.Label(scan_row, text="seconds").pack(side="left")

        scan_info_badge = tk.Label(
            scan_row,
            text="i",
            width=2,
            relief="ridge",
            bd=1,
            highlightthickness=0,
            cursor="question_arrow",
            bg=_theme_color_literal("#e9e9e9", role="button_bg"),
            fg=_theme_color_literal("black", role="fg"),
        )
        scan_info_badge.pack(side="left", padx=(8, 0))
        _attach_hover_tooltip(
            scan_info_badge,
            "SnowRunner checks are important: this sets how often the editor checks for SnowRunner and save-file changes.\n\n"
            "Lower values are safer and detect things faster, but use more CPU.\n"
            "Higher values improve performance but can miss short changes or delay the final backup after game close.\n\n"
            "Even at 1 second, autobackups are still triggered by actual save-file changes (not every second).",
        )

        # small red help text under the autosave checkbox
        tk.Label(frm,
                 text="Autosaves work only if the editor is running in the background",
                 fg="red",
                 justify="left",
                 wraplength=440).pack(anchor="w", pady=(0,8))

        # Max backups (normal)
        row1 = ttk.Frame(frm)
        row1.pack(fill="x", pady=(6, 2))
        ttk.Label(row1, text="Max backups (0 = unlimited):").pack(side="left")
        try:
            ttk.Entry(row1, textvariable=max_backups_var_local, width=8).pack(side="left", padx=(8, 0))
        except Exception:
            tmpmessagebox_val = tk.StringVar(win, value=str(cfg.get("max_backups", "20")))
            ttk.Entry(row1, textvariable=tmpmessagebox_val, width=8).pack(side="left", padx=(8, 0))

        # Max autobackups (separate)
        row2 = ttk.Frame(frm)
        row2.pack(fill="x", pady=(4, 2))
        ttk.Label(row2, text="Max autobackups (0 = unlimited):").pack(side="left")
        try:
            ttk.Entry(row2, textvariable=max_autobackups_var_local, width=8).pack(side="left", padx=(8, 0))
        except Exception:
            tmp_ab_val = tk.StringVar(win, value=str(cfg.get("max_autobackups", "50")))
            ttk.Entry(row2, textvariable=tmp_ab_val, width=8).pack(side="left", padx=(8, 0))

        ttk.Separator(frm, orient="horizontal").pack(fill="x", pady=(12, 8))
        ttk.Label(frm, text="Startup", font=("TkDefaultFont", 11, "bold")).pack(anchor="w", pady=(0, 6))

        startup_normal_cb = ttk.Checkbutton(
            frm,
            text="Start editor with Windows",
            variable=startup_with_windows_var,
            command=_on_startup_normal_toggle,
        )
        startup_normal_cb.pack(anchor="w", pady=(0, 2))

        if not startup_supported:
            startup_normal_cb.configure(state="disabled")
            ttk.Label(
                frm,
                text="Windows startup integration is unavailable on this platform.",
                style="Warning.TLabel",
            ).pack(anchor="w", pady=(2, 6))

        # Buttons
        btn_row = ttk.Frame(frm)
        btn_row.pack(fill="x", pady=(14, 0))

        def _save_and_close():
            # push local popup values back into globals if they exist, and persist to config
            try:
                if 'make_backup_var' in globals() and make_backup_var is not None:
                    make_backup_var.set(_cfg_bool(make_backup_var_local.get()))
            except Exception:
                pass
            try:
                if 'full_backup_var' in globals() and full_backup_var is not None:
                    full_backup_var.set(_cfg_bool(full_backup_var_local.get()))
            except Exception:
                pass
            try:
                if 'max_backups_var' in globals() and max_backups_var is not None:
                    max_backups_var.set(str(max_backups_var_local.get()))
            except Exception:
                pass
            try:
                if 'max_autobackups_var' in globals() and max_autobackups_var is not None:
                    max_autobackups_var.set(str(max_autobackups_var_local.get()))
            except Exception:
                pass
            try:
                if 'autosave_var' in globals() and autosave_var is not None:
                    autosave_var.set(_cfg_bool(autosave_var.get(), default=False))
            except Exception:
                pass

            # Persist to config file as canonical source of truth
            try:
                new_cfg = load_config() or {}
            except Exception:
                new_cfg = {}

            startup_normal = bool(startup_with_windows_var.get())

            try:
                new_cfg["make_backup"] = _cfg_bool(make_backup_var_local.get(), default=True)
                new_cfg["full_backup"] = _cfg_bool(full_backup_var_local.get(), default=False)
                new_cfg["max_backups"] = _parse_nonnegative_int(max_backups_var_local.get(), _parse_nonnegative_int(new_cfg.get("max_backups", 20), 20))
                new_cfg["max_autobackups"] = _parse_nonnegative_int(max_autobackups_var_local.get(), _parse_nonnegative_int(new_cfg.get("max_autobackups", 50), 50))
                new_cfg["autosave"] = _cfg_bool(autosave_var.get(), default=False)
                new_cfg["autosave_backup_on_game_exit"] = _cfg_bool(autosave_backup_on_game_exit_var.get(), default=False)
                new_cfg["autosave_poll_interval_seconds"] = _sanitize_autosave_poll_interval_seconds(
                    autosave_poll_interval_var.get(),
                    default=_sanitize_autosave_poll_interval_seconds(new_cfg.get("autosave_poll_interval_seconds", 60), default=60),
                )
                autosave_poll_interval_var.set(str(new_cfg["autosave_poll_interval_seconds"]))
                new_cfg["start_with_windows"] = bool(startup_normal)
                new_cfg["start_with_windows_hidden"] = False
                if startup_normal:
                    new_cfg.update(_startup_registration_metadata())
                else:
                    new_cfg.pop("start_with_windows_registered_version", None)
                    new_cfg.pop("start_with_windows_registered_target", None)
                    new_cfg.pop("start_with_windows_registered_args", None)
                    new_cfg.pop("start_with_windows_registered_workdir", None)
            except Exception:
                # fallbacks
                new_cfg.setdefault("max_backups", 20)
                new_cfg.setdefault("max_autobackups", 50)
            try:
                save_config(new_cfg)
            except Exception as e:
                print("[Backup Settings] Failed to save config:", e)

            if startup_supported:
                ok, startup_msg = _apply_startup_mode(startup_normal)
                if not ok:
                    print(f"[Startup] apply failed: {startup_msg}")
                    if startup_normal:
                        _delete_config_keys(
                            [
                                "start_with_windows_registered_version",
                                "start_with_windows_registered_target",
                                "start_with_windows_registered_args",
                                "start_with_windows_registered_workdir",
                            ]
                        )
                    set_app_status(f"Backup settings saved. Startup setting could not be applied: {startup_msg}", timeout_ms=9000)
                else:
                    if startup_normal:
                        _update_config_values(_startup_registration_metadata())
                    else:
                        _delete_config_keys(
                            [
                                "start_with_windows_registered_version",
                                "start_with_windows_registered_target",
                                "start_with_windows_registered_args",
                                "start_with_windows_registered_workdir",
                            ]
                        )
                    show_info("Settings", "Backup settings saved.")
            else:
                show_info("Settings", "Backup settings saved.")

            try:
                stop_autosave_monitor()
            except Exception:
                pass
            try:
                _autosave_toggled()
            except Exception:
                pass

            try:
                win.destroy()
            except Exception:
                pass

        def _cancel():
            try:
                win.destroy()
            except Exception:
                pass

        ttk.Button(btn_row, text="Cancel", command=_cancel).pack(side="right", padx=(6,0))
        ttk.Button(btn_row, text="Save", command=_save_and_close).pack(side="right")

        # Ensure monitor state matches checkbox now (no restart needed)
        try:
            _autosave_toggled()
        except Exception:
            pass

        # Keep popup modal until dismissed if possible
        try:
            win.grab_set()
        except Exception:
            pass

    # wire the settings button
    settings_btn.config(command=open_backup_settings)

    # --- top-row buttons ---
    refresh_btn = ttk.Button(top_row, text="Refresh")
    refresh_btn.pack(side="right", padx=(4, 0))

    # Back button removed — navigation is simplified (only folder-level recall supported)
    recall_btn = ttk.Button(top_row, text="Recall Selected", state="disabled")
    recall_btn.pack(side="right", padx=(6, 0))

    make_full_backup_btn = ttk.Button(top_row, text="Make Full Backup")
    make_full_backup_btn.pack(side="right", padx=(6, 0))

    # --- treeview / table with additional columns and matching colours and size ---
    even_bg = STRIPE_B
    odd_bg = STRIPE_A
    empty_bg = "#f0f0f0"

    # Use a plain tk.Frame so the visible background behind the Treeview rows matches exactly
    tree_frame = tk.Frame(container, bg=empty_bg)
    tree_frame.pack(fill="both", expand=True, padx=4, pady=4)

    # Determine the app's default font so Treeview text matches Objectives+ labels.
    # Fall back to a safe tuple if font APIs aren't available in the runtime.
    try:
        import tkinter.font as tkfont
        default_font = tkfont.nametofont("TkDefaultFont")
        fam = default_font.actual().get("family", "TkDefaultFont")
        size = default_font.actual().get("size", 10)
        item_font = (fam, size)
        heading_font = (fam, size, "bold")
    except Exception:
        item_font = ("TkDefaultFont", 10)
        heading_font = ("TkDefaultFont", 10, "bold")

    style = ttk.Style()
    try:
        # Optionally force a theme that respects colours (uncomment to try): style.theme_use('clam')
        style.configure("Backups.Treeview",
                        background=empty_bg,
                        fieldbackground=empty_bg,
                        bordercolor=empty_bg,
                        relief="flat",
                        borderwidth=0,
                        rowheight=30,       # match Objectives+ row height
                        font=item_font)     # MATCH Objectives+ font size
        style.configure("Backups.Treeview.Heading",
                        background=empty_bg,
                        relief="flat",
                        borderwidth=0,
                        font=heading_font)
        # selection appearance (tweak as desired)
        palette = _get_effective_theme()
        style.map("Backups.Treeview",
                  background=[("selected", palette["accent"])],
                  foreground=[("selected", palette["accent_fg"])])
    except Exception:
        # harmless if a theme refuses some options
        pass

    cols = ("name", "time")
    tree = ttk.Treeview(tree_frame, columns=cols, show="headings", style="Backups.Treeview")
    tree.heading("name", text="Name")
    tree.heading("time", text="Saved Time")
    tree.column("name", width=600, anchor="w")
    tree.column("time", width=180, anchor="center")

    vsb = ttk.Scrollbar(tree_frame, orient="vertical", command=tree.yview)
    tree.configure(yscrollcommand=vsb.set)

    # Pack the tree + scrollbar inside the plain frame so the surrounding background matches even_bg
    tree.pack(side="left", fill="both", expand=True)
    vsb.pack(side="right", fill="y")

    # Configure alternating row colours using tags (exact hexes used)
    try:
        tree.tag_configure("even", background=even_bg, font=item_font)
        tree.tag_configure("odd", background=odd_bg, font=item_font)
        tree.tag_configure("filler", background=empty_bg, font=item_font)
    except Exception:
        # some ttk themes ignore tag styling — that's harmless; rows will still show something
        pass



    # state dict removed — UI operates in folder-only mode

    def _get_backup_dir():
        path = save_path_var.get() if save_path_var is not None else ""
        if not path:
            return None
        save_dir = os.path.dirname(path)
        backup_dir = os.path.join(save_dir, "backup")
        return backup_dir

    def _add_backups_filler_rows(real_count: int):
        """Paint remaining visible area with forced #f0f0f0 rows (theme fallback)."""
        try:
            row_h = 30
            view_h = int(tree.winfo_height() or 0)
            visible_rows = max(0, int(view_h / row_h) + 1)
            filler_needed = max(0, visible_rows - int(real_count))
            for i in range(filler_needed):
                tree.insert(
                    "",
                    "end",
                    iid=f"filler_{i}",
                    values=("", ""),
                    tags=("filler",),
                )
        except Exception:
            pass

    def _refresh_backups_filler_only():
        try:
            children = list(tree.get_children())
        except Exception:
            return
        real_ids = [iid for iid in children if not str(iid).startswith("filler_")]
        for iid in children:
            if str(iid).startswith("filler_"):
                try:
                    tree.delete(iid)
                except Exception:
                    pass
        _add_backups_filler_rows(len(real_ids))

    def list_backup_folders():
        """Populate the backups treeview with folders from the backup directory.
        Rows get alternating 'even'/'odd' tags so the Treeview can display two-tone rows.
        """
        # clear existing rows
        tree.delete(*tree.get_children())

        backup_dir = _get_backup_dir()
        if not backup_dir or not os.path.exists(backup_dir):
            tree.insert("", "end", values=("No backups found (set save path or create backups first)", ""))
            _add_backups_filler_rows(1)
            recall_btn.config(state="disabled")
            return

        try:
            items = sorted(os.listdir(backup_dir), reverse=True)
            if not items:
                tree.insert("", "end", values=("No backups found", ""))
                _add_backups_filler_rows(1)
                recall_btn.config(state="disabled")
                return

            # Ensure alternating-row tags exist (some themes may ignore these but it's harmless)
            odd_bg = STRIPE_A
            even_bg = STRIPE_B
            try:
                tree.tag_configure("odd", background=odd_bg)
                tree.tag_configure("even", background=even_bg)
            except Exception:
                # some ttk themes or environments may not allow tag styling — ignore safely
                pass

            real_count = 0
            for idx, name in enumerate(items):
                p = os.path.join(backup_dir, name)
                label = name + ("/" if os.path.isdir(p) else "")

                # Try to extract saved time from folder name (backup-DD.MM.YYYY HH-MM-SS)
                time_str = ""
                m = re.match(r'^(?:backup|autobackup)-(\d{2}\.\d{2}\.\d{4}) (\d{2}-\d{2}-\d{2})', name)
                if m:
                    try:
                        dt = datetime.strptime(f"{m.group(1)} {m.group(2)}", "%d.%m.%Y %H-%M-%S")
                        time_str = dt.strftime("%d.%m.%Y %H:%M:%S")
                    except Exception:
                        time_str = ""

                # Fallback to filesystem mtime if parsing failed
                if not time_str:
                    try:
                        mtime = os.path.getmtime(p)
                        time_str = datetime.fromtimestamp(mtime).strftime("%d.%m.%Y %H:%M:%S")
                    except Exception:
                        time_str = "Failed to get time"

                tag = "even" if (idx % 2 == 0) else "odd"
                tree.insert("", "end", values=(label, time_str), tags=(tag,))
                real_count += 1

            _add_backups_filler_rows(real_count)

            # operate in folder-only mode; ensure recall disabled until selection
            recall_btn.config(state="disabled")

        except Exception as e:
            tree.insert("", "end", values=(f"Error listing backups: {e}", ""))
            _add_backups_filler_rows(1)
            recall_btn.config(state="disabled")



    # list_files_in_backup removed: per-file recall and folder drilling disabled

    def _selected_item():
        sel = tree.selection()
        if not sel:
            return None
        iid = sel[0]
        if str(iid).startswith("filler_"):
            return None
        vals = tree.item(sel[0], "values")
        if not vals:
            return None
        first = str(vals[0] or "")
        if (not first.strip()) or first.startswith("No backups found") or first.startswith("Error listing backups:"):
            return None
        return vals[0]  # relname or folder label

    def on_tree_double_click(event):
        # Double-click disabled: do nothing to avoid drilling into backup folders.
        return

    def on_tree_select(event):
        sel = tree.selection()
        if not sel:
            recall_btn.config(state="disabled")
            return
        iid = sel[0]
        if str(iid).startswith("filler_"):
            recall_btn.config(state="disabled")
            return
        vals = tree.item(sel[0], "values")
        if not vals:
            recall_btn.config(state="disabled")
            return
        first = str(vals[0] or "")
        if (not first.strip()) or first.startswith("No backups found") or first.startswith("Error listing backups:"):
            recall_btn.config(state="disabled")
            return
        # Only folder-level rows are shown; enable recall when an item is selected
        recall_btn.config(state="normal")

    def on_refresh():
        # Always show folder-level listing; disable drilling into backup folders.
        list_backup_folders()

    def on_make_full_backup():
        path = str(save_path_var.get() if save_path_var is not None else "").strip()
        if not path or not os.path.exists(path):
            messagebox.showerror("Backup", "Save file not found. Select a valid save file first.")
            return
        try:
            make_backup_if_enabled(path, force_full=True)
            list_backup_folders()
        except Exception as e:
            messagebox.showerror("Backup", f"Failed to create full backup:\n{e}")

    def on_recall_selected():
        """
        If in folders mode: restore the entire selected backup folder into save folder.
        If in files mode: restore the selected CompleteSave file + matching companions (existing logic).
        """
        sel = _selected_item()
        if not sel:
            show_info("Recall", "No item selected.")
            return

        backup_dir = _get_backup_dir()
        if not backup_dir:
            messagebox.showerror("Recall", "Save folder/backup folder not found.")
            return

        # Restore the entire selected backup folder
        folder_label = sel
        folder_name = folder_label.rstrip("/")
        chosen = os.path.join(backup_dir, folder_name)
        if not os.path.exists(chosen):
            messagebox.showerror("Recall", f"Backup folder not found: {folder_name}")
            return
        if not messagebox.askyesno("Recall full backup", f"Restore entire backup '{folder_name}' to the save folder? This will overwrite files. Continue?"):
            return
        save_dir = os.path.dirname(save_path_var.get()) if save_path_var is not None else None
        if not save_dir or not os.path.isdir(save_dir):
            return messagebox.showerror("Recall", "Save folder not set or invalid.")
        copied = 0
        for root, _, files in os.walk(chosen):
            for f in files:
                src = os.path.join(root, f)
                rel = os.path.relpath(src, chosen)
                dst = os.path.join(save_dir, rel)
                try:
                    os.makedirs(os.path.dirname(dst), exist_ok=True)
                    shutil.copy2(src, dst)
                    copied += 1
                except Exception as e:
                    print(f"[Recall full] failed {src} -> {dst}: {e}")
                    continue
        show_info("Recall", f"Recalled {copied} files from backup '{folder_name}'.")
        # refresh listing
        list_backup_folders()

    _backups_resize_job = {"id": None}
    def _schedule_backups_resize_refresh(_event=None):
        try:
            if _backups_resize_job.get("id") is not None:
                tree.after_cancel(_backups_resize_job["id"])
        except Exception:
            pass
        try:
            _backups_resize_job["id"] = tree.after(
                70,
                lambda: (_backups_resize_job.__setitem__("id", None), _refresh_backups_filler_only()),
            )
        except Exception:
            _refresh_backups_filler_only()

    # Bindings
    tree.bind("<Double-1>", on_tree_double_click)
    tree.bind("<<TreeviewSelect>>", on_tree_select)
    tree.bind("<Configure>", _schedule_backups_resize_refresh)
    refresh_btn.config(command=on_refresh)
    make_full_backup_btn.config(command=on_make_full_backup)
    # back_btn removed — no command to bind
    recall_btn.config(command=on_recall_selected)

    # initial populate
    list_backup_folders()
    
# ───────────────────────────────────    
    # --- Attach auto-refresh to save_path_var AFTER tree exists (works on new and old tkinter) ---
    def _on_save_path_change(*_args):
        try:
            # clear current rows then re-list (list_backup_folders will repopulate)
            try:
                # defensive: ensure `tree` still exists
                for iid in tree.get_children():
                    tree.delete(iid)
            except Exception:
                pass
            list_backup_folders()
        except Exception:
            # swallow to avoid trace crashes
            pass

    try:
        # remove any previous traces to avoid duplication (best-effort)
        _remove_var_traces(save_path_var)
    except Exception:
        pass

    try:
        # modern tkinter
        save_path_var.trace_add("write", _on_save_path_change)
    except Exception:
        try:
            # fallback for older tkinter
            save_path_var.trace("w", _on_save_path_change)
        except Exception:
            pass
    # --- end auto-refresh wiring ---

# ───────────────────────────────────

# TAB: Objectives+ (launch_gui -> tab_objectives)
def create_objectives_tab(tab, save_path_var):
    """
    Mounts the VirtualObjectivesFast into the provided `tab`.
    Must be called after host has set AppID and prepared main Tk root.
    """
    try:
        v = VirtualObjectivesFast(tab, save_path_var)

        try:
            v.build_ui()
        except Exception as e:
            try:
                messagebox.showwarning("Objectives+ error", f"build_ui() failed:\n{e}")
            except Exception:
                pass

        try:
            if hasattr(v, "frame") and not v.frame.winfo_ismapped():
                v.frame.pack(fill="both", expand=True)
        except Exception:
            pass

        try:
            # Quick load from cached/bundled CSV first (no blocking build)
            v.load_data_thread(allow_build=False, preserve_changes=False, keep_existing_items=False, show_loading=True)
            try:
                if _get_objectives_safe_fallback_mode():
                    v._set_status_temp("Safe fallback enabled — using GitHub data", 3500)
            except Exception:
                pass
            prefetch_state = _objectives_prefetch_snapshot()

            if prefetch_state.get("inflight"):
                try:
                    v._set_status_temp("Background refresh already running...", 2500)
                except Exception:
                    pass

                # If user opens Objectives+ while startup refresh is still running,
                # reload once the background worker finishes so newest cache appears.
                def _wait_for_prefetch_then_reload(remaining=120):
                    try:
                        st = _objectives_prefetch_snapshot()
                        if st.get("inflight") and remaining > 0:
                            if hasattr(tab, "after"):
                                tab.after(1000, lambda: _wait_for_prefetch_then_reload(remaining - 1))
                            return
                        if st.get("built"):
                            v.load_data_thread(allow_build=False, preserve_changes=True, keep_existing_items=True, show_loading=False)
                            try:
                                v._set_status_temp("Updated to latest data", 2000)
                            except Exception:
                                pass
                        else:
                            # Background refresh ended without fresh data: try regular tab refresh path.
                            v.refresh_data_async()
                    except Exception:
                        pass

                try:
                    if hasattr(tab, "after"):
                        tab.after(1000, _wait_for_prefetch_then_reload)
                except Exception:
                    pass
            elif prefetch_state.get("completed") and prefetch_state.get("built"):
                try:
                    v._set_status_temp("Using latest startup-cached data", 2000)
                except Exception:
                    pass
            else:
                # Kick off background refresh to fetch newer data
                v.refresh_data_async()
        except Exception as e:
            try:
                messagebox.showwarning("Objectives+ loader error", f"Failed to start data loader:\n{e}")
            except Exception:
                pass

    except Exception as e:
        # Fallback placeholder (created lazily here to avoid GUI imports at module import time)
        try:
            top = ttk.Frame(tab)
            top.pack(fill='x', padx=6, pady=6)
            parquet_var = tk.StringVar(value="")
            ttk.Label(top, text="Parquet file:").pack(side='left')
            ttk.Entry(top, textvariable=parquet_var, width=60).pack(side='left', padx=(6,4))
            def pick_parquet():
                p = filedialog.askopenfilename(filetypes=[("Parquet files","*.parquet"),("All","*.*")])
                if p:
                    parquet_var.set(p)
            ttk.Button(top, text="Browse...", command=pick_parquet).pack(side='left', padx=4)

            body = ttk.Frame(tab)
            body.pack(fill='both', expand=True, padx=6, pady=6)
            info = ttk.Label(body, text="Objectives+ — failed to initialize (see console).", wraplength=700, justify='left')
            info.pack(anchor='w', pady=(0,8))
        except Exception:
            # If we can't even import tkinter for the fallback, do nothing (import-safety preserved).
            log(f"Failed to initialize Objectives+ fallback placeholder: {e}")
__all__ = ["VirtualObjectivesFast", "create_objectives_tab", "default_parquet_path", "DEBUG"]

# UI helper: "Check All" for groups of IntVar checkboxes
def _add_check_all_checkbox(tab, all_vars, before_widget=None, label="Check All"):
    guard = {"busy": False}
    check_all_var = tk.IntVar(value=0)

    def set_all():
        if guard["busy"]:
            return
        guard["busy"] = True
        try:
            val = 1 if check_all_var.get() else 0
            for v in all_vars:
                try:
                    v.set(val)
                except Exception:
                    pass
        finally:
            guard["busy"] = False

    def sync_all(*_):
        if guard["busy"]:
            return
        guard["busy"] = True
        try:
            if not all_vars:
                all_on = False
            else:
                all_on = True
                for v in all_vars:
                    try:
                        if not v.get():
                            all_on = False
                            break
                    except Exception:
                        all_on = False
                        break
            check_all_var.set(1 if all_on else 0)
        finally:
            guard["busy"] = False

    cb = ttk.Checkbutton(tab, text=label, variable=check_all_var, command=set_all)
    pack_kwargs = {"anchor": "center", "pady": (5, 0)}
    if before_widget is not None:
        pack_kwargs["before"] = before_widget
    cb.pack(**pack_kwargs)

    for v in all_vars:
        try:
            v.trace_add("write", sync_all)
        except Exception:
            try:
                v.trace("w", sync_all)
            except Exception:
                pass

    # Ensure initial state matches current selections
    sync_all()
    return check_all_var

# UI helper: shared season/base-map selector used by multiple tabs
def _build_region_selector(
    tab,
    seasons,
    base_maps,
    other_var=None,
    other_label="Other Season number (e.g. 18, 19, 20)",
    base_maps_label="Base Maps:",
    base_maps_label_font=None,
    season_pady=(0, 10),
    base_maps_label_pady=(5, 0),
):
    season_vars = []
    map_vars = []
    all_check_vars = []

    if other_var is None:
        other_var = tk.StringVar()

    season_frame = ttk.Frame(tab)
    season_frame.pack(pady=season_pady)

    left_column = ttk.Frame(season_frame)
    left_column.pack(side="left", padx=10, anchor="n")

    right_column = ttk.Frame(season_frame)
    right_column.pack(side="left", padx=10, anchor="n")

    for idx, (label, value) in enumerate(seasons, start=1):
        var = tk.IntVar()
        column = left_column if idx <= len(seasons) / 2 else right_column
        cb = ttk.Checkbutton(column, text=label, variable=var)
        cb.pack(anchor="w", pady=2)
        season_vars.append((value, var))
        all_check_vars.append(var)

    ttk.Label(tab, text=other_label).pack(pady=5)
    ttk.Entry(tab, textvariable=other_var).pack(pady=5)

    if base_maps_label_font is not None:
        ttk.Label(tab, text=base_maps_label, font=base_maps_label_font).pack(pady=base_maps_label_pady)
    else:
        ttk.Label(tab, text=base_maps_label).pack(pady=base_maps_label_pady)

    map_frame = ttk.Frame(tab)
    map_frame.pack(anchor="center", pady=5)

    for label, value in base_maps:
        var = tk.IntVar()
        cb = ttk.Checkbutton(map_frame, text=label, variable=var)
        cb.pack(anchor="w")
        map_vars.append((value, var))
        all_check_vars.append(var)

    return {
        "season_vars": season_vars,
        "map_vars": map_vars,
        "all_check_vars": all_check_vars,
        "other_var": other_var,
        "season_frame": season_frame,
        "map_frame": map_frame,
    }

def _collect_checked_values(pairs):
    return [value for value, var in pairs if bool(var.get())]

def _append_other_season_int(selected, other_var):
    try:
        if other_var is not None and other_var.get().isdigit():
            selected.append(int(other_var.get()))
    except Exception:
        pass

def _append_other_region_code(selected, other_var):
    try:
        if other_var is not None and other_var.get().isdigit():
            selected.append(f"US_{int(other_var.get()):02}")
    except Exception:
        pass

def _collect_selected_regions(season_vars, map_vars, other_var=None):
    selected = _collect_checked_values(season_vars)
    selected += _collect_checked_values(map_vars)
    _append_other_region_code(selected, other_var)
    return selected

def _load_common_ssl_path_from_config():
    try:
        cfg = load_config()
        return cfg.get("common_ssl_path", "") if isinstance(cfg, dict) else ""
    except Exception:
        return ""

def _save_common_ssl_path_to_config(path):
    try:
        cfg = load_config() or {}
        cfg["common_ssl_path"] = path
        save_config(cfg)
    except Exception:
        pass

def _find_common_ssl_save_in_folder(folder, allow_json=True):
    if not folder or not os.path.isdir(folder):
        return None
    exts = (".cfg", ".dat", ".json") if allow_json else (".cfg", ".dat")
    # prefer exact commonsslsave filenames
    preferred = ("commonsslsave.cfg", "commonsslsave.dat", "common_ssl_save.cfg", "common_ssl_save.dat")
    candidates = []
    try:
        for fname in os.listdir(folder):
            low = fname.lower()
            if low in preferred:
                candidates.append(os.path.join(folder, fname))
        if not candidates:
            for fname in os.listdir(folder):
                low = fname.lower()
                if "common" in low and "ssl" in low and low.endswith(exts):
                    candidates.append(os.path.join(folder, fname))
    except Exception:
        return None
    return candidates[0] if candidates else None

def _pick_common_ssl_file(save_path_var, allow_json=True):
    startdir = os.path.dirname(save_path_var.get()) if save_path_var.get() else os.getcwd()
    if allow_json:
        filetypes = [("CommonSslSave", "*.cfg *.dat *.json"), ("All files", "*.*")]
    else:
        filetypes = [("CommonSslSave", "*.cfg *.dat"), ("All files", "*.*")]
    return filedialog.askopenfilename(initialdir=startdir, filetypes=filetypes)

def _sync_common_ssl_from_save(main_save_path, target_var, on_load, allow_json=True):
    try:
        if not main_save_path or not os.path.exists(main_save_path):
            return False
        folder = os.path.dirname(main_save_path)
        chosen = _find_common_ssl_save_in_folder(folder, allow_json=allow_json)
        if chosen:
            target_var.set(chosen)
            try:
                on_load(chosen)
            except Exception:
                pass
            _save_common_ssl_path_to_config(chosen)
            return True
    except Exception:
        pass
    return False

def _trace_var_write(var, callback):
    try:
        var.trace_add("write", lambda *a: callback())
    except Exception:
        try:
            var.trace("w", lambda *a: callback())
        except Exception:
            pass

# TAB: Contests (launch_gui -> tab_contests)
def create_contest_tab(tab, save_path_var):

    seasons = [(name, i) for i, name in enumerate(SEASON_LABELS, start=1)]
    maps = [(name, code) for code, name in BASE_MAPS]
    selector = _build_region_selector(tab, seasons, maps, season_pady=5)
    season_vars = selector["season_vars"]
    map_vars = selector["map_vars"]
    all_check_vars = selector["all_check_vars"]
    other_season_var = selector["other_var"]

    def on_click():
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")
        selected_seasons = _collect_checked_values(season_vars)
        _append_other_season_int(selected_seasons, other_season_var)
        selected_maps = _collect_checked_values(map_vars)
        if not selected_seasons and not selected_maps:
            return show_info("Info", "No seasons or maps selected.")
        mark_discovered_contests_complete(path, selected_seasons, selected_maps)

    ttk.Button(tab, text="Mark Contests Complete", command=on_click).pack(pady=10)
    _add_check_all_checkbox(tab, all_check_vars)

    ttk.Label(
        tab,
        text="You must accepted (discovered) the contests for them to be marked as completed.",
        style="Warning.TLabel",
        font=("TkDefaultFont", 9, "bold"),
        wraplength=400,
        justify="center"
    ).pack(pady=(5, 10))

    ttk.Label(
        tab,
        text="also completes all unfinished tasks found on the map",
        style="Warning.TLabel",
        font=("TkDefaultFont", 9, "bold"),
        wraplength=400,
        justify="center"
    ).pack(pady=(5, 10))
# Helper for Upgrades tab actions (launch_gui -> tab_upgrades)
def find_and_modify_upgrades(save_path, selected_region_codes):
    make_backup_if_enabled(save_path)
    try:
        with open(save_path, "r", encoding="utf-8") as f:
            content = f.read()

        match = re.search(r'"upgradesGiverData"\s*:\s*{', content)
        if not match:
            messagebox.showerror("Error", "No upgradesGiverData found in file.")
            return

        start_index = match.end() - 1
        block, block_start, block_end = extract_brace_block(content, start_index)
        upgrades_data = json.loads(block)
        added = _ensure_upgrades_defaults(upgrades_data)
        updated = 0

        for map_key, upgrades in upgrades_data.items():
            if not isinstance(upgrades, dict):
                continue
            for code in selected_region_codes:
                if f"level_{code.lower()}" in map_key.lower():
                    for upgrade_key, value in upgrades.items():
                        if value in (0, 1):
                            upgrades[upgrade_key] = 2
                            updated += 1
                    break

        new_block = json.dumps(upgrades_data, separators=(",", ":"))
        content = content[:block_start] + new_block + content[block_end:]

        with open(save_path, "w", encoding="utf-8") as f:
            f.write(content)

        msg = f"Updated {updated} upgrades."
        if added:
            msg += f" Added {added} missing entries."
        show_info("Success", msg)
    except Exception as e:
        messagebox.showerror("Error", str(e))
        
ACHIEVEMENT_NAMES = {
    "YouCanDrive_CompleteTutorial": "Yeah, you can drive!",
    "GetOverHere_Winch": "Get Over Here",
    "StepLightly_10Rec": "Tread Softly (Step Lightly)",
    "UncleScrooge_100000money": "Uncle Scrooge",
    "TheBlueHall_WaterDrive": "The Blue Hall",
    "Gallo24_AddonsPrice": "Gallo 24",
    "PlayYourWay_2000Dmg": "Play Your Way",
    "Untouch_TaskConWithoutDmg": "Untouchable",
    "DeerHunt_FindAllUpgMichig": "Deer Hunt",
    "BeringStraight_StateTruckInGarAlaska": "Bering Strait",
    "ThroughBlood_ManualLoad": "Through Blood & Sweat",
    "18Wheels_OwnAzov4220Antarctic": "18 Wheels is Not Enough",
    "Simply_DeliverEveryTypeCargo": "Simply Delivered",
    "Garages_ExploreAll": "All Starts From a Garage",
    "DreamsCT_RepairAllPipes": "Dreams Come True",
    "TheBlackShuck_TruckDistance": "The Black Shuck",
    "EatSlDR_DeliverOilRigToDrill": "Eat, Sleep, Drill, Repeat",
    "WatchPoints_ExploreAll": "All Along the Watchtower",
    "BrokenHorse_BrokenWheels": "Broken Horse",
    "TheDuel_GetLessDmgOnRedScout": "The Duel",
    "Moosehunt_FindAllUpgAlaska": "Moose Hunt",
    "WhyProblem_PullVehicleOutWater": "Problem Solved",
    "BearHunt_FindAllUpgTaymir": "Bear Hunt",
    "FrontierElite_CompleteAllContracts": "Workaholic",
    "Pedal_TravelFromOneGate": "Pedal to the Metal",
    "WorkersUnite_VisitZone": "Workers Unite",
    "WhatsAMile_MAZ500": "What's a mile?",
    "MasterFuel_TravelReg1tank": "Fuel Economy",
    "Goliath_RaiseTrailerWithCrane": "Goliath",
    "WhereAreLogs_VisitEvLogAr": "Where are the logs?",
    "Convoy_BrokenEngine": "Convoy",
    "WesternWind_PacP12": "Western Wind",
    "MoreThanTwo_AllUsTrucks": "Stars and Stripes",
    "AintNoRest_CompleteAllTaskCont": "Ain't no rest for the...trucker?",
    "VictoryParade_AllRuTrucks": "Victory Parade",
    "Farmer_SmashPumpkins": "Once a Farmer, always a Farmer",
    "ModelCollector_AllTrucks": "Model Collector",
    "OneWithTruck_ComplAllAchiev": "One With The Truck",
}
# ---------------- Exact completed blocks mapping ----------------
# When a checkbox is checked, we will write the corresponding dictionary below (exact fields).
PRESET_COMPLETED_BLOCKS = {
    "YouCanDrive_CompleteTutorial": {
        "$type": "IntAchievementState",
        "currentValue": 1,
        "isUnlocked": True
    },
    "GetOverHere_Winch": {
        "$type": "PlatformtIntAchievementState",
        "isUnlocked": True,
        "commonValue": 6,
        "psValue": 6,
        "psIsUnlocked": False
    },
    "StepLightly_10Rec": {
        "$type": "PlatformtIntAchievementState",
        "isUnlocked": True,
        "commonValue": 10,
        "psValue": 10,
        "psIsUnlocked": False
    },
    "UncleScrooge_100000money": {
        "$type": "PlatformtIntAchievementState",
        "isUnlocked": True,
        "commonValue": 136150,
        "psValue": 136150,
        "psIsUnlocked": False
    },
    "TheBlueHall_WaterDrive": {
        "$type": "PlatformtIntAchievementState",
        "isUnlocked": True,
        "commonValue": 1000,
        "psValue": 1000,
        "psIsUnlocked": False
    },
    "Gallo24_AddonsPrice": {
        "$type": "UpgradeAchievementState",
        "upgrades": {
            "pacific_p12w": 0,
            "chevy_apache": 11800,
            "jeep_wrangler": -3500,
            "frogc8crawl/362792": 0,
            "z2_cat993k/2592837": 88600,
            "jeep_cj7_renegade": 27300,
            "racecar_181/1945834": 165700,
            "tatra_t813": 7500,
            "frogc8mud/362792": 0,
            "krs_58_bandit": 3600,
            "zikz_612h_mastodont": 44300,
            "yar_87": 13200,
            "zikz_612h_se_mastodon/3057044": 131200,
            "frogc8/362792": 0,
            "inchworm_7850/1700168": 67400,
            "rezvani_hercules_6x6": 22100,
            "ws_6900xd_twin": 6700
        },
        "currentValue": 1,
        "isUnlocked": True
    },
    "PlayYourWay_2000Dmg": {
        "$type": "PlatformtIntAchievementState",
        "isUnlocked": True,
        "commonValue": 2064,
        "psValue": 2064,
        "psIsUnlocked": False
    },
    "Untouch_TaskConWithoutDmg": {
        "psValuesArray": [],
        "$type": "PlatformIntWithStringArrayAchievementState",
        "isUnlocked": True,
        "commonValue": 10,
        "psValue": 10,
        "commonValuesArray": [],
        "psIsUnlocked": False
    },
    "DeerHunt_FindAllUpgMichig": {
        "$type": "IntWithStringArrayAchievementState",
        "currentValue": 21,
        "isUnlocked": True,
        "valuesArray": [
            "chevrolet_ck1500_suspension_high","international_fleetstar_f2070a_transferbox_allwheels","g_scout_offroad",
            "us_truck_old_engine_1","gmc9500_suspension_high","fleetstar_f2070a_suspension_high","us_scout_old_engine_ck1500",
            "us_scout_old_engine_1","us_truck_old_engine_4070","white_ws4964_suspension_high","chevrolet_ck1500_diff_lock",
            "gmc_9500_diff_lock","ws_4964_white_transferbox_allwheels","g_scout_highway","international_scout_800_suspension_high",
            "us_scout_old_engine_2","chevrolet_kodiakC70_suspension_high","ws_4964_white_diff_lock","us_truck_old_engine_clt",
            "g_truck_offroad","us_truck_old_heavy_engine_1"
        ]
    },
    "BeringStraight_StateTruckInGarAlaska": {
        "$type": "PlatformtIntAchievementState",
        "isUnlocked": True,
        "commonValue": 1,
        "psValue": 1,
        "psIsUnlocked": False
    },
    "ThroughBlood_ManualLoad": {
        "$type": "PlatformtIntAchievementState",
        "isUnlocked": True,
        "commonValue": 4,
        "psValue": 4,
        "psIsUnlocked": False
    },
    "18Wheels_OwnAzov4220Antarctic": {
        "$type": "IntAchievementState",
        "currentValue": 1,
        "isUnlocked": True
    },
    "Simply_DeliverEveryTypeCargo": {
        "psValuesArray": [
            "CargoMetalPlanks","CargoWoodenPlanks","CargoBricks","CargoConcreteBlocks","CargoServiceSpareParts",
            "CargoBigDrill","CargoServiceSparePartsSpecial","CargoVehiclesSpareParts","CargoCrateLarge","CargoConcreteSlab",
            "CargoBarrels","CargoContainerLargeDrilling","CargoBags","CargoBarrelsOil","CargoContainerSmall","CargoPipesSmall"
        ],
        "$type": "PlatformIntWithStringArrayAchievementState",
        "isUnlocked": True,
        "commonValue": 21,
        "psValue": 16,
        "commonValuesArray": [
            "CargoMetalPlanks","CargoWoodenPlanks","CargoBricks","CargoConcreteBlocks","CargoServiceSpareParts",
            "CargoBigDrill","CargoServiceSparePartsSpecial","CargoVehiclesSpareParts","CargoCrateLarge","CargoConcreteSlab",
            "CargoBarrels","CargoContainerLargeDrilling","CargoBags","CargoBarrelsOil","CargoContainerSmall","CargoPipesSmall",
            "CargoContainerLarge","CargoPipesMedium","CargoPipeLarge","CargoRadioactive","CargoContainerSmallSpecial"
        ],
        "psIsUnlocked": False
    },
    "Garages_ExploreAll": {
        "$type": "IntWithStringArrayAchievementState",
        "currentValue": 6,
        "isUnlocked": True,
        "valuesArray": [
            "level_us_01_01 || US_01_01_GARAGE_ENTRANCE","level_us_02_01 || US_02_01_GARAGE_ENTRANCE",
            "level_us_01_02 || GARAGE_ENTRANCE_0","level_ru_02_02 || RU_02_02_GARAGE_ENTRANCE",
            "level_us_02_03_new || US_02_03_GARAGE_ENTRANCE","level_ru_02_03 || RU_02_03_GARAGE_ENTRANCE"
        ]
    },
    "DreamsCT_RepairAllPipes": {
        "$type": "IntWithStringArrayAchievementState",
        "currentValue": 4,
        "isUnlocked": True,
        "valuesArray": ["US_02_01_PIPELINE_OBJ","US_02_04_PIPELINE_BUILDING_CNT","US_02_02_PIPELINE_OBJ","US_02_03_PIPELINE_OBJ"]
    },
    "TheBlackShuck_TruckDistance": {
        "$type": "PlatformtIntAchievementState",
        "isUnlocked": True,
        "commonValue": 1000006,
        "psValue": 621377,
        "psIsUnlocked": False
    },
    "EatSlDR_DeliverOilRigToDrill": {
        "$type": "IntWithStringArrayAchievementState",
        "currentValue": 3,
        "isUnlocked": True,
        "valuesArray": ["US_02_01_DISASS_OBJ","US_02_02_DISASS_OBJ","US_02_03_DISASS_OBJ"]
    },
    "WatchPoints_ExploreAll": {
        "$type": "IntWithStringArrayAchievementState",
        "currentValue": 54,
        "isUnlocked": True,
        "valuesArray": [
            "level_us_01_01_US_01_01_W9","level_us_01_01_US_01_01_W3","level_us_01_01_US_01_01_W6","level_us_01_01_US_01_01_W7",
            "level_us_01_01_US_01_01_W1","level_us_01_01_US_01_01_W8","level_us_01_01_US_01_01_W5","level_us_01_01_US_01_01_W4",
            "level_us_01_02_US_01_02_W4","level_us_01_02_US_01_02_W3","level_us_01_02_US_01_02_W5","level_us_01_02_US_01_02_W7",
            "level_us_01_02_US_01_02_W2","level_us_01_02_US_01_02_W1","level_us_01_03_US_01_03_W1","level_us_01_03_US_01_03_W8",
            "level_us_02_01_US_02_01_WP_04","level_us_02_01_US_02_01_WP_02","level_ru_02_02_RU_02_02_W3","level_us_02_02_new_US_02_02_WP_03",
            "level_us_02_04_new_US_02_04_W4","level_us_02_03_new_US_02_03_WP_03","level_us_01_04_new_US_01_04_W2","level_us_01_03_US_01_03_W3",
            "level_us_01_03_US_01_03_W2","level_us_01_03_US_01_03_W4","level_us_01_03_US_01_03_W6","level_us_01_03_US_01_03_W7",
            "level_us_01_03_US_01_03_W5","level_us_01_04_new_US_01_04_W1","level_us_01_04_new_US_01_04_W4","level_us_01_04_new_US_01_04_W3",
            "level_us_02_01_US_02_01_WP_03","level_us_02_01_US_02_01_WP_01","level_ru_02_03_RU_02_03_WATCHPOINT_2","level_us_02_03_new_US_02_03_WP_02",
            "level_us_02_03_new_US_02_03_WP_01","level_us_02_03_new_US_02_03_WP_05","level_us_02_03_new_US_02_03_WP_04","level_us_02_02_new_US_02_02_WP_02",
            "level_us_02_02_new_US_02_02_WP_01","level_us_02_04_new_US_02_04_W1","level_us_02_04_new_US_02_04_W2","level_us_02_04_new_US_02_04_W3",
            "level_ru_02_02_RU_02_02_W2","level_ru_02_02_RU_02_02_W1","level_ru_02_01_crop_WATCHPOINT_CHURCH_NORTH","level_ru_02_01_crop_WATCHPOINT_HILL_EAST",
            "level_ru_02_01_crop_WATCHPOINT_HILL_SOUTH","level_ru_02_01_crop_WATCHPOINT_SWAMP_EAST","level_ru_02_01_crop_WATCHPOINT_HILL_SOUTHWEST",
            "level_ru_02_01_crop_WATCHPOINT_CLIFFSIDE_WEST","level_ru_02_03_RU_02_03_WATCHPOINT_3","level_ru_02_03_RU_02_03_WATCHPOINT_1"
        ]
    },
    "BrokenHorse_BrokenWheels": {
        "$type": "PlatformtIntAchievementState",
        "isUnlocked": True,
        "commonValue": 1019,
        "psValue": 0,
        "psIsUnlocked": False
    },
    "TheDuel_GetLessDmgOnRedScout": {
        "$type": "PlatformtIntAchievementState",
        "isUnlocked": True,
        "commonValue": 1,
        "psValue": 1,
        "psIsUnlocked": False
    },
    "Moosehunt_FindAllUpgAlaska": {
        "$type": "IntWithStringArrayAchievementState",
        "currentValue": 23,
        "isUnlocked": True,
        "valuesArray": [
            "us_special_engine_1","hummer_h2_suspension_high","cat_ct680_transferbox_allwheels","hummer_h2_diff_lock",
            "us_scout_modern_engine_1","g_truck_highrange","us_truck_old_engine_2","us_special_engine_2","g_special_offroad",
            "ank_mk38_suspension_high","ws_6900xd_twin_suspension_high","international_paystar_5070_suspension_high",
            "us_truck_modern_engine_1","freightliner_m916a1_suspension_high","ford_clt_suspension_high","us_scout_modern_engine_2",
            "freightliner_114sd_suspension_high","freightliner_114sd_transferbox_allwheels","chevrolet_kodiak_c70_transferbox_allwheels",
            "royal_bm17_suspension_high","us_truck_old_heavy_engine_2","us_truck_modern_engine_2","international_loadstar_1700_suspension_high"
        ]
    },
    "WhyProblem_PullVehicleOutWater": {
        "$type": "PlatformtIntAchievementState",
        "isUnlocked": True,
        "commonValue": 1,
        "psValue": 1,
        "psIsUnlocked": False
    },
    "BearHunt_FindAllUpgTaymir": {
        "$type": "IntWithStringArrayAchievementState",
        "currentValue": 21,
        "isUnlocked": True,
        "valuesArray": [
            "ru_truck_modern_engine_1","ru_truck_modern_engine_2","ru_scout_old_engine_2","khan_lo4f_suspension_high",
            "ru_truck_old_heavy_engine_2","ru_special_engine_2","ru_special_engine_1","don_71_suspension_high",
            "ru_scout_old_engine_1","voron_d53233_suspension_high","don_71_suspension_ultimate","ru_truck_old_heavy_engine_1",
            "ru_truck_old_engine_2","tuz_166_suspension_ultimate","tuz_166_suspension_high","voron_grad_suspension_high",
            "zikz_5368_diff_lock","zikz_5368_suspension_high","tayga_6436_suspension_high","ru_scout_modern_engine_2","step_310e_suspension_high"
        ]
    },
    "FrontierElite_CompleteAllContracts": {
        "$type": "IntWithStringArrayAchievementState",
        "currentValue": 65,
        "isUnlocked": True,
        "valuesArray": [
            "US_01_01_EXPLORING_WATCHTOWER_OBJ","US_01_01_EXPLORING_TRUCK_OBJ","US_01_01_BUILD_A_BRIDGE_OBJ","US_01_01_EXPLORE_GARAGE_OBJ",
            "US_01_01_FARM_DELIVERY_OBJ","US_01_01_SUPPLIES_FOR_FARMERS_OBJ","US_01_01_FACTORY_RECOVERY_OBJ","US_01_01_DRILLING_RECOVERY_OBJ",
            "US_01_01_LOST_CONTAINERS_OBJ","US_01_02_RESOURCES_FOR_WINTER_OBJ","US_01_02_FARM_ORDER_OBJ","US_01_01_TOWN_STORAGE_OBJ",
            "US_01_03_POWER_WIRES_1_CONTRACT_OBJ","US_01_03_LUMBER_MILL_REACTIVATION_OBJ","US_01_03_LOST_CARGO_TSK","US_01_03_CARGO_PORT_OBJ",
            "US_01_04_CARGO_DELIVERING_OBJ","US_01_02_MATERIALS_ORDER_OBJ","US_01_02_WORK_FOR_OLD_SWEAT_OBJ","US_01_02_FUEL_ORDER_OBJ",
            "RU_02_02_RESEARCH","RU_02_02_RADAR_TOWER_RECOVERY","US_02_01_PIPELINE_OBJ","US_02_01_BARRELS_OBJ","US_02_01_DISASS_OBJ",
            "US_02_01_POLAR_BASE_OBJ","US_02_01_SPECIAL_DELIVERY_OBJ","US_02_01_DRILL_DELIVERY_OBJ","US_02_01_OIL_DELIVERY_OBJ",
            "US_02_03_TOWN_DELIVERY_OBJ","US_02_03_POLAR_BASE_OBJ","US_02_04_PIPELINE_BUILDING_CNT","US_02_04_SERVICE_HUB_REACTIVATION_CNT",
            "US_02_01_OIL_DELIVERY_02_OBJ","US_02_02_PIPELINE_OBJ","US_02_04_SPECIAL_CARGO_DELIVERYNG_CNT","US_02_02_MILL_DELIVERY_OBJ",
            "US_02_02_DRILLING_PARTS_OBJ","US_02_03_CRATES_OF_CONSUMABLES_OBJ","US_02_03_DRILL_DELIVERY_OBJ","US_02_02_DISASS_OBJ","US_02_03_DISASS_OBJ",
            "US_02_03_SPECIAL_DELIVERY_OBJ","US_02_02_SPECIAL_DELIVERY_OBJ","US_02_03_PIPELINE_OBJ","US_02_03_MAZUT_OBJ","US_02_02_POLAR_BASE_OBJ",
            "US_02_02_VILLAGE_DELIVERY_OBJ","US_02_02_TSTOP_DELIVERY_OBJ","RU_02_02_HUB_RECOVERY","RU_02_02_HUB_RECOVERY_2","RU_02_02_MAZUT_DELIVERY",
            "RU_02_02_WOODEN_PLANKS_DELIVERY","RU_02_02_FARM_SUPPLY","RU_02_02_GORLAG_CLEANING","RU_02_01_PROSPECTING_01_OBJ",
            "RU_02_01_SERVICE_HUB_RECOVERY_01_OBJ","RU_02_01_PROSPECTING_02_OBJ","RU_02_03_GARAGE_AND_WAREHOUSE_RESTORATION_OBJ",
            "RU_02_01_SERVICE_HUB_RECOVERY_02_OBJ","RU_02_03_CONTRACT_SCAN_POINTS_OBJ","RU_02_01_OILRIG_RECOVERY_OBJ","RU_02_03_PIER_RECOVERY_OBJ",
            "RU_02_03_DERRICK_DELIVERY_OBJ","RU_02_03_DRILLING_EQUIPMENT_DELIVERY_OBJ"
        ]
    },
    "Pedal_TravelFromOneGate": {
        "$type": "PlatformtIntAchievementState",
        "isUnlocked": True,
        "commonValue": 1,
        "psValue": 1,
        "psIsUnlocked": False
    },
    "WorkersUnite_VisitZone": {
        "psValuesArray": ["level_ru_02_03 || RU_02_03_LENIN_ZONE","level_ru_02_02 || RU_02_02_STATUE"],
        "$type": "PlatformIntWithStringArrayAchievementState",
        "isUnlocked": True,
        "commonValue": 2,
        "psValue": 2,
        "commonValuesArray": ["level_ru_02_03 || RU_02_03_LENIN_ZONE","level_ru_02_02 || RU_02_02_STATUE"],
        "psIsUnlocked": False
    },
    "WhatsAMile_MAZ500": {
        "$type": "PlatformtIntAchievementState",
        "isUnlocked": True,
        "commonValue": 10,
        "psValue": 10,
        "psIsUnlocked": False
    },
    "MasterFuel_TravelReg1tank": {
        "psValuesArray": ["level_ru_03_01","level_ru_03_02","level_ru_05_01","level_us_11_01","level_ru_08_01","level_us_01_02","level_us_02_01","level_us_02_02_new","level_us_02_04_new","level_us_02_03_new","level_us_01_01","level_us_01_03","level_us_01_04_new","level_ru_02_02","level_ru_02_01_crop","level_ru_02_04","level_ru_02_03"],
        "$type": "PlatformIntWithStringArrayAchievementState",
        "isUnlocked": True,
        "commonValue": 3,
        "psValue": 3,
        "commonValuesArray": ["level_ru_03_01","level_ru_03_02","level_ru_05_01","level_us_11_01","level_ru_08_01","level_us_01_02","level_us_02_01","level_us_02_02_new","level_us_02_04_new","level_us_02_03_new","level_us_01_01","level_us_01_03","level_us_01_04_new","level_ru_02_02","level_ru_02_01_crop","level_ru_02_04","level_ru_02_03"],
        "psIsUnlocked": False
    },
    "Goliath_RaiseTrailerWithCrane": {
        "$type": "PlatformtIntAchievementState",
        "isUnlocked": True,
        "commonValue": 1,
        "psValue": 1,
        "psIsUnlocked": False
    },
    "WhereAreLogs_VisitEvLogAr": {
        "psValuesArray": [
            "level_us_01_01 || US_01_01_LUMBER_MILL","level_us_01_04_new || US_01_04_LOG_LOADING","level_us_01_03 || US_01_03_LUMBER_MILL_UNLOCK",
            "level_us_02_01 || US_02_01_LOG_STATION","level_us_02_01 || US_02_01_LUMBER_MILL","level_us_02_03_new || US_02_03_LOG_STATION_02",
            "level_us_02_03_new || US_02_03_LOG_STATION_01","level_us_02_02_new || US_02_02_MILL","level_us_02_03_new || US_02_03_MILL",
            "level_ru_02_02 || RU_02_02_LUMBER_MILL","level_ru_02_01_crop || RU_02_01_OLD_LUMBERMILL","level_ru_02_03 || RU_02_03_SAWMILL_2_PICKUP"
        ],
        "$type": "PlatformIntWithStringArrayAchievementState",
        "isUnlocked": True,
        "commonValue": 12,
        "psValue": 12,
        "commonValuesArray": [
            "level_us_01_01 || US_01_01_LUMBER_MILL","level_us_01_04_new || US_01_04_LOG_LOADING","level_us_01_03 || US_01_03_LUMBER_MILL_UNLOCK",
            "level_us_02_01 || US_02_01_LOG_STATION","level_us_02_01 || US_02_01_LUMBER_MILL","level_us_02_03_new || US_02_03_LOG_STATION_02",
            "level_us_02_03_new || US_02_03_LOG_STATION_01","level_us_02_02_new || US_02_02_MILL","level_us_02_03_new || US_02_03_MILL",
            "level_ru_02_02 || RU_02_02_LUMBER_MILL","level_ru_02_01_crop || RU_02_01_OLD_LUMBERMILL","level_ru_02_03 || RU_02_03_SAWMILL_2_PICKUP"
        ],
        "psIsUnlocked": False
    },
    "Convoy_BrokenEngine": {
        "$type": "PlatformtIntAchievementState",
        "isUnlocked": True,
        "commonValue": 1,
        "psValue": 1,
        "psIsUnlocked": False
    },
    "WesternWind_PacP12": {
        "$type": "PlatformtIntAchievementState",
        "isUnlocked": True,
        "commonValue": 10,
        "psValue": 0,
        "psIsUnlocked": False
    },
    "MoreThanTwo_AllUsTrucks": {
        "$type": "IntWithStringArrayAchievementState",
        "currentValue": 23,
        "isUnlocked": True,
        "valuesArray": [
            "chevrolet_ck1500","gmc_9500","international_fleetstar_f2070a","chevrolet_kodiakc70","international_scout_800",
            "international_transtar_4070a","pacific_p12w","ws_6900xd_twin","ws_4964_white","international_loadstar_1700",
            "international_paystar_5070","hummer_h2","ank_mk38_ht","pacific_p16","royal_bm17","derry_longhorn_3194","derry_longhorn_4520",
            "cat_745c","ank_mk38","cat_ct680","ford_clt9000","freightliner_114sd","freightliner_m916a1"
        ]
    },
    "AintNoRest_CompleteAllTaskCont": {
        "$type": "IntWithStringArrayAchievementState",
        "currentValue": 150,
        "isUnlocked": True,
        "valuesArray": [
            "US_01_01_KING_OF_HILLS_TSK",
            "US_01_01_DROWNED_TRUCK_02_TSK",
            "US_01_01_WOODEN_BRIDGE_TSK",
            "US_01_01_MOUNTAIN_BRIDGE_TSK",
            "US_01_01_FALLEN_POWER_LINES_TSK",
            "US_01_01_LANDSLIDE_TSK",
            "US_01_01_ROAD_BLOCKAGE_TSK",
            "US_01_01_DROWNED_TRUCK_03_TSK",
            "US_01_01_DROWNED_TRUCK_01_TSK",
            "US_01_01_MISSED_OILTANK_TSK",
            "US_01_01_THE_PLACE_BEYOND_THE_SPRUCES_TSK",
            "US_01_01_MOTEL_NEEDS_TSK",
            "US_01_01_STUCK_TRAILER_TSK",
            "US_01_01_SWAMP_EXPLORATION_TSK",
            "US_01_01_LOCAL_ENTERTAINMENT_TSK",
            "US_01_01_LOST_CARGO_TSK",
            "US_01_01_BOATMAN_TOOLS_DELIVERY_TSK",
            "US_01_02_UNLUCKY_FISHERMAN_TSK",
            "US_01_02_FALLEN_ROCKS_TSK",
            "US_01_02_CLEAR_ROCKS_01_TSK",
            "US_01_02_FOOD_FOR_WORKERS_TSK",
            "US_01_02_RIVER_CROSSING_TSK",
            "US_01_02_WOODEN_BRIDGE_TSK",
            "US_01_02_SOLID_FOUNDATION_TSK",
            "US_01_02_REPAIR_THE_TRUCK_TSK",
            "US_01_02_FIND_THE_ANTENNA_TOWER_TSK",
            "US_01_03_TRUCK_REPAIR",
            "US_01_03_SWAMP_CROSSING_02_TSK",
            "US_01_03_SHORT_CUT_TSK",
            "US_01_03_SWAMP_CROSSING_01_TSK",
            "US_01_03_SWAMP_CROSSING_03_TSK",
            "US_01_04_BUILD_A_BRIDGE_OBJ_1",
            "US_01_04_BUILD_A_BRIDGE_OBJ_2",
            "US_01_04_BUILD_A_BRIDGE_OBJ_3",
            "US_01_02_DRILL_FOR_OUTCAST_TSK",
            "US_01_02_BARRELS_DELIVERY_TSK",
            "US_01_01_WOODEN_ORDER_CNT",
            "US_01_01_FOOD_DELIVERY_CNT",
            "US_01_01_METEO_DATA_CNT",
            "US_01_02_LOST_TRAILER_TSK",
            "US_01_02_LOST_BAGS_TSK",
            "US_01_02_MICHIGAN_TRIAL_TSK",
            "US_01_02_TRUCK_RESTORATION_TSK",
            "US_01_02_CLEAN_THE_RIVER_EAST_TSK",
            "US_01_02_BRICKS_DELIVERY_TSK",
            "US_01_02_CLEAN_THE_RIVER_WEST_TSK",
            "US_01_02_HOUSE_RENOVATION_CNT",
            "US_01_02_FLOODED_HOUSE_CNT",
            "US_02_01_HUMMER_TSK",
            "RU_02_03_TASK_DOCUMENTARY_OBJ",
            "US_02_02_BRIDGE_RECOVERY_TSK",
            "US_02_03_BLOCKED_TUNNEL_TSK",
            "US_01_04_LOST_SHIP_OBJ",
            "US_01_03_DROPPED_VEHICLE_SEARCHING_TSK_02",
            "US_01_03_DROPPED_VEHICLE_SEARCHING_TSK_01",
            "US_01_03_FIND_THE_ANTENNA_TSK",
            "US_01_03_FIX_THE_ANTENNA_TSK",
            "US_01_03_BARREL_CNT",
            "US_01_04_PATH__PASSING_TSK",
            "US_01_04_EXPLORING_CNT",
            "US_01_04_FIND_LOST_TRUCK_TSK",
            "US_01_04_FALLEN_CARGO_TSK",
            "US_01_02_FARMERS_NEEDS_CNT",
            "US_01_04_OBSERVATION_DECK_TSK",
            "US_01_04_LOST_CARGO_DELIVERY_TSK",
            "US_01_03_DROPPED_VEHICLE_SEARCHING_TSK_03",
            "US_02_01_ROCK_TSK",
            "US_02_01_FIX_A_BRIDGE_TSK",
            "US_02_01_STONE_FALL_TSK",
            "US_02_01_LOST_OILTANK_TSK",
            "US_02_01_SERVICE_RETURN_TSK",
            "US_02_01_ABANDONED_SUPPLIES_TSK",
            "US_02_01_OILTANK_DELIVERY_TSK",
            "US_02_01_STUCK_SCOUT_TSK",
            "US_02_01_ROCK_FALL_TSK",
            "US_02_01_TRAILER_PARK_TSK",
            "US_02_01_EMPLOYEE_DISLOCATION_CNT",
            "US_02_01_RADIOSTATION_TSK",
            "US_02_01_POWERLINE_CHECK_TSK",
            "US_02_01_BAGS_ON_ICE_TSK",
            "US_02_01_LOST_TUBE_TSK",
            "US_02_01_MOUNTAIN_CONQUEST_1_CNT",
            "US_02_01_MOUNTAIN_CONQUEST_2_CNT",
            "US_02_01_FLAGS_CNT",
            "US_02_03_FAILED_FISHING_A_TSK",
            "US_02_03_REPAIR_THE_BRIDGE_TSK",
            "US_02_03_DERRY_LONGHORN_TSK",
            "US_02_03_THEFT_OF_FUEL_TSK",
            "US_02_03_OUT_OF_FUEL_TSK",
            "US_02_03_LONG_BRIDGE_RECOVERY_TSK",
            "US_02_03_SCOUT_IN_TROUBLE_TSK",
            "US_02_03_BUILDING_MATERIALS_TSK",
            "US_02_04_MOUNTAIN_CLEANING_TSK",
            "US_02_04_CAR_HELP_TSK",
            "US_02_04_BRIDGE_BUILDING_TSK",
            "US_02_04_BROKEN_POLE_TSK",
            "US_02_02_ENVIRONMENTAL_ISSUE_TSK",
            "US_02_02_WORKING_STIFF_TSK",
            "US_02_02_BRICKS_ON_RIVER_TSK",
            "US_02_03_WEATHER_FORECAST_CNT",
            "US_02_04_FRAGILE_DELIVERY_CNT",
            "US_02_02_SERVICE_CONVOY_TSK",
            "US_02_04_SIDEBOARD_SPAWN_TSK",
            "US_02_04_MATERIAL_DELIVERYING_TSK",
            "US_02_04_LOST_CARGO_TSK",
            "US_02_04_FARMER_HOME_TSK",
            "US_02_02_RIVER_CONTEST_CNT",
            "US_02_02_TO_THE_TOWER_CNT",
            "US_02_01_CANT_GO_TO_WASTE_TSK",
            "US_02_01_CONTAINERS_IN_RIVER_TSK",
            "RU_02_02_DAMAGED_TRUCK_04_TSK",
            "RU_02_02_LOST_CARGO_01_TSK",
            "RU_02_02_LOST_CARGO_04_TSK",
            "RU_02_02_STUCK_TRUCK_05_TSK",
            "RU_02_02_STUCK_TRUCK_02_TSK",
            "RU_02_02_DAMAGED_TRUCK_03_TSK",
            "RU_02_02_LOST_CARGO_05_TSK",
            "RU_02_02_DAMAGED_TRUCK_02_TSK",
            "RU_02_02_DAMAGED_TRUCK_01_TSK",
            "RU_02_02_LOST_CARGO_03_TSK",
            "RU_02_02_LOST_CARGO_02_TSK",
            "RU_02_02_STUCK_TRUCK_03_TSK",
            "RU_02_02_STUCK_TRUCK_TSK",
            "RU_02_02_STUCK_TRUCK_04_TSK",
            "RU_02_03_TASK_FIND_THE_TRUCK_OBJ",
            "RU_02_01_HTRUCK_REFUEL_TSK",
            "RU_02_01_REPAIR_TRUCK_HIGHWAY_TSK",
            "RU_02_01_EXAMINE_EAST_TSK",
            "RU_02_01_TOWER_CLEARING_A_TSK",
            "RU_02_01_OILRIG_SAMPLING_TSK",
            "RU_02_01_FIREWATCH_SUPPLY_CNT",
            "RU_02_03_CONTEST_WOODEN_DELIVEY_WAREHOUSE_OBJ",
            "RU_02_02_FLAG_2_CNT",
            "RU_02_02_BARRELS_DELIVERY_CNT",
            "RU_02_03_TASK_BUILD_BRIDGE_OBJ",
            "RU_02_03_TASK_FIND_THE_CAR_OBJ",
            "RU_02_01_VILLAGE_RESTORATION_TSK",
            "RU_02_03_CONTEST_BARRELS_DELIVERY_OBJ",
            "RU_02_01_SERVHUB_FUEL_RESTOCK_CNT",
            "RU_02_03_CONTEST_WOODEN_DELIVEY_PIRS_OBJ",
            "RU_02_03_SAWMILL_RECOVERY_OBJ",
            "RU_02_02_CONTAINER_DELIVERY_CNT",
            "RU_02_02_FLAG_1_CNT",
            "RU_02_01_EXAMINE_SOUTH_TSK",
            "RU_02_03_TASK_METAL_DELIVERY_OBJ",
            "RU_02_03_TASK_SEARCH_OBJ",
            "RU_02_03_CONTEST_METAL_DELIVERY_OBJ",
            "RU_02_01_REFUEL_TRUCK_SWAMP_TSK",
            "RU_02_01_HERMIT_RESCUE_TSK",
            "RU_02_01_SHIP_REPAIRS_CNT"
        ]
    },
    "VictoryParade_AllRuTrucks": {
        "$type": "IntWithStringArrayAchievementState",
        "currentValue": 18,
        "isUnlocked": True,
        "valuesArray": [
            "yar_87","zikz_5368","khan_lo4f","don_71","azov_64131","voron_d53233","kolob_74941","voron_ae4380","azov_5319",
            "tuz_420_tatarin","azov_73210","azov_4220_antarctic","kolob_74760","tayga_6436","tuz_166","voron_grad","step_310e","dan_96320"
        ]
    },
    "Farmer_SmashPumpkins": {
        "$type": "PlatformtIntAchievementState",
        "isUnlocked": True,
        "commonValue": 500,
        "psValue": 82,
        "psIsUnlocked": False
    },
    "ModelCollector_AllTrucks": {
        "$type": "IntWithStringArrayAchievementState",
        "currentValue": 41,
        "isUnlocked": True,
        "valuesArray": [
            "chevrolet_ck1500","gmc_9500","international_fleetstar_f2070a","chevrolet_kodiakc70","international_scout_800","international_transtar_4070a",
            "yar_87","pacific_p12w","zikz_5368","khan_lo4f","don_71","ws_6900xd_twin","ws_4964_white","international_loadstar_1700","international_paystar_5070",
            "azov_64131","voron_d53233","hummer_h2","kolob_74941","voron_ae4380","ank_mk38_ht","azov_5319","tuz_420_tatarin","pacific_p16","azov_73210","royal_bm17","derry_longhorn_3194","derry_longhorn_4520","azov_4220_antarctic","cat_745c","kolob_74760","ank_mk38","tayga_6436","tuz_166","voron_grad","cat_ct680","ford_clt9000","freightliner_114sd","freightliner_m916a1","step_310e","dan_96320"
        ]
    },
    "OneWithTruck_ComplAllAchiev": {
        "psValuesArray": ["GetOverHere_Winch","YouCanDrive_CompleteTutorial","StepLightly_10Rec","UncleScrooge_100000money","TheBlueHall_WaterDrive","PlayYourWay_2000Dmg","Goliath_RaiseTrailerWithCrane","Gallo24_AddonsPrice","TheDuel_GetLessDmgOnRedScout","WhyProblem_PullVehicleOutWater","Convoy_BrokenEngine","WhatsAMile_MAZ500","Untouch_TaskConWithoutDmg","BeringStraight_StateTruckInGarAlaska","Pedal_TravelFromOneGate","MasterFuel_TravelReg1tank","WorkersUnite_VisitZone","ThroughBlood_ManualLoad"],
        "$type": "PlatformIntWithStringArrayAchievementState",
        "isUnlocked": True,
        "commonValue": 37,
        "psValue": 18,
        "commonValuesArray": ["GetOverHere_Winch","YouCanDrive_CompleteTutorial","StepLightly_10Rec","UncleScrooge_100000money","TheBlueHall_WaterDrive","PlayYourWay_2000Dmg","Goliath_RaiseTrailerWithCrane","Gallo24_AddonsPrice","TheDuel_GetLessDmgOnRedScout","WhyProblem_PullVehicleOutWater","Convoy_BrokenEngine","WhatsAMile_MAZ500","Untouch_TaskConWithoutDmg","BeringStraight_StateTruckInGarAlaska","Pedal_TravelFromOneGate","MasterFuel_TravelReg1tank","WorkersUnite_VisitZone","ThroughBlood_ManualLoad","DeerHunt_FindAllUpgMichig","EatSlDR_DeliverOilRigToDrill","DreamsCT_RepairAllPipes","18Wheels_OwnAzov4220Antarctic","TheBlackShuck_TruckDistance","Moosehunt_FindAllUpgAlaska","WesternWind_PacP12","MoreThanTwo_AllUsTrucks","ModelCollector_AllTrucks","VictoryParade_AllRuTrucks","Garages_ExploreAll","BearHunt_FindAllUpgTaymir","FrontierElite_CompleteAllContracts","AintNoRest_CompleteAllTaskCont","WatchPoints_ExploreAll","BrokenHorse_BrokenWheels","Simply_DeliverEveryTypeCargo","WhereAreLogs_VisitEvLogAr","Farmer_SmashPumpkins"],
        "psIsUnlocked": False
    }
}


# TAB: Achievements (launch_gui -> tab_achievements)
def create_achievements_tab(tab, save_path_var, plugin_loaders):
    """
    Achievements — top-level tab.
    Auto-detects CommonSslSave (if known), auto-loads achievements and shows
    them as checkboxes arranged in 3 centered columns. Only Browse + Save are shown.
    """

    top = ttk.Frame(tab)
    top.pack(fill="x", pady=6, padx=8)
    ttk.Label(top, text="CommonSslSave file:").pack(side="left")
    achievements_path_var = tk.StringVar()
    ttk.Entry(top, textvariable=achievements_path_var, width=70).pack(side="left", padx=6, fill="x", expand=True)

    def pick_file():
        p = _pick_common_ssl_file(save_path_var, allow_json=True)
        if not p:
            return
        achievements_path_var.set(p)
        _save_common_ssl_path_to_config(p)
        load_achievements_from_file(p)

    ttk.Button(top, text="Browse...", command=pick_file).pack(side="left", padx=(4,0))

    hint = ("The editor will try to auto-detect the CommonSslSave (from config or the save folder) and load it automatically. "
            "Use Browse... to select another file.")
    ttk.Label(tab, text=hint, wraplength=1000, justify="left").pack(fill="x", padx=10, pady=(6, 8))
    ttk.Label(
        tab,
        text="Steam achievements will also be unlocked, but they can’t be removed with this editor. It’s meant mainly for the in-game Achievements tab.",
        wraplength=1000,
        justify="left",
        style="Warning.TLabel",
    ).pack(fill="x", padx=10, pady=(6, 8))

    # central area: we'll place a centered frame with a 3-column grid of checkboxes
    body_outer = ttk.Frame(tab)
    body_outer.pack(fill="both", expand=True, padx=10, pady=6)
    center_container = ttk.Frame(body_outer)
    center_container.pack(expand=True)
    grid_frame = ttk.Frame(center_container)
    grid_frame.pack(anchor="center", pady=10)

    # internal containers
    ach_vars = {}   # id -> IntVar
    ach_states = {} # id -> state dict

    def _create_checkboxes(ach_dict):
        # clears previous
        for w in grid_frame.winfo_children():
            w.destroy()
        ach_vars.clear()
        ach_states.clear()

        keys = sorted(ach_dict.keys(), key=lambda k: ACHIEVEMENT_NAMES.get(k, k).lower())
        # layout into 3 columns
        cols = 3
        for idx, key in enumerate(keys):
            st = ach_dict.get(key, {})
            is_unlocked = bool(st.get("isUnlocked")) if isinstance(st, dict) else bool(st)
            var = tk.IntVar(value=1 if is_unlocked else 0)
            display = ACHIEVEMENT_NAMES.get(key, key)
            cb = ttk.Checkbutton(grid_frame, text=display, variable=var)
            r = idx // cols
            c = idx % cols
            cb.grid(row=r, column=c, sticky="w", padx=12, pady=6)
            ach_vars[key] = var
            ach_states[key] = st if isinstance(st, dict) else {"isUnlocked": is_unlocked}

    def load_achievements_from_file(path=None):
        p = path or achievements_path_var.get()
        if not p or not os.path.exists(p):
            return
        try:
            with open(p, "r", encoding="utf-8") as f:
                content = f.read()
            m = re.search(r'"CommonSslSave"\s*:\s*{', content)
            if not m:
                # try directly if this file *is* a CommonSslSave JSON dump
                try:
                    parsed_direct = json.loads(content)
                    ssl_val = parsed_direct.get("SslValue") or parsed_direct
                    ach = ssl_val.get("achievementStates", {})
                    if isinstance(ach, dict):
                        _create_checkboxes(ach)
                        achievements_path_var.set(p)
                        return
                except Exception:
                    pass
                return messagebox.showerror("Error", "CommonSslSave block not found in file.")
            block_str, bs, be = extract_brace_block(content, m.end() - 1)
            parsed = json.loads(block_str)
            ssl_value = parsed.get("SslValue") or parsed
            ach = ssl_value.get("achievementStates", {}) if isinstance(ssl_value, dict) else {}
            if not isinstance(ach, dict):
                ach = {}
            _create_checkboxes(ach)
            achievements_path_var.set(p)
        except Exception as e:
            return messagebox.showerror("Error", f"Failed to load achievements:\n{e}")

    # fallback builder (use module-level if available)
    def build_fallback_for_key_local(key: str, unlocked: bool = True) -> dict:
        try:
            # prefer module-level helper if available
            if "build_fallback_for_key" in globals() and callable(globals().get("build_fallback_for_key")):
                return globals()["build_fallback_for_key"](key, unlocked)
            return {"$type": "IntAchievementState", "isUnlocked": bool(unlocked), "currentValue": 1 if unlocked else 0}
        except Exception:
            return {"isUnlocked": bool(unlocked)}

    # Save function (writes only achievementStates shallow merge; keeps other parts untouched)
    def save_achievements_to_file():
        """
        Save: for each checked achievement, write the exact completed block from PRESET_COMPLETED_BLOCKS.
        For checked keys without a preset, preserve original entry if present or use fallback templates.
        Unchecked achievements are left unchanged.
        """
        p = achievements_path_var.get()
        if not p or not os.path.exists(p):
            return messagebox.showerror("Error", "CommonSslSave file not found.")
        try:
            try:
                make_backup_if_enabled(p)
            except Exception:
                pass

            with open(p, "r", encoding="utf-8") as f:
                content = f.read()

            m = re.search(r'"CommonSslSave"\s*:\s*{', content)
            orig_parsed = None
            orig_ach = {}
            bs = be = None

            if m:
                block_str, bs, be = extract_brace_block(content, m.end() - 1)
                try:
                    orig_parsed = json.loads(block_str)
                except Exception:
                    orig_parsed = None
                if orig_parsed:
                    ssl_val = orig_parsed.get("SslValue") or orig_parsed
                    if isinstance(ssl_val, dict):
                        orig_ach = ssl_val.get("achievementStates", {}) or {}
                    else:
                        orig_ach = {}
            else:
                # attempt direct SslValue JSON
                try:
                    parsed_direct = json.loads(content)
                    ssl_val = parsed_direct.get("SslValue") or parsed_direct
                    orig_ach = (ssl_val.get("achievementStates") if isinstance(ssl_val, dict) else {}) or {}
                    bs = be = None
                    orig_parsed = parsed_direct
                except Exception:
                    return messagebox.showerror("Error", "CommonSslSave block not found; cannot save.")

            # Build new_ach starting from original so unchecked achievements are preserved
            new_ach = dict(orig_ach)

            # iterate UI keys and for those checked, replace with exact completed block if available
            for key, var in ach_vars.items():
                try:
                    checked = bool(var.get())
                except Exception:
                    checked = False
                if not checked:
                    # don't modify if unchecked
                    continue

                # if preset exact completed block exists, use it (ensure isUnlocked true)
                if key in PRESET_COMPLETED_BLOCKS:
                    block = dict(PRESET_COMPLETED_BLOCKS[key])
                    # force isUnlocked True in case preset missed it
                    block["isUnlocked"] = True
                    new_ach[key] = block
                    continue

                # else if original entry exists, toggle its isUnlocked True and keep other fields
                if key in orig_ach and isinstance(orig_ach[key], dict):
                    base = dict(orig_ach[key])
                    base["isUnlocked"] = True
                    new_ach[key] = base
                    continue

                # otherwise, build a fallback shape (use previous heuristics)
                fallback = build_fallback_for_key_local(key, True)
                new_ach[key] = fallback

            # Put new_ach into orig_parsed and write back
            if orig_parsed is None:
                out_block = {"SslType": "CommonSaveObject", "SslValue": {"achievementStates": new_ach}}
                new_block_str = json.dumps(out_block, separators=(",", ":"))
                with open(p, "w", encoding="utf-8") as out_f:
                    out_f.write(new_block_str)
                show_info("Saved", "Achievements saved to file (rewrote file).")
                return

            parsed_to_write = dict(orig_parsed)
            if "SslValue" in parsed_to_write and isinstance(parsed_to_write["SslValue"], dict):
                parsed_to_write["SslValue"]["achievementStates"] = new_ach
            else:
                parsed_to_write["achievementStates"] = new_ach

            new_block_str = json.dumps(parsed_to_write, separators=(",", ":"))
            if bs is not None and be is not None:
                new_content = content[:bs] + new_block_str + content[be:]
                with open(p, "w", encoding="utf-8") as out_f:
                    out_f.write(new_content)
            else:
                with open(p, "w", encoding="utf-8") as out_f:
                    out_f.write(new_block_str)

            try:
                cfg = load_config() or {}
                cfg["common_ssl_path"] = p
                save_config(cfg)
            except Exception:
                pass

            show_info("Saved", "Achievements saved to file.")
        except Exception as e:
            messagebox.showerror("Save error", f"Failed to save achievements:\n{e}")

    # Bottom: Save button (centered)
    bottom = ttk.Frame(tab)
    bottom.pack(fill="x", padx=12, pady=(6,12))
    ttk.Button(bottom, text="Save to file", command=save_achievements_to_file).pack(anchor="center")

    # --- Auto-detect helper (same-folder strategy) for Achievements ---
    def sync_achievements_from_save(main_save_path):
        _sync_common_ssl_from_save(
            main_save_path,
            achievements_path_var,
            load_achievements_from_file,
            allow_json=True
        )

    # register auto-detect with plugin_loaders (if provided) so other parts of the app can also trigger it
    try:
        if isinstance(plugin_loaders, list) and sync_achievements_from_save not in plugin_loaders:
            plugin_loaders.append(sync_achievements_from_save)
    except Exception:
        pass

    # trace main save path so we run detection whenever it changes (like Trials does)
    _trace_var_write(save_path_var, lambda: sync_achievements_from_save(save_path_var.get()))

    # Auto-detect & load on creation (if possible)
    try:
        cp = _load_common_ssl_path_from_config()
        if cp and os.path.exists(cp):
            load_achievements_from_file(cp)
        else:
            _ = sync_achievements_from_save(save_path_var.get()) if save_path_var and save_path_var.get() else None
    except Exception:
        pass

    return


# TAB: PROS (launch_gui -> tab_pros)
def create_pros_tab(tab, save_path_var, plugin_loaders):
    """
    PROS tab — manages givenProsEntitlements in CommonSslSave.
    Auto-detects CommonSslSave in the same folder as the main save.
    """
    PROS_URL = "https://prismray.io/games/snowrunner"
    PROS_ENTITLEMENTS = [
        ("Mammoth Ornament & Stickers", "ProsRegistrationReward"),
        ("An exclusive Voron-AE4380 skin and three unique stickers", "ProsRoadcraftReward"),
    ]

    pros_path_var = tk.StringVar()
    try:
        cp = _load_common_ssl_path_from_config()
        if cp:
            pros_path_var.set(cp)
    except Exception:
        pass

    # --- Top: file picker ---
    top = ttk.Frame(tab)
    top.pack(fill="x", pady=6, padx=8)
    ttk.Label(top, text="CommonSslSave file:").pack(side="left")
    ttk.Entry(top, textvariable=pros_path_var, width=70).pack(side="left", padx=6, fill="x", expand=True)

    def pick_pros_file():
        p = _pick_common_ssl_file(save_path_var, allow_json=True)
        if not p:
            return
        pros_path_var.set(p)
        _save_common_ssl_path_to_config(p)
        load_pros_file(p)

    ttk.Button(top, text="Browse...", command=pick_pros_file).pack(side="left", padx=(4,0))

    # --- PROS explanation ---
    pros_hint = (
        "PROS lets you keep your SnowRunner progress synced across platforms. "
        "For example, you can start on PC and continue on PlayStation. "
        "It also grants some rewards — and you can toggle those rewards here "
        "without linking your account to PROS."
    )
    ttk.Label(tab, text=pros_hint, wraplength=1000, justify="center").pack(fill="x", padx=10, pady=(4, 10))

    # --- PROS link buttons (centered, a bit lower) ---
    link_frame = ttk.Frame(tab)
    link_frame.pack(fill="x", padx=10, pady=(0, 12))
    link_center = ttk.Frame(link_frame)
    link_center.pack(anchor="center")

    def open_pros():
        try:
            webbrowser.open(PROS_URL)
        except Exception as e:
            messagebox.showerror("Error", f"Failed to open browser:\n{e}")

    def copy_link():
        try:
            root = tab.winfo_toplevel()
            root.clipboard_clear()
            root.clipboard_append(PROS_URL)
            root.update()
            show_info("Copied", "PROS link copied to clipboard.")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to copy link:\n{e}")

    ttk.Button(link_center, text="Open PROS", command=open_pros).pack(side="left", padx=(0, 10))
    ttk.Button(link_center, text="Copy Link", command=copy_link).pack(side="left")

    # --- Body: checkboxes (centered) ---
    body = ttk.Frame(tab)
    body.pack(fill="both", expand=True, padx=10, pady=6)
    center_container = ttk.Frame(body)
    center_container.pack(expand=True)

    pros_vars = {}
    for label, key in PROS_ENTITLEMENTS:
        var = tk.IntVar(value=0)
        cb = ttk.Checkbutton(center_container, text=label, variable=var)
        cb.pack(anchor="w", padx=8, pady=8)
        pros_vars[key] = var

    # --- helpers ---
    def _parse_common_ssl(content):
        """
        Returns (parsed_obj, block_start, block_end) where block_start/end are
        only set if CommonSslSave block is found. parsed_obj is the parsed JSON
        for the CommonSslSave block or the whole file.
        """
        m = re.search(r'"CommonSslSave"\s*:\s*{', content)
        if m:
            block_str, bs, be = extract_brace_block(content, m.end() - 1)
            parsed = json.loads(block_str)
            return parsed, bs, be
        # fallback: try direct JSON
        parsed = json.loads(content)
        return parsed, None, None

    def _get_entitlements_from_parsed(parsed_obj):
        if isinstance(parsed_obj, dict) and isinstance(parsed_obj.get("SslValue"), dict):
            return parsed_obj["SslValue"].get("givenProsEntitlements", [])
        if isinstance(parsed_obj, dict):
            return parsed_obj.get("givenProsEntitlements", [])
        return []

    def _set_entitlements_on_parsed(parsed_obj, ent_list):
        if isinstance(parsed_obj, dict) and isinstance(parsed_obj.get("SslValue"), dict):
            parsed_obj["SslValue"]["givenProsEntitlements"] = ent_list
        elif isinstance(parsed_obj, dict):
            parsed_obj["givenProsEntitlements"] = ent_list

    def load_pros_file(path=None):
        p = path or pros_path_var.get()
        if not p or not os.path.exists(p):
            return
        try:
            with open(p, "r", encoding="utf-8") as f:
                content = f.read()
            parsed, _, _ = _parse_common_ssl(content)
            ent = _get_entitlements_from_parsed(parsed)
            if not isinstance(ent, list):
                ent = []
            for _, key in PROS_ENTITLEMENTS:
                pros_vars[key].set(1 if key in ent else 0)
            _save_common_ssl_path_to_config(p)
        except Exception as e:
            messagebox.showerror("Error", f"Failed to read CommonSslSave:\n{e}")

    def save_pros():
        path = pros_path_var.get()
        if not path or not os.path.exists(path):
            return messagebox.showerror("Error", "CommonSslSave file not found.")
        try:
            try:
                if "make_backup_if_enabled" in globals() and callable(globals()["make_backup_if_enabled"]):
                    make_backup_if_enabled(path)
            except Exception:
                pass

            with open(path, "r", encoding="utf-8") as f:
                content = f.read()

            parsed, bs, be = _parse_common_ssl(content)
            ent = _get_entitlements_from_parsed(parsed)
            if not isinstance(ent, list):
                ent = []

            # Update entries (preserve any other entitlements)
            for _, key in PROS_ENTITLEMENTS:
                checked = bool(pros_vars[key].get())
                if checked:
                    if key not in ent:
                        ent.append(key)
                else:
                    ent = [x for x in ent if x != key]

            _set_entitlements_on_parsed(parsed, ent)

            new_block_str = json.dumps(parsed, separators=(",", ":"))
            if bs is not None and be is not None:
                new_content = content[:bs] + new_block_str + content[be:]
            else:
                new_content = new_block_str

            with open(path, "w", encoding="utf-8") as out_f:
                out_f.write(new_content)

            _save_common_ssl_path_to_config(path)

            show_info("Saved", "PROS entitlements saved successfully.")
        except Exception as e:
            messagebox.showerror("Save error", f"Failed to save PROS entitlements:\n{e}")

    # --- Bottom: centered Save button ---
    bottom = ttk.Frame(tab)
    bottom.pack(fill="x", padx=12, pady=(6,12))
    ttk.Button(bottom, text="Save PROS", command=save_pros).pack(anchor="center")

    # Auto-detect helper (same-folder strategy)
    def sync_pros_from_save(main_save_path):
        _sync_common_ssl_from_save(
            main_save_path,
            pros_path_var,
            load_pros_file,
            allow_json=True
        )

    # register auto-detect
    try:
        if isinstance(plugin_loaders, list) and sync_pros_from_save not in plugin_loaders:
            plugin_loaders.append(sync_pros_from_save)
    except Exception:
        pass

    # trace main save path to trigger detection
    _trace_var_write(save_path_var, lambda: sync_pros_from_save(save_path_var.get()))

    # Auto-load saved path if present; otherwise attempt same-folder detection
    try:
        if pros_path_var.get() and os.path.exists(pros_path_var.get()):
            load_pros_file(pros_path_var.get())
        else:
            _ = sync_pros_from_save(save_path_var.get()) if save_path_var and save_path_var.get() else None
    except Exception:
        pass

    return


# TAB: Trials (launch_gui -> tab_trials)
def create_trials_tab(tab, save_path_var, plugin_loaders):
    """
    Trials tab — no scrollbar, checkbox block uses available vertical space and is
    horizontally centered. Checkbox labels remain left-aligned inside the block.
    """
    TRIALS_LIST = [
        ("Ride-on King", "TRIAL_01_01_SCOUTING_CNT"),
        ("Lost in wilderness", "TRIAL_01_02_TRUCK_TSK"),
        ("Snowbound Valley", "TRIAL_02_01_DELIVERING"),
        ("Zalukodes", "TRIAL_02_02_SEARCH_CNT"),
        ("Northern Thread", "TRIAL_03_01_SCOUTING_CNT"),
        ("Wolves' Bog", "TRIAL_03_03_SCOUTING_CNT"),
        ("The Slope", "TRIAL_04_02_TSK"),
        ("Escape from Tretyakov", "TRIAL_04_01_SCOUTING_CNT"),
        ("Aftermath", "TRIAL_05_01_TSK"),
        ("Tumannaya Pass", "TRIAL_03_02_DELIVERY_CNT"),
    ]

    trials_path_var = tk.StringVar()
    try:
        cp = _load_common_ssl_path_from_config()
        if cp:
            trials_path_var.set(cp)
    except Exception:
        pass

    # --- Top: file picker ---
    top = ttk.Frame(tab)
    top.pack(fill="x", pady=6, padx=8)
    ttk.Label(top, text="CommonSslSave file:").pack(side="left")
    ttk.Entry(top, textvariable=trials_path_var, width=70).pack(side="left", padx=6, fill="x", expand=True)

    def pick_trials_file():
        p = _pick_common_ssl_file(save_path_var, allow_json=False)
        if not p:
            return
        trials_path_var.set(p)
        _save_common_ssl_path_to_config(p)
        load_trials_file(p)

    ttk.Button(top, text="Browse...", command=pick_trials_file).pack(side="left", padx=(4,0))

    # helpful text
    hint = ("Find and select the CommonSslSave.cfg or .dat — it should be located in the same folder as the main save file. "
            "The editor will try to auto-detect it from the main save automatically; if it doesn't or picks the wrong file, select it here.")
    ttk.Label(tab, text=hint, wraplength=1000, justify="left").pack(fill="x", padx=10, pady=(0,6))

    # --- Body: full available space, center block placed exactly in the middle, no scrollbar ---
    body_outer = ttk.Frame(tab)
    body_outer.pack(fill="both", expand=True, padx=10, pady=6)

    # container that we size and center inside body_outer
    center_container = ttk.Frame(body_outer, relief="flat", borderwidth=0)
    center_container.pack_propagate(False)  # we set width/height explicitly

    # content frame that will size itself to the checkboxes (DO NOT stretch to full width)
    content = ttk.Frame(center_container)

    # function to size the center_container and center the content frame inside it
    def _place_center(_ev=None):
        bw = body_outer.winfo_width() or 800
        bh = body_outer.winfo_height() or 400

        # make sure widget sizes are up-to-date before measuring
        content.update_idletasks()
        req_w = content.winfo_reqwidth() or 320
        req_h = content.winfo_reqheight() or 200

        # clamp the container width to a fraction of available width, but don't make it smaller than content
        frac = 0.50
        desired_w = int(max(320, min(900, bw * frac, req_w + 40)))  # add a little padding
        # allow container height to fit content but leave room for top controls + bottom button
        margin_vertical = 120
        max_allowed_h = max(200, bh - margin_vertical)
        desired_h = int(min(max_allowed_h, req_h + 24))

        center_container.configure(width=desired_w, height=desired_h)
        # center the container itself in the body (both axes)
        center_container.place_configure(relx=0.5, rely=0.5, anchor="center")

        # now center the content frame inside the container (content keeps its natural width)
        # place it horizontally centered; vertically align it to the top of the container to keep spacing natural
        content.place_configure(relx=0.5, rely=0.0, anchor="n")

        # final layout pass
        tab.update_idletasks()

    body_outer.bind("<Configure>", _place_center)

    # increase font size slightly for readability (unchanged)
    try:
        cb_font = tkfont.nametofont("TkDefaultFont").copy()
        cb_font.configure(size=max(cb_font.cget("size"), 12))
    except Exception:
        cb_font = None

    # Create checkboxes left-aligned inside the content frame (they will not stretch the content frame)
    trial_vars = {}
    for name, code in TRIALS_LIST:
        v = tk.IntVar(value=0)
        cb = ttk.Checkbutton(content, text=name, variable=v)
        cb.pack(fill="x", anchor="w", padx=8, pady=8)
        if cb_font:
            try:
                cb.configure(font=cb_font)
            except Exception:
                pass
        trial_vars[code] = v

    # initial layout pass so the placement calculation has actual sizes
    tab.update_idletasks()
    _place_center()


    # --- helpers to parse/write finishedTrials (unchanged) ---
    def _parse_finished_trials_from_text(text):
        m = re.search(r'"finishedTrials"\s*:\s*(\[[^\]]*\])', text, flags=re.DOTALL)
        if not m:
            return []
        try:
            arr = json.loads(m.group(1))
            if isinstance(arr, list):
                return arr
        except Exception:
            pass
        return []

    def _write_finished_trials_into_text(text, finished_list):
        arr_text = json.dumps(finished_list)
        if re.search(r'"finishedTrials"\s*:\s*\[', text, flags=re.DOTALL):
            return re.sub(r'"finishedTrials"\s*:\s*\[[^\]]*\]', f'"finishedTrials":{arr_text}', text, flags=re.DOTALL)
        idx = text.find("{")
        if idx != -1:
            insert_pos = idx + 1
            return text[:insert_pos] + f'\n"finishedTrials":{arr_text},' + text[insert_pos:]
        return text + f'\n"finishedTrials":{arr_text}\n'

    def load_trials_file(path):
        if not path or not os.path.exists(path):
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            finished = _parse_finished_trials_from_text(content)
            for _, code in TRIALS_LIST:
                trial_vars[code].set(1 if code in finished else 0)
            _save_common_ssl_path_to_config(path)
            # re-layout to adapt center size
            tab.update_idletasks()
            _place_center()
        except Exception as e:
            messagebox.showerror("Error", f"Failed to read CommonSslSave:\n{e}")

    def save_trials():
        path = trials_path_var.get()
        if not path or not os.path.exists(path):
            return messagebox.showerror("Error", "CommonSslSave file not found.")
        finished = [code for _, code in TRIALS_LIST if trial_vars[code].get()]
        try:
            try:
                if "make_backup_if_enabled" in globals() and callable(globals()["make_backup_if_enabled"]):
                    make_backup_if_enabled(path)
            except Exception:
                print("[Warning] backup failed while saving trials")
            with open(path, "r", encoding="utf-8") as f:
                text = f.read()
            new_text = _write_finished_trials_into_text(text, finished)
            with open(path, "w", encoding="utf-8") as f:
                f.write(new_text)
            _save_common_ssl_path_to_config(path)
            show_info("Saved", "Trials saved successfully.")
        except Exception as e:
            messagebox.showerror("Save error", f"Failed to save trials:\n{e}")

    # --- Bottom: centered Save Trials button ---
    bottom = ttk.Frame(tab)
    bottom.pack(fill="x", padx=12, pady=(6,12))
    ttk.Button(bottom, text="Save Trials", command=save_trials).pack(anchor="center")

    # Auto-load saved path if present
    if trials_path_var.get() and os.path.exists(trials_path_var.get()):
        load_trials_file(trials_path_var.get())

    # Auto-detect helper (same-folder strategy)
    def sync_trials_from_save(main_save_path):
        _sync_common_ssl_from_save(
            main_save_path,
            trials_path_var,
            load_trials_file,
            allow_json=False
        )

    # register auto-detect
    try:
        if isinstance(plugin_loaders, list) and sync_trials_from_save not in plugin_loaders:
            plugin_loaders.append(sync_trials_from_save)
    except Exception:
        pass

    # trace main save path to trigger detection
    _trace_var_write(save_path_var, lambda: sync_trials_from_save(save_path_var.get()))


# TAB: Upgrades (launch_gui -> tab_upgrades)
def create_upgrades_tab(tab, save_path_var):
    seasons = [(label, code) for _, (code, label) in SEASON_ENTRIES]
    maps = [(name, code) for code, name in BASE_MAPS]
    selector = _build_region_selector(tab, seasons, maps)
    season_vars = selector["season_vars"]
    map_vars = selector["map_vars"]
    all_check_vars = selector["all_check_vars"]
    other_season_var = selector["other_var"]

    def on_apply():
        path = save_path_var.get()
        if not os.path.exists(path):
            messagebox.showerror("Error", "Save file not found.")
            return
        selected_regions = _collect_selected_regions(season_vars, map_vars, other_season_var)
        if not selected_regions:
            show_info("Info", "No seasons or maps selected.")
            return
        find_and_modify_upgrades(path, selected_regions)

    ttk.Button(tab, text="Unlock Upgrades", command=on_apply).pack(pady=(10, 5))
    _add_check_all_checkbox(tab, all_check_vars)

    ttk.Label(tab, text="At least one upgrade must be marked or collected in-game for this to work.",
              style="Warning.TLabel").pack(pady=(0, 2))
    ttk.Label(tab, text="If a new season is added, you may need to mark or collect one new upgrade.",
              style="Warning.TLabel").pack()
# TAB: Game Stats (launch_gui -> tab_stats)
def create_game_stats_tab(tab, save_path_var, plugin_loaders):

    stats_vars = {}
    distance_vars = {}

    # Full mapping for region codes -> full names (uppercase keys)
    REGION_ORDER = list(REGION_LONG_NAME_MAP.keys())

    def nice_name(raw_key: str) -> str:
        """Turn MONEY_SPENT → Money Spent and fix plural forms"""
        name = raw_key.replace("_", " ").title()
        replacements = {
            "Truck Sold": "Trucks Sold",
            "Truck Bought": "Trucks Bought",
            "Trailer Sold": "Trailers Sold",
            "Trailer Bought": "Trailers Bought",
            "Addon Sold": "Addons Sold",
            "Addon Bought": "Addons Bought",
        }
        return replacements.get(name, name)

    # Find best distance block
    def _find_best_distance_block(content):
        matches = list(re.finditer(r'"distance"\s*:\s*{', content))
        if not matches:
            return None
        best = None
        best_count = -1
        for m in matches:
            try:
                block, bstart, bend = extract_brace_block(content, m.end() - 1)
                parsed = json.loads(block)
                cnt = sum(1 for k in parsed.keys() if str(k).upper() in REGION_ORDER or str(k).upper() == "TRIALS")
                if cnt > best_count:
                    best_count = cnt
                    best = (parsed, bstart, bend)
            except Exception:
                continue
        return best

    # === UI setup ===
    outer_frame = ttk.Frame(tab)
    outer_frame.pack(fill="both", expand=True, pady=20)

    # center everything
    center_frame = ttk.Frame(outer_frame)
    center_frame.pack(anchor="center")

    # grid columns: distance (0–1), spacer (2), stats (3–4)
    for idx in range(5):
        center_frame.grid_columnconfigure(idx, weight=0, pad=10)

    # === Refresh function ===
    def refresh_ui(path):
        for child in center_frame.winfo_children():
            child.destroy()
        stats_vars.clear()
        distance_vars.clear()

        if not os.path.exists(path):
            return

        with open(path, "r", encoding="utf-8") as f:
            content = f.read()

        # parse gameStat
        game_stat = {}
        m_stat = re.search(r'"gameStat"\s*:\s*{', content)
        if m_stat:
            block, _, _ = extract_brace_block(content, m_stat.end() - 1)
            game_stat = json.loads(block)

        # parse distance
        found = _find_best_distance_block(content)
        distance_parsed = found[0] if found else {}

        # headers
        ttk.Label(center_frame, text="Distance Driven", font=("TkDefaultFont", 12, "bold")).grid(row=0, column=0, columnspan=2, pady=(0, 15), sticky="w")
        ttk.Label(center_frame, text="Game Statistics", font=("TkDefaultFont", 12, "bold")).grid(row=0, column=3, columnspan=2, pady=(0, 15), sticky="w")

        # distance rows
        def dist_sort_key(k):
            up = str(k).upper()
            if up in REGION_ORDER:
                return (0, REGION_ORDER.index(up))
            return (1, str(k).upper())

        dist_items = sorted(distance_parsed.items(), key=lambda kv: dist_sort_key(kv[0]))
        for i, (region, value) in enumerate(dist_items, start=1):
            region_up = str(region).upper()
            label_text = REGION_LONG_NAME_MAP.get(region_up, region)
            ttk.Label(center_frame, text=label_text + ":", anchor="w", justify="left").grid(row=i, column=0, sticky="w", padx=(0, 6), pady=2)
            var = tk.StringVar(value=str(value))
            distance_vars[region] = var
            ttk.Entry(center_frame, textvariable=var, width=12).grid(row=i, column=1, sticky="w", pady=2)

        # stats rows
        for j, (key, value) in enumerate(game_stat.items(), start=1):
            ttk.Label(center_frame, text=nice_name(key) + ":", anchor="w", justify="left").grid(row=j, column=3, sticky="w", padx=(0, 6), pady=3)
            var = tk.StringVar(value=str(value))
            stats_vars[key] = var
            ttk.Entry(center_frame, textvariable=var, width=20).grid(row=j, column=4, sticky="w", pady=3)

        # Save button
        final_row = 1 + max(len(dist_items), len(game_stat))
        btn = ttk.Button(center_frame, text="Save All", command=save_all)
        btn.grid(row=final_row, column=0, columnspan=5, pady=(15, 0))

    def save_all():
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")

        # 🔹 Make a backup first (use the central, existing function)
        try:
            # If the function exists in globals, call it; otherwise, attempt direct name
            if "make_backup_if_enabled" in globals():
                make_backup_if_enabled(path)
            else:
                # fallback: if old name exists, try it (defensive)
                if "make_backup" in globals():
                    globals()["make_backup"](path)
                elif "make_backup_var" in globals() and callable(globals().get("make_backup_var")):
                    globals()["make_backup_var"](path)
                else:
                    print("[Backup] No backup function found; skipping backup.")
        except Exception as e:
            print(f"[Backup] Exception while attempting backup: {e}")

        # read file
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()

        # update gameStat
        m_stat = re.search(r'"gameStat"\s*:\s*{', content)
        if m_stat:
            block, start, end = extract_brace_block(content, m_stat.end() - 1)
            data = json.loads(block)
            for key, var in stats_vars.items():
                try:
                    data[key] = int(var.get())
                except ValueError:
                    try:
                        data[key] = float(var.get())
                    except ValueError:
                        data[key] = var.get()
            new_block = json.dumps(data, separators=(",", ":"))
            content = content[:start] + new_block + content[end:]

        # update distance
        found = _find_best_distance_block(content)
        if found:
            dist_data, dstart, dend = found
            for key, var in distance_vars.items():
                try:
                    dist_data[key] = int(var.get())
                except ValueError:
                    try:
                        dist_data[key] = float(var.get())
                    except ValueError:
                        dist_data[key] = var.get()
            new_block = json.dumps(dist_data, separators=(",", ":"))
            content = content[:dstart] + new_block + content[dend:]

        # write back
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)

        show_info("Success", "Stats and distances updated.")
        refresh_ui(path)

    # loader hook
    plugin_loaders.append(refresh_ui)

    if os.path.exists(save_path_var.get()):
        refresh_ui(save_path_var.get())
# TAB: Watchtowers (launch_gui -> tab_watchtowers)
def create_watchtowers_tab(tab, save_path_var):
    seasons = [(label, code) for _, (code, label) in SEASON_ENTRIES]
    maps = [(name, code) for code, name in BASE_MAPS]
    selector = _build_region_selector(tab, seasons, maps)
    season_vars = selector["season_vars"]
    map_vars = selector["map_vars"]
    all_check_vars = selector["all_check_vars"]
    other_season_var = selector["other_var"]

    def on_apply():
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")
        selected_regions = _collect_selected_regions(season_vars, map_vars, other_season_var)
        if not selected_regions:
            return show_info("Info", "No seasons or maps selected.")
        unlock_watchtowers(path, selected_regions)

    ttk.Button(tab, text="Unlock Watchtowers", command=on_apply).pack(pady=(10, 5))
    _add_check_all_checkbox(tab, all_check_vars)
    ttk.Label(tab, text="It will mark them as found but wont reveal the map use the Fog Tool for that.",
              style="Warning.TLabel").pack()

# TAB: Discoveries (launch_gui -> tab_discoveries)
def create_discoveries_tab(tab, save_path_var):
    seasons = [(label, code) for _, (code, label) in SEASON_ENTRIES]
    maps = [(name, code) for code, name in BASE_MAPS]
    selector = _build_region_selector(tab, seasons, maps)
    season_vars = selector["season_vars"]
    map_vars = selector["map_vars"]
    all_check_vars = selector["all_check_vars"]
    other_season_var = selector["other_var"]

    def on_apply():
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")
        selected_regions = _collect_selected_regions(season_vars, map_vars, other_season_var)
        if not selected_regions:
            return show_info("Info", "No seasons or maps selected.")
        unlock_discoveries(path, selected_regions)

    ttk.Button(tab, text="Unlock Discoveries", command=on_apply).pack(pady=(10, 5))
    _add_check_all_checkbox(tab, all_check_vars)
    ttk.Label(tab, text="Sets discovered trucks to their max for selected regions but won't add them to garage.",
              style="Warning.TLabel").pack()

# TAB: Levels (launch_gui -> tab_levels)
def create_levels_tab(tab, save_path_var):
    seasons = [(label, code) for _, (code, label) in SEASON_ENTRIES]
    maps = [(name, code) for code, name in BASE_MAPS]
    selector = _build_region_selector(tab, seasons, maps)
    season_vars = selector["season_vars"]
    map_vars = selector["map_vars"]
    all_check_vars = selector["all_check_vars"]
    other_season_var = selector["other_var"]

    def on_apply():
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")
        selected_regions = _collect_selected_regions(season_vars, map_vars, other_season_var)
        if not selected_regions:
            return show_info("Info", "No seasons or maps selected.")
        unlock_levels(path, selected_regions)

    ttk.Button(tab, text="Unlock Levels", command=on_apply).pack(pady=(10, 5))
    _add_check_all_checkbox(tab, all_check_vars)
    ttk.Label(
        tab,
        text="Lets you view regions you haven't visited yet.",
        style="Warning.TLabel"
    ).pack()

# TAB: Garages (launch_gui -> tab_garages)
def create_garages_tab(tab, save_path_var):
    upgrade_all_var = tk.IntVar()
    seasons = [(label, code) for _, (code, label) in SEASON_ENTRIES]
    maps = [(name, code) for code, name in BASE_MAPS]
    selector = _build_region_selector(tab, seasons, maps)
    season_vars = selector["season_vars"]
    map_vars = selector["map_vars"]
    all_check_vars = selector["all_check_vars"]
    other_season_var = selector["other_var"]

    def on_apply():
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")
        selected_regions = _collect_selected_regions(season_vars, map_vars, other_season_var)
        if not selected_regions:
            return show_info("Info", "No seasons or maps selected.")
        unlock_garages(path, selected_regions, upgrade_all=bool(upgrade_all_var.get()))

    ttk.Button(tab, text="Unlock Garages", command=on_apply).pack(pady=(10, 5))
    _add_check_all_checkbox(tab, all_check_vars)
    ttk.Checkbutton(tab, text="Upgrade All Garages", variable=upgrade_all_var).pack(anchor="center", pady=(4, 0))
    ttk.Label(
        tab,
        text=(
            "Garages will be unlocked but may be hidden under fog of war. To make it work correctly, "
            "don’t open the map itself to go into the garage. Instead, in map-selection "
            "put your cursor over the map you want — you should see a yellow-highlighted garage icon in the bottom part of the map labeled "
            "'Garage Opened'. Click it to port into the garage instantly. The garage can still be hidden "
            "under fog, so drive to the yellow garage box (entrance/move to garage) to reveal it on the map. "
            "Recover feature on that map will be semi-broken until you find the garage entrance. Note: some garage entrances "
            "are hidden behind a quest, so you may need to use Objectives+ or complete it yourself "
            "(e.g., the garage in Amur – Chernokamensk)."
        ),
        style="Warning.TLabel",
        wraplength=1000,
        justify="left"
    ).pack(pady=(6, 0), padx=12)

# =============================================================================
# SECTION: Vehicles Tab (STS object editing)
# Used In: launch_gui -> Vehicles
# =============================================================================
_KNOWN_TRUCK_IDS_DEFAULT = sorted({
    "ank_mk38",
    "ank_mk38_ht",
    "azov_4220_antarctic",
    "azov_43_191_sprinter",
    "azov_5319",
    "azov_64131",
    "azov_670963n",
    "azov_73210",
    "boar_45318",
    "cat_745c",
    "cat_ct680",
    "chevrolet_ck1500",
    "chevrolet_kodiakc70",
    "dan_96320",
    "derry_longhorn_3194",
    "derry_longhorn_4520",
    "don_71",
    "femm_37at",
    "ford_clt9000",
    "freightliner_114sd",
    "freightliner_m916a1",
    "futom_7290ra",
    "gmc_9500",
    "hummer_h2",
    "international_fleetstar_f2070a",
    "international_loadstar_1700",
    "international_paystar_5070",
    "international_scout_800",
    "international_transtar_4070a",
    "jangsu_rx600",
    "jeep_cj7_renegade",
    "jeep_wrangler",
    "kenworth_c500",
    "khan_lo4f",
    "kolob_74760",
    "kolob_74941",
    "mack_defense_m917",
    "navistar_5000_mv",
    "pacific_p12w",
    "pacific_p16",
    "rezvani_hercules_6x6",
    "royal_bm17",
    "step_310e",
    "tatra_t813",
    "tatra_t815_7",
    "tayga_6436",
    "tuz_166",
    "tuz_420_tatarin",
    "voron_ae4380",
    "voron_d53233",
    "voron_grad",
    "ws_4964_white",
    "ws_6900xd_twin",
    "yar_87",
    "zikz_5368",
    "zikz_612h_mastodont",
})

_VEHICLE_BRAND_HINTS = {
    "ank", "azov", "boar", "cat", "chevrolet", "dan", "derry", "don", "femm", "ford",
    "freightliner", "futom", "gmc", "hummer", "international", "jangsu", "jeep", "kenworth",
    "khan", "kolob", "krs", "land", "mack", "navistar", "pacific", "rezvani", "royal", "step", "tatra",
    "tayga", "tuz", "voron", "western", "chevy", "ws", "yar", "zikz",
    # Extra mod/season brands seen in saves/static id lists.
    "aac", "aramatsu", "ankatra", "avenhorn", "burlak", "earthroamer", "kirovets",
    "mercer", "mtb", "neo", "padera", "plad", "sleiter",
}

_VEHICLE_ID_BLOCKLIST_PARTS = (
    "engine", "gearbox", "suspension", "wheels", "rim_", "tires", "tire", "transferbox",
    "diff_lock", "bumper", "snorkel", "roofrack", "gabarite", "headlight", "horn", "paint",
    "addon", "cabin", "grill", "cargo_", "bone", "sticker", "stuff_", "airfreshener",
)

# STS scanning guardrail:
# these are usually component/customization ids, not movable world objects.
_STS_COMPONENT_TYPE_BLOCKLIST_PARTS = (
    "_default",
    "_fender_",
    "exhaust",
    "threshold",
    "treshhold",
    "spotlight",
    "lightbar",
    "wheel_addon",
    "wheel_default",
    "diff_lock",
    "mudguard",
    "mud_guards",
    "bumper_",
    "paint_",
    "decal_",
)


def _vehicle_humanize_id(raw: Any) -> str:
    value = str(raw or "").strip()
    if not value:
        return ""
    if value.startswith("{") and value.endswith("}"):
        return value

    base = value.split("/", 1)[0]
    parts = [p for p in re.split(r"[_\-]+", base) if p]
    out = []
    for p in parts:
        if p.isdigit():
            out.append(p)
        elif re.fullmatch(r"\d+[a-z]", p):
            out.append(p[:-1] + p[-1].upper())
        elif re.fullmatch(r"[a-z]\d+[a-z]?", p):
            if p[-1].isalpha():
                out.append(p[0].upper() + p[1:-1] + p[-1].upper())
            else:
                out.append(p[0].upper() + p[1:])
        elif len(p) <= 3 and p.isalpha():
            out.append(p.upper())
        else:
            out.append(p.capitalize())
    return " ".join(out) if out else value


_VEHICLE_REAL_NAME_MAP_CACHE = None
_VEHICLE_MAP_DISPLAY_INDEX_CACHE = None
_VEHICLE_METADATA_CACHE_INFO = None
_VEHICLE_METADATA_CACHE_LOCK = threading.Lock()
_VEHICLE_STATIC_ID_SOURCE_CACHE = None
_VEHICLE_STATIC_ID_SOURCE_LOCK = threading.Lock()


def _vehicle_static_ids_file_path() -> str:
    candidates = []
    try:
        base_dir = os.path.dirname(os.path.abspath(__file__))
    except Exception:
        base_dir = os.getcwd()
    candidates.append(os.path.join(base_dir, "experiments", "truck_trailer_ids.txt"))
    candidates.append(os.path.join(os.getcwd(), "experiments", "truck_trailer_ids.txt"))
    for p in candidates:
        if p and os.path.exists(p):
            return p
    return candidates[0]


def _vehicle_load_static_id_source(force_reload: bool = False) -> Dict[str, Any]:
    global _VEHICLE_STATIC_ID_SOURCE_CACHE

    if (not force_reload) and isinstance(_VEHICLE_STATIC_ID_SOURCE_CACHE, dict):
        return _VEHICLE_STATIC_ID_SOURCE_CACHE

    with _VEHICLE_STATIC_ID_SOURCE_LOCK:
        if (not force_reload) and isinstance(_VEHICLE_STATIC_ID_SOURCE_CACHE, dict):
            return _VEHICLE_STATIC_ID_SOURCE_CACHE

        path = _vehicle_static_ids_file_path()
        out = {
            "path": path,
            "name_map": {},
            "truck_ids": [],
            "trailer_ids": [],
            "truck_ids_lower": set(),
            "trailer_ids_lower": set(),
            "all_ids_lower": set(),
            "base_ids_lower": set(),
            "truck_base_ids_lower": set(),
            "trailer_base_ids_lower": set(),
        }
        if not path or (not os.path.exists(path)):
            _VEHICLE_STATIC_ID_SOURCE_CACHE = out
            return _VEHICLE_STATIC_ID_SOURCE_CACHE

        name_map = {}
        truck_ids = set()
        trailer_ids = set()
        all_ids_lower = set()
        base_ids_lower = set()
        truck_base_ids_lower = set()
        trailer_base_ids_lower = set()
        section = ""

        def _looks_like_map_or_task_id(tl: str) -> bool:
            if re.match(r"^[a-z]{2}_\d{2}_", tl):
                return True
            if any(tok in tl for tok in ("_trial_", "_tsk_", "_task_", "_contract_")):
                return True
            return False

        def _is_canonical_truck_static_id(raw: str) -> bool:
            t0 = str(raw or "").strip()
            if not t0:
                return False
            tl = t0.lower()
            if t0 != tl:
                return False
            if "trailer" in tl:
                return False
            if not re.fullmatch(r"[a-z0-9_\-./]+", tl):
                return False
            if _looks_like_map_or_task_id(tl):
                return False
            if any(tok in tl for tok in ("_old_engine_", "skin_")):
                return False
            parts = [p for p in re.split(r"[_\-]+", tl) if p]
            if not parts:
                return False
            return parts[0] in _VEHICLE_BRAND_HINTS

        def _is_canonical_trailer_static_id(raw: str) -> bool:
            t0 = str(raw or "").strip()
            if not t0:
                return False
            tl = t0.lower()
            if t0 != tl:
                return False
            if not re.fullmatch(r"[a-z0-9_\-./]+", tl):
                return False
            if _looks_like_map_or_task_id(tl):
                return False
            return ("trailer" in tl) or (tl in {"generator", "cultivator", "harvester", "planter", "driller"})

        try:
            with open(path, "r", encoding="utf-8-sig", errors="replace") as f:
                for raw_line in f:
                    line = str(raw_line or "").strip()
                    if not line:
                        continue

                    upper = line.upper()
                    if upper.startswith("TRUCK IDS"):
                        section = "truck"
                        continue
                    if upper.startswith("TRAILER IDS"):
                        section = "trailer"
                        continue
                    if "=" not in line:
                        continue

                    left, right = line.split("=", 1)
                    type_id = str(left or "").strip()
                    display_name = str(right or "").strip()
                    if not type_id:
                        continue
                    if not display_name:
                        display_name = _vehicle_humanize_id(type_id)
                    if not display_name:
                        display_name = type_id

                    # Keep multiple key casings for robust lookup in STS/save variants.
                    for key in {type_id, type_id.lower(), type_id.upper()}:
                        k = str(key or "").strip()
                        if not k:
                            continue
                        if k not in name_map:
                            name_map[k] = display_name

                    tl = type_id.lower()
                    all_ids_lower.add(tl)
                    if section == "truck":
                        truck_ids.add(type_id)
                        if _is_canonical_truck_static_id(type_id):
                            base_ids_lower.add(tl)
                            truck_base_ids_lower.add(tl)
                    elif section == "trailer":
                        trailer_ids.add(type_id)
                        if _is_canonical_trailer_static_id(type_id):
                            base_ids_lower.add(tl)
                            trailer_base_ids_lower.add(tl)
        except Exception:
            pass

        out["name_map"] = name_map
        out["truck_ids"] = sorted(truck_ids, key=lambda x: str(x).lower())
        out["trailer_ids"] = sorted(trailer_ids, key=lambda x: str(x).lower())
        out["truck_ids_lower"] = {str(x).strip().lower() for x in truck_ids if str(x).strip()}
        out["trailer_ids_lower"] = {str(x).strip().lower() for x in trailer_ids if str(x).strip()}
        out["all_ids_lower"] = all_ids_lower
        out["base_ids_lower"] = base_ids_lower
        out["truck_base_ids_lower"] = truck_base_ids_lower
        out["trailer_base_ids_lower"] = trailer_base_ids_lower

        _VEHICLE_STATIC_ID_SOURCE_CACHE = out
        return _VEHICLE_STATIC_ID_SOURCE_CACHE


def _vehicle_static_name_map(force_reload: bool = False) -> Dict[str, str]:
    data = _vehicle_load_static_id_source(force_reload=force_reload)
    name_map = data.get("name_map", {}) if isinstance(data, dict) else {}
    return dict(name_map) if isinstance(name_map, dict) else {}


def _vehicle_static_truck_ids(force_reload: bool = False) -> List[str]:
    data = _vehicle_load_static_id_source(force_reload=force_reload)
    vals = data.get("truck_base_ids_lower", set()) if isinstance(data, dict) else set()
    if not isinstance(vals, (set, list, tuple)):
        return []
    return sorted({str(v).strip().lower() for v in vals if str(v).strip()})


def _vehicle_is_static_truck_id(raw_type_id: Any) -> bool:
    t = str(raw_type_id or "").strip().lower()
    if not t:
        return False
    s = set(_vehicle_static_truck_ids(force_reload=False))
    return t in s


def _vehicle_metadata_cache_path(kind: str) -> str:
    try:
        cfg_dir = os.path.dirname(CONFIG_FILE)
    except Exception:
        cfg_dir = ""
    if not cfg_dir:
        try:
            cfg_dir = os.path.expanduser("~")
        except Exception:
            cfg_dir = ""
    if not cfg_dir:
        cfg_dir = os.getcwd()

    k = str(kind or "").strip().lower()
    if k == "maps":
        name = ".snowrunner_editor_vehicle_map_index.json"
    else:
        name = ".snowrunner_editor_vehicle_name_map.json"
    return os.path.join(cfg_dir, name)


def _vehicle_read_json_cache(path: str) -> Dict[str, Any]:
    if not path or not os.path.exists(path):
        return {}
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            return data
    except Exception:
        pass
    return {}


def _vehicle_write_json_cache(path: str, payload: Dict[str, Any]) -> None:
    if not path or not isinstance(payload, dict):
        return
    try:
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    except Exception:
        pass
    tmp = path + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, separators=(",", ":"))
        os.replace(tmp, path)
    except Exception:
        try:
            if os.path.exists(tmp):
                os.remove(tmp)
        except Exception:
            pass


def _vehicle_collect_maprunner_js_texts(allow_online: bool = False) -> List[str]:
    """
    Collect JS text blobs using the same MapRunner pipeline as Objectives+:
      - in-memory canonical roles
      - cached canonical JS files
      - optional online refresh with random chunk role detection
    """
    try:
        _mr_choose_best_js_roles()
    except Exception:
        pass

    try:
        _mr_load_cached_canonical_js_to_mem()
    except Exception:
        pass

    if allow_online:
        try:
            _mr_download_js_step()
        except Exception:
            pass

    try:
        _mr_choose_best_js_roles()
    except Exception:
        pass

    texts: List[str] = []
    seen_texts = set()

    def _add_text(raw: Any) -> None:
        try:
            txt = _mr_decode_bytes_to_text(raw) if raw is not None else None
        except Exception:
            txt = None
        if not txt or not isinstance(txt, str):
            return
        if txt in seen_texts:
            return
        seen_texts.add(txt)
        texts.append(txt)

    try:
        _add_text(_mr_get_file_bytes_or_mem(_MR_CANONICAL_NAMES["data"]))
    except Exception:
        pass
    try:
        _add_text(_mr_get_file_bytes_or_mem(_MR_CANONICAL_NAMES["desc"]))
    except Exception:
        pass

    try:
        for name, bs in list(_MR_IN_MEM_FILES.items()):
            if not str(name or "").lower().endswith(".js"):
                continue
            _add_text(bs)
    except Exception:
        pass

    return texts


def _vehicle_extract_metadata_from_js_texts(
    texts: List[str], localization_seed: Optional[Dict[str, str]] = None
) -> (Dict[str, str], Dict[str, Dict[str, str]]):
    localization = {}
    if isinstance(localization_seed, dict) and localization_seed:
        for k, v in localization_seed.items():
            key = str(k or "").strip()
            val = str(v or "").strip()
            if key and val:
                localization[key] = val
    id_to_token = {}
    level_tokens = {}
    level_slugs = {}

    pat_name_key = re.compile(
        r'"name"\s*:\s*"(UI_(?:VEHICLE|TRAILER)_[A-Z0-9_]+)"\s*,\s*"key"\s*:\s*"([a-z0-9_./-]+)"',
        flags=re.IGNORECASE,
    )
    pat_key_name = re.compile(
        r'"key"\s*:\s*"([a-z0-9_./-]+)"\s*,\s*"name"\s*:\s*"(UI_(?:VEHICLE|TRAILER)_[A-Z0-9_]+)"',
        flags=re.IGNORECASE,
    )
    pat_level_levelname = re.compile(
        r'"level"\s*:\s*"level_([a-z0-9_]+)"\s*,\s*"levelName"\s*:\s*"([^"]+)"',
        flags=re.IGNORECASE,
    )
    pat_levelname_level = re.compile(
        r'"levelName"\s*:\s*"([^"]+)"\s*,\s*"level"\s*:\s*"level_([a-z0-9_]+)"',
        flags=re.IGNORECASE,
    )
    pat_level_map_slug = re.compile(
        r'"level"\s*:\s*"level_([a-z0-9_]+)"[\s\S]{0,220}?"map"\s*:\s*"([^"]+)"',
        flags=re.IGNORECASE,
    )

    for text in texts or []:
        if not text:
            continue

        # If localization seed is missing/incomplete, keep filling from scanned JS.
        try:
            parsed_loc = _mr_parse_localization_from_desc_text(text) or {}
        except Exception:
            parsed_loc = {}
        if parsed_loc:
            for k, v in parsed_loc.items():
                if k not in localization:
                    localization[k] = v

        try:
            for m in pat_name_key.finditer(text):
                token = str(m.group(1) or "").strip()
                type_id = str(m.group(2) or "").strip()
                if not token or not type_id:
                    continue
                if not _sts_is_vehicle_or_trailer_type(type_id, ""):
                    continue
                id_to_token.setdefault(type_id, token)
            for m in pat_key_name.finditer(text):
                type_id = str(m.group(1) or "").strip()
                token = str(m.group(2) or "").strip()
                if not token or not type_id:
                    continue
                if not _sts_is_vehicle_or_trailer_type(type_id, ""):
                    continue
                id_to_token.setdefault(type_id, token)
        except Exception:
            pass

        try:
            for m in pat_level_levelname.finditer(text):
                level = _map_normalize_id(m.group(1))
                token = str(m.group(2) or "").strip()
                if level and token:
                    level_tokens.setdefault(level, set()).add(token)
            for m in pat_levelname_level.finditer(text):
                token = str(m.group(1) or "").strip()
                level = _map_normalize_id(m.group(2))
                if level and token:
                    level_tokens.setdefault(level, set()).add(token)
            for m in pat_level_map_slug.finditer(text):
                level = _map_normalize_id(m.group(1))
                slug = str(m.group(2) or "").strip()
                if level and slug and level not in level_slugs:
                    level_slugs[level] = slug
        except Exception:
            pass

    name_map = {}
    for type_id, token in id_to_token.items():
        name = _experiments_translate_token(token, localization) if isinstance(localization, dict) and localization else token
        name = _experiments_clean_text(name) if name else ""
        if (not name) or _experiments_is_likely_token(name):
            name = _vehicle_humanize_id(type_id)
        name_map[type_id] = name

    map_index = {}
    all_levels = set(level_tokens.keys()) | set(level_slugs.keys())
    for map_id in sorted(all_levels):
        region_code = _map_region_code_from_map_id(map_id)
        region_name = _map_region_name_from_code(region_code)
        map_name = ""

        tokens = sorted(
            list(level_tokens.get(map_id, set())),
            key=lambda t: (
                0 if str(t).upper().endswith("_NAME") else 1,
                0 if not str(t).upper().startswith("LEVEL_") else 1,
                len(str(t)),
            ),
        )
        for token in tokens:
            try:
                translated = _experiments_translate_token(token, localization)
            except Exception:
                translated = token
            cleaned = _experiments_clean_text(translated) if translated else ""
            if cleaned and not _experiments_is_likely_token(cleaned):
                map_name = cleaned
                break

        if not map_name:
            slug = level_slugs.get(map_id, "")
            map_name = _map_humanize_slug(slug)

        if not map_name:
            map_name = map_id

        map_index[map_id] = {
            "map_id": map_id,
            "region_code": region_code,
            "region_name": region_name,
            "map_name": map_name,
        }

    token_map_pat = re.compile(
        r"^(?:LEVEL_)?((?:US|RU)_\d{2}_\d{2}(?:_(?:NEW|CROP))?|TRIAL_\d{2}_\d{2})_NAME$",
        flags=re.IGNORECASE,
    )
    for token, value in list(localization.items()):
        m = token_map_pat.match(str(token or "").strip())
        if not m:
            continue
        map_id = _map_normalize_id(m.group(1))
        cleaned = _experiments_clean_text(value)
        if not cleaned or _experiments_is_likely_token(cleaned):
            continue

        entry = map_index.get(map_id)
        if not isinstance(entry, dict):
            region_code = _map_region_code_from_map_id(map_id)
            entry = {
                "map_id": map_id,
                "region_code": region_code,
                "region_name": _map_region_name_from_code(region_code),
                "map_name": cleaned,
            }
            map_index[map_id] = entry
            continue

        current_name = str(entry.get("map_name", "") or "").strip()
        if not current_name or current_name == map_id or _experiments_is_likely_token(current_name):
            entry["map_name"] = cleaned

    return name_map, map_index


def _vehicle_normalize_name_map(payload: Any) -> Dict[str, str]:
    out = {}
    if not isinstance(payload, dict):
        return out
    for raw_k, raw_v in payload.items():
        key = str(raw_k or "").strip()
        val = str(raw_v or "").strip()
        if not key:
            continue
        if not val or _experiments_is_likely_token(val):
            val = _vehicle_humanize_id(key)
        out[key] = val
    return out


def _vehicle_normalize_map_index(payload: Any) -> Dict[str, Dict[str, str]]:
    out = {}
    if not isinstance(payload, dict):
        return out
    for raw_mid, raw_entry in payload.items():
        map_id = _map_normalize_id(raw_mid)
        if not map_id:
            continue
        if isinstance(raw_entry, dict):
            region_code = str(raw_entry.get("region_code", "") or "").strip().upper()
            map_name = str(raw_entry.get("map_name", "") or "").strip()
            region_name = str(raw_entry.get("region_name", "") or "").strip()
        else:
            region_code = ""
            map_name = ""
            region_name = ""
        if not region_code:
            region_code = _map_region_code_from_map_id(map_id)
        if not region_name:
            region_name = _map_region_name_from_code(region_code)
        if not map_name:
            map_name = map_id
        out[map_id] = {
            "map_id": map_id,
            "region_code": region_code,
            "region_name": region_name,
            "map_name": map_name,
        }
    return out


def _vehicle_name_quality(name: str, type_id: str = "") -> int:
    text = str(name or "").strip()
    if not text:
        return 0
    low = text.lower()
    words = [w for w in re.split(r"\s+", text) if w]

    # Broken/unresolved strings should never win merges.
    if _experiments_is_likely_token(text):
        return 1
    if any(mark in text for mark in ("�", "Ð", "Ñ", "Ã", "Â")):
        return 1
    if low.startswith(("g ", "w ")):
        return 1
    if any(tok in low for tok in (" default", "skin ", " old engine", "deleted")):
        return 1
    if any(ch in text for ch in (".", "!", "?", ";", ":")):
        return 1
    if len(text) > 60 or len(words) > 8:
        return 1
    if low.startswith(("a ", "an ", "the ")) and len(words) >= 5:
        return 1

    # Humanized id is acceptable fallback, but lower confidence than true names.
    if type_id and text == _vehicle_humanize_id(type_id):
        return 2

    score = 3
    if re.search(r"[A-Z]", text) and (not text.islower()):
        score += 1
    if len(words) <= 4:
        score += 1
    return min(5, score)


def _vehicle_map_name_quality(name: str, map_id: str = "") -> int:
    text = str(name or "").strip()
    if not text:
        return 0
    if _experiments_is_likely_token(text):
        return 1
    if map_id and _map_normalize_id(text) == _map_normalize_id(map_id):
        return 2
    return 3


def _vehicle_merge_name_maps(base: Dict[str, str], incoming: Dict[str, str]) -> Dict[str, str]:
    out = dict(base or {})
    for k, v in (incoming or {}).items():
        key = str(k or "").strip()
        if not key:
            continue
        new_val = str(v or "").strip()
        old_val = str(out.get(key, "") or "").strip()
        if _vehicle_name_quality(new_val, key) >= _vehicle_name_quality(old_val, key):
            out[key] = new_val
    return out


def _vehicle_merge_map_index(
    base: Dict[str, Dict[str, str]],
    incoming: Dict[str, Dict[str, str]],
) -> Dict[str, Dict[str, str]]:
    out = dict(base or {})
    for raw_mid, raw_entry in (incoming or {}).items():
        map_id = _map_normalize_id(raw_mid)
        if not map_id:
            continue
        old = out.get(map_id, {}) if isinstance(out.get(map_id), dict) else {}
        new = raw_entry if isinstance(raw_entry, dict) else {}

        old_name = str(old.get("map_name", "") or "").strip()
        new_name = str(new.get("map_name", "") or "").strip()

        chosen_name = old_name
        if _vehicle_map_name_quality(new_name, map_id) >= _vehicle_map_name_quality(old_name, map_id):
            chosen_name = new_name or old_name

        region_code = str(new.get("region_code", "") or old.get("region_code", "") or "").strip().upper()
        if not region_code:
            region_code = _map_region_code_from_map_id(map_id)
        region_name = str(new.get("region_name", "") or old.get("region_name", "") or "").strip()
        if not region_name:
            region_name = _map_region_name_from_code(region_code)
        if not chosen_name:
            chosen_name = map_id

        out[map_id] = {
            "map_id": map_id,
            "region_code": region_code,
            "region_name": region_name,
            "map_name": chosen_name,
        }
    return out


def _vehicle_load_metadata(force_reload: bool = False, allow_online: bool = False):
    global _VEHICLE_REAL_NAME_MAP_CACHE, _VEHICLE_MAP_DISPLAY_INDEX_CACHE, _VEHICLE_METADATA_CACHE_INFO

    # Quick in-memory hit (lock held only for this tiny section).
    with _VEHICLE_METADATA_CACHE_LOCK:
        if (
            (not force_reload)
            and isinstance(_VEHICLE_REAL_NAME_MAP_CACHE, dict)
            and isinstance(_VEHICLE_MAP_DISPLAY_INDEX_CACHE, dict)
        ):
            info = _VEHICLE_METADATA_CACHE_INFO if isinstance(_VEHICLE_METADATA_CACHE_INFO, dict) else {}
            return _VEHICLE_REAL_NAME_MAP_CACHE, _VEHICLE_MAP_DISPLAY_INDEX_CACHE, info

    # Read local backup without holding the lock.
    name_map = _vehicle_normalize_name_map(_vehicle_read_json_cache(_vehicle_metadata_cache_path("names")))
    map_index = _vehicle_normalize_map_index(_vehicle_read_json_cache(_vehicle_metadata_cache_path("maps")))
    source_tags = []
    if name_map or map_index:
        source_tags.append("backup")

    # Always merge local static ids/names from experiments/truck_trailer_ids.txt.
    try:
        static_map = _vehicle_normalize_name_map(_vehicle_static_name_map(force_reload=force_reload))
    except Exception:
        static_map = {}
    if static_map:
        name_map = _vehicle_merge_name_maps(name_map, static_map)
        source_tags.append("local_ids")

    # Fast path for normal UI: use local backup immediately.
    if (not force_reload) and (not allow_online) and (name_map or map_index):
        with _VEHICLE_METADATA_CACHE_LOCK:
            current_names = _VEHICLE_REAL_NAME_MAP_CACHE if isinstance(_VEHICLE_REAL_NAME_MAP_CACHE, dict) else {}
            current_maps = _VEHICLE_MAP_DISPLAY_INDEX_CACHE if isinstance(_VEHICLE_MAP_DISPLAY_INDEX_CACHE, dict) else {}
            if current_names:
                name_map = _vehicle_merge_name_maps(name_map, current_names)
            if current_maps:
                map_index = _vehicle_merge_map_index(map_index, current_maps)

            _VEHICLE_REAL_NAME_MAP_CACHE = name_map
            _VEHICLE_MAP_DISPLAY_INDEX_CACHE = map_index
            _VEHICLE_METADATA_CACHE_INFO = {
                "source": ",".join(source_tags) if source_tags else "none",
                "name_count": len(name_map),
                "map_count": len(map_index),
            }
            return _VEHICLE_REAL_NAME_MAP_CACHE, _VEHICLE_MAP_DISPLAY_INDEX_CACHE, _VEHICLE_METADATA_CACHE_INFO

    # Potentially slow JS discovery/download/parsing; keep lock released.
    texts = _vehicle_collect_maprunner_js_texts(allow_online=allow_online)
    if texts:
        loc_seed = {}
        try:
            desc_choice = _mr_choose_first_available([_MR_CANONICAL_NAMES["desc"], "desc.js"])
        except Exception:
            desc_choice = None
        try:
            loc_seed = _mr_collect_localization(desc_choice) if desc_choice else {}
        except Exception:
            loc_seed = {}

        parsed_names, parsed_maps = _vehicle_extract_metadata_from_js_texts(texts, localization_seed=loc_seed)
        parsed_names = _vehicle_normalize_name_map(parsed_names)
        parsed_maps = _vehicle_normalize_map_index(parsed_maps)
        if parsed_names:
            name_map = _vehicle_merge_name_maps(name_map, parsed_names)
        if parsed_maps:
            map_index = _vehicle_merge_map_index(map_index, parsed_maps)
        if parsed_names or parsed_maps:
            source_tags.append("online" if allow_online else "objectives_cache")
            _vehicle_write_json_cache(_vehicle_metadata_cache_path("names"), name_map)
            _vehicle_write_json_cache(_vehicle_metadata_cache_path("maps"), map_index)

    # Final cache swap under lock.
    with _VEHICLE_METADATA_CACHE_LOCK:
        current_names = _VEHICLE_REAL_NAME_MAP_CACHE if isinstance(_VEHICLE_REAL_NAME_MAP_CACHE, dict) else {}
        current_maps = _VEHICLE_MAP_DISPLAY_INDEX_CACHE if isinstance(_VEHICLE_MAP_DISPLAY_INDEX_CACHE, dict) else {}
        if current_names:
            name_map = _vehicle_merge_name_maps(name_map, current_names)
        if current_maps:
            map_index = _vehicle_merge_map_index(map_index, current_maps)

        _VEHICLE_REAL_NAME_MAP_CACHE = name_map
        _VEHICLE_MAP_DISPLAY_INDEX_CACHE = map_index
        _VEHICLE_METADATA_CACHE_INFO = {
            "source": ",".join(source_tags) if source_tags else "none",
            "name_count": len(name_map),
            "map_count": len(map_index),
        }
        return _VEHICLE_REAL_NAME_MAP_CACHE, _VEHICLE_MAP_DISPLAY_INDEX_CACHE, _VEHICLE_METADATA_CACHE_INFO


def _vehicle_load_real_name_map(force_reload: bool = False) -> Dict[str, str]:
    name_map, _, _ = _vehicle_load_metadata(force_reload=force_reload, allow_online=False)
    return name_map if isinstance(name_map, dict) else {}


def _vehicle_display_name(type_id: str) -> str:
    t = str(type_id or "").strip()
    if not t:
        return ""
    name_map = _vehicle_load_real_name_map()
    name = ""
    if isinstance(name_map, dict):
        name = str(name_map.get(t, "") or "").strip()
        if not name:
            name = str(name_map.get(t.lower(), "") or "").strip()
        if not name:
            name = str(name_map.get(t.upper(), "") or "").strip()
    if name:
        # Reject low-quality labels from noisy metadata (description text, defaults, etc.).
        if _vehicle_name_quality(name, t) >= 3:
            return name
    return _vehicle_humanize_id(t)


def _vehicle_display_name_for_entry(type_id: str, object_id: str = "") -> str:
    t = str(type_id or "").strip()
    o = str(object_id or "").strip()
    if not t and not o:
        return ""

    def _clean_id(raw: str) -> str:
        x = str(raw or "").strip()
        if not x:
            return ""
        x = re.sub(r"^(?:g_special_|g_|w_)", "", x, flags=re.IGNORECASE)
        x = re.sub(r"(?:_default|_skin_?\d*|_?\d+)$", "", x, flags=re.IGNORECASE)
        return x

    ids = []
    for raw in (t, o):
        rid = str(raw or "").strip()
        if not rid:
            continue
        ids.append(rid)
        ids.append(_clean_id(rid))
        m = re.search(r"(?:^|_)(?:truck|scout)_old_engine_([a-z0-9_]+?)(?:_\d+)?$", rid.lower())
        if m:
            model = str(m.group(1) or "").strip()
            if model:
                ids.append(model)
                ids.append(re.sub(r"([a-z])(\d)", r"\1_\2", model))
                ids.append(re.sub(r"(\d)([a-z])", r"\1_\2", model))

    seen = set()
    candidates = []
    for raw in ids:
        rid = str(raw or "").strip()
        if not rid:
            continue
        lk = rid.lower()
        if lk in seen:
            continue
        seen.add(lk)
        candidates.append(rid)

    def _score(name: str, cid: str) -> int:
        s = _vehicle_name_quality(name, cid)
        low = str(name or "").strip().lower()
        if not low:
            return -100
        if "deleted" in low:
            s -= 5
        if any(tok in low for tok in (" default", "skin ", " old engine", " g truck", " w truck", " g scout", " w scout")):
            s -= 3
        if low.startswith(("g ", "w ")):
            s -= 2
        return s

    best_name = ""
    best_score = -10000
    for cid in candidates:
        nm = _vehicle_display_name(cid)
        sc = _score(nm, cid)
        if sc > best_score:
            best_score = sc
            best_name = nm

    if best_name:
        return best_name
    return _vehicle_display_name(t or o)


def _map_normalize_id(raw: Any) -> str:
    value = str(raw or "").strip().upper()
    if value.startswith("LEVEL_"):
        value = value[6:]
    return value


def _map_region_code_from_map_id(map_id: str) -> str:
    mid = _map_normalize_id(map_id)
    parts = [p for p in mid.split("_") if p]
    if len(parts) >= 2 and parts[0] in {"US", "RU"} and parts[1].isdigit():
        return f"{parts[0]}_{parts[1]}"
    if parts and parts[0] == "TRIAL":
        return "TRIALS"
    return ""


def _map_region_name_from_code(region_code: str) -> str:
    code = str(region_code or "").strip().upper()
    if not code:
        return ""
    if code in REGION_NAME_MAP:
        return REGION_NAME_MAP.get(code, code)
    if code == "TRIALS":
        return "Trials"
    return code


def _map_humanize_slug(value: str) -> str:
    raw = str(value or "").strip()
    if not raw:
        return ""
    token = raw.split("/")[-1]
    token = re.sub(r"[-_]+", " ", token).strip()
    if not token:
        return ""
    return " ".join(w[:1].upper() + w[1:] if w else "" for w in token.split())


def _vehicle_load_map_display_index(force_reload: bool = False) -> Dict[str, Dict[str, str]]:
    _, map_index, _ = _vehicle_load_metadata(force_reload=force_reload, allow_online=False)
    return map_index if isinstance(map_index, dict) else {}


def _map_display_info(map_id: str) -> Dict[str, str]:
    mid = _map_normalize_id(map_id)
    index = _vehicle_load_map_display_index()
    if isinstance(index, dict):
        found = index.get(mid)
        if isinstance(found, dict):
            return {
                "map_id": _map_normalize_id(found.get("map_id", mid)),
                "region_code": str(found.get("region_code", "") or "").upper(),
                "region_name": str(found.get("region_name", "") or "").strip(),
                "map_name": str(found.get("map_name", "") or "").strip() or mid,
            }

    region_code = _map_region_code_from_map_id(mid)
    region_name = _map_region_name_from_code(region_code)
    return {
        "map_id": mid,
        "region_code": region_code,
        "region_name": region_name,
        "map_name": mid,
    }


def _detect_complete_save_slot_from_path(path: str) -> int:
    base = os.path.splitext(os.path.basename(str(path or "")))[0].lower()
    if base == "completesave":
        return 1
    if base == "completesave1":
        return 2
    if base == "completesave2":
        return 3
    if base == "completesave3":
        return 4
    return 1


def _slot_to_sts_prefix(slot: int) -> str:
    try:
        s = int(slot)
    except Exception:
        s = 1
    return "" if s <= 1 else f"{s - 1}_"


def _is_probable_truck_type_id(raw_type_id: Any) -> bool:
    t = str(raw_type_id or "").strip().lower()
    if not t:
        return False
    if "trailer" in t:
        return False
    if not re.fullmatch(r"[a-z0-9_\-./]+", t):
        return False
    base = t.split("/", 1)[0]
    for blocked in _VEHICLE_ID_BLOCKLIST_PARTS:
        if blocked in base:
            return False
    for blocked in _STS_COMPONENT_TYPE_BLOCKLIST_PARTS:
        if blocked in base:
            return False
    parts = [p for p in re.split(r"[_\-]+", base) if p]
    if t in _KNOWN_TRUCK_IDS_DEFAULT:
        return True
    return bool(parts and parts[0] in _VEHICLE_BRAND_HINTS)


def _sts_is_vehicle_or_trailer_type(type_id: str, object_id: str = "") -> bool:
    t = str(type_id or "").strip().lower()
    if not t:
        return False

    base = t.split("/", 1)[0]
    if not re.fullmatch(r"[a-z0-9_\-./]+", t):
        return False
    if len(base) < 3:
        return False
    if base == "skin" or base.startswith("skin_"):
        return False

    static_data = _vehicle_load_static_id_source(force_reload=False)
    static_known = static_data.get("base_ids_lower", set()) if isinstance(static_data, dict) else set()
    if isinstance(static_known, set) and base in static_known:
        return True

    # Accept explicit old-engine world prefab ids early.
    # Example: us_truck_old_engine_avenhorn_a15_0
    if re.search(r"^(?:[a-z]{2,4}_)?(?:truck|scout)_old_engine_[a-z0-9_]+$", base):
        return True

    for blocked in _STS_COMPONENT_TYPE_BLOCKLIST_PARTS:
        if blocked in base:
            return False

    if "trailer" in t:
        return True

    for blocked in _VEHICLE_ID_BLOCKLIST_PARTS:
        if blocked in base:
            return False

    oid_lower = str(object_id or "").strip().lower()
    if oid_lower.startswith("bone") or oid_lower.endswith("_cdt"):
        return False
    if base.startswith(("g_", "w_")) and base.endswith("_default"):
        return False
    if base.startswith("g_special_") and (oid_lower.endswith("_default") or oid_lower.startswith(("w_", "g_"))):
        return False
    if isinstance(static_known, set) and oid_lower in static_known:
        return True

    parts = [p for p in re.split(r"[_\-]+", base) if p]
    if parts and parts[0] in _VEHICLE_BRAND_HINTS:
        return True
    if t in _KNOWN_TRUCK_IDS_DEFAULT:
        return True

    oid = str(object_id or "").upper()
    # GUID-style object IDs in STS are commonly used for movable trucks/trailers.
    # If the type passed blocklists above, accept unknown models too.
    if re.fullmatch(r"\{[0-9A-Fa-f\-]{36}\}", str(object_id or "").strip()):
        return True
    if "TRUCK" in oid or "SCOUT" in oid or "TRAILER" in oid:
        return True

    return False


def _sts_is_denorm_float(value: float) -> bool:
    try:
        v = abs(float(value))
    except Exception:
        return True
    return (v > 0.0) and (v < 1e-20)


def _sts_has_valid_transform_at(data: bytes, coord_off: int) -> bool:
    if not isinstance(coord_off, int):
        return False
    if coord_off < 32 or (coord_off + 12) > len(data):
        return False
    try:
        vals = struct.unpack_from("<8f", data, coord_off - 32)
    except Exception:
        return False
    if not all(math.isfinite(v) for v in vals):
        return False
    n1 = math.sqrt(sum(v * v for v in vals[:4]))
    n2 = math.sqrt(sum(v * v for v in vals[4:8]))
    return (0.75 <= n1 <= 1.25) and (0.75 <= n2 <= 1.25)


def _sts_parse_guid_vehicle_blocks(data: bytes, source_file: str, existing_objects: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """
    Parse "type + empty object id + GUID" STS blocks used by player vehicles/trailers.
    These blocks hold many transforms; we cluster world-space transforms and keep a
    list of coordinate offsets so move/unstuck can shift the whole block safely.
    """
    payload = bytes(data or b"")
    size = len(payload)
    if size < 96:
        return []

    map_info = _map_display_info(_map_id_from_sts_filename(source_file))
    hits = []

    # Find block starts.
    for i in range(size - (2 + 3 + 2 + 1 + 2 + 3)):
        try:
            type_len = struct.unpack_from("<H", payload, i)[0]
        except Exception:
            continue
        if type_len < 3 or type_len > 128:
            continue

        type_beg = i + 2
        type_end = type_beg + type_len
        if type_end + 2 + 1 >= size:
            continue
        if payload[type_end - 1] != 0:
            continue

        type_raw = payload[type_beg:type_end - 1]
        if not type_raw or any((b < 32 or b > 126) for b in type_raw):
            continue
        type_id = type_raw.decode("ascii", errors="ignore").strip()
        if not type_id:
            continue

        obj_len = struct.unpack_from("<H", payload, type_end)[0]
        if obj_len != 1:
            continue
        obj_beg = type_end + 2
        obj_end = obj_beg + obj_len
        if obj_end + 2 >= size or payload[obj_end - 1] != 0:
            continue

        # GUID is usually the next length-prefixed string.
        guid_len = struct.unpack_from("<H", payload, obj_end)[0]
        if guid_len < 3 or guid_len > 80:
            continue
        guid_beg = obj_end + 2
        guid_end = guid_beg + guid_len
        if guid_end > size or payload[guid_end - 1] != 0:
            continue
        guid_raw = payload[guid_beg:guid_end - 1]
        if not guid_raw or any((b < 32 or b > 126) for b in guid_raw):
            continue
        guid = guid_raw.decode("ascii", errors="ignore").strip()
        if not re.fullmatch(r"\{[0-9A-Fa-f\-]{36}\}", guid):
            continue
        if guid.upper() == "{00000000-0000-0000-0000-000000000000}":
            continue

        if not _sts_is_vehicle_or_trailer_type(type_id, guid):
            continue

        hits.append(
            {
                "start_off": int(i),
                "type_id": type_id,
                "guid": guid,
                "type_len_off": int(i),
                "type_len_size": 2,
                "type_beg": int(type_beg),
                "type_end": int(type_end),
                "obj_len_off": int(type_end),
                "obj_len_size": 2,
                "obj_beg": int(obj_beg),
                "obj_end": int(obj_end),
                "guid_len_off": int(obj_end),
                "guid_len_size": 2,
                "guid_beg": int(guid_beg),
                "guid_end": int(guid_end),
                "after_guid_off": int(guid_end),
            }
        )

    if not hits:
        return []

    hits.sort(key=lambda h: int(h.get("start_off", 0)))
    out = []
    existing = list(existing_objects or [])

    for idx, hit in enumerate(hits):
        block_start = int(hit.get("after_guid_off", 0))
        if idx + 1 < len(hits):
            block_end = int(hits[idx + 1].get("start_off", block_start))
        else:
            block_end = min(size, block_start + 24000)
        if block_end <= block_start + 64:
            continue

        candidates = []
        # Byte-wise scan because these transforms are not always 4-byte aligned.
        for coord_off in range(block_start + 32, min(block_end, size - 12)):
            try:
                x, y, z = struct.unpack_from("<fff", payload, coord_off)
            except Exception:
                continue
            if not (math.isfinite(x) and math.isfinite(y) and math.isfinite(z)):
                continue
            if max(abs(x), abs(y), abs(z)) > 5000:
                continue
            if _sts_is_denorm_float(x) or _sts_is_denorm_float(y) or _sts_is_denorm_float(z):
                continue
            # Ignore tiny local/unit vectors; keep only world-like coordinates.
            if max(abs(x), abs(y), abs(z)) < 20.0:
                continue
            if not _sts_has_valid_transform_at(payload, coord_off):
                continue
            # Translation row sanity:
            # [x, y, z, 1.0] and previous row W ~= 0.0
            # keeps us on real transform anchors, avoids false positives in packed data.
            if coord_off < 4 or (coord_off + 16) > size:
                continue
            try:
                prev_w = float(struct.unpack_from("<f", payload, coord_off - 4)[0])
                row_w = float(struct.unpack_from("<f", payload, coord_off + 12)[0])
            except Exception:
                continue
            if not (math.isfinite(prev_w) and math.isfinite(row_w)):
                continue
            if abs(prev_w) > 0.25:
                continue
            if abs(row_w - 1.0) > 0.25:
                continue
            candidates.append((int(coord_off), float(x), float(y), float(z)))

        if not candidates:
            continue

        # Group by rounded position and pick the densest world-space cluster.
        # Tie-break by |x|+|z| so local tiny transforms near origin lose.
        buckets: Dict[Any, List[Any]] = {}
        for c in candidates:
            key = (round(c[1], 1), round(c[2], 1), round(c[3], 1))
            buckets.setdefault(key, []).append(c)
        best_key = max(
            buckets.keys(),
            key=lambda k: (len(buckets.get(k, [])), abs(float(k[0])) + abs(float(k[2]))),
        )
        best_bucket = list(buckets.get(best_key, []))
        if not best_bucket:
            continue

        # Keep edits bounded to the selected cluster only.
        anchor = min(
            best_bucket,
            key=lambda c: abs(int(c[0]) - int(hit.get("start_off", 0))),
        )
        ax, ay, az = float(anchor[1]), float(anchor[2]), float(anchor[3])
        coord_group = list(best_bucket)
        anchor_off = int(anchor[0])
        sorted_unique = sorted({int(c[0]) for c in coord_group})
        coord_offs = [anchor_off] + [off for off in sorted_unique if off != anchor_off]
        if not coord_offs:
            continue

        type_id = str(hit.get("type_id", "") or "")
        guid = str(hit.get("guid", "") or "")

        # For GUID-style entries, GUID itself is the only safe dedupe key.
        # Position/type-based dedupe can hide valid trucks parked close together.
        duplicate = False
        for ex in existing:
            ex_oid = str(ex.get("object_id", "") or "").strip()
            if ex_oid and guid and ex_oid.lower() == guid.lower():
                duplicate = True
                break
        if duplicate:
            continue

        is_trailer = "trailer" in type_id.lower()
        obj = {
            "file": os.path.basename(source_file),
            "map_id": map_info.get("map_id", ""),
            "map_name": map_info.get("map_name", ""),
            "region_code": map_info.get("region_code", ""),
            "region_name": map_info.get("region_name", ""),
            "kind": "Trailer" if is_trailer else "Vehicle",
            "type_id": type_id,
            "name": _vehicle_display_name_for_entry(type_id, guid),
            "object_id": guid,
            "guid": guid,
            "start_off": int(hit.get("start_off", -1)),
            "type_len_off": int(hit.get("type_len_off", -1)),
            "type_len_size": int(hit.get("type_len_size", 0)),
            "type_beg": int(hit.get("type_beg", -1)),
            "type_end": int(hit.get("type_end", -1)),
            "obj_len_off": int(hit.get("obj_len_off", -1)),
            "obj_len_size": int(hit.get("obj_len_size", 0)),
            "obj_beg": int(hit.get("obj_beg", -1)),
            "obj_end": int(hit.get("obj_end", -1)),
            "guid_len_off": int(hit.get("guid_len_off", -1)),
            "guid_len_size": int(hit.get("guid_len_size", 0)),
            "guid_beg": int(hit.get("guid_beg", -1)),
            "guid_end": int(hit.get("guid_end", -1)),
            "coord_off": int(anchor_off),
            "coord_offs": coord_offs,
            "end_off": int(block_end),
            "allow_delete": True,
            "x": float(ax),
            "y": float(ay),
            "z": float(az),
        }
        out.append(obj)
        existing.append(obj)

    return out


def _sts_parse_movable_objects(payload: bytes, source_file: str) -> List[Dict[str, Any]]:
    data = bytes(payload or b"")
    size = len(data)
    if size < 96:
        return []

    out = []
    seen = set()
    i = 0
    min_tail = 48 + 12  # x,y,z float32 after id-string + 48 bytes
    map_info = _map_display_info(_map_id_from_sts_filename(source_file))

    def _try_parse_at(offset: int, len_size: int):
        if len_size == 2:
            if offset + 2 + 3 + 2 + 1 + min_tail > size:
                return None
            type_len = struct.unpack_from("<H", data, offset)[0]
        else:
            if offset + 4 + 3 + 4 + 1 + min_tail > size:
                return None
            type_len = struct.unpack_from("<I", data, offset)[0]

        if type_len < 3 or type_len > 128:
            return None

        type_beg = offset + len_size
        type_end = type_beg + type_len
        if type_end + len_size + 1 + min_tail > size:
            return None
        if data[type_end - 1] != 0:
            return None

        type_raw = data[type_beg:type_end - 1]
        if not type_raw:
            return None
        if any((b < 32 or b > 126) for b in type_raw):
            return None
        type_id = type_raw.decode("ascii", errors="ignore").strip()
        if not type_id:
            return None
        if type_id.lower().startswith("deleted_"):
            return None

        if len_size == 2:
            obj_len = struct.unpack_from("<H", data, type_end)[0]
        else:
            obj_len = struct.unpack_from("<I", data, type_end)[0]
        if obj_len < 1 or obj_len > 196:
            return None

        obj_beg = type_end + len_size
        obj_end = obj_beg + obj_len
        if obj_end + min_tail > size:
            return None
        if data[obj_end - 1] != 0:
            return None

        obj_raw = data[obj_beg:obj_end - 1]
        if any((b < 32 or b > 126) for b in obj_raw):
            return None
        object_id = obj_raw.decode("ascii", errors="ignore").strip()
        if object_id and (object_id.lower().startswith("bone") or object_id.lower().endswith("_cdt")):
            return None

        # Optional GUID string (common in classic movable entries).
        guid_len_off = -1
        guid_len_size = 0
        guid_beg = -1
        guid_end = -1
        guid_value = ""
        try:
            if len_size == 2:
                guid_len = struct.unpack_from("<H", data, obj_end)[0]
            else:
                guid_len = struct.unpack_from("<I", data, obj_end)[0]
            if 3 <= int(guid_len) <= 80:
                gb = obj_end + len_size
                ge = gb + int(guid_len)
                if ge <= size and data[ge - 1] == 0:
                    g_raw = data[gb:ge - 1]
                    if g_raw and all((32 <= b <= 126) for b in g_raw):
                        g_txt = g_raw.decode("ascii", errors="ignore").strip()
                        if re.fullmatch(r"\{[0-9A-Fa-f\-]{36}\}", g_txt):
                            if g_txt.upper() == "{00000000-0000-0000-0000-000000000000}":
                                g_txt = ""
                            guid_len_off = int(obj_end)
                            guid_len_size = int(len_size)
                            guid_beg = int(gb)
                            guid_end = int(ge)
                            guid_value = g_txt
        except Exception:
            pass

        object_or_guid = guid_value or object_id
        if not object_or_guid:
            return None
        # Keep showing legacy "deleted_entry_*" rows when a valid GUID still exists,
        # so user can finalize true deletion.
        if object_id.lower().startswith("deleted_entry_") and not guid_value:
            return None

        if not _sts_is_vehicle_or_trailer_type(type_id, object_or_guid):
            return None

        def _read_valid_coord(off: int):
            if off < 0 or (off + 12) > size:
                return None
            try:
                x0, y0, z0 = struct.unpack_from("<fff", data, off)
            except Exception:
                return None
            if not (math.isfinite(x0) and math.isfinite(y0) and math.isfinite(z0)):
                return None
            if max(abs(x0), abs(y0), abs(z0)) > 5_000_000:
                return None
            if _sts_is_denorm_float(x0) or _sts_is_denorm_float(y0) or _sts_is_denorm_float(z0):
                return None
            if max(abs(x0), abs(y0), abs(z0)) < 20.0:
                return None
            if not _sts_has_valid_transform_at(data, off):
                return None
            # Translation row sanity:
            # [x, y, z, 1.0] and previous row W ~= 0.0
            # avoids shifted/adjacent float triplets in the same block.
            if off < 4 or (off + 16) > size:
                return None
            try:
                prev_w = float(struct.unpack_from("<f", data, off - 4)[0])
                row_w = float(struct.unpack_from("<f", data, off + 12)[0])
            except Exception:
                return None
            if (not math.isfinite(prev_w)) or (not math.isfinite(row_w)):
                return None
            if abs(prev_w) > 0.25:
                return None
            if abs(row_w - 1.0) > 0.25:
                return None
            return (float(x0), float(y0), float(z0))

        coord_off = -1
        x = y = z = 0.0

        # Fast-path around the legacy fixed offset.
        base = int(obj_end + 48)
        for cand in (
            base,
            base - 4,
            base + 4,
            base - 8,
            base + 8,
            base - 12,
            base + 12,
            base - 16,
            base + 16,
        ):
            xyz0 = _read_valid_coord(int(cand))
            if xyz0 is None:
                continue
            coord_off = int(cand)
            x, y, z = xyz0
            break

        # Fallback for nested/variant classic entries:
        # search ahead in a bounded window for the first valid world transform.
        if coord_off < 0:
            scan_beg = max(32, int(obj_end + 16))
            scan_end = min(size - 12, int(obj_end + 8192))
            for cand in range(scan_beg, scan_end):
                xyz0 = _read_valid_coord(int(cand))
                if xyz0 is None:
                    continue
                coord_off = int(cand)
                x, y, z = xyz0
                break

        if coord_off < 0:
            return None

        return {
            "type_id": type_id,
            "object_id": object_id,
            "start_off": offset,
            "type_len_off": int(offset),
            "type_len_size": int(len_size),
            "type_beg": int(type_beg),
            "type_end": int(type_end),
            "obj_len_off": int(type_end),
            "obj_len_size": int(len_size),
            "obj_beg": int(obj_beg),
            "obj_end": int(obj_end),
            "guid": str(guid_value or ""),
            "guid_len_off": int(guid_len_off),
            "guid_len_size": int(guid_len_size),
            "guid_beg": int(guid_beg),
            "guid_end": int(guid_end),
            "coord_off": coord_off,
            "x": float(x),
            "y": float(y),
            "z": float(z),
            "entry_min_end": int(coord_off + 12),
            "next_off": obj_end,
        }

    while i + 2 + 3 + 2 + 1 + min_tail <= size:
        parsed = _try_parse_at(i, 2)
        if parsed is None:
            parsed = _try_parse_at(i, 4)
        if parsed is None:
            i += 1
            continue

        type_id = parsed["type_id"]
        object_id = parsed["object_id"]
        coord_off = parsed["coord_off"]
        x, y, z = parsed["x"], parsed["y"], parsed["z"]

        key = (coord_off, type_id, object_id)
        if key not in seen:
            seen.add(key)
            is_trailer = ("trailer" in type_id.lower()) or ("TRAILER" in object_id.upper())
            out.append(
                {
                    "file": os.path.basename(source_file),
                    "map_id": map_info.get("map_id", ""),
                    "map_name": map_info.get("map_name", ""),
                    "region_code": map_info.get("region_code", ""),
                    "region_name": map_info.get("region_name", ""),
                    "kind": "Trailer" if is_trailer else "Vehicle",
                    "type_id": type_id,
                    "name": _vehicle_display_name_for_entry(type_id, object_id),
                    "object_id": object_id,
                    "start_off": int(parsed.get("start_off", -1)),
                    "type_len_off": int(parsed.get("type_len_off", -1)),
                    "type_len_size": int(parsed.get("type_len_size", 0)),
                    "type_beg": int(parsed.get("type_beg", -1)),
                    "type_end": int(parsed.get("type_end", -1)),
                    "obj_len_off": int(parsed.get("obj_len_off", -1)),
                    "obj_len_size": int(parsed.get("obj_len_size", 0)),
                    "obj_beg": int(parsed.get("obj_beg", -1)),
                    "obj_end": int(parsed.get("obj_end", -1)),
                    "guid": str(parsed.get("guid", "") or ""),
                    "guid_len_off": int(parsed.get("guid_len_off", -1)),
                    "guid_len_size": int(parsed.get("guid_len_size", 0)),
                    "guid_beg": int(parsed.get("guid_beg", -1)),
                    "guid_end": int(parsed.get("guid_end", -1)),
                    "coord_off": coord_off,
                    "coord_offs": [int(coord_off)],
                    "end_off": int(parsed.get("entry_min_end", coord_off + 12)),
                    "allow_delete": True,
                    "x": x,
                    "y": y,
                    "z": z,
                }
            )

        i = max(i + 1, int(parsed.get("next_off", i + 1)))

    # Merge additional vehicle/trailer blocks (GUID-style entries used by player vehicles).
    try:
        extras = _sts_parse_guid_vehicle_blocks(data, source_file, out)
        if extras:
            out.extend(extras)
    except Exception:
        pass

    # Collapse duplicate representations of the same world object.
    # Some STS files include component/default aliases pointing to the same transform.
    # Keep the best-looking row per GUID or per position cluster.
    try:
        def _entry_quality(obj: Dict[str, Any]) -> int:
            type_id = str(obj.get("type_id", "") or "").strip().lower()
            object_id = str(obj.get("object_id", "") or "").strip().lower()
            name = str(obj.get("name", "") or "").strip().lower()
            score = 0
            if re.fullmatch(r"\{[0-9A-Fa-f\-]{36}\}", str(obj.get("guid", "") or "")):
                score += 8
            if ("trailer" in type_id) or _is_probable_truck_type_id(type_id):
                score += 4
            score += int(_vehicle_name_quality(name, type_id))
            if any(tok in type_id for tok in ("_default", "skin", "deleted")):
                score -= 4
            if "_old_engine_" in type_id:
                score -= 3
            if type_id.startswith("g_special_"):
                score -= 3
            if any(tok in object_id for tok in ("_default", "skin", "deleted")):
                score -= 3
            if any(tok in name for tok in (" default", "skin ", "deleted", " old engine")):
                score -= 2
            if type_id.startswith(("g_", "w_")):
                score -= 3
            return score

        chosen = {}
        order = []
        for obj in out:
            if not isinstance(obj, dict):
                continue
            kind = str(obj.get("kind", "") or "").strip().lower()
            guid = str(obj.get("guid", "") or "").strip().lower()
            try:
                x = round(float(obj.get("x", 0.0)), 2)
                y = round(float(obj.get("y", 0.0)), 2)
                z = round(float(obj.get("z", 0.0)), 2)
            except Exception:
                x = y = z = 0.0

            if re.fullmatch(r"\{[0-9A-Fa-f\-]{36}\}", guid):
                key = ("guid", guid)
            else:
                key = ("pos", kind, x, y, z)

            prev = chosen.get(key)
            if prev is None:
                chosen[key] = obj
                order.append(key)
                continue
            if _entry_quality(obj) > _entry_quality(prev):
                chosen[key] = obj

        out = [chosen[k] for k in order if k in chosen]

        # Second pass: collapse leftovers that still share the same position.
        # This catches GUID/non-GUID aliases of the same visible object.
        chosen2 = {}
        order2 = []
        for obj in out:
            if not isinstance(obj, dict):
                continue
            kind = str(obj.get("kind", "") or "").strip().lower()
            try:
                x = round(float(obj.get("x", 0.0)), 2)
                y = round(float(obj.get("y", 0.0)), 2)
                z = round(float(obj.get("z", 0.0)), 2)
            except Exception:
                x = y = z = 0.0
            key2 = ("pos", kind, x, y, z)
            prev = chosen2.get(key2)
            if prev is None:
                chosen2[key2] = obj
                order2.append(key2)
                continue
            if _entry_quality(obj) > _entry_quality(prev):
                chosen2[key2] = obj

        out = [chosen2[k] for k in order2 if k in chosen2]
    except Exception:
        pass

    # Best-effort full entry boundaries for delete:
    # use next parsed entry start as end when available, otherwise keep minimal end.
    try:
        ordered = [
            o
            for o in out
            if isinstance(o.get("start_off"), int)
            and int(o.get("start_off")) >= 0
        ]
        ordered.sort(key=lambda o: int(o.get("start_off", 0)))
        for idx, obj in enumerate(ordered):
            try:
                min_end = int(obj.get("end_off", 0))
            except Exception:
                min_end = 0
            if min_end <= int(obj.get("start_off", 0)):
                min_end = int(obj.get("coord_off", 0)) + 12

            if idx + 1 < len(ordered):
                next_start = int(ordered[idx + 1].get("start_off", min_end))
                if next_start > min_end:
                    obj["end_off"] = next_start
                else:
                    obj["end_off"] = min_end
            else:
                obj["end_off"] = min_end
    except Exception:
        pass

    return out


def _sts_load_file(path: str) -> Dict[str, Any]:
    with open(path, "rb") as f:
        raw = f.read()
    if len(raw) < 6:
        raise ValueError(f"STS file too small: {os.path.basename(path)}")

    declared_size = struct.unpack_from("<I", raw, 0)[0]
    dec = zlib.decompressobj()
    payload = dec.decompress(raw[4:])
    try:
        payload += dec.flush()
    except Exception:
        pass
    trailer = bytes(dec.unused_data or b"")
    return {
        "path": path,
        "declared_size": int(declared_size),
        "payload": bytearray(payload),
        # Preserve bytes after zlib stream (game expects them).
        "trailer": trailer,
    }


def _sts_write_file(path: str, payload: bytes, trailer: bytes = b""):
    data = bytes(payload or b"")
    comp = zlib.compress(data)
    tail = bytes(trailer or b"")
    with open(path, "wb") as f:
        f.write(struct.pack("<I", len(data)))
        f.write(comp)
        if tail:
            f.write(tail)


def _map_id_from_sts_filename(path_or_name: str) -> str:
    base = os.path.splitext(os.path.basename(str(path_or_name or "")))[0].lower()
    m = re.match(r"^(?:\d+_)?sts_level_(.+)$", base)
    if not m:
        return ""
    return m.group(1)


def _list_sts_files_for_slot_region(save_folder: str, slot: int, region_code: str) -> List[str]:
    if not os.path.isdir(save_folder):
        return []

    region = str(region_code or "").strip().lower()
    prefix = _slot_to_sts_prefix(slot).lower()
    target_prefix = f"{prefix}sts_level_"
    out = []
    try:
        names = sorted(os.listdir(save_folder))
    except Exception:
        return []

    for name in names:
        low = name.lower()
        if not (low.startswith(target_prefix) and (low.endswith(".cfg") or low.endswith(".dat"))):
            continue
        map_id = _map_id_from_sts_filename(name)
        if not map_id:
            continue
        if region and region != "all" and not map_id.startswith(region + "_"):
            continue
        out.append(os.path.join(save_folder, name))

    return out


# TAB: Vehicles (launch_gui -> tab_vehicles)
def create_vehicles_tab(tab, save_path_var):
    # ---------------------------------------------------------------------
    # STS controls
    # ---------------------------------------------------------------------
    sts_state = {
        "files": {},
        "objects": [],
        "row_to_obj": {},
        "backed_up_files": set(),
        "load_token": 0,
        "is_loading": False,
        "loaded_save_path": "",
        "loaded_save_mtime": None,
    }
    metadata_state = {
        "refresh_running": False,
        "refresh_done": False,
    }
    sts_state["raw_objects"] = []

    _GROUP_AXIS_TOL = 1.0
    _GROUP_DIST_TOL = 1.35

    def _obj_num(obj: Dict[str, Any], key: str) -> float:
        try:
            return float(obj.get(key, 0.0))
        except Exception:
            return 0.0

    def _obj_group_key(obj: Dict[str, Any]):
        file_path = str(obj.get("file_path", "") or "").strip().lower()
        kind = str(obj.get("kind", "") or "").strip().lower()
        map_id = str(obj.get("map_id", "") or "").strip().lower()
        # Group by resolved display name first; fallback to type id.
        name = str(obj.get("name", "") or "").strip().lower()
        if not name:
            name = str(obj.get("type_id", "") or "").strip().lower()
        return (file_path, kind, map_id, name)

    def _obj_is_close(a: Dict[str, Any], b: Dict[str, Any]) -> bool:
        ax, ay, az = _obj_num(a, "x"), _obj_num(a, "y"), _obj_num(a, "z")
        bx, by, bz = _obj_num(b, "x"), _obj_num(b, "y"), _obj_num(b, "z")
        dx = abs(ax - bx)
        dy = abs(ay - by)
        dz = abs(az - bz)
        if dx > _GROUP_AXIS_TOL or dy > _GROUP_AXIS_TOL or dz > _GROUP_AXIS_TOL:
            return False
        return ((dx * dx) + (dy * dy) + (dz * dz)) <= (_GROUP_DIST_TOL * _GROUP_DIST_TOL)

    def _obj_anchor_quality(obj: Dict[str, Any]) -> int:
        score = 0
        guid = str(obj.get("guid", "") or "").strip()
        oid = str(obj.get("object_id", "") or "").strip()
        if re.fullmatch(r"\{[0-9A-Fa-f\-]{36}\}", guid):
            score += 8
        if re.fullmatch(r"\{[0-9A-Fa-f\-]{36}\}", oid):
            score += 6
        if oid and (not oid.lower().startswith("deleted")):
            score += 2
        score += int(_vehicle_name_quality(str(obj.get("name", "") or ""), str(obj.get("type_id", "") or "")))
        return score

    def _build_grouped_objects_from_raw(raw_objects: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        buckets = {}
        for obj in raw_objects or []:
            if not isinstance(obj, dict):
                continue
            buckets.setdefault(_obj_group_key(obj), []).append(obj)

        grouped = []
        for _k, items in buckets.items():
            if not items:
                continue
            used = [False] * len(items)
            for i, base in enumerate(items):
                if used[i]:
                    continue
                used[i] = True
                cluster = [base]
                changed = True
                while changed:
                    changed = False
                    for j, cand in enumerate(items):
                        if used[j]:
                            continue
                        if any(_obj_is_close(cand, cur) for cur in cluster):
                            used[j] = True
                            cluster.append(cand)
                            changed = True
                if len(cluster) <= 1:
                    grouped.append(base)
                    continue
                anchor = max(cluster, key=_obj_anchor_quality)
                disp = dict(anchor)
                disp["is_group"] = True
                disp["group_members"] = list(cluster)
                disp["group_anchor_obj"] = anchor
                disp["group_size"] = int(len(cluster))
                grouped.append(disp)

        grouped.sort(
            key=lambda o: (
                str(o.get("region_name", "")),
                str(o.get("map_name", "")),
                str(o.get("map_id", "")),
                str(o.get("file", "")),
                str(o.get("kind", "")),
                str(o.get("name", "")),
                _obj_num(o, "x"),
                _obj_num(o, "z"),
            )
        )
        return grouped

    def _rebuild_grouped_objects():
        raw = sts_state.get("raw_objects", [])
        sts_state["objects"] = _build_grouped_objects_from_raw(raw if isinstance(raw, list) else [])

    top = ttk.Frame(tab)
    top.pack(fill="x", padx=10, pady=(10, 6))

    ttk.Label(top, text="Type:").pack(side="left")
    type_filter_var = tk.StringVar(value="All")
    type_filter_cb = ttk.Combobox(top, textvariable=type_filter_var, state="readonly", width=10, values=["All"])
    type_filter_cb.pack(side="left", padx=(4, 8))

    ttk.Label(top, text="Region:").pack(side="left")
    region_filter_var = tk.StringVar(value="All")
    region_filter_cb = ttk.Combobox(top, textvariable=region_filter_var, state="readonly", width=20, values=["All"])
    region_filter_cb.pack(side="left", padx=(4, 8))

    ttk.Label(top, text="Map:").pack(side="left")
    map_filter_var = tk.StringVar(value="All")
    map_filter_cb = ttk.Combobox(top, textvariable=map_filter_var, state="readonly", width=24, values=["All"])
    map_filter_cb.pack(side="left", padx=(4, 8))

    ttk.Label(top, text="Name:").pack(side="left")
    name_filter_var = tk.StringVar(value="")
    name_filter_entry = ttk.Entry(top, textvariable=name_filter_var, width=22)
    name_filter_entry.pack(side="left", padx=(4, 0))

    sts_status_var = tk.StringVar(value="Select a save to load STS objects.")
    ttk.Label(tab, textvariable=sts_status_var).pack(fill="x", padx=10, pady=(0, 6))

    tree_wrap = tk.Frame(tab, bg="#f0f0f0", bd=0, highlightthickness=0)
    tree_wrap.pack(fill="both", expand=True, padx=10, pady=(0, 6))

    cols = ("kind", "name", "region", "map", "x", "y", "z")
    try:
        _vpalette = _get_effective_theme(_is_dark_mode_active())
    except Exception:
        _vpalette = {}
    _tree_fg = str((_vpalette.get("fg") if isinstance(_vpalette, dict) else "") or "#000000")
    _tree_empty_bg = "#f0f0f0"
    _tree_sel_bg = str((_vpalette.get("accent") if isinstance(_vpalette, dict) else "") or "#4A90E2")
    _tree_sel_fg = str((_vpalette.get("accent_fg") if isinstance(_vpalette, dict) else "") or "#FFFFFF")
    _head_bg = str((_vpalette.get("button_bg") if isinstance(_vpalette, dict) else "") or STRIPE_B)
    _head_active_bg = str((_vpalette.get("button_active_bg") if isinstance(_vpalette, dict) else "") or _head_bg)
    try:
        tree_wrap.configure(bg=_tree_empty_bg)
    except Exception:
        pass
    try:
        _vstyle = ttk.Style()
        _vstyle.configure(
            "Vehicles.Treeview",
            rowheight=30,
            background=_tree_empty_bg,
            fieldbackground=_tree_empty_bg,
            foreground=_tree_fg,
        )
        _vstyle.map(
            "Vehicles.Treeview",
            background=[("selected", _tree_sel_bg)],
            foreground=[("selected", _tree_sel_fg)],
        )
        _vstyle.configure("Vehicles.Treeview.Heading", background=_head_bg, foreground=_tree_fg)
        _vstyle.map("Vehicles.Treeview.Heading", background=[("active", _head_active_bg)])
    except Exception:
        pass
    tree = ttk.Treeview(tree_wrap, columns=cols, show="headings", selectmode="extended", style="Vehicles.Treeview")
    headings = {
        "kind": "Type",
        "name": "Name",
        "region": "Region",
        "map": "Map",
        "x": "X",
        "y": "Y",
        "z": "Z",
    }
    widths = {
        "kind": 72,
        "name": 240,
        "region": 150,
        "map": 180,
        "x": 78,
        "y": 78,
        "z": 78,
    }
    for c in cols:
        tree.heading(c, text=headings[c])
        tree.column(c, width=widths[c], anchor="w")
    try:
        tree.tag_configure("even", background=STRIPE_B)
        tree.tag_configure("odd", background=STRIPE_A)
        tree.tag_configure("filler", background="#f0f0f0")
    except Exception:
        pass

    yscroll = ttk.Scrollbar(tree_wrap, orient="vertical", command=tree.yview)
    xscroll = ttk.Scrollbar(tree_wrap, orient="horizontal", command=tree.xview)
    tree.configure(yscrollcommand=yscroll.set, xscrollcommand=xscroll.set)
    tree.grid(row=0, column=0, sticky="nsew")
    yscroll.grid(row=0, column=1, sticky="ns")
    xscroll.grid(row=1, column=0, sticky="ew")
    tree_wrap.grid_rowconfigure(0, weight=1)
    tree_wrap.grid_columnconfigure(0, weight=1)
    try:
        tree.configure(takefocus=0)
    except Exception:
        pass

    edit_row = ttk.Frame(tab)
    edit_row.pack(fill="x", padx=10, pady=(0, 8))

    def _attach_vehicles_hover_tooltip(anchor_widget, tooltip_text):
        tip_state = {"win": None, "job": None}

        def _cancel_job():
            job = tip_state.get("job")
            if job is not None:
                try:
                    anchor_widget.after_cancel(job)
                except Exception:
                    pass
                tip_state["job"] = None

        def _hide(_event=None):
            _cancel_job()
            tip = tip_state.get("win")
            if tip is not None:
                try:
                    tip.destroy()
                except Exception:
                    pass
                tip_state["win"] = None

        def _show_now():
            _hide()
            try:
                tip = tk.Toplevel(anchor_widget)
                tip.wm_overrideredirect(True)
                try:
                    tip.withdraw()
                except Exception:
                    pass
                try:
                    tip.attributes("-topmost", True)
                except Exception:
                    pass
                x = int(anchor_widget.winfo_rootx() + anchor_widget.winfo_width() + 8)
                y = int(anchor_widget.winfo_rooty() + anchor_widget.winfo_height() + 6)
                tip.geometry(f"+{x}+{y}")
                tk.Label(
                    tip,
                    text=str(tooltip_text or ""),
                    justify="left",
                    wraplength=520,
                    bg="#fffbe6",
                    fg="black",
                    relief="solid",
                    bd=1,
                    padx=8,
                    pady=6,
                ).pack()
                tip_state["win"] = tip
                try:
                    tip.deiconify()
                except Exception:
                    pass
            except Exception:
                _hide()

        def _schedule_show(_event=None):
            _cancel_job()
            try:
                tip_state["job"] = anchor_widget.after(260, _show_now)
            except Exception:
                _show_now()

        anchor_widget.bind("<Enter>", _schedule_show, add="+")
        anchor_widget.bind("<Leave>", _hide, add="+")
        anchor_widget.bind("<ButtonPress>", _hide, add="+")
        anchor_widget.bind("<FocusOut>", _hide, add="+")

    vehicles_info_badge = tk.Label(
        top,
        text="i",
        width=2,
        relief="ridge",
        bd=1,
        highlightthickness=0,
        cursor="question_arrow",
        bg="#d32f2f",
        fg="#ffffff",
    )
    vehicles_info_badge.pack(side="right", padx=(8, 0))
    _attach_vehicles_hover_tooltip(
        vehicles_info_badge,
        "Use with caution. These actions can cause serious save issues. Make sure backups are enabled and be ready to restore a backup if something goes wrong. The safest use is selecting one entry at a time and lifting by +2 to +5, or deleting a single entry. Large bulk edits (especially setting many trucks/trailers to the same XYZ) can produce broken or unstable results.",
    )

    ttk.Label(edit_row, text="Lift Y by:").pack(side="left")
    lift_var = tk.StringVar(value="2.0")
    ttk.Entry(edit_row, textvariable=lift_var, width=8).pack(side="left", padx=(6, 12))

    ttk.Label(edit_row, text="X:").pack(side="left")
    x_var = tk.StringVar()
    ttk.Entry(edit_row, textvariable=x_var, width=12).pack(side="left", padx=(4, 8))

    ttk.Label(edit_row, text="Y:").pack(side="left")
    y_var = tk.StringVar()
    ttk.Entry(edit_row, textvariable=y_var, width=12).pack(side="left", padx=(4, 8))

    ttk.Label(edit_row, text="Z:").pack(side="left")
    z_var = tk.StringVar()
    ttk.Entry(edit_row, textvariable=z_var, width=12).pack(side="left", padx=(4, 12))

    filter_zero_var = tk.BooleanVar(value=True)
    _tree_refresh_guard = {"busy": False}
    _tree_resize_job = {"id": None}

    def _row_values(obj: Dict[str, Any]):
        return (
            obj.get("kind", ""),
            obj.get("name", ""),
            obj.get("region_name", ""),
            obj.get("map_name", "") or obj.get("map_id", ""),
            f"{float(obj.get('x', 0.0)):.3f}",
            f"{float(obj.get('y', 0.0)):.3f}",
            f"{float(obj.get('z', 0.0)):.3f}",
        )

    def _set_combo_values(cb: ttk.Combobox, var: tk.StringVar, values: List[str]):
        vals = values if values else ["All"]
        cb["values"] = vals
        current = str(var.get() or "").strip()
        if current not in vals:
            var.set(vals[0])

    def _iter_filtered_objects(apply_map_filter: bool = True):
        selected_type = str(type_filter_var.get() or "All").strip().lower()
        selected_region = str(region_filter_var.get() or "All").strip().lower()
        selected_map = str(map_filter_var.get() or "All").strip().lower()
        name_query = str(name_filter_var.get() or "").strip().lower()

        for obj in sts_state.get("objects", []):
            if bool(filter_zero_var.get()):
                try:
                    ox = float(obj.get("x", 0.0))
                    oy = float(obj.get("y", 0.0))
                    oz = float(obj.get("z", 0.0))
                except Exception:
                    ox = oy = oz = 0.0
                if abs(ox) < 1e-9 and abs(oy) < 1e-9 and abs(oz) < 1e-9:
                    continue

            kind = str(obj.get("kind", "") or "").strip().lower()
            region = str(obj.get("region_name", "") or "").strip().lower()
            map_name = str(obj.get("map_name", "") or obj.get("map_id", "") or "").strip().lower()
            disp_name = str(obj.get("name", "") or "").strip().lower()
            type_id = str(obj.get("type_id", "") or "").strip().lower()
            object_id = str(obj.get("object_id", "") or "").strip()
            # Name filter should be based on real display names only.
            resolved_name = (
                str(_vehicle_display_name_for_entry(type_id, object_id) or "").strip().lower()
                if (type_id or object_id)
                else ""
            )

            if selected_type != "all" and kind != selected_type:
                continue
            if selected_region != "all" and region != selected_region:
                continue
            if apply_map_filter and selected_map != "all" and map_name != selected_map:
                continue
            if name_query and (name_query not in disp_name) and (name_query not in resolved_name):
                continue
            yield obj

    def _refresh_filter_values():
        objs = sts_state.get("objects", []) if isinstance(sts_state.get("objects"), list) else []
        type_values = ["All"] + sorted({str(o.get("kind", "") or "").strip() for o in objs if str(o.get("kind", "") or "").strip()})
        region_values = ["All"] + sorted({str(o.get("region_name", "") or "").strip() for o in objs if str(o.get("region_name", "") or "").strip()})
        _set_combo_values(type_filter_cb, type_filter_var, type_values)
        _set_combo_values(region_filter_cb, region_filter_var, region_values)

        filtered = list(_iter_filtered_objects(apply_map_filter=False))

        map_values = ["All"] + sorted(
            {
                str(o.get("map_name", "") or o.get("map_id", "") or "").strip()
                for o in filtered
                if str(o.get("map_name", "") or o.get("map_id", "") or "").strip()
            }
        )
        _set_combo_values(map_filter_cb, map_filter_var, map_values)

    def _refresh_tree():
        if _tree_refresh_guard.get("busy"):
            return
        _tree_refresh_guard["busy"] = True
        try:
            for iid in tree.get_children():
                tree.delete(iid)
            sts_state["row_to_obj"] = {}

            real_count = 0
            for row_idx, obj in enumerate(_iter_filtered_objects(apply_map_filter=True)):
                iid = f"row_{row_idx}"
                tag = "even" if (row_idx % 2 == 0) else "odd"
                tree.insert("", "end", iid=iid, values=_row_values(obj), tags=(tag,))
                sts_state["row_to_obj"][iid] = obj
                real_count += 1

            # Fallback for Windows/native themes that may ignore Treeview fieldbackground:
            # paint remaining visible area with explicit #f0f0f0 filler rows.
            try:
                row_h = 30
                view_h = int(tree.winfo_height() or 0)
                visible_rows = max(0, int(view_h / row_h) + 1)
                filler_needed = max(0, visible_rows - real_count)
                for i in range(filler_needed):
                    tree.insert(
                        "",
                        "end",
                        iid=f"filler_{i}",
                        values=("", "", "", "", "", "", ""),
                        tags=("filler",),
                    )
            except Exception:
                pass
        finally:
            _tree_refresh_guard["busy"] = False

    def _schedule_tree_resize_refresh(_event=None):
        try:
            if _tree_resize_job.get("id") is not None:
                tab.after_cancel(_tree_resize_job["id"])
        except Exception:
            pass
        try:
            _tree_resize_job["id"] = tab.after(70, lambda: (_tree_resize_job.__setitem__("id", None), _refresh_tree()))
        except Exception:
            _refresh_tree()

    def _relabel_loaded_objects_from_metadata():
        changed = False
        objs = sts_state.get("raw_objects", [])
        if not isinstance(objs, list) or not objs:
            return
        for obj in objs:
            if not isinstance(obj, dict):
                continue
            type_id = str(obj.get("type_id", "") or "").strip()
            object_id = str(obj.get("object_id", "") or "").strip()
            if type_id or object_id:
                new_name = _vehicle_display_name_for_entry(type_id, object_id)
                if new_name and new_name != str(obj.get("name", "") or ""):
                    obj["name"] = new_name
                    changed = True

            map_id = str(obj.get("map_id", "") or "").strip()
            if map_id:
                info = _map_display_info(map_id)
                new_region = str(info.get("region_name", "") or "").strip()
                new_map = str(info.get("map_name", "") or "").strip()
                if new_region and new_region != str(obj.get("region_name", "") or ""):
                    obj["region_name"] = new_region
                    changed = True
                if new_map and new_map != str(obj.get("map_name", "") or ""):
                    obj["map_name"] = new_map
                    changed = True

        if changed:
            _rebuild_grouped_objects()
            _refresh_filter_values()
            _refresh_tree()

    def _refresh_vehicle_metadata_in_background(force: bool = False):
        if metadata_state.get("refresh_running"):
            return
        if metadata_state.get("refresh_done") and (not force):
            return
        # Never compete with STS parsing; refresh metadata once STS is done.
        if sts_state.get("is_loading"):
            return

        metadata_state["refresh_running"] = True

        def _worker():
            ok = False
            try:
                _vehicle_load_metadata(force_reload=True, allow_online=True)
                ok = True
            except Exception:
                ok = False

            def _apply():
                metadata_state["refresh_running"] = False
                if not ok:
                    return
                metadata_state["refresh_done"] = True
                _relabel_loaded_objects_from_metadata()

            try:
                tab.after(0, _apply)
            except Exception:
                pass

        threading.Thread(target=_worker, daemon=True).start()

    def _clear_sts_view(message: str):
        sts_state["load_token"] = int(sts_state.get("load_token", 0)) + 1
        sts_state["is_loading"] = False
        sts_state["loaded_save_path"] = ""
        sts_state["loaded_save_mtime"] = None
        sts_state["files"] = {}
        sts_state["raw_objects"] = []
        sts_state["objects"] = []
        sts_state["row_to_obj"] = {}
        _refresh_filter_values()
        _refresh_tree()
        sts_status_var.set(message)

    def _load_sts_objects(manual: bool = True):
        if sts_state.get("is_loading"):
            if manual:
                return show_info("Vehicles", "STS loading is already in progress.")
            return

        save_path = save_path_var.get()
        if not save_path or not os.path.exists(save_path):
            if manual:
                return messagebox.showerror("Error", "CompleteSave file not found.")
            sts_status_var.set("Select a valid save file to load STS objects.")
            return
        try:
            save_mtime = float(os.path.getmtime(save_path))
        except Exception:
            save_mtime = None

        # Keep already loaded data when save file didn't change.
        if (
            (not manual)
            and str(sts_state.get("loaded_save_path", "") or "") == str(save_path)
            and sts_state.get("loaded_save_mtime", None) == save_mtime
        ):
            _refresh_filter_values()
            _refresh_tree()
            return

        folder = os.path.dirname(save_path)
        slot_n = _detect_complete_save_slot_from_path(save_path)
        sts_files = _list_sts_files_for_slot_region(folder, slot_n, "ALL")
        if not sts_files:
            _clear_sts_view(f"No STS files found for save slot {slot_n}.")
            sts_state["loaded_save_path"] = save_path
            sts_state["loaded_save_mtime"] = save_mtime
            return

        token = int(sts_state.get("load_token", 0)) + 1
        sts_state["load_token"] = token
        sts_state["is_loading"] = True
        sts_state["files"] = {}
        sts_state["raw_objects"] = []
        sts_state["objects"] = []
        sts_state["row_to_obj"] = {}
        _refresh_filter_values()
        _refresh_tree()
        sts_status_var.set(f"Loading STS objects... 0/{len(sts_files)} files (slot {slot_n})")

        progress = {
            "loaded_files": 0,
            "loaded_raw_objects": 0,
            "loaded_grouped_objects": 0,
            "errors": 0,
        }

        def _is_current() -> bool:
            return token == int(sts_state.get("load_token", -1))

        def _apply_chunk(fpath: str, fdata: Dict[str, Any], objs: List[Dict[str, Any]], err_text: str = ""):
            if not _is_current():
                return
            if err_text:
                progress["errors"] += 1
            else:
                sts_state["files"][fpath] = fdata
                for obj in objs:
                    obj["file_path"] = fpath
                sts_state["raw_objects"].extend(objs)
                _rebuild_grouped_objects()
                progress["loaded_files"] = int(progress.get("loaded_files", 0)) + 1
                progress["loaded_raw_objects"] = len(sts_state.get("raw_objects", []))
                progress["loaded_grouped_objects"] = len(sts_state.get("objects", []))

            _refresh_filter_values()
            _refresh_tree()
            processed = int(progress.get("loaded_files", 0)) + int(progress.get("errors", 0))
            sts_status_var.set(
                f"Loading STS objects... {processed}/{len(sts_files)} files"
                f" | entries: {progress.get('loaded_grouped_objects', 0)}"
                f" (raw: {progress.get('loaded_raw_objects', 0)})"
                + (f" | failed: {progress.get('errors', 0)}" if progress.get("errors", 0) else "")
            )

        def _finish_loading():
            if not _is_current():
                return
            try:
                sts_state["raw_objects"].sort(
                    key=lambda o: (
                        str(o.get("region_name", "")),
                        str(o.get("map_name", "")),
                        str(o.get("map_id", "")),
                        str(o.get("file", "")),
                        str(o.get("kind", "")),
                        str(o.get("name", "")),
                        str(o.get("object_id", "")),
                    )
                )
            except Exception:
                pass
            _rebuild_grouped_objects()
            _refresh_filter_values()
            _refresh_tree()
            sts_state["is_loading"] = False
            sts_state["loaded_save_path"] = save_path
            sts_state["loaded_save_mtime"] = save_mtime

            msg = (
                f"Loaded {len(sts_state.get('objects', []))} movable entries from "
                f"{progress.get('loaded_files', 0)} STS files (slot {slot_n}). "
                f"(raw: {len(sts_state.get('raw_objects', []))})"
            )
            if progress.get("errors", 0):
                msg += f" ({progress.get('errors', 0)} failed)"
            sts_status_var.set(msg)
            # After STS list is already usable, refresh metadata in background.
            _refresh_vehicle_metadata_in_background(force=False)

        def _run_loader():
            for fpath in sts_files:
                if not _is_current():
                    return
                try:
                    fdata = _sts_load_file(fpath)
                    objs = _sts_parse_movable_objects(fdata.get("payload", b""), fpath)
                    try:
                        tab.after(0, lambda p=fpath, d=fdata, o=objs: _apply_chunk(p, d, o, ""))
                    except Exception:
                        pass
                except Exception as e:
                    try:
                        tab.after(0, lambda p=fpath, err=str(e): _apply_chunk(p, {}, [], err))
                    except Exception:
                        pass

            try:
                tab.after(0, _finish_loading)
            except Exception:
                pass

        threading.Thread(target=_run_loader, daemon=True).start()

    def _selected_rows():
        out = []
        for iid in tree.selection():
            obj = sts_state["row_to_obj"].get(iid)
            if isinstance(obj, dict):
                out.append((iid, obj))
        return out

    def _expand_members_with_linked_entries(members: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        out = []
        seen_ids = set()
        link_keys = set()

        for obj in members or []:
            if not isinstance(obj, dict):
                continue
            oid = id(obj)
            if oid not in seen_ids:
                seen_ids.add(oid)
                out.append(obj)
            fpath = str(obj.get("file_path", "") or "").strip()
            ref_id = str(obj.get("guid", "") or obj.get("object_id", "") or "").strip()
            if fpath and ref_id:
                link_keys.add((fpath, ref_id.lower()))

        if not link_keys:
            return out

        for obj in sts_state.get("raw_objects", []) or []:
            if not isinstance(obj, dict):
                continue
            oid = id(obj)
            if oid in seen_ids:
                continue
            fpath = str(obj.get("file_path", "") or "").strip()
            ref_id = str(obj.get("guid", "") or obj.get("object_id", "") or "").strip()
            if not fpath or not ref_id:
                continue
            if (fpath, ref_id.lower()) not in link_keys:
                continue
            seen_ids.add(oid)
            out.append(obj)

        return out

    def _selected_edit_units():
        rows = _selected_rows()
        if not rows:
            return []
        units = []
        seen_members = set()

        for iid, display_obj in rows:
            if not isinstance(display_obj, dict):
                continue
            raw_members = []
            if bool(display_obj.get("is_group")) and isinstance(display_obj.get("group_members"), list):
                for m in display_obj.get("group_members", []):
                    if isinstance(m, dict):
                        raw_members.append(m)
            else:
                raw_members.append(display_obj)

            raw_members = _expand_members_with_linked_entries(raw_members)
            deduped = []
            for m in raw_members:
                mid = id(m)
                if mid in seen_members:
                    continue
                seen_members.add(mid)
                deduped.append(m)
            if not deduped:
                continue

            anchor_obj = display_obj.get("group_anchor_obj") if isinstance(display_obj, dict) else None
            if not isinstance(anchor_obj, dict):
                anchor_obj = deduped[0]

            units.append(
                {
                    "iid": iid,
                    "display_obj": display_obj,
                    "anchor_obj": anchor_obj,
                    "members": deduped,
                }
            )

        return units

    def _select_filtered_rows():
        rows = [iid for iid in tree.get_children() if iid in sts_state.get("row_to_obj", {})]
        if not rows:
            return
        try:
            tree.selection_set(rows)
            tree.focus(rows[0])
            tree.see(rows[0])
        except Exception:
            pass

    def _unselect_filtered_rows():
        try:
            tree.selection_remove(tree.selection())
        except Exception:
            pass

    def _on_tree_select(_event=None):
        # Remove filler/empty rows from selection so "blank area" cannot stay selected.
        current = list(tree.selection())
        if current:
            real = [iid for iid in current if iid in sts_state.get("row_to_obj", {})]
            if len(real) != len(current):
                try:
                    if real:
                        tree.selection_set(real)
                    else:
                        tree.selection_remove(current)
                except Exception:
                    pass

        rows = _selected_rows()
        if len(rows) != 1:
            return
        _, obj = rows[0]
        x_var.set(f"{float(obj.get('x', 0.0)):.3f}")
        y_var.set(f"{float(obj.get('y', 0.0)):.3f}")
        z_var.set(f"{float(obj.get('z', 0.0)):.3f}")

    def _on_tree_click(event):
        try:
            region = str(tree.identify("region", event.x, event.y) or "")
        except Exception:
            region = ""
        if region not in {"cell", "tree"}:
            return
        iid = str(tree.identify_row(event.y) or "")
        if iid and iid in sts_state.get("row_to_obj", {}):
            return
        try:
            tree.selection_remove(tree.selection())
        except Exception:
            pass
        try:
            tree.focus("")
        except Exception:
            pass
        return "break"

    tree.bind("<Button-1>", _on_tree_click, add="+")
    tree.bind("<<TreeviewSelect>>", _on_tree_select)
    tree.bind("<Configure>", _schedule_tree_resize_refresh)

    def _save_touched_files(touched_paths: Set[str]):
        saved = 0
        for path in sorted(set(touched_paths or [])):
            entry = sts_state["files"].get(path)
            if not isinstance(entry, dict):
                continue
            payload = entry.get("payload", b"")
            if not isinstance(payload, (bytes, bytearray)):
                continue
            trailer = entry.get("trailer", b"")
            try:
                if path not in sts_state["backed_up_files"]:
                    try:
                        make_backup_if_enabled(path)
                    except Exception:
                        pass
                    sts_state["backed_up_files"].add(path)
                _sts_write_file(path, payload, trailer=trailer)
                saved += 1
            except Exception as e:
                raise RuntimeError(f"Failed to save {os.path.basename(path)}: {e}")
        return saved

    def _coord_offsets_for_obj(obj: Dict[str, Any], payload: bytearray) -> List[int]:
        offs = []
        raw = obj.get("coord_offs")
        if isinstance(raw, list):
            for v in raw:
                try:
                    iv = int(v)
                except Exception:
                    continue
                offs.append(iv)
        if not offs:
            try:
                offs.append(int(obj.get("coord_off", -1)))
            except Exception:
                pass
        out = []
        seen = set()
        max_off = max(0, len(payload) - 12)
        for iv in offs:
            if iv < 0 or iv > max_off:
                continue
            if iv in seen:
                continue
            seen.add(iv)
            out.append(iv)
        # Keep edits bounded even if parser ever returns a huge list.
        if len(out) > 128:
            out = out[:128]
        return out

    def _collect_transform_offsets_in_range(payload: bytearray, scan_start: int, scan_end: int) -> List[int]:
        out = []
        if not isinstance(payload, (bytes, bytearray)):
            return out
        size = len(payload)
        beg = max(32, int(scan_start))
        end = min(int(scan_end), size - 12)
        if end <= beg:
            return out
        for coord_off in range(beg, end):
            try:
                x, y, z = struct.unpack_from("<fff", payload, coord_off)
            except Exception:
                continue
            if not (math.isfinite(x) and math.isfinite(y) and math.isfinite(z)):
                continue
            if max(abs(x), abs(y), abs(z)) > 5000000:
                continue
            if _sts_is_denorm_float(x) or _sts_is_denorm_float(y) or _sts_is_denorm_float(z):
                continue
            if max(abs(x), abs(y), abs(z)) < 20.0:
                continue
            if not _sts_has_valid_transform_at(payload, coord_off):
                continue
            if coord_off < 4 or (coord_off + 16) > size:
                continue
            try:
                prev_w = float(struct.unpack_from("<f", payload, coord_off - 4)[0])
                row_w = float(struct.unpack_from("<f", payload, coord_off + 12)[0])
            except Exception:
                continue
            if (not math.isfinite(prev_w)) or (not math.isfinite(row_w)):
                continue
            if abs(prev_w) > 0.25:
                continue
            if abs(row_w - 1.0) > 0.25:
                continue
            out.append(int(coord_off))
            if len(out) >= 4096:
                break
        return sorted(set(out))

    def _all_transform_offsets_for_obj(obj: Dict[str, Any], payload: bytearray) -> List[int]:
        if not isinstance(payload, bytearray):
            return []

        size = len(payload)
        base_offs = _coord_offsets_for_obj(obj, payload)
        off_set = set(base_offs)

        def _ival(key: str, default: int = -1) -> int:
            try:
                return int(obj.get(key, default))
            except Exception:
                return default

        start_off = _ival("start_off", -1)
        end_off = _ival("end_off", -1)
        if start_off >= 0 and end_off > start_off:
            scan_beg = max(0, start_off)
            scan_end = min(size, end_off)
            try:
                off_set.update(_collect_transform_offsets_in_range(payload, scan_beg, scan_end))
            except Exception:
                pass

        # Fallback: capture nearby valid transform anchors around known offsets.
        # Some vehicles have extra parts in nearby sub-blocks not listed in coord_offs.
        anchor_xyz = None
        if base_offs:
            try:
                anchor_xyz = struct.unpack_from("<fff", payload, int(base_offs[0]))
            except Exception:
                anchor_xyz = None

        for base in base_offs[:16]:
            win_beg = max(32, int(base) - 4096)
            win_end = min(size, int(base) + 4096)
            try:
                nearby = _collect_transform_offsets_in_range(payload, win_beg, win_end)
            except Exception:
                nearby = []
            if not nearby:
                continue
            if anchor_xyz is None:
                off_set.update(nearby)
                continue
            ax, ay, az = anchor_xyz
            for off in nearby:
                try:
                    x, y, z = struct.unpack_from("<fff", payload, int(off))
                except Exception:
                    continue
                # Keep nearby parts of the same object cluster, avoid unrelated neighbors.
                if (x - ax) * (x - ax) + (y - ay) * (y - ay) + (z - az) * (z - az) <= 80.0 * 80.0:
                    off_set.add(int(off))

        out = sorted(v for v in off_set if 0 <= int(v) <= max(0, size - 12))
        if len(out) > 4096:
            out = out[:4096]
        return out

    def _unstuck_selected():
        if sts_state.get("is_loading"):
            return show_info("Vehicles", "Wait for STS loading to finish first.")
        units = _selected_edit_units()
        if not units:
            return show_info("Vehicles", "No vehicle/trailer selected.")

        try:
            lift = float(str(lift_var.get() or "0").strip())
        except Exception:
            return messagebox.showerror("Error", "Lift Y value is invalid.")
        if abs(lift) < 1e-9:
            return show_info("Vehicles", "Lift value is 0, nothing to apply.")

        touched = set()
        moved_parts = 0
        for unit in units:
            for obj in unit.get("members", []):
                if not isinstance(obj, dict):
                    continue
                path = obj.get("file_path")
                entry = sts_state["files"].get(path)
                if not isinstance(entry, dict):
                    continue
                payload = entry.get("payload")
                if not isinstance(payload, bytearray):
                    continue

                coord_offs = _all_transform_offsets_for_obj(obj, payload)
                if not coord_offs:
                    continue

                # Shift all tracked transforms in this object together.
                for off in coord_offs:
                    try:
                        cx, cy, cz = struct.unpack_from("<fff", payload, off)
                    except Exception:
                        continue
                    struct.pack_into("<fff", payload, off, float(cx), float(cy + lift), float(cz))

                obj["x"] = float(obj.get("x", 0.0))
                obj["y"] = float(obj.get("y", 0.0)) + lift
                obj["z"] = float(obj.get("z", 0.0))
                touched.add(path)
                moved_parts += 1

        try:
            saved = _save_touched_files(touched)
        except Exception as e:
            return messagebox.showerror("Error", str(e))
        _rebuild_grouped_objects()
        _refresh_filter_values()
        _refresh_tree()
        sts_status_var.set(
            f"Unstuck applied to {len(units)} selected entries ({moved_parts} linked parts). Saved {saved} STS files."
        )

    def _apply_xyz_selected():
        if sts_state.get("is_loading"):
            return show_info("Vehicles", "Wait for STS loading to finish first.")
        units = _selected_edit_units()
        if not units:
            return show_info("Vehicles", "No vehicle/trailer selected.")

        sx = str(x_var.get() or "").strip()
        sy = str(y_var.get() or "").strip()
        sz = str(z_var.get() or "").strip()
        if not sx and not sy and not sz:
            return show_info("Vehicles", "X/Y/Z fields are empty.")

        try:
            vx = float(sx) if sx else None
            vy = float(sy) if sy else None
            vz = float(sz) if sz else None
        except Exception:
            return messagebox.showerror("Error", "X/Y/Z values are invalid.")

        touched = set()
        moved_parts = 0
        for unit in units:
            anchor = unit.get("anchor_obj")
            if not isinstance(anchor, dict):
                continue
            ox = float(anchor.get("x", 0.0))
            oy = float(anchor.get("y", 0.0))
            oz = float(anchor.get("z", 0.0))
            tx = ox if vx is None else float(vx)
            ty = oy if vy is None else float(vy)
            tz = oz if vz is None else float(vz)
            dx = tx - ox
            dy = ty - oy
            dz = tz - oz

            for obj in unit.get("members", []):
                if not isinstance(obj, dict):
                    continue
                path = obj.get("file_path")
                entry = sts_state["files"].get(path)
                if not isinstance(entry, dict):
                    continue
                payload = entry.get("payload")
                if not isinstance(payload, bytearray):
                    continue

                coord_offs = _all_transform_offsets_for_obj(obj, payload)
                if not coord_offs:
                    continue

                # Apply anchor delta to all parts of this grouped object.
                for off in coord_offs:
                    try:
                        cx, cy, cz = struct.unpack_from("<fff", payload, off)
                    except Exception:
                        continue
                    struct.pack_into("<fff", payload, off, float(cx + dx), float(cy + dy), float(cz + dz))

                obj["x"] = float(obj.get("x", 0.0)) + dx
                obj["y"] = float(obj.get("y", 0.0)) + dy
                obj["z"] = float(obj.get("z", 0.0)) + dz
                touched.add(path)
                moved_parts += 1

        try:
            saved = _save_touched_files(touched)
        except Exception as e:
            return messagebox.showerror("Error", str(e))
        _rebuild_grouped_objects()
        _refresh_filter_values()
        _refresh_tree()
        sts_status_var.set(
            f"Custom XYZ applied to {len(units)} selected entries ({moved_parts} linked parts). Saved {saved} STS files."
        )

    def _delete_selected_entries():
        if sts_state.get("is_loading"):
            return show_info("Vehicles", "Wait for STS loading to finish first.")
        units = _selected_edit_units()
        if not units:
            return show_info("Vehicles", "No vehicle/trailer selected.")

        target_members = []
        seen_member_ids = set()
        for unit in units:
            for obj in unit.get("members", []):
                if not isinstance(obj, dict):
                    continue
                oid = id(obj)
                if oid in seen_member_ids:
                    continue
                seen_member_ids.add(oid)
                target_members.append(obj)

        try:
            ok = messagebox.askyesno(
                "Delete selected entries?",
                f"Delete {len(target_members)} selected map entries from STS files?\n\nThis cannot be undone without backup.",
            )
        except Exception:
            ok = True
        if not ok:
            return

        by_file = {}
        for obj in target_members:
            path = obj.get("file_path")
            if not path:
                continue
            by_file.setdefault(path, []).append(obj)

        touched = set()
        deleted_obj_ids = set()
        deleted_count = 0
        skipped_count = 0

        def _write_span_string(buf: bytearray, beg: int, end: int, seed_text: str, keep_guid_shape: bool = False) -> bool:
            if beg < 0 or end <= beg:
                return False
            if beg >= len(buf):
                return False
            end2 = min(int(end), len(buf))
            if end2 <= beg:
                return False
            span_len = int(end2 - beg)
            if span_len <= 0:
                return False
            if span_len == 1:
                try:
                    buf[beg] = 0
                    return True
                except Exception:
                    return False

            text_len = span_len - 1  # keep terminating NUL byte in place
            if keep_guid_shape and text_len == 38:
                seed = "{00000000-0000-0000-0000-000000000000}"
            else:
                seed = str(seed_text or "deleted")
            raw = bytearray(seed.encode("ascii", errors="ignore"))
            if not raw:
                raw = bytearray(b"deleted")

            try:
                # Fill with '_' then overlay seed text; this preserves exact span length.
                fill = bytearray(b"_" * text_len)
                lim = min(text_len, len(raw))
                fill[:lim] = raw[:lim]
                buf[beg:beg + text_len] = bytes(fill)
                buf[beg + text_len] = 0
                return True
            except Exception:
                return False

        def _rewrite_all_cstring_occurrences(buf: bytearray, target_text: str, replacement_text: str) -> int:
            target = str(target_text or "")
            if not target:
                return 0
            try:
                t_bytes = target.encode("ascii")
            except Exception:
                return 0
            if not t_bytes:
                return 0

            repl = str(replacement_text or "")
            try:
                r_bytes = repl.encode("ascii")
            except Exception:
                r_bytes = b"deleted"
            if not r_bytes:
                r_bytes = b"deleted"

            needle = t_bytes + b"\x00"
            count = 0
            pos = 0
            max_pos = max(0, len(buf) - len(needle))
            while pos <= max_pos:
                idx = buf.find(needle, pos)
                if idx < 0:
                    break
                span_len = len(t_bytes)
                fill = bytearray(b"_" * span_len)
                lim = min(span_len, len(r_bytes))
                fill[:lim] = r_bytes[:lim]
                try:
                    buf[idx:idx + span_len] = bytes(fill)
                    # keep terminal NUL unchanged
                    count += 1
                except Exception:
                    pass
                pos = idx + len(needle)
            return count

        def _invalidate_entry(payload: bytearray, obj: Dict[str, Any]) -> bool:
            changed = False

            def _ival(key: str, default: int = -1) -> int:
                try:
                    return int(obj.get(key, default))
                except Exception:
                    return default

            start_off = _ival("start_off", -1)
            end_off = _ival("end_off", -1)
            # Keep binary length/layout stable: invalidate identifying strings/lengths in place.
            type_beg = _ival("type_beg", -1)
            type_end = _ival("type_end", -1)
            obj_beg = _ival("obj_beg", -1)
            obj_end = _ival("obj_end", -1)
            guid_beg = _ival("guid_beg", -1)
            guid_end = _ival("guid_end", -1)

            def _zero_guid_literals_in_range(buf: bytearray, beg: int, end: int) -> int:
                if beg < 0 or end <= beg or beg >= len(buf):
                    return 0
                e2 = min(int(end), len(buf))
                if e2 <= beg:
                    return 0
                try:
                    chunk = bytes(buf[beg:e2])
                except Exception:
                    return 0
                # Match canonical GUID text with braces. Replace in-place with zero GUID text.
                pat = re.compile(rb"\{[0-9A-Fa-f]{8}-[0-9A-Fa-f]{4}-[0-9A-Fa-f]{4}-[0-9A-Fa-f]{4}-[0-9A-Fa-f]{12}\}")
                repl = b"{00000000-0000-0000-0000-000000000000}"
                count = 0
                for m in pat.finditer(chunk):
                    s = beg + int(m.start())
                    t = s + 38
                    if s < 0 or t > len(buf):
                        continue
                    try:
                        if bytes(buf[s:t]) != repl:
                            buf[s:t] = repl
                            count += 1
                    except Exception:
                        pass
                return count

            # Keep binary structure and string lengths untouched.
            # We only rewrite string content in-place so parser offsets stay valid.
            if _write_span_string(payload, type_beg, type_end, "deleted_type"):
                changed = True
            if _write_span_string(payload, obj_beg, obj_end, "deleted_entry_id"):
                changed = True
            if _write_span_string(payload, guid_beg, guid_end, "deleted_guid", keep_guid_shape=True):
                changed = True

            # Rewrite all direct C-string occurrences of this object id / guid in the file.
            type_id_value = str(obj.get("type_id", "") or "").strip()
            if type_id_value:
                if _rewrite_all_cstring_occurrences(payload, type_id_value, "deleted_type"):
                    changed = True
            object_id = str(obj.get("object_id", "") or "").strip()
            if object_id:
                if _rewrite_all_cstring_occurrences(payload, object_id, "deleted_entry_id"):
                    changed = True
            if re.fullmatch(r"\{[0-9A-Fa-f\-]{36}\}", object_id):
                if _rewrite_all_cstring_occurrences(payload, object_id, "{00000000-0000-0000-0000-000000000000}"):
                    changed = True
            guid_value = str(obj.get("guid", "") or "").strip()
            if re.fullmatch(r"\{[0-9A-Fa-f\-]{36}\}", guid_value):
                if _rewrite_all_cstring_occurrences(payload, guid_value, "{00000000-0000-0000-0000-000000000000}"):
                    changed = True
            # Also scrub any GUID literals in this entry block (handles nested/variant refs).
            if start_off >= 0 and end_off > start_off:
                if _zero_guid_literals_in_range(payload, start_off, end_off):
                    changed = True

            return changed

        for path, objs in by_file.items():
            entry = sts_state["files"].get(path)
            payload = entry.get("payload") if isinstance(entry, dict) else None
            if not isinstance(payload, bytearray):
                skipped_count += len(objs)
                continue

            for obj in objs:
                try:
                    ok_inv = _invalidate_entry(payload, obj)
                except Exception:
                    ok_inv = False
                if ok_inv:
                    deleted_count += 1
                    deleted_obj_ids.add(id(obj))
                    touched.add(path)
                else:
                    skipped_count += 1

        if not touched:
            return show_info("Vehicles", "Failed to delete selected entries.")

        try:
            saved = _save_touched_files(touched)
        except Exception as e:
            return messagebox.showerror("Error", str(e))

        sts_state["raw_objects"] = [o for o in sts_state.get("raw_objects", []) if id(o) not in deleted_obj_ids]
        _rebuild_grouped_objects()
        _refresh_filter_values()
        _refresh_tree()
        sts_status_var.set(
            f"Deleted {deleted_count} entries. Saved {saved} STS files."
            + (f" Skipped {skipped_count}." if skipped_count else "")
        )

    def _on_type_or_region_filter_change(_event=None):
        _refresh_filter_values()
        _refresh_tree()

    def _on_map_filter_change(_event=None):
        _refresh_tree()

    def _on_name_filter_change(_event=None):
        _refresh_filter_values()
        _refresh_tree()

    type_filter_cb.bind("<<ComboboxSelected>>", _on_type_or_region_filter_change)
    region_filter_cb.bind("<<ComboboxSelected>>", _on_type_or_region_filter_change)
    map_filter_cb.bind("<<ComboboxSelected>>", _on_map_filter_change)
    name_filter_entry.bind("<KeyRelease>", _on_name_filter_change)

    ttk.Button(edit_row, text="Select Filtered", command=_select_filtered_rows).pack(side="left", padx=(0, 8))
    ttk.Button(edit_row, text="Unselect Filtered", command=_unselect_filtered_rows).pack(side="left", padx=(0, 8))
    ttk.Button(edit_row, text="Delete Selected", command=_delete_selected_entries).pack(side="left", padx=(0, 12))
    ttk.Button(edit_row, text="Unstuck Selected (+Y)", command=_unstuck_selected).pack(side="left", padx=(0, 8))
    ttk.Button(edit_row, text="Apply Custom XYZ", command=_apply_xyz_selected).pack(side="left")
    ttk.Checkbutton(
        edit_row,
        text="Filter X0 Y0 Z0",
        variable=filter_zero_var,
        command=_on_type_or_region_filter_change,
    ).pack(side="left", padx=(12, 0))

    def _on_save_path_changed():
        path = save_path_var.get()
        if path and os.path.exists(path):
            _clear_sts_view("Loading STS objects in background...")
            _load_sts_objects(manual=False)
        else:
            _clear_sts_view("Select a valid save file to load STS objects.")

    def _on_tab_visible(_event=None):
        _refresh_vehicle_metadata_in_background(force=False)
        path = save_path_var.get()
        if not path or not os.path.exists(path):
            return
        if sts_state.get("is_loading"):
            return
        # Always keep data fresh when this tab becomes visible.
        _load_sts_objects(manual=False)

    _on_save_path_changed()
    try:
        tab.after(1200, lambda: _refresh_vehicle_metadata_in_background(force=False))
    except Exception:
        pass
    tab.bind("<Visibility>", _on_tab_visible)
    _trace_var_write(save_path_var, _on_save_path_changed)
# =============================================================================
# SECTION: Objective-State Helpers (used by Objectives+)
# Used In: Objectives+ task accept/re-accept and objective status operations
# =============================================================================
def _experiments_dedupe_ids(ids):
    seen = set()
    out = []
    for raw in ids or []:
        if raw is None:
            continue
        value = str(raw).strip()
        if not value or value in seen:
            continue
        seen.add(value)
        out.append(value)
    return out


def _experiments_clean_text(value):
    text = "" if value is None else str(value)
    text = re.sub(r"<[^>]+>", "", text)
    text = re.sub(r"\s+", " ", text).strip()
    return text


def _experiments_is_likely_token(value):
    text = str(value or "").strip()
    if not text:
        return False
    if text.startswith("UI_") or text.startswith("EXP_"):
        return True
    if re.fullmatch(r"[A-Z0-9_]+", text):
        return True
    if re.fullmatch(r"(level_)?[a-z]{2}_\d{2}(?:_\d{2})?(?:_name|_desc)?", text):
        return True
    return False


def _experiments_translate_token(token, localization):
    tok = str(token or "").strip()
    if not tok:
        return ""
    if not isinstance(localization, dict) or not localization:
        return tok

    candidates = [tok]
    if tok.startswith("EXP_"):
        candidates.append(tok[4:])
    else:
        candidates.append("EXP_" + tok)
    if tok.startswith("UI_") and not tok.startswith("EXP_UI_"):
        candidates.append("EXP_" + tok)
    if tok.endswith("_NAME"):
        candidates.append(tok[:-5])
    if tok.endswith("_DESC"):
        candidates.append(tok[:-5])

    for candidate in list(candidates):
        if candidate:
            candidates.append(candidate.upper())
            candidates.append(candidate.lower())

    seen = set()
    for candidate in candidates:
        if not candidate or candidate in seen:
            continue
        seen.add(candidate)
        if candidate in localization:
            return _experiments_clean_text(localization.get(candidate))

    return tok


def _experiments_humanize_objective_key(objective_id):
    oid = str(objective_id or "").strip()
    if not oid:
        return ""
    parts = [p for p in oid.split("_") if p]
    if len(parts) > 3 and parts[1].isdigit() and parts[2].isdigit():
        parts = parts[3:]
    if parts and parts[-1] in {"TSK", "OBJ", "CNT", "CONTRACT"}:
        parts = parts[:-1]
    if not parts:
        return oid
    return _experiments_clean_text(" ".join(p.capitalize() for p in parts))


def _experiments_load_objective_index():
    """
    Load objective index rows from maprunner_data.csv.
    Returns a list of normalized rows.
    """
    csv_path = resource_path("maprunner_data.csv")
    if not os.path.exists(csv_path):
        return []

    localization = {}

    rows = []
    try:
        with open(csv_path, "r", encoding="utf-8", newline="") as f:
            reader = csv.DictReader(f)
            for row in reader:
                key = str(row.get("key", "")).strip()
                if not key:
                    continue

                raw_display = str(row.get("displayName", "")).strip()
                display = _experiments_translate_token(raw_display, localization)
                if not display or _experiments_is_likely_token(display):
                    display = _experiments_humanize_objective_key(key)

                region_code = str(row.get("region", "")).strip()
                raw_region_name = str(row.get("region_name", "")).strip() or REGION_NAME_MAP.get(region_code, "")
                region_name = _experiments_translate_token(raw_region_name, localization)
                if not region_name or _experiments_is_likely_token(region_name):
                    region_name = REGION_NAME_MAP.get(region_code, raw_region_name or region_code)

                raw_desc = str(row.get("descriptionText", "")).strip()
                description = _experiments_translate_token(raw_desc, localization)
                description = _experiments_clean_text(description)
                if _experiments_is_likely_token(description):
                    description = ""

                rows.append(
                    {
                        "key": key,
                        "displayName": display or key,
                        "category": str(row.get("category", "")).strip(),
                        "region": region_code,
                        "region_name": region_name,
                        "type": str(row.get("type", "")).strip(),
                        "cargo_needed": str(row.get("cargo_needed", "")).strip(),
                        "descriptionText": description,
                    }
                )
    except Exception as e:
        print(f"[Experiments] Failed to read maprunner_data.csv: {e}")
        return []

    dedup = {}
    for row in rows:
        k = row["key"]
        if k not in dedup:
            dedup[k] = row
    return list(dedup.values())


_EXPERIMENTS_OBJECTIVE_ROW_BY_KEY = None


def _experiments_get_objective_row_by_key():
    global _EXPERIMENTS_OBJECTIVE_ROW_BY_KEY
    if isinstance(_EXPERIMENTS_OBJECTIVE_ROW_BY_KEY, dict):
        return _EXPERIMENTS_OBJECTIVE_ROW_BY_KEY
    rows = _experiments_load_objective_index()
    mapping = {}
    for row in rows:
        key = str(row.get("key", "")).strip()
        if key and key not in mapping:
            mapping[key] = row
    _EXPERIMENTS_OBJECTIVE_ROW_BY_KEY = mapping
    return mapping


def _experiments_is_task_objective(objective_id, row_by_key=None, meta_kind=None):
    oid = str(objective_id or "").strip()
    if not oid:
        return False

    mapping = row_by_key if isinstance(row_by_key, dict) else _experiments_get_objective_row_by_key()
    row = mapping.get(oid, {})
    if isinstance(row, dict):
        category = str(row.get("category", "") or "").strip().upper()
        if "TASK" in category:
            return True
        if "CONTRACT" in category or "CONTEST" in category:
            return False

    kind_map = meta_kind if isinstance(meta_kind, dict) else _experiments_load_meta_objective_kind()
    kind = str(kind_map.get(oid, "") or "").strip().lower()
    if kind == "task":
        return True
    if kind in {"contract", "contest"}:
        return False

    # Fallback by common SnowRunner suffix naming.
    upper = oid.upper()
    if upper.endswith("_TSK"):
        return True
    if upper.endswith("_OBJ") or upper.endswith("_CNT"):
        return False

    return False


def _experiments_find_save_keys(doc):
    keys = []
    if not isinstance(doc, dict):
        return keys
    for k, v in doc.items():
        if isinstance(k, str) and re.fullmatch(r"CompleteSave\d*", k) and isinstance(v, dict):
            keys.append(k)
    return keys


def _experiments_read_save_doc(path):
    with open(path, "r", encoding="utf-8") as f:
        raw = f.read()
    had_null = raw.endswith("\0")
    clean = raw.rstrip("\0")
    doc = json.loads(clean)
    save_keys = _experiments_find_save_keys(doc)
    if not save_keys:
        raise ValueError("No CompleteSave* block found in file.")
    return doc, had_null, save_keys


def _experiments_write_save_doc(path, doc, had_null=False):
    out = json.dumps(doc, separators=(",", ":"), ensure_ascii=False)
    if had_null:
        out += "\0"
    with open(path, "w", encoding="utf-8") as f:
        f.write(out)


def _experiments_iter_ssl_values(doc, save_keys):
    for save_key in save_keys:
        save_obj = doc.get(save_key)
        if not isinstance(save_obj, dict):
            continue
        ssl_value = save_obj.get("SslValue")
        if not isinstance(ssl_value, dict):
            ssl_value = {}
            save_obj["SslValue"] = ssl_value
        yield save_key, save_obj, ssl_value


_EXPERIMENTS_JS_OBJECTIVE_INDEX = None
_EXPERIMENTS_JS_LOCALIZATION = None
_EXPERIMENTS_JS_LOAD_INFO = None
_EXPERIMENTS_META_OBJECTIVE_KIND = None


def _experiments_extract_json_parse_payload(text):
    """
    Extract JSON.parse('<payload>') payload from a JS bundle.
    """
    if not text:
        return None
    idx = text.find("JSON.parse")
    if idx < 0:
        return None
    i = text.find("(", idx)
    if i < 0:
        return None
    j = i + 1
    while j < len(text) and text[j].isspace():
        j += 1
    if j >= len(text) or text[j] not in ("'", '"'):
        return None
    raw = _mr_extract_js_string_literal(text, j)
    if raw is None:
        return None
    try:
        return codecs.decode(raw.replace(r"\/", "/"), "unicode_escape")
    except Exception:
        return raw


def _experiments_load_js_objective_sources(force_reload=False):
    """
    Load objective definitions/localization for objective-state seeding.
    Priority:
      1) MapRunner in-memory canonical JS (`data.js` / `desc.js`) if available.
      2) Cached canonical JS saved by Objectives+ from earlier online runs.
      3) Fresh MapRunner fetch + role detection (handles random chunk names).
    """
    global _EXPERIMENTS_JS_OBJECTIVE_INDEX, _EXPERIMENTS_JS_LOCALIZATION, _EXPERIMENTS_JS_LOAD_INFO

    if (
        not force_reload
        and isinstance(_EXPERIMENTS_JS_OBJECTIVE_INDEX, dict)
        and isinstance(_EXPERIMENTS_JS_LOCALIZATION, dict)
        and isinstance(_EXPERIMENTS_JS_LOAD_INFO, dict)
    ):
        return _EXPERIMENTS_JS_OBJECTIVE_INDEX, _EXPERIMENTS_JS_LOCALIZATION, _EXPERIMENTS_JS_LOAD_INFO

    objective_index = {}
    localization = {}
    info = {
        "data_path": "",
        "desc_path": "",
        "data_entries": 0,
        "localization_entries": 0,
    }

    def _merge_objective_entries(arr):
        if not isinstance(arr, list):
            return
        for entry in arr:
            if not isinstance(entry, dict):
                continue
            key = str(entry.get("key", "")).strip()
            if key and key not in objective_index:
                objective_index[key] = entry

    def _parse_data_text(text):
        payload = _experiments_extract_json_parse_payload(text)
        if not payload:
            return 0
        try:
            arr = json.loads(payload)
        except Exception:
            return 0
        before = len(objective_index)
        _merge_objective_entries(arr)
        return max(0, len(objective_index) - before)

    def _parse_desc_text(text):
        parsed = _mr_parse_localization_from_desc_text(text) or {}
        if not parsed:
            return 0
        if not localization:
            localization.update(parsed)
        else:
            for k, v in parsed.items():
                if k not in localization:
                    localization[k] = v
        return len(parsed)

    def _try_parse_canonical_mr_sources():
        parsed_any = False
        try:
            _mr_choose_best_js_roles()
        except Exception:
            pass

        try:
            data_bs = _mr_get_file_bytes_or_mem(_MR_CANONICAL_NAMES["data"])
            data_text = _mr_decode_bytes_to_text(data_bs) if data_bs is not None else None
            if data_text:
                added = _parse_data_text(data_text)
                if added > 0 and not info["data_path"]:
                    info["data_path"] = "in-memory:data.js"
                    parsed_any = True
        except Exception:
            pass

        try:
            desc_bs = _mr_get_file_bytes_or_mem(_MR_CANONICAL_NAMES["desc"])
            desc_text = _mr_decode_bytes_to_text(desc_bs) if desc_bs is not None else None
            if desc_text:
                parsed = _parse_desc_text(desc_text)
                if parsed > 0 and not info["desc_path"]:
                    info["desc_path"] = "in-memory:desc.js"
                    parsed_any = True
        except Exception:
            pass
        return parsed_any

    # 1) First try already-loaded MapRunner canonical sources.
    _try_parse_canonical_mr_sources()

    # 2) Try cached canonical JS (saved by previous Objectives+ fetch).
    if not objective_index or not localization:
        try:
            loaded_cached = _mr_load_cached_canonical_js_to_mem()
            if loaded_cached:
                if "data" in loaded_cached and not info["data_path"]:
                    info["data_path"] = f"cache:{os.path.basename(loaded_cached['data'])}"
                if "desc" in loaded_cached and not info["desc_path"]:
                    info["desc_path"] = f"cache:{os.path.basename(loaded_cached['desc'])}"
            _try_parse_canonical_mr_sources()
        except Exception:
            pass

    # 3) If still missing, fetch/resolve MapRunner JS roles (random chunk names supported).
    if not objective_index or not localization:
        try:
            _mr_download_js_step()
            _try_parse_canonical_mr_sources()
        except Exception:
            pass

    info["data_entries"] = len(objective_index)
    info["localization_entries"] = len(localization)

    _EXPERIMENTS_JS_OBJECTIVE_INDEX = objective_index
    _EXPERIMENTS_JS_LOCALIZATION = localization
    _EXPERIMENTS_JS_LOAD_INFO = info
    return objective_index, localization, info


def _experiments_load_meta_objective_kind():
    """
    Parse meta_desc_ssl.ps and map objective id -> kind:
      task / contract / contest
    """
    global _EXPERIMENTS_META_OBJECTIVE_KIND
    if isinstance(_EXPERIMENTS_META_OBJECTIVE_KIND, dict):
        return _EXPERIMENTS_META_OBJECTIVE_KIND

    kind_map = {}
    path = ""
    try:
        path = resource_path("meta_desc_ssl.ps")
    except Exception:
        path = ""

    if path and os.path.exists(path):
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as f:
                text = f.read()
            pattern = re.compile(
                r'__type\s*=\s*"(TaskSettings|ContractSettings|ContestSettings)"[\s\S]{0,420}?__sslBrandName\s*=\s*"([A-Z0-9_]+)"',
                flags=re.IGNORECASE,
            )
            for m in pattern.finditer(text):
                raw_type = str(m.group(1) or "").strip().lower()
                obj_id = str(m.group(2) or "").strip()
                if not obj_id:
                    continue
                if raw_type.startswith("task"):
                    kind = "task"
                elif raw_type.startswith("contract"):
                    kind = "contract"
                elif raw_type.startswith("contest"):
                    kind = "contest"
                else:
                    continue
                if obj_id not in kind_map:
                    kind_map[obj_id] = kind
        except Exception as e:
            print(f"[Experiments] Failed to parse meta_desc_ssl.ps: {e}")

    _EXPERIMENTS_META_OBJECTIVE_KIND = kind_map
    return kind_map


def _experiments_parse_id_collection(raw):
    if isinstance(raw, dict):
        shape = "dict"
        items = list(raw.keys())
    elif isinstance(raw, list):
        shape = "list"
        items = [x for x in raw if isinstance(x, str)]
    else:
        shape = "list"
        items = []
    return shape, _experiments_dedupe_ids(items)


def _experiments_pack_id_collection(shape, items):
    if shape == "dict":
        return {k: True for k in items}
    return list(items)


def _experiments_add_ids_to_collection(raw, ids):
    shape, items = _experiments_parse_id_collection(raw)
    ids = _experiments_dedupe_ids(ids)
    if not ids:
        return _experiments_pack_id_collection(shape, items), 0
    seen = set(items)
    added = 0
    for oid in ids:
        if oid in seen:
            continue
        items.append(oid)
        seen.add(oid)
        added += 1
    return _experiments_pack_id_collection(shape, items), added


def _experiments_remove_ids_from_collection(raw, ids):
    shape, items = _experiments_parse_id_collection(raw)
    ids_set = set(_experiments_dedupe_ids(ids))
    if not ids_set:
        return _experiments_pack_id_collection(shape, items), 0
    new_items = [x for x in items if x not in ids_set]
    removed = len(items) - len(new_items)
    return _experiments_pack_id_collection(shape, new_items), removed


def _experiments_guess_map_from_objective_id(objective_id):
    oid = str(objective_id or "").strip()
    if not oid:
        return ""

    parts = oid.split("_")
    if len(parts) >= 3 and parts[1].isdigit() and parts[2].isdigit():
        return f"level_{parts[0].lower()}_{parts[1]}_{parts[2]}"

    m = re.search(r"(US|RU)_(\d{2})_(\d{2})", oid, flags=re.IGNORECASE)
    if m:
        return f"level_{m.group(1).lower()}_{m.group(2)}_{m.group(3)}"

    return ""


def _experiments_guess_zone_from_objective_id(objective_id):
    oid = str(objective_id or "").strip()
    if not oid:
        return ""

    base = re.sub(r"_(TSK|OBJ|CNT)$", "", oid, flags=re.IGNORECASE)
    if base:
        return base
    return oid


_EXPERIMENTS_KNOWN_CARGO_TYPES = {
    "CargoMetalPlanks",
    "CargoWoodenPlanks",
    "CargoWoodenPlanks2",
    "CargoBricks",
    "CargoConcreteBlocks",
    "CargoConcreteSlab",
    "CargoServiceSpareParts",
    "CargoServiceSparePartsSpecial",
    "CargoVehiclesSpareParts",
    "CargoCrateLarge",
    "CargoBigDrill",
    "CargoBarrels",
    "CargoBarrelsOil",
    "CargoContainerSmall",
    "CargoContainerSmallSpecial",
    "CargoContainerLarge",
    "CargoContainerLargeDrilling",
    "CargoBags",
    "CargoPipesSmall",
    "CargoPipesMedium",
    "CargoPipeLarge",
    "CargoRadioactive",
}


_EXPERIMENTS_CARGO_ALIAS = {
    "metalplanks": "CargoMetalPlanks",
    "woodenplanks": "CargoWoodenPlanks2",
    "bricks": "CargoBricks",
    "blocks": "CargoConcreteBlocks",
    "concreteblocks": "CargoConcreteBlocks",
    "concreteslab": "CargoConcreteSlab",
    "servicespareparts": "CargoServiceSpareParts",
    "vehiclesspareparts": "CargoVehiclesSpareParts",
    "cratelarge": "CargoCrateLarge",
    "bigdrill": "CargoBigDrill",
    "barrels": "CargoBarrels",
    "oilbarrels": "CargoBarrelsOil",
    "containersmall": "CargoContainerSmall",
    "containerlarge": "CargoContainerLarge",
    "bags": "CargoBags",
    "smallpipes": "CargoPipesSmall",
    "pipessmall": "CargoPipesSmall",
    "mediumpipes": "CargoPipesMedium",
    "pipesmedium": "CargoPipesMedium",
    "largepipes": "CargoPipeLarge",
    "pipeslarge": "CargoPipeLarge",
}


def _experiments_normalize_key_token(value):
    return re.sub(r"[^a-z0-9]+", "", str(value or "").lower())


def _experiments_guess_cargo_type(label):
    raw = str(label or "").strip()
    if not raw:
        return None

    if raw.startswith("Cargo") and re.fullmatch(r"Cargo[A-Za-z0-9_]+", raw):
        return raw

    norm = _experiments_normalize_key_token(raw)
    alias = _EXPERIMENTS_CARGO_ALIAS.get(norm)
    if alias:
        return alias

    camel = re.sub(r"[^A-Za-z0-9]+", " ", raw).strip()
    if camel:
        camel = "".join(p[:1].upper() + p[1:] for p in camel.split() if p)
        candidate = "Cargo" + camel
        if candidate in _EXPERIMENTS_KNOWN_CARGO_TYPES:
            return candidate

    for known in _EXPERIMENTS_KNOWN_CARGO_TYPES:
        if _experiments_normalize_key_token(known.replace("Cargo", "")) == norm:
            return known

    return None


def _experiments_parse_cargo_needed(cargo_needed_text):
    """
    Parse maprunner cargo string like:
      "2× Concrete Slab; 1× Metal Planks"
    into list of (count, cargo_type).
    """
    text = str(cargo_needed_text or "").strip()
    if not text:
        return []

    items = []
    chunks = [c.strip() for c in re.split(r"[;,]+", text) if c.strip()]
    for chunk in chunks:
        m = re.match(r"^\s*(\d+)\s*[x×]\s*(.+?)\s*$", chunk, flags=re.IGNORECASE)
        if m:
            count = max(1, int(m.group(1)))
            label = m.group(2).strip()
        else:
            count = 1
            label = chunk

        cargo_type = _experiments_guess_cargo_type(label)
        if not cargo_type:
            continue
        items.append((count, cargo_type))
    return items


def _experiments_collect_marker_data(markers, objective_id):
    zones = []
    level_name = ""
    for marker in markers or []:
        if not isinstance(marker, dict):
            continue
        zone = str(marker.get("key", "")).strip()
        if zone:
            zones.append(zone)
        if not level_name:
            lv = str(marker.get("level", "")).strip()
            if not lv:
                lv = str(marker.get("map", "")).strip()
            if lv:
                level_name = lv

    zones = _experiments_dedupe_ids(zones)
    if not level_name:
        level_name = _experiments_guess_map_from_objective_id(objective_id)
    if not zones:
        fallback_zone = _experiments_guess_zone_from_objective_id(objective_id)
        if fallback_zone:
            zones = [fallback_zone]
    return level_name, zones


def _experiments_build_stage_from_js(stage_def, root_markers, objective_id):
    stage = stage_def if isinstance(stage_def, dict) else {}
    markers = stage.get("markers")
    if not isinstance(markers, list):
        markers = root_markers if isinstance(root_markers, list) else []

    map_name, zones = _experiments_collect_marker_data(markers, objective_id)

    cargo_actions = []
    cargo_items = stage.get("cargo")
    if isinstance(cargo_items, list):
        for cargo in cargo_items:
            if not isinstance(cargo, dict):
                continue
            cargo_type = str(cargo.get("key", "")).strip()
            if not cargo_type:
                cargo_type = _experiments_guess_cargo_type(cargo.get("name", ""))
            if not cargo_type:
                continue
            raw_count = cargo.get("count", 1)
            try:
                aim_value = int(float(raw_count))
            except Exception:
                aim_value = 1
            if aim_value <= 0:
                aim_value = 1

            cargo_actions.append(
                {
                    "cargoState": {"aimValue": aim_value, "type": cargo_type, "curValue": 0},
                    "map": map_name or "",
                    "zones": list(zones),
                    "zoneColorOverride": {"r": 0.0, "g": 185.0, "b": 25.0, "a": 125.0},
                    "isZoneVisited": False,
                    "platformColorOverride": None,
                    "modelBuildingTag": "",
                    "isNeedVisitOnTruck": False,
                    "truckUid": "",
                    "platformId": "",
                    "isVisibleWithPlatform": False,
                    "unloadingMode": 0,
                }
            )

    truck_delivery_states = []
    stage_type = str(stage.get("type", "") or "").strip()
    nested = stage.get("objectives")
    if isinstance(nested, list) and (stage_type == "truckDelivery" or any(isinstance(x, dict) and x.get("key") for x in nested)):
        for item in nested:
            if not isinstance(item, dict):
                continue
            truck_id = str(item.get("key", "")).strip()
            if not truck_id:
                continue
            truck_delivery_states.append(
                {
                    "isDelivered": False,
                    "truckId": truck_id,
                    "deliveryZones": list(zones),
                    "mapDelivery": map_name or "",
                }
            )
    elif stage_type == "truckDelivery":
        truck_delivery_states.append(
            {
                "isDelivered": False,
                "truckId": "",
                "deliveryZones": list(zones),
                "mapDelivery": map_name or "",
            }
        )

    visit_all = None
    if not cargo_actions and not truck_delivery_states and map_name and zones:
        visit_all = {
            "map": map_name,
            "zoneStates": [
                {
                    "zone": zone,
                    "truckUid": "",
                    "isVisited": False,
                    "isVisitWithCertainTruck": False,
                }
                for zone in zones
            ],
        }

    return {
        "cargoDeliveryActions": cargo_actions,
        "makeActionInZone": None,
        "farmingState": None,
        "truckDeliveryStates": truck_delivery_states,
        "truckRepairStates": [],
        "changeTruckState": None,
        "cargoSpawnState": [],
        "livingAreaState": None,
        "visitAllZonesState": visit_all,
    }


def _experiments_build_stage_states_from_js_objective(objective_id):
    objective_index, _, _ = _experiments_load_js_objective_sources()
    entry = objective_index.get(str(objective_id))
    if not isinstance(entry, dict):
        return []

    root_markers = entry.get("markers")
    if not isinstance(root_markers, list):
        root_markers = []

    stage_defs = entry.get("objectives")
    stage_states = []
    if isinstance(stage_defs, list):
        for stage_def in stage_defs:
            if not isinstance(stage_def, dict):
                continue
            stage_state = _experiments_build_stage_from_js(stage_def, root_markers, objective_id)
            stage_states.append(stage_state)

    if not stage_states and root_markers:
        stage_states.append(_experiments_build_stage_from_js({"markers": root_markers}, root_markers, objective_id))

    return stage_states


def _experiments_build_placeholder_stage_state(objective_id):
    level_name = _experiments_guess_map_from_objective_id(objective_id)
    zone_name = _experiments_guess_zone_from_objective_id(objective_id)
    objective_row = _experiments_get_objective_row_by_key().get(str(objective_id), {})
    objective_type = str(objective_row.get("type", "") or "").strip()
    if not objective_type:
        meta_kind = _experiments_load_meta_objective_kind().get(str(objective_id), "")
        if meta_kind == "contest":
            objective_type = "exploration"
    cargo_needed = objective_row.get("cargo_needed", "")

    visit_all = None
    if level_name and zone_name:
        visit_all = {
            "map": level_name,
            "zoneStates": [
                {
                    "zone": zone_name,
                    "truckUid": "",
                    "isVisited": False,
                    "isVisitWithCertainTruck": False,
                }
            ],
        }

    cargo_actions = []
    if objective_type == "cargoDelivery":
        for count, cargo_type in _experiments_parse_cargo_needed(cargo_needed):
            cargo_actions.append(
                {
                    "cargoState": {"aimValue": count, "type": cargo_type, "curValue": 0},
                    "map": level_name or "",
                    "zones": [zone_name] if zone_name else [],
                    "zoneColorOverride": {"r": 0.0, "g": 185.0, "b": 25.0, "a": 125.0},
                    "isZoneVisited": False,
                    "platformColorOverride": None,
                    "modelBuildingTag": "",
                    "isNeedVisitOnTruck": False,
                    "truckUid": "",
                    "platformId": "",
                    "isVisibleWithPlatform": False,
                    "unloadingMode": 0,
                }
            )

    truck_delivery_states = []
    if objective_type == "truckDelivery":
        truck_delivery_states.append(
            {
                "isDelivered": False,
                "truckId": "",
                "deliveryZones": [zone_name] if zone_name else [],
                "mapDelivery": level_name or "",
            }
        )

    return {
        "cargoDeliveryActions": cargo_actions,
        "makeActionInZone": None,
        "farmingState": None,
        "truckDeliveryStates": truck_delivery_states,
        "truckRepairStates": [],
        "changeTruckState": None,
        "cargoSpawnState": [],
        "livingAreaState": None,
        "visitAllZonesState": visit_all if objective_type == "exploration" else None,
    }


def _experiments_seed_objective_state_with_source(objective_id, stage_mode="none"):
    """
    stage_mode:
      - 'none': no stagesState key (let game generate from objective defs)
      - 'placeholder': inject a non-completing stage (prefer JS-based mission stages)
    """
    state = {
        "failReasons": {},
        "id": objective_id,
        "spentTime": 0.0,
        "isTimerStarted": True,
        "isFinished": False,
        "wasCompletedAtLeastOnce": False,
    }

    source = "none"
    mode = str(stage_mode or "none").strip().lower()
    if mode == "placeholder":
        js_stages = _experiments_build_stage_states_from_js_objective(objective_id)
        if js_stages:
            state["stagesState"] = js_stages
            source = "js"
        else:
            state["stagesState"] = [_experiments_build_placeholder_stage_state(objective_id)]
            source = "fallback"

    return state, source


def _experiments_seed_objective_state(objective_id, stage_mode="none"):
    state, _ = _experiments_seed_objective_state_with_source(objective_id, stage_mode=stage_mode)
    return state


def _experiments_apply_to_save(path, mutator, create_backup=True):
    if not path or not os.path.exists(path):
        messagebox.showerror("Error", "Save file not found.")
        return None

    if create_backup:
        try:
            make_backup_if_enabled(path)
        except Exception as e:
            print(f"[Experiments] Backup warning: {e}")

    try:
        doc, had_null, save_keys = _experiments_read_save_doc(path)
    except Exception as e:
        messagebox.showerror("Error", f"Failed to parse save file:\n{e}")
        return None

    stats = {"blocks": 0}
    try:
        for _, _, ssl_value in _experiments_iter_ssl_values(doc, save_keys):
            stats["blocks"] += 1
            mutator(ssl_value, stats)
        _experiments_write_save_doc(path, doc, had_null=had_null)
    except Exception as e:
        messagebox.showerror("Error", f"Failed to apply experiment change:\n{e}")
        return None

    return stats


def _experiments_accept_objectives(
    path,
    objective_ids,
    add_discovered=True,
    seed_states=True,
    seed_stage_mode="placeholder",
    reset_to_unfinished=True,
    touch_existing_states=False,
    remove_from_finished=True,
    remove_from_viewed=True,
    track_first=False,
    trust_ids_as_tasks=False,
):
    all_ids = _experiments_dedupe_ids(objective_ids)
    if not all_ids:
        return None

    if trust_ids_as_tasks:
        ids = list(all_ids)
        non_task_skipped = 0
    else:
        row_by_key = _experiments_get_objective_row_by_key()
        meta_kind = _experiments_load_meta_objective_kind()
        ids = [oid for oid in all_ids if _experiments_is_task_objective(oid, row_by_key=row_by_key, meta_kind=meta_kind)]
        non_task_skipped = max(0, len(all_ids) - len(ids))
    if not ids:
        return {"blocks": 0, "ids_skipped_non_tasks": non_task_skipped}

    def _mutator(ssl_value, stats):
        stats.setdefault("discovered_added", 0)
        stats.setdefault("states_seeded", 0)
        stats.setdefault("states_seeded_js", 0)
        stats.setdefault("states_seeded_fallback", 0)
        stats.setdefault("states_touched", 0)
        stats.setdefault("finished_removed", 0)
        stats.setdefault("viewed_removed", 0)
        stats.setdefault("tracked_set", 0)
        stats.setdefault("ids_skipped_finished", 0)
        if "ids_skipped_non_tasks" not in stats:
            stats["ids_skipped_non_tasks"] = non_task_skipped

        finished_raw = ssl_value.get("finishedObjs", [])
        _, finished_ids = _experiments_parse_id_collection(finished_raw)
        finished_set = set(finished_ids)
        active_ids = [oid for oid in ids if oid not in finished_set]
        stats["ids_skipped_finished"] += max(0, len(ids) - len(active_ids))

        if not active_ids:
            return

        if add_discovered:
            new_raw, added = _experiments_add_ids_to_collection(ssl_value.get("discoveredObjectives", []), active_ids)
            ssl_value["discoveredObjectives"] = new_raw
            stats["discovered_added"] += added

        states = ssl_value.get("objectiveStates")
        if not isinstance(states, dict):
            states = {}

        for oid in active_ids:
            state = states.get(oid)
            is_new_state = False
            if not isinstance(state, dict):
                if not seed_states:
                    continue
                state, seeded_source = _experiments_seed_objective_state_with_source(oid, stage_mode=seed_stage_mode)
                if seeded_source == "js":
                    stats["states_seeded_js"] += 1
                elif seeded_source == "fallback":
                    stats["states_seeded_fallback"] += 1
                states[oid] = state
                stats["states_seeded"] += 1
                is_new_state = True

            state["id"] = oid
            if "failReasons" not in state or not isinstance(state.get("failReasons"), dict):
                state["failReasons"] = {}
            if "spentTime" not in state:
                state["spentTime"] = 0.0
            if "isTimerStarted" not in state:
                state["isTimerStarted"] = True

            if reset_to_unfinished and (is_new_state or touch_existing_states):
                state["isFinished"] = False
                state["wasCompletedAtLeastOnce"] = False
                state["isTimerStarted"] = True

            stats["states_touched"] += 1

        ssl_value["objectiveStates"] = states

        if remove_from_finished:
            # Safeguard: never remove objectives that are already finished in this block.
            removable = [oid for oid in active_ids if oid not in finished_set]
            if removable:
                new_finished, removed = _experiments_remove_ids_from_collection(finished_raw, removable)
                ssl_value["finishedObjs"] = new_finished
                stats["finished_removed"] += removed

        if remove_from_viewed:
            viewed_raw = ssl_value.get("viewedUnactivatedObjectives", [])
            if isinstance(viewed_raw, list):
                ids_set = set(active_ids)
                new_viewed = [v for v in viewed_raw if isinstance(v, str) and v not in ids_set]
                stats["viewed_removed"] += max(0, len(viewed_raw) - len(new_viewed))
                ssl_value["viewedUnactivatedObjectives"] = new_viewed
            elif isinstance(viewed_raw, dict):
                new_viewed, removed = _experiments_remove_ids_from_collection(viewed_raw, active_ids)
                stats["viewed_removed"] += removed
                ssl_value["viewedUnactivatedObjectives"] = new_viewed
            else:
                ssl_value["viewedUnactivatedObjectives"] = viewed_raw

        if track_first and active_ids:
            ssl_value["trackedObjective"] = active_ids[0]
            stats["tracked_set"] += 1

    return _experiments_apply_to_save(path, _mutator, create_backup=True)


def _experiments_reaccept_finished_tasks(
    path,
    objective_ids,
    add_discovered=True,
    seed_states=True,
    seed_stage_mode="placeholder",
    reset_to_unfinished=True,
    touch_existing_states=False,
    remove_from_viewed=True,
    track_first=False,
    trust_ids_as_tasks=False,
):
    all_ids = _experiments_dedupe_ids(objective_ids)
    if not all_ids:
        return None

    if trust_ids_as_tasks:
        ids = list(all_ids)
        non_task_skipped = 0
    else:
        row_by_key = _experiments_get_objective_row_by_key()
        meta_kind = _experiments_load_meta_objective_kind()
        ids = [oid for oid in all_ids if _experiments_is_task_objective(oid, row_by_key=row_by_key, meta_kind=meta_kind)]
        non_task_skipped = max(0, len(all_ids) - len(ids))
    if not ids:
        return {"blocks": 0, "ids_skipped_non_tasks": non_task_skipped}

    def _mutator(ssl_value, stats):
        stats.setdefault("discovered_added", 0)
        stats.setdefault("states_seeded", 0)
        stats.setdefault("states_seeded_js", 0)
        stats.setdefault("states_seeded_fallback", 0)
        stats.setdefault("states_touched", 0)
        stats.setdefault("finished_removed", 0)
        stats.setdefault("viewed_removed", 0)
        stats.setdefault("tracked_set", 0)
        stats.setdefault("ids_skipped_not_finished", 0)
        if "ids_skipped_non_tasks" not in stats:
            stats["ids_skipped_non_tasks"] = non_task_skipped

        finished_raw = ssl_value.get("finishedObjs", [])
        _, finished_ids = _experiments_parse_id_collection(finished_raw)
        finished_set = set(finished_ids)
        target_ids = [oid for oid in ids if oid in finished_set]
        stats["ids_skipped_not_finished"] += max(0, len(ids) - len(target_ids))

        if not target_ids:
            return

        # Re-accept requires removing tasks from finishedObjs first.
        new_finished, removed = _experiments_remove_ids_from_collection(finished_raw, target_ids)
        ssl_value["finishedObjs"] = new_finished
        stats["finished_removed"] += removed

        if add_discovered:
            new_raw, added = _experiments_add_ids_to_collection(ssl_value.get("discoveredObjectives", []), target_ids)
            ssl_value["discoveredObjectives"] = new_raw
            stats["discovered_added"] += added

        states = ssl_value.get("objectiveStates")
        if not isinstance(states, dict):
            states = {}

        for oid in target_ids:
            state = states.get(oid)
            is_new_state = False
            if not isinstance(state, dict):
                if not seed_states:
                    continue
                state, seeded_source = _experiments_seed_objective_state_with_source(oid, stage_mode=seed_stage_mode)
                if seeded_source == "js":
                    stats["states_seeded_js"] += 1
                elif seeded_source == "fallback":
                    stats["states_seeded_fallback"] += 1
                states[oid] = state
                stats["states_seeded"] += 1
                is_new_state = True

            state["id"] = oid
            if "failReasons" not in state or not isinstance(state.get("failReasons"), dict):
                state["failReasons"] = {}
            if "spentTime" not in state:
                state["spentTime"] = 0.0
            if "isTimerStarted" not in state:
                state["isTimerStarted"] = True

            if reset_to_unfinished and (is_new_state or touch_existing_states):
                state["isFinished"] = False
                state["wasCompletedAtLeastOnce"] = False
                state["isTimerStarted"] = True

            stats["states_touched"] += 1

        ssl_value["objectiveStates"] = states

        if remove_from_viewed:
            viewed_raw = ssl_value.get("viewedUnactivatedObjectives", [])
            if isinstance(viewed_raw, list):
                ids_set = set(target_ids)
                new_viewed = [v for v in viewed_raw if isinstance(v, str) and v not in ids_set]
                stats["viewed_removed"] += max(0, len(viewed_raw) - len(new_viewed))
                ssl_value["viewedUnactivatedObjectives"] = new_viewed
            elif isinstance(viewed_raw, dict):
                new_viewed, removed = _experiments_remove_ids_from_collection(viewed_raw, target_ids)
                stats["viewed_removed"] += removed
                ssl_value["viewedUnactivatedObjectives"] = new_viewed
            else:
                ssl_value["viewedUnactivatedObjectives"] = viewed_raw

        if track_first and target_ids:
            ssl_value["trackedObjective"] = target_ids[0]
            stats["tracked_set"] += 1

    return _experiments_apply_to_save(path, _mutator, create_backup=True)


def _experiments_order_collection_items(existing_items, final_set, priority=None):
    """
    Preserve original order where possible and append missing keys using priority order.
    """
    if final_set is None:
        final_set = set()
    if priority is None:
        priority = []

    out = []
    seen = set()
    for item in existing_items:
        if item in final_set and item not in seen:
            out.append(item)
            seen.add(item)

    for item in priority:
        if item in final_set and item not in seen:
            out.append(item)
            seen.add(item)

    for item in sorted(final_set):
        if item not in seen:
            out.append(item)
            seen.add(item)

    return out


def _experiments_set_objective_state_flags(
    path,
    objective_ids,
    *,
    seed_missing=True,
    is_finished=None,
    was_completed=None,
    is_timer_started=None,
    spent_time=None,
    clear_fail_reasons=False,
    clear_stages=False,
):
    ids = _experiments_dedupe_ids(objective_ids)
    if not ids:
        return None

    spent_time_value = None
    if spent_time is not None:
        spent_time_value = float(spent_time)

    def _mutator(ssl_value, stats):
        stats.setdefault("states_seeded", 0)
        stats.setdefault("states_touched", 0)

        states = ssl_value.get("objectiveStates")
        if not isinstance(states, dict):
            states = {}

        for oid in ids:
            state = states.get(oid)
            if not isinstance(state, dict):
                if not seed_missing:
                    continue
                state = _experiments_seed_objective_state(oid)
                states[oid] = state
                stats["states_seeded"] += 1

            state["id"] = oid
            if "failReasons" not in state or not isinstance(state.get("failReasons"), dict):
                state["failReasons"] = {}
            if "stagesState" not in state or not isinstance(state.get("stagesState"), list):
                state["stagesState"] = []

            if is_finished is not None:
                state["isFinished"] = bool(is_finished)
            if was_completed is not None:
                state["wasCompletedAtLeastOnce"] = bool(was_completed)
            if is_timer_started is not None:
                state["isTimerStarted"] = bool(is_timer_started)
            if spent_time is not None:
                state["spentTime"] = spent_time_value
            if clear_fail_reasons:
                state["failReasons"] = {}
            if clear_stages:
                state["stagesState"] = []

            stats["states_touched"] += 1

        ssl_value["objectiveStates"] = states

    return _experiments_apply_to_save(path, _mutator, create_backup=True)


def _experiments_mutate_collection_key(path, key, objective_ids, mode):
    ids = _experiments_dedupe_ids(objective_ids)
    if not ids:
        return None

    allowed = {"discoveredObjectives", "finishedObjs", "viewedUnactivatedObjectives"}
    if key not in allowed:
        raise ValueError(f"Unsupported collection key: {key}")
    if mode not in {"add", "remove"}:
        raise ValueError(f"Unsupported mutate mode: {mode}")

    def _mutator(ssl_value, stats):
        stats.setdefault("changed", 0)
        current_raw = ssl_value.get(key, [] if key != "finishedObjs" else {})
        if mode == "add":
            new_raw, changed = _experiments_add_ids_to_collection(current_raw, ids)
        else:
            new_raw, changed = _experiments_remove_ids_from_collection(current_raw, ids)
        ssl_value[key] = new_raw
        stats["changed"] += changed

    return _experiments_apply_to_save(path, _mutator, create_backup=True)


def _experiments_sync_finished_from_states(path, *, add_finished=True, remove_not_finished=False):
    if not add_finished and not remove_not_finished:
        return None

    def _mutator(ssl_value, stats):
        stats.setdefault("changed", 0)
        stats.setdefault("finished_from_states", 0)

        states = ssl_value.get("objectiveStates")
        finished_from_states = set()
        if isinstance(states, dict):
            for oid, state in states.items():
                if not isinstance(oid, str) or not isinstance(state, dict):
                    continue
                if bool(state.get("isFinished")):
                    finished_from_states.add(oid)

        shape, items = _experiments_parse_id_collection(ssl_value.get("finishedObjs", []))
        final_set = set(items)

        if remove_not_finished:
            final_set &= finished_from_states
        if add_finished:
            final_set |= finished_from_states

        ordered = _experiments_order_collection_items(items, final_set, priority=sorted(finished_from_states))
        ssl_value["finishedObjs"] = _experiments_pack_id_collection(shape, ordered)

        stats["finished_from_states"] += len(finished_from_states)
        stats["changed"] += abs(len(items) - len(ordered))

    return _experiments_apply_to_save(path, _mutator, create_backup=True)


def _experiments_set_tracked_objective(path, objective_id):
    tracked = ""
    if objective_id is not None:
        tracked = str(objective_id).strip()

    def _mutator(ssl_value, stats):
        stats.setdefault("changed_blocks", 0)
        old = str(ssl_value.get("trackedObjective", "") or "").strip()
        if old != tracked:
            stats["changed_blocks"] += 1
        ssl_value["trackedObjective"] = tracked

    return _experiments_apply_to_save(path, _mutator, create_backup=True)


def _experiments_collect_save_snapshot(path):
    if not path or not os.path.exists(path):
        return None

    doc, _, save_keys = _experiments_read_save_doc(path)
    snapshot = {
        "path": path,
        "blocks": [],
        "totals": {
            "blocks": 0,
            "discovered": 0,
            "finished": 0,
            "viewed": 0,
            "states": 0,
            "states_finished": 0,
            "tracked_nonempty": 0,
        },
    }

    for save_key, _, ssl_value in _experiments_iter_ssl_values(doc, save_keys):
        d_shape, d_items = _experiments_parse_id_collection(ssl_value.get("discoveredObjectives", []))
        f_shape, f_items = _experiments_parse_id_collection(ssl_value.get("finishedObjs", []))
        v_shape, v_items = _experiments_parse_id_collection(ssl_value.get("viewedUnactivatedObjectives", []))

        states = ssl_value.get("objectiveStates", {})
        states_count = 0
        states_finished = 0
        if isinstance(states, dict):
            for oid, state in states.items():
                if not isinstance(oid, str):
                    continue
                states_count += 1
                if isinstance(state, dict) and bool(state.get("isFinished")):
                    states_finished += 1

        tracked = str(ssl_value.get("trackedObjective", "") or "").strip()

        block = {
            "save_key": save_key,
            "discovered_count": len(d_items),
            "discovered_shape": d_shape,
            "finished_count": len(f_items),
            "finished_shape": f_shape,
            "viewed_count": len(v_items),
            "viewed_shape": v_shape,
            "states_count": states_count,
            "states_finished": states_finished,
            "tracked": tracked,
        }
        snapshot["blocks"].append(block)

        snapshot["totals"]["blocks"] += 1
        snapshot["totals"]["discovered"] += len(d_items)
        snapshot["totals"]["finished"] += len(f_items)
        snapshot["totals"]["viewed"] += len(v_items)
        snapshot["totals"]["states"] += states_count
        snapshot["totals"]["states_finished"] += states_finished
        if tracked:
            snapshot["totals"]["tracked_nonempty"] += 1

    return snapshot


def _experiments_apply_status_preset(path, objective_ids, status):
    """
    Approximate ObjectiveStatus transitions using known save keys:
    NEW, VIEWED, ACTIVE, TRACKED, LOCKED, COMPLETED.
    """
    ids = _experiments_dedupe_ids(objective_ids)
    if not ids:
        return None

    status_norm = str(status or "").strip().upper()
    allowed = {"NEW", "VIEWED", "ACTIVE", "TRACKED", "LOCKED", "COMPLETED"}
    if status_norm not in allowed:
        raise ValueError(f"Unsupported status preset: {status}")

    ids_set = set(ids)

    def _ensure_state(states, oid):
        state = states.get(oid)
        seeded = 0
        if not isinstance(state, dict):
            state = _experiments_seed_objective_state(oid)
            states[oid] = state
            seeded = 1
        state["id"] = oid
        if "failReasons" not in state or not isinstance(state.get("failReasons"), dict):
            state["failReasons"] = {}
        if "stagesState" not in state or not isinstance(state.get("stagesState"), list):
            state["stagesState"] = []
        return state, seeded

    def _mutator(ssl_value, stats):
        stats.setdefault("states_seeded", 0)
        stats.setdefault("states_touched", 0)
        stats.setdefault("tracked_changed", 0)

        d_shape, d_items = _experiments_parse_id_collection(ssl_value.get("discoveredObjectives", []))
        f_shape, f_items = _experiments_parse_id_collection(ssl_value.get("finishedObjs", []))
        v_shape, v_items = _experiments_parse_id_collection(ssl_value.get("viewedUnactivatedObjectives", []))

        d_set = set(d_items)
        f_set = set(f_items)
        v_set = set(v_items)

        states = ssl_value.get("objectiveStates")
        if not isinstance(states, dict):
            states = {}

        if status_norm in {"NEW", "LOCKED"}:
            d_set -= ids_set
            v_set -= ids_set
            f_set -= ids_set
            for oid in ids:
                state = states.get(oid)
                if isinstance(state, dict):
                    state["id"] = oid
                    state["isFinished"] = False
                    state["wasCompletedAtLeastOnce"] = False
                    state["isTimerStarted"] = True
                    stats["states_touched"] += 1
        elif status_norm == "VIEWED":
            d_set |= ids_set
            v_set |= ids_set
            f_set -= ids_set
            for oid in ids:
                state, seeded = _ensure_state(states, oid)
                stats["states_seeded"] += seeded
                state["isFinished"] = False
                state["wasCompletedAtLeastOnce"] = False
                state["isTimerStarted"] = True
                stats["states_touched"] += 1
        elif status_norm == "ACTIVE":
            d_set |= ids_set
            v_set -= ids_set
            f_set -= ids_set
            for oid in ids:
                state, seeded = _ensure_state(states, oid)
                stats["states_seeded"] += seeded
                state["isFinished"] = False
                state["wasCompletedAtLeastOnce"] = False
                state["isTimerStarted"] = True
                stats["states_touched"] += 1
        elif status_norm == "TRACKED":
            d_set |= ids_set
            v_set -= ids_set
            f_set -= ids_set
            for oid in ids:
                state, seeded = _ensure_state(states, oid)
                stats["states_seeded"] += seeded
                state["isFinished"] = False
                state["wasCompletedAtLeastOnce"] = False
                state["isTimerStarted"] = True
                stats["states_touched"] += 1
            old = str(ssl_value.get("trackedObjective", "") or "").strip()
            if old != ids[0]:
                stats["tracked_changed"] += 1
            ssl_value["trackedObjective"] = ids[0]
        elif status_norm == "COMPLETED":
            d_set |= ids_set
            v_set -= ids_set
            f_set |= ids_set
            for oid in ids:
                state, seeded = _ensure_state(states, oid)
                stats["states_seeded"] += seeded
                state["isFinished"] = True
                state["wasCompletedAtLeastOnce"] = True
                state["isTimerStarted"] = True
                stats["states_touched"] += 1

        if status_norm in {"NEW", "LOCKED"}:
            old = str(ssl_value.get("trackedObjective", "") or "").strip()
            if old in ids_set:
                ssl_value["trackedObjective"] = ""
                stats["tracked_changed"] += 1

        d_out = _experiments_order_collection_items(d_items, d_set, priority=ids)
        f_out = _experiments_order_collection_items(f_items, f_set, priority=ids)
        v_out = _experiments_order_collection_items(v_items, v_set, priority=ids)

        ssl_value["discoveredObjectives"] = _experiments_pack_id_collection(d_shape, d_out)
        ssl_value["finishedObjs"] = _experiments_pack_id_collection(f_shape, f_out)
        ssl_value["viewedUnactivatedObjectives"] = _experiments_pack_id_collection(v_shape, v_out)
        ssl_value["objectiveStates"] = states

    return _experiments_apply_to_save(path, _mutator, create_backup=True)


# ---------- FACTOR_RULE_DEFINITIONS ----------
# IMPORTANT:
# - each rule (except game difficulty) gets an extra "random" choice
# - random resolves to a real option during save
FACTOR_RULE_DEFINITIONS = [
    ("Game difficulty", "gameDifficultyMode", {"Normal": 0, "Hard": 1, "New Game+": 2}),
    ("Truck availability", "truckAvailability", {
        "default": 1,
        "all trucks available from start": 0,
        "5-15 trucks in each garage": 3,
        "store unlocks at rank 10": 2,
        "store unlocks at rank 20": 2,
        "store unlocks at rank 30": 2,
        "store is locked": 4
    }),
    ("Truck pricing", "truckPricingFactor", {"default": 1, "free": 0, "2x": 2, "4x": 4, "6x": 6}),
    ("Truck selling price", "truckSellingFactor", {"normal price": 1, "50%": 0.5, "30%": 0.3, "10%": 0.1, "cant be sold": -1}),
    ("DLC vehicles availability", "isDLCVehiclesAvailable", {"available": True, "unavailable": False}),
    ("Vehicle storage slots", "vehicleStorageSlots", {"default": 0, "only 3": 3, "only 5": 5, "only 10": 10, "only scouts": -1}),
    ("External addon availability", "externalAddonAvailability", {
        "default": 0,
        "all addons unlocked": 1
    }),
    ("Internal addon availability", "internalAddonAvailability", {
        "default": 0,
        "all internal addons unlocked": 1
    }),
    ("Tire availability", "tyreAvailability", {
        "default": 1,
        "all tires available": 0,
        "highway and allroad": 2,
        "highway, allroad, offroad": 3,
        "no mud tires": 4,
        "no chained tires": 5
    }),
    ("Vehicle addon pricing", "addonPricingFactor", {"default": 1, "free": 0, "2x": 2, "4x": 4, "6x": 6}),
    ("Addon selling price", "addonSellingFactor", {"normal": 1.0, "10%": 0.1, "30%": 0.3, "50%": 0.5, "no refunds": 0}),
    ("Trailer store availability", "trailerStoreAviability", {"default": 1, "not available": 0}),
    ("Trailer availability", "trailerAvailability", {"default": 0, "all trailers available": 1, "not available": 2}),
    ("Trailer pricing", "trailerPricingFactor", {"normal price": 1, "free": 0, "2x": 2, "4x": 4, "6x": 6}),
    ("Trailer selling price", "trailerSellingFactor", {"normal price": 1, "50%": 0.5, "30%": 0.3, "10%": 0.1, "cant be sold": -1}),
    ("Fuel price", "fuelPriceFactor", {
        "normal price": 1,
        "free": 0,
        "2x": 2,
        "4x": 4,
        "6x": 6
    }),
    ("Garage repair price", "garageRepairePriceFactor", {
        "default": 1,
        "no auto repair": -1,
        "2x": 2,
        "4x": 4,
        "6x": 6
    }),
    ("Garage refuelling", "isGarageRefuelAvailable", {"available": True, "unavailable": False}),
    ("Repair points cost", "repairPointsCostFactor", {
        "default": 1,
        "hard mode rules": 1,
        "free": 0,
        "2x": 2,
        "4x": 4,
        "6x": 6
    }),
    ("Repair points required", "repairPointsRequiredFactor", {"default": 1, "2x less": 0.5, "2x": 2, "4x": 4, "6x": 6}),
    ("Vehicle repair regional rules", "regionRepaireMoneyFactor", {
        "default": 1,
        "2x price and points": 2,
        "3x price and points": 3,
        "4x price and points": 4,
        "unavailable": 0
    }),
    ("Vehicle damage", "vehicleDamageFactor", {"default": 1, "no damage": 0, "2x": 2, "3x": 3, "5x": 5}),
    ("Recovery price", "recoveryPriceFactor", {
        "default": 1,
        "hard mode price": 0,
        "2x": 2,
        "4x": 4,
        "6x": 6,
        "unavailable": -1
    }),
    ("Automatic cargo loading", "loadingPriceFactor", {"free": 0, "paid": 1, "2x": 2, "4x": 4, "6x": 6}),
    ("Truck switching price (minimap)", "teleportationPrice", {"free": 0, "500": 500, "1000": 1000, "2000": 2000, "5000": 5000}),
    ("Region traveling price", "regionTravellingPriceFactor", {
        "default": 1,
        "hard mode rules": 1,
        "free": 0,
        "2x": 2,
        "4x": 4,
        "6x": 6
    }),
    ("Task and contest payouts", "tasksAndContestsPayoutsFactor", {"normal": 1, "50%": 0.5, "150%": 1.5, "200%": 2, "300%": 3}),
    ("Contracts payouts", "contractsPayoutsFactor", {"normal": 1, "50%": 0.5, "150%": 1.5, "200%": 2, "300%": 3}),
    ("Max contest attempts", "maxContestAttempts", {"default": -1, "1 attempt": 1, "3 attempts": 3, "5 attempts": 5, "gold time only": -1}),
    ("Map marker style", "isMapMarkerAsInHardMode", {"default": False, "hard mode": True}),
]

_RULE_RANDOM_LABEL = "random"
_RULE_RANDOM_VALUE = "__RULE_RANDOM__"

# Key -> NGP dictionary key + label -> dictionary state.
_RULE_NGP_DICT_META = {
    "truckAvailability": ("TRUCK_AVAILABILITY", {
        "default": 0,
        "all trucks available from start": 1,
        "5-15 trucks in each garage": 2,
        "store unlocks at rank 10": 3,
        "store unlocks at rank 20": 4,
        "store unlocks at rank 30": 5,
        "store is locked": 6
    }),
    "truckPricingFactor": ("TRUCK_PRICING", {"default": 0, "free": 1, "2x": 2, "4x": 3, "6x": 4}),
    "truckSellingFactor": ("TRUCK_SELLING", {"normal price": 0, "50%": 1, "30%": 2, "10%": 3, "cant be sold": 4}),
    "isDLCVehiclesAvailable": ("DLC_VEHICLES", {"available": 0, "unavailable": 1}),
    "vehicleStorageSlots": ("VEHICLE_STORAGE", {"default": 0, "only 3": 1, "only 5": 2, "only 10": 3, "only scouts": 4}),
    "externalAddonAvailability": ("ADDON_AVAILABILITY", {"default": 0, "all addons unlocked": 1}),
    "internalAddonAvailability": ("INTENAL_ADDON_AVAILABILITY", {
        "default": 0,
        "all internal addons unlocked": 1
    }),
    "tyreAvailability": ("TYRE_AVAILABILITY", {
        "default": 0,
        "all tires available": 1,
        "highway and allroad": 2,
        "highway, allroad, offroad": 3,
        "no mud tires": 4,
        "no chained tires": 5
    }),
    "trailerStoreAviability": ("TRAILER_STORE_AVAILBILITY", {"default": 1, "not available": 0}),
    "trailerAvailability": ("TRAILER_AVAILABILITY", {"default": 0, "all trailers available": 1, "not available": 2}),
    "trailerPricingFactor": ("TRAILER_PRICING", {"normal price": 0, "free": 1, "2x": 2, "4x": 3, "6x": 4}),
    "trailerSellingFactor": ("TRAILER_SELLING", {"normal price": 0, "50%": 1, "30%": 2, "10%": 3, "cant be sold": 4}),
    "fuelPriceFactor": ("FUEL_PRICE", {"normal price": 0, "free": 1, "2x": 2, "4x": 3, "6x": 4}),
    "garageRepairePriceFactor": ("GARAGE_REPAIRE", {"default": 0, "no auto repair": 1, "2x": 2, "4x": 3, "6x": 4}),
    "isGarageRefuelAvailable": ("GARAGE_REFUEL", {"available": 0, "unavailable": 1}),
    "repairPointsCostFactor": ("REPAIR_POINTS_COST", {"default": 0, "hard mode rules": 1, "free": 0, "2x": 2, "4x": 3, "6x": 4}),
    "repairPointsRequiredFactor": ("REPAIR_POINTS_AMOUNT", {"default": 0, "2x less": 1, "2x": 2, "4x": 3, "6x": 4}),
    "regionRepaireMoneyFactor": ("REGIONAL_REPAIR", {
        "default": 0,
        "2x price and points": 1,
        "3x price and points": 2,
        "4x price and points": 3,
        "unavailable": 4
    }),
    "vehicleDamageFactor": ("VEHICLE_DAMAGE", {"default": 0, "no damage": 1, "2x": 2, "3x": 3, "5x": 4}),
    "recoveryPriceFactor": ("RECOVERY", {"default": 0, "hard mode price": 1, "2x": 2, "4x": 3, "6x": 4, "unavailable": 5}),
    "loadingPriceFactor": ("LOADING", {"free": 0, "paid": 1, "2x": 2, "4x": 3, "6x": 4}),
    "teleportationPrice": ("TELEPORTATION", {"free": 0, "500": 1, "1000": 2, "2000": 3, "5000": 4}),
    "regionTravellingPriceFactor": ("REGION_TRAVELLING", {"default": 0, "hard mode rules": 1, "free": 0, "2x": 2, "4x": 3, "6x": 4}),
    "tasksAndContestsPayoutsFactor": ("TASKS_CONTESTS", {"normal": 0, "50%": 1, "150%": 2, "200%": 3, "300%": 4}),
    "contractsPayoutsFactor": ("CONTRACTS", {"normal": 0, "50%": 1, "150%": 2, "200%": 3, "300%": 4}),
    "maxContestAttempts": ("CONTEST_ATTEMPTS", {"default": 0, "1 attempt": 1, "3 attempts": 2, "5 attempts": 3, "gold time only": 4}),
    "isMapMarkerAsInHardMode": ("MAP_MARKER", {"default": 0, "hard mode": 1}),
    "addonPricingFactor": ("ADDON_PRICING", {"default": 0, "free": 1, "2x": 2, "4x": 3, "6x": 4}),
}

_INTERNAL_ADDON_AMOUNT_BY_LABEL = {
    # Randomized internal-addon presets are intentionally not exposed in the editor.
}

# defensive globals
try:
    dropdown_widgets
except NameError:
    dropdown_widgets = {}
try:
    rule_savers
except NameError:
    rule_savers = []
try:
    FACTOR_RULE_VARS
except NameError:
    FACTOR_RULE_VARS = []

# ---------- SAFE helpers ----------

_key_pattern_cache = {}
# -----------------------------------------------------------------------------
# END SECTION: Tab Builders (UI construction)
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Rules Tab Helpers (Rules tab)
# Used In: create_rules_tab, sync_all_rules
# =============================================================================
def _value_pattern():
    # Matches: quoted string OR array OR object OR primitive (no comma/closing brace)
    return r'(?:"[^"]*"|\[[^\]]*\]|\{[^}]*\}|[^,}]+)'

def _set_key_in_text(content: str, key: str, json_value: str) -> str:
    """
    Safely replace or insert '"key": <json_value>'.
    json_value must be a literal text (e.g. json.dumps(value)).
    Handles arrays/objects/strings/numbers/true/false.
    """
    pat = _key_pattern_cache.get(key)
    if pat is None:
        vp = _value_pattern()
        pat = re.compile(rf'("{re.escape(key)}"\s*:\s*)({vp})', flags=re.IGNORECASE)
        _key_pattern_cache[key] = pat
    if pat.search(content):
        content = pat.sub(lambda m: m.group(1) + json_value, content)
    else:
        content = content.replace("{", f'{{"{key}": {json_value}, ', 1)
    return content

def _choose_safe_default(options):
    for _, v in options.items():
        return v
    return 0

def _make_key_saver(key, options, var):
    def saver(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            value = options.get(var.get(), _choose_safe_default(options))
            json_value = json.dumps(value)
            content = _set_key_in_text(content, key, json_value)
            with open(path, "w", encoding="utf-8") as f:
                f.write(content)
        except Exception as e:
            print(f"[rules saver] {key} failed: {e}")
    return saver

def _make_backup(path):
    bakfunc = globals().get("make_backup_if_enabled")
    try:
        if callable(bakfunc):
            bakfunc(path)
        # intentionally do nothing when the folder-backup function is missing:
        # we no longer create path + ".bak" files anywhere.
    except Exception:
        pass

# defaults you requested
_DEFAULT_RECOVERY_PRICE = [0,0,2500,5000,8000,5000,2000]
_DEFAULT_FULL_REPAIR_PRICE = [0,0,1500,2500,5000,2500,1500]
_DEFAULT_SETTINGS_DICT = {
    "ADDON_AVAILABILITY":1,"CONTEST_ATTEMPTS":0,"STARTING_MONEY":0,"REPAIR_POINTS_AMOUNT":0,"TRUCK_SELLING":0,"MAP_MARKER":0,
    "TRAILER_AVAILABILITY":1,"RECOVERY":0,"TIME_SETTINGS":0,"STARTING_RANK":0,"GARAGE_REPAIRE":0,"TYRE_AVAILABILITY":1,
    "REPAIR_POINTS_COST":0,"TRUCK_AVAILABILITY":3,"REGION_TRAVELLING":0,"VEHICLE_STORAGE":0,"LOADING":0,"FUEL_PRICE":1,
    "STARTING_RULES":0,"INTENAL_ADDON_AVAILABILITY":1,"TASKS_CONTESTS":0,"GARAGE_REFUEL":0,"TRAILER_STORE_AVAILBILITY":0,
    "DLC_VEHICLES":1,"TELEPORTATION":0,"CONTRACTS":0,"TRAILER_PRICING":0,"TRUCK_PRICING":0,"TRAILER_SELLING":0,"VEHICLE_DAMAGE":0,
    "ADDON_PRICING":0,"REGIONAL_REPAIR":0
}
_DEFAULT_DEPLOY_PRICE = {"Region":3500,"Map":1000}
_DEFAULT_AUTOLOAD_PRICE = 150

# ---------- UI builder ----------
# TAB: Rules (launch_gui -> tab_rules)
def create_rules_tab(tab_rules, save_path_var):
    """
    3-column centered rules UI. Register loader + trace save_path_var for immediate sync.
    """
    global FACTOR_RULE_VARS, rule_savers, dropdown_widgets

    FACTOR_RULE_VARS = []
    rule_savers = []
    dropdown_widgets = {}
    random_rules_var = tk.BooleanVar(value=False)

    def _set_all_rules_to_random():
        for rule in FACTOR_RULE_VARS:
            if rule["key"] == "gameDifficultyMode":
                continue
            if _RULE_RANDOM_LABEL in rule["options"]:
                try:
                    rule["var"].set(_RULE_RANDOM_LABEL)
                except Exception:
                    pass

    def _on_random_rules_toggle():
        if random_rules_var.get():
            _set_all_rules_to_random()

    # UI container + scrollable canvas
    container = ttk.Frame(tab_rules)
    container.pack(fill="both", expand=True, padx=8, pady=8)

    canvas_wrap = ttk.Frame(container)
    canvas_wrap.pack(fill="both", expand=True)

    canvas = tk.Canvas(canvas_wrap, highlightthickness=0)
    vscroll = ttk.Scrollbar(canvas_wrap, orient="vertical", command=canvas.yview)
    canvas.configure(yscrollcommand=vscroll.set)
    canvas.pack(side="left", fill="both", expand=True)
    vscroll.pack(side="right", fill="y")

    wrapper = ttk.Frame(canvas)
    window_id = canvas.create_window((0, 0), window=wrapper, anchor="nw")

    # expose for window auto-sizing
    try:
        globals()["_RULES_CONTENT_FRAME"] = wrapper
        globals()["_RULES_CANVAS"] = canvas
    except Exception:
        pass

    def _on_canvas_config(e):
        canvas.itemconfig(window_id, width=e.width)
    canvas.bind("<Configure>", _on_canvas_config)
    wrapper.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))

    # center layout (left/right spacers)
    wrapper.columnconfigure(0, weight=1)
    wrapper.columnconfigure(1, weight=0)
    wrapper.columnconfigure(2, weight=1)

    center_frame = ttk.Frame(wrapper)
    center_frame.grid(row=0, column=1, sticky="n")

    # build entries
    entries = []
    for label, key, options in FACTOR_RULE_DEFINITIONS:
        if not isinstance(options, dict):
            try:
                options = {str(x): x for x in options}
            except Exception:
                options = {"default": 0}
        else:
            options = dict(options)
        if key != "gameDifficultyMode" and _RULE_RANDOM_LABEL not in options:
            options[_RULE_RANDOM_LABEL] = _RULE_RANDOM_VALUE
        var = tk.StringVar(value=list(options.keys())[0])
        rule = {"label": label, "key": key, "options": options, "var": var}
        FACTOR_RULE_VARS.append(rule)
        entries.append(rule)

    COLS = 3
    for ci in range(COLS):
        center_frame.columnconfigure(ci, weight=1, uniform="rulecol")

    r = 0
    c = 0
    for rule in entries:
        label_text = rule["label"]
        key = rule["key"]
        opts = rule["options"]
        var = rule["var"]
        card = ttk.Frame(center_frame, padding=(10, 8), relief="groove")
        card.grid(row=r, column=c, padx=12, pady=8, sticky="nsew")
        ttk.Label(card, text=label_text + ":", font=("TkDefaultFont", 9)).pack(anchor="w")
        cb = ttk.Combobox(card, textvariable=var, values=list(opts.keys()), state="readonly")
        cb.pack(fill="x", pady=(6,2))
        dropdown_widgets[key] = cb
        rule_savers.append(_make_key_saver(key, opts, var))

        c += 1
        if c >= COLS:
            c = 0
            r += 1

    # ---------- sanitizers/helpers used in save ----------
    def _ensure_key_with_default_text(text, key, pyvalue, treat_zero_as_missing=False):
        """Replace explicit null or 0 (optionally) for key, or insert if missing."""
        json_value = json.dumps(pyvalue)
        null_pat = re.compile(rf'("{re.escape(key)}"\s*:\s*)null', flags=re.IGNORECASE)
        if null_pat.search(text):
            text = null_pat.sub(lambda m: m.group(1) + json_value, text)
        if treat_zero_as_missing:
            # replace "key": 0 (word boundary)
            zero_pat = re.compile(rf'("{re.escape(key)}"\s*:\s*)0\b', flags=re.IGNORECASE)
            if zero_pat.search(text):
                text = zero_pat.sub(lambda m: m.group(1) + json_value, text)
        if f'"{key}"' not in text:
            text = text.replace("{", f'{{"{key}": {json_value}, ', 1)
        return text

    def _ensure_array_key(text, key, default_list):
        """
        Ensure key : [ ... ] exists and is valid.
        Replace if missing, not array, length too short, or indices 2..n are non-numeric or zero.
        """
        pat = re.compile(rf'"{re.escape(key)}"\s*:\s*(\[[^\]]*\])', flags=re.IGNORECASE)
        m = pat.search(text)
        if m:
            arr_text = m.group(1)
            try:
                arr = json.loads(arr_text)
                if not isinstance(arr, list) or len(arr) < len(default_list):
                    text = _set_key_in_text(text, key, json.dumps(default_list))
                else:
                    bad = False
                    for i in range(2, len(default_list)):
                        try:
                            val = arr[i]
                            if not isinstance(val, (int, float)) or val == 0:
                                bad = True
                                break
                        except Exception:
                            bad = True
                            break
                    if bad:
                        text = _set_key_in_text(text, key, json.dumps(default_list))
            except Exception:
                text = _set_key_in_text(text, key, json.dumps(default_list))
        else:
            text = _set_key_in_text(text, key, json.dumps(default_list))
        return text

    def _ensure_settings_dictionary(text, default_dict):
        # explicit null or 0 -> replace
        if re.search(r'"settingsDictionaryForNGPScreen"\s*:\s*null', text, flags=re.IGNORECASE) or re.search(r'"settingsDictionaryForNGPScreen"\s*:\s*0\b', text):
            text = re.sub(r'"settingsDictionaryForNGPScreen"\s*:\s*(null|0\b)', f'"settingsDictionaryForNGPScreen": {json.dumps(default_dict)}', text, flags=re.IGNORECASE)
        # if present as object -> validate parse
        m = re.search(r'"settingsDictionaryForNGPScreen"\s*:\s*({[^}]*})', text)
        if m:
            try:
                obj = json.loads(m.group(1))
                if not isinstance(obj, dict):
                    text = _set_key_in_text(text, "settingsDictionaryForNGPScreen", json.dumps(default_dict))
            except Exception:
                text = _set_key_in_text(text, "settingsDictionaryForNGPScreen", json.dumps(default_dict))
        else:
            # missing -> insert
            text = _set_key_in_text(text, "settingsDictionaryForNGPScreen", json.dumps(default_dict))
        return text

    def _read_scalar_key(text: str, key: str):
        m = re.search(
            rf'"{re.escape(key)}"\s*:\s*(".*?"|[-]?\d+(\.\d+)?|true|false|null)',
            text,
            flags=re.IGNORECASE,
        )
        if not m:
            return None
        raw = m.group(1).strip()
        rl = raw.lower()
        if rl == "true":
            return True
        if rl == "false":
            return False
        if rl == "null":
            return None
        if raw.startswith('"') and raw.endswith('"'):
            return raw[1:-1]
        try:
            if "." in raw:
                return float(raw)
            return int(raw)
        except Exception:
            return raw

    def _load_settings_dictionary(text: str, default_dict: dict):
        out = dict(default_dict)
        m = re.search(r'"settingsDictionaryForNGPScreen"\s*:\s*({[^}]*})', text)
        if not m:
            return out
        try:
            obj = json.loads(m.group(1))
            if isinstance(obj, dict):
                out.update(obj)
        except Exception:
            pass
        return out

    def _resolve_rule_selection(rule: dict):
        opts = rule["options"]
        current_label = rule["var"].get()
        current_value = opts.get(current_label, _choose_safe_default(opts))
        if current_label != _RULE_RANDOM_LABEL and current_value != _RULE_RANDOM_VALUE:
            return current_label, current_value

        concrete_labels = [lab for lab, val in opts.items() if lab != _RULE_RANDOM_LABEL and val != _RULE_RANDOM_VALUE]
        if not concrete_labels:
            safe_label = next(iter(opts.keys()), _RULE_RANDOM_LABEL)
            safe_value = opts.get(safe_label, 0)
            return safe_label, safe_value

        chosen_label = random.choice(concrete_labels)
        chosen_value = opts.get(chosen_label, _choose_safe_default(opts))
        try:
            # Update UI to the concrete value that was written to the save.
            rule["var"].set(chosen_label)
        except Exception:
            pass
        return chosen_label, chosen_value

    # ---------- save/apply logic ----------
    def apply_all_rules():
        path = save_path_var.get()
        if not path or not os.path.exists(path):
            messagebox.showerror("Error", "Please select a valid save file first.")
            return

        tmp = path + ".rules_tmp"
        try:
            shutil.copy2(path, tmp)
        except Exception as e:
            messagebox.showerror("Error", f"Could not create temporary copy: {e}")
            return

        try:
            if random_rules_var.get():
                _set_all_rules_to_random()

            # 1) Resolve "random" labels to concrete choices up-front.
            #    This guarantees savers, linked logic, and dictionary sync all use
            #    the same final choice.
            resolved_rule_choices = {}
            for rule in FACTOR_RULE_VARS:
                resolved_rule_choices[rule["key"]] = _resolve_rule_selection(rule)

            # 2) Run direct key savers (non-virtual rules).
            for saver in rule_savers:
                try:
                    saver(tmp)
                except Exception as se:
                    print("rule saver error:", se)

            # 3) Read back for custom/special rule handling.
            with open(tmp, "r", encoding="utf-8") as f:
                text = f.read()

            # 4) Ensure each rule key exists and is not null.
            for rule in FACTOR_RULE_VARS:
                internal_key = rule["key"]
                options = rule["options"]
                safe = _choose_safe_default(options)
                text = _ensure_key_with_default_text(text, internal_key, safe, treat_zero_as_missing=False)

            # 5) Apply special linked rule behavior.
            for rule in FACTOR_RULE_VARS:
                key = rule["key"]
                opts = rule["options"]
                label, selected_value = resolved_rule_choices.get(
                    key, (rule["var"].get(), opts.get(rule["var"].get(), _choose_safe_default(opts)))
                )

                if key == "gameDifficultyMode":
                    try:
                        is_hard_bool = int(selected_value) == 1
                    except Exception:
                        is_hard_bool = False
                    text = _set_key_in_text(text, "isHardMode", json.dumps(is_hard_bool))
                    continue

                if key == "truckAvailability":
                    # Distinguish rank 10/20/30 when the base value is "AVAILABLE_FROM_LEVEL".
                    if label == "store unlocks at rank 10":
                        text = _set_key_in_text(text, "truckAvailabilityLevel", json.dumps(10))
                    elif label == "store unlocks at rank 20":
                        text = _set_key_in_text(text, "truckAvailabilityLevel", json.dumps(20))
                    elif label == "store unlocks at rank 30":
                        text = _set_key_in_text(text, "truckAvailabilityLevel", json.dumps(30))
                    continue

                if key == "internalAddonAvailability":
                    amt = _INTERNAL_ADDON_AMOUNT_BY_LABEL.get(label)
                    if amt is not None:
                        text = _set_key_in_text(text, "internalAddonAmount", json.dumps(int(amt)))
                    continue

                if key == "maxContestAttempts":
                    text = _set_key_in_text(text, "isGoldFailReason", json.dumps(label == "gold time only"))
                    if label == "gold time only":
                        text = _set_key_in_text(text, "maxContestAttempts", json.dumps(-1))
                    continue

                if key == "regionRepaireMoneyFactor":
                    # Keep money and points factors in sync for regional repair rule.
                    text = _set_key_in_text(text, "regionRepairePointsFactor", json.dumps(selected_value))
                    continue

                if key == "isDLCVehiclesAvailable":
                    # Keep this companion flag coherent with current availability choice.
                    try:
                        text = _set_key_in_text(text, "needToAddDlcTrucks", json.dumps(bool(selected_value)))
                    except Exception:
                        pass

            # 6) Ensure key defaults and special arrays.
            text = _ensure_key_with_default_text(text, "autoloadPrice", _DEFAULT_AUTOLOAD_PRICE, treat_zero_as_missing=True)
            text = _ensure_array_key(text, "recoveryPrice", _DEFAULT_RECOVERY_PRICE)
            text = _ensure_array_key(text, "fullRepairPrice", _DEFAULT_FULL_REPAIR_PRICE)

            # 7) settingsDictionaryForNGPScreen: ensure exists, then sync from selected rule labels.
            text = _ensure_settings_dictionary(text, _DEFAULT_SETTINGS_DICT)
            settings_dict = _load_settings_dictionary(text, _DEFAULT_SETTINGS_DICT)
            for rule in FACTOR_RULE_VARS:
                key = rule["key"]
                label, _ = resolved_rule_choices.get(key, (rule["var"].get(), None))
                meta = _RULE_NGP_DICT_META.get(key)
                if not meta:
                    continue
                ngp_key, label_to_state = meta
                state = label_to_state.get(label)
                if state is not None:
                    settings_dict[ngp_key] = int(state)
            text = _set_key_in_text(text, "settingsDictionaryForNGPScreen", json.dumps(settings_dict))

            # 8) deployPrice ensure object with Region/Map
            m = re.search(r'"deployPrice"\s*:\s*({[^}]*})', text)
            if m:
                try:
                    dp = json.loads(m.group(1))
                    if not isinstance(dp, dict) or "Region" not in dp or "Map" not in dp:
                        text = _set_key_in_text(text, "deployPrice", json.dumps(_DEFAULT_DEPLOY_PRICE))
                except Exception:
                    text = _set_key_in_text(text, "deployPrice", json.dumps(_DEFAULT_DEPLOY_PRICE))
            else:
                text = _set_key_in_text(text, "deployPrice", json.dumps(_DEFAULT_DEPLOY_PRICE))

            # 9) Compare & write
            with open(path, "r", encoding="utf-8") as f:
                original = f.read()

            if text == original:
                try:
                    os.remove(tmp)
                except Exception:
                    pass
                show_info("No changes", "No rule changes detected.")
                return

            _make_backup(path)
            with open(path, "w", encoding="utf-8") as f:
                f.write(text)
            try:
                os.remove(tmp)
            except Exception:
                pass
            show_info("Success", "Rules applied successfully.")
        except Exception as e:
            try:
                os.remove(tmp)
            except Exception:
                pass
            messagebox.showerror("Save failed", f"Failed to apply rules: {e}")

    # ---------- sync UI values from save to comboboxes ----------
    def sync_all_rules_from_save(path):
        if not path or not os.path.exists(path):
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            for rule in FACTOR_RULE_VARS:
                internal_key = rule["key"]
                options = rule["options"]
                var = rule["var"]

                # Special state inference for real keys.
                if internal_key == "truckAvailability":
                    avail = _read_scalar_key(content, "truckAvailability")
                    if avail == 2:
                        lvl = _read_scalar_key(content, "truckAvailabilityLevel")
                        if lvl is not None and int(lvl) >= 30 and "store unlocks at rank 30" in options:
                            var.set("store unlocks at rank 30")
                        elif lvl is not None and int(lvl) >= 20 and "store unlocks at rank 20" in options:
                            var.set("store unlocks at rank 20")
                        elif "store unlocks at rank 10" in options:
                            var.set("store unlocks at rank 10")
                        continue

                if internal_key == "maxContestAttempts":
                    is_gold = _read_scalar_key(content, "isGoldFailReason")
                    if is_gold is True and "gold time only" in options:
                        var.set("gold time only")
                        continue

                if internal_key == "regionRepaireMoneyFactor":
                    money_factor = _read_scalar_key(content, "regionRepaireMoneyFactor")
                    points_factor = _read_scalar_key(content, "regionRepairePointsFactor")
                    if money_factor is not None and points_factor is not None:
                        for lab, val in options.items():
                            if str(money_factor) == str(val) and str(points_factor) == str(val):
                                var.set(lab)
                                break
                        continue

                rawv = _read_scalar_key(content, internal_key)
                if rawv is None:
                    continue
                for lab, val in options.items():
                    if str(val) == str(rawv):
                        var.set(lab)
                        break
        except Exception as e:
            print("sync failed:", e)

    # ---------- register loader & trace save_path_var ----------
    pls = globals().get("plugin_loaders")
    if pls is None:
        plugin_loaders = []
        pls = plugin_loaders
    try:
        if sync_all_rules_from_save not in pls:
            pls.append(sync_all_rules_from_save)
    except Exception as e:
        print("Could not register rules loader in plugin_loaders:", e)

    try:
        save_path_var.trace_add("write", lambda *args: sync_all_rules_from_save(save_path_var.get()))
    except Exception:
        try:
            save_path_var.trace("w", lambda *args: sync_all_rules_from_save(save_path_var.get()))
        except Exception:
            pass

    # bottom Save button (centered)
    bottom = ttk.Frame(container)
    bottom.pack(fill="x", pady=(6,10))
    ttk.Checkbutton(bottom, text="Random rules", variable=random_rules_var, command=_on_random_rules_toggle).pack(anchor="center", pady=(0, 6))
    button_row = ttk.Frame(bottom)
    button_row.pack(fill="x")
    ttk.Frame(button_row).pack(side="left", expand=True)
    ttk.Button(button_row, text="Save Rules to Save File", command=apply_all_rules, width=30).pack(side="left")
    ttk.Frame(button_row).pack(side="left", expand=True)

    # initial sync
    p = save_path_var.get()
    if p and os.path.exists(p):
        sync_all_rules_from_save(p)

    return {
        "factor_vars": FACTOR_RULE_VARS,
        "rule_savers": rule_savers,
        "dropdown_widgets": dropdown_widgets
    }
# ---------- END: Final Rules tab ----------


GITHUB_RELEASES_API = "https://api.github.com/repos/MrBoxik/SnowRunner-Save-Editor/releases"
GITHUB_RELEASES_PAGE = "https://github.com/MrBoxik/SnowRunner-Save-Editor/releases"
GITHUB_MAIN_PAGE = "https://github.com/MrBoxik/SnowRunner-Save-Editor"
# -----------------------------------------------------------------------------
# END SECTION: Rules Tab Helpers (Rules tab)
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Update Checks
# Used In: Settings tab -> "Check for Update"
# =============================================================================
def _platform_release_suffix(system_name=None):
    system = str(system_name or platform.system() or "").strip().lower()
    if system == "windows":
        return "a"
    if system == "linux":
        return "b"
    if system == "darwin":
        return "c"
    return ""


def _select_latest_release_for_platform(releases, suffix):
    """Pick latest release matching suffix (a/b/c). Fallback to all releases when needed."""
    candidates = []
    for rel in releases:
        if not isinstance(rel, dict):
            continue
        tag_raw = str(rel.get("tag_name", "") or "").lstrip("v").strip()
        if not tag_raw:
            continue
        if suffix and not tag_raw.lower().endswith(suffix.lower()):
            continue
        num = normalize_version(tag_raw)
        published = str(rel.get("published_at", "") or rel.get("created_at", "") or "")
        candidates.append((num, published, tag_raw, rel))

    if not candidates and suffix:
        # Fallback for legacy tags that may not carry platform suffix.
        for rel in releases:
            if not isinstance(rel, dict):
                continue
            tag_raw = str(rel.get("tag_name", "") or "").lstrip("v").strip()
            if not tag_raw:
                continue
            num = normalize_version(tag_raw)
            published = str(rel.get("published_at", "") or rel.get("created_at", "") or "")
            candidates.append((num, published, tag_raw, rel))

    if not candidates:
        return None, ""

    candidates.sort(key=lambda x: (x[0], x[1]), reverse=True)
    _, _, tag_raw, rel = candidates[0]
    return rel, tag_raw


def _pick_windows_release_download_url(release, tag_raw):
    """Prefer .exe asset URL + expected size from release assets; fallback to default URL."""
    assets = release.get("assets") if isinstance(release, dict) else None
    picks = []
    if isinstance(assets, list):
        for asset in assets:
            if not isinstance(asset, dict):
                continue
            name = str(asset.get("name", "") or "")
            url = str(asset.get("browser_download_url", "") or "").strip()
            if not url:
                continue
            lname = name.lower()
            if not lname.endswith(".exe"):
                continue
            size_val = asset.get("size")
            try:
                size_val = int(size_val)
            except Exception:
                size_val = None
            score = 0
            if "snowrunner" in lname:
                score += 2
            if "editor" in lname:
                score += 1
            picks.append((score, lname, url, size_val))

    if picks:
        picks.sort(key=lambda x: (x[0], x[1]), reverse=True)
        return {
            "url": picks[0][2],
            "expected_size": picks[0][3],
        }

    clean_tag = str(tag_raw or "").strip()
    return {
        "url": f"https://github.com/MrBoxik/SnowRunner-Save-Editor/releases/download/{clean_tag}/snowrunner_editor.exe",
        "expected_size": None,
    }


def _download_file(url, dest_path, timeout=45, progress_callback=None):
    req = urllib.request.Request(
        str(url or ""),
        headers={
            "User-Agent": "SnowRunnerEditor/1.0",
            "Accept": "application/octet-stream",
        },
    )
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        total_bytes = None
        try:
            content_len = resp.headers.get("Content-Length")
            if content_len:
                total_bytes = int(content_len)
        except Exception:
            total_bytes = None

        bytes_read = 0
        t_start = time.time()
        t_last = t_start
        report_interval = 0.15

        if callable(progress_callback):
            try:
                progress_callback(0, total_bytes, 0.0, None)
            except Exception:
                pass

        with open(dest_path, "wb") as out:
            while True:
                chunk = resp.read(1024 * 64)
                if not chunk:
                    break
                out.write(chunk)
                bytes_read += len(chunk)

                now = time.time()
                if callable(progress_callback) and (now - t_last) >= report_interval:
                    elapsed = max(now - t_start, 0.001)
                    speed_bps = bytes_read / elapsed
                    eta_sec = None
                    if total_bytes and speed_bps > 0:
                        eta_sec = max((total_bytes - bytes_read) / speed_bps, 0.0)
                    try:
                        progress_callback(bytes_read, total_bytes, speed_bps, eta_sec)
                    except Exception:
                        pass
                    t_last = now

        if callable(progress_callback):
            now = time.time()
            elapsed = max(now - t_start, 0.001)
            speed_bps = bytes_read / elapsed
            eta_sec = 0.0 if total_bytes else None
            try:
                progress_callback(bytes_read, total_bytes, speed_bps, eta_sec)
            except Exception:
                pass


def _resolve_windows_update_work_dir(fallback_dir=""):
    """
    Resolve a writable working directory for updater artifacts.
    Prefer the editor data folder (same location as config) so update temp files
    stay out of the dist/exe folder.
    """
    try:
        preferred = os.path.abspath(str(get_editor_data_dir() or "").strip())
        if preferred:
            os.makedirs(preferred, exist_ok=True)
            return preferred
    except Exception:
        pass

    try:
        fb = os.path.abspath(str(fallback_dir or "").strip())
    except Exception:
        fb = ""
    if not fb:
        try:
            fb = os.path.abspath(tempfile.gettempdir())
        except Exception:
            fb = os.path.abspath(".")
    try:
        os.makedirs(fb, exist_ok=True)
    except Exception:
        pass
    return fb


def _prepare_windows_self_update(
    download_url,
    latest_tag,
    expected_size=None,
    progress_callback=None,
):
    """
    Download latest .exe and return update payload for external replacer.
    """
    if platform.system() != "Windows":
        raise RuntimeError("Auto update is available only on Windows.")
    if not getattr(sys, "frozen", False):
        raise RuntimeError("Auto update is available only in the built .exe.")

    current_exe = os.path.abspath(sys.executable)
    if not os.path.isfile(current_exe):
        raise RuntimeError("Current executable path is invalid.")

    tag = str(latest_tag or "").strip() or "latest"
    target_dir = os.path.dirname(current_exe)
    if not os.path.isdir(target_dir):
        raise RuntimeError("Executable directory is invalid.")
    # Keep update payload in editor data folder (same place as config) for cleaner dist folder.
    # Use per-run non-.exe payload name to avoid clashes with stale updater runs.
    work_dir = _resolve_windows_update_work_dir(target_dir)
    run_id = f"{int(time.time())}_{os.getpid()}"
    new_exe = os.path.join(work_dir, f"snowrunner_editor_update_payload_{run_id}.bin")
    try:
        if os.path.exists(new_exe):
            os.remove(new_exe)
    except Exception:
        pass

    _download_file(
        download_url,
        new_exe,
        timeout=60,
        progress_callback=progress_callback,
    )
    try:
        size = os.path.getsize(new_exe)
    except Exception:
        size = 0
    if size < 1024 * 200:
        raise RuntimeError("Downloaded file is unexpectedly small; update aborted.")
    if expected_size and size != int(expected_size):
        raise RuntimeError(
            f"Downloaded file size mismatch ({size} vs expected {int(expected_size)})."
        )

    return {
        "target_exe": current_exe,
        "new_exe": new_exe,
        "latest_tag": tag,
    }


def _run_windows_updater_script(update_payload):
    if platform.system() != "Windows":
        raise RuntimeError("Updater launcher is Windows-only.")

    if not isinstance(update_payload, dict):
        raise RuntimeError("Invalid updater payload.")

    target_exe = os.path.abspath(str(update_payload.get("target_exe", "") or "").strip())
    new_exe = os.path.abspath(str(update_payload.get("new_exe", "") or "").strip())
    if not target_exe or not new_exe:
        raise RuntimeError("Updater payload is missing executable paths.")
    if not os.path.isfile(new_exe):
        raise RuntimeError("Downloaded update file is missing.")
    script_dir = _resolve_windows_update_work_dir(os.path.dirname(target_exe))
    launch_token = f"{int(time.time() * 1000)}_{os.getpid()}"

    def _ps_quote(text):
        return str(text or "").replace("'", "''")

    ack_path = os.path.join(script_dir, f"snowrunner_editor_updater_ack_{launch_token}.txt")

    def _wait_for_launch_ack(log_path, ack_file_path, token, timeout_sec=3.0):
        deadline = time.time() + float(timeout_sec)
        marker = f"run={token}"
        while time.time() < deadline:
            try:
                if os.path.exists(ack_file_path):
                    return True
            except Exception:
                pass
            try:
                if os.path.exists(log_path):
                    with open(log_path, "r", encoding="utf-8", errors="ignore") as fh:
                        content = fh.read()
                    if marker in content:
                        return True
            except Exception:
                pass
            time.sleep(0.08)
        return False

    script_path = os.path.join(script_dir, f"snowrunner_editor_updater_{int(time.time())}.ps1")
    log_path = os.path.join(tempfile.gettempdir(), "snowrunner_updater.log")
    ps_script = (
        "$ErrorActionPreference='Continue'\n"
        f"$target='{_ps_quote(target_exe)}'\n"
        f"$newFile='{_ps_quote(new_exe)}'\n"
        f"$workDir='{_ps_quote(script_dir)}'\n"
        f"$releases='{_ps_quote(GITHUB_RELEASES_PAGE)}'\n"
        f"$runId='{_ps_quote(launch_token)}'\n"
        f"$ackFile='{_ps_quote(ack_path)}'\n"
        "$tmpCopy=($target + '.updating.tmp')\n"
        "$pyiVars=@('_MEIPASS2','_PYI_PARENT_PROCESS_LEVEL','_PYI_APPLICATION_HOME_DIR','_PYI_ARCHIVE_FILE','_PYI_SPLASH_IPC','_PYI_SPLASH_IPC_PORT','_PYI_SPLASH_IPC_SOCKET','_PYI_PROCNAME')\n"
        "$log=([System.IO.Path]::Combine([System.IO.Path]::GetTempPath(),'snowrunner_updater.log'))\n"
        "function LogLine([string]$m){ try{ Add-Content -LiteralPath $log -Value ((Get-Date -Format 's') + ' ' + $m) -Encoding UTF8 } catch{} }\n"
        "LogLine ('Updater started [v15-configworkdir] run=' + $runId + ' target=' + $target + ' new=' + $newFile + ' work=' + $workDir)\n"
        "try{ Set-Content -LiteralPath $ackFile -Value ('run=' + $runId) -Encoding Ascii -Force } catch{}\n"
        "if(-not (Test-Path -LiteralPath $newFile)){\n"
        "  LogLine 'Payload missing before replace; aborting'\n"
        "  Start-Process -FilePath $releases\n"
        "  try{ Remove-Item -LiteralPath $ackFile -Force -ErrorAction SilentlyContinue } catch{}\n"
        "  exit\n"
        "}\n"
        "$ok=$false\n"
        "for($i=0;$i -lt 360;$i++){\n"
        "  try{\n"
        "    Copy-Item -LiteralPath $newFile -Destination $tmpCopy -Force -ErrorAction Stop\n"
        "    if(Test-Path -LiteralPath $target){ Remove-Item -LiteralPath $target -Force -ErrorAction Stop }\n"
        "    Move-Item -LiteralPath $tmpCopy -Destination $target -Force -ErrorAction Stop\n"
        "    $ok=$true\n"
        "    LogLine 'Replace succeeded'\n"
        "    break\n"
        "  }\n"
        "  catch{\n"
        "    LogLine ('Replace retry #' + $i + ' failed: ' + $_.Exception.Message)\n"
        "    Remove-Item -LiteralPath $tmpCopy -Force -ErrorAction SilentlyContinue\n"
        "    if(-not (Test-Path -LiteralPath $newFile)){\n"
        "      LogLine 'Payload missing during retries; aborting'\n"
        "      break\n"
        "    }\n"
        "    Start-Sleep -Milliseconds 250\n"
        "  }\n"
        "}\n"
        "if($ok){\n"
        "  foreach($ev in $pyiVars){\n"
        "    try{ Remove-Item -Path ('Env:' + $ev) -ErrorAction SilentlyContinue } catch{}\n"
        "    try{ [System.Environment]::SetEnvironmentVariable($ev, $null, 'Process') } catch{}\n"
        "  }\n"
        "  LogLine 'Cleared inherited PyInstaller environment vars'\n"
        "  Start-Sleep -Milliseconds 250\n"
        "  $started=$false\n"
        "  try{\n"
        "    $launcher=[System.IO.Path]::Combine($workDir, ('snowrunner_editor_relaunch_' + $runId + '.cmd'))\n"
        "    $cmd=@\"\n"
        "@echo off\n"
        "set _MEIPASS2=\n"
        "set _PYI_PARENT_PROCESS_LEVEL=\n"
        "set _PYI_APPLICATION_HOME_DIR=\n"
        "set _PYI_ARCHIVE_FILE=\n"
        "set _PYI_SPLASH_IPC=\n"
        "set _PYI_SPLASH_IPC_PORT=\n"
        "set _PYI_SPLASH_IPC_SOCKET=\n"
        "set _PYI_PROCNAME=\n"
        "timeout /t 1 /nobreak >nul\n"
        "start \"\" \"$target\"\n"
        "del /f /q \"%~f0\" >nul 2>&1\n"
        "\"@\n"
        "    Set-Content -LiteralPath $launcher -Value $cmd -Encoding Ascii -Force\n"
        "    Start-Process -FilePath $launcher -WindowStyle Hidden -ErrorAction Stop\n"
        "    $started=$true\n"
        "  }\n"
        "  catch{\n"
        "    LogLine ('Relaunch scheduler failed: ' + $_.Exception.Message)\n"
        "  }\n"
        "  if($started){\n"
        "    LogLine 'Started updated editor'\n"
        "    Remove-Item -LiteralPath $newFile -Force -ErrorAction SilentlyContinue\n"
        "    Remove-Item -LiteralPath $tmpCopy -Force -ErrorAction SilentlyContinue\n"
        "  }\n"
        "  else{\n"
        "    LogLine 'Failed to start updated editor; opening releases page'\n"
        "    Start-Process -FilePath $releases\n"
        "  }\n"
        "}\n"
        "else{\n"
        "  Remove-Item -LiteralPath $tmpCopy -Force -ErrorAction SilentlyContinue\n"
        "  Remove-Item -LiteralPath $newFile -Force -ErrorAction SilentlyContinue\n"
        "  LogLine 'Replace failed; opening releases page'\n"
        "  Start-Process -FilePath $releases\n"
        "}\n"
        "try{ Remove-Item -LiteralPath $ackFile -Force -ErrorAction SilentlyContinue } catch{}\n"
        "try{ Remove-Item -LiteralPath $PSCommandPath -Force -ErrorAction SilentlyContinue } catch{}\n"
    )
    # Windows PowerShell treats UTF-16 BOM scripts as canonical; this avoids
    # Unicode path mangling on non-ASCII usernames (e.g., Vlastnik with accents).
    with open(script_path, "w", encoding="utf-16", newline="\r\n") as f:
        f.write(ps_script)

    si = None
    try:
        si = subprocess.STARTUPINFO()
        si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
    except Exception:
        si = None
    CREATE_NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0x08000000)
    DETACHED_PROCESS = getattr(subprocess, "DETACHED_PROCESS", 0x00000008)
    CREATE_NEW_PROCESS_GROUP = getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0x00000200)
    CREATE_BREAKAWAY_FROM_JOB = getattr(subprocess, "CREATE_BREAKAWAY_FROM_JOB", 0x01000000)
    launch_flags = (
        CREATE_NO_WINDOW
        | DETACHED_PROCESS
        | CREATE_NEW_PROCESS_GROUP
        | CREATE_BREAKAWAY_FROM_JOB
    )
    launch_error = None
    launch_variants = [
        (
            "powershell",
            [
                "powershell",
                "-NoProfile",
                "-ExecutionPolicy",
                "Bypass",
                "-WindowStyle",
                "Hidden",
                "-File",
                script_path,
            ],
            launch_flags,
            2.4,
        ),
        (
            "pwsh",
            [
                "pwsh",
                "-NoProfile",
                "-ExecutionPolicy",
                "Bypass",
                "-WindowStyle",
                "Hidden",
                "-File",
                script_path,
            ],
            launch_flags,
            2.4,
        ),
        (
            "cmd->powershell",
            [
                "cmd",
                "/c",
                "start",
                "",
                "powershell",
                "-NoProfile",
                "-ExecutionPolicy",
                "Bypass",
                "-WindowStyle",
                "Hidden",
                "-File",
                script_path,
            ],
            CREATE_NO_WINDOW,
            3.0,
        ),
        (
            "cmd->pwsh",
            [
                "cmd",
                "/c",
                "start",
                "",
                "pwsh",
                "-NoProfile",
                "-ExecutionPolicy",
                "Bypass",
                "-WindowStyle",
                "Hidden",
                "-File",
                script_path,
            ],
            CREATE_NO_WINDOW,
            3.0,
        ),
    ]
    for variant_name, argv, flags, ack_timeout in launch_variants:
        try:
            try:
                if os.path.exists(ack_path):
                    os.remove(ack_path)
            except Exception:
                pass
            proc = subprocess.Popen(
                argv,
                startupinfo=si,
                creationflags=flags,
                close_fds=True,
            )
            # Quick sanity check: if launcher dies instantly with non-zero, fallback.
            time.sleep(0.20)
            rc = proc.poll()
            if rc is not None and rc != 0:
                launch_error = RuntimeError(f"{variant_name} exited immediately with code {rc}")
                continue
            # Reliable handoff: updater must confirm startup via ack file/log marker.
            if _wait_for_launch_ack(log_path, ack_path, launch_token, timeout_sec=ack_timeout):
                return
            launch_error = RuntimeError(f"{variant_name} did not acknowledge updater start (rc={rc})")
            continue
        except Exception as e:
            launch_error = e
            continue

    raise RuntimeError(f"Failed to launch updater shell: {launch_error}")


def _cleanup_windows_update_artifacts(exe_path=None):
    """
    Best-effort cleanup of updater leftovers next to the running executable.
    Keeps only the main .exe after successful in-place update.
    """
    if platform.system() != "Windows":
        return
    # Never clean updater artifacts while an in-process update is being prepared/launched.
    # This avoids races where payload/ack files are removed before the updater consumes them.
    try:
        if bool(globals().get("_WINDOWS_UPDATE_IN_PROGRESS", False)):
            return
    except Exception:
        pass

    try:
        if exe_path:
            target_exe = os.path.abspath(str(exe_path))
        elif getattr(sys, "frozen", False):
            target_exe = os.path.abspath(sys.executable)
        else:
            return
    except Exception:
        return

    base_dir = os.path.dirname(target_exe)
    if not base_dir or not os.path.isdir(base_dir):
        return

    artifact_dirs = []
    try:
        if os.path.isdir(base_dir):
            artifact_dirs.append(base_dir)
    except Exception:
        pass
    try:
        work_dir = _resolve_windows_update_work_dir(base_dir)
        if work_dir and os.path.isdir(work_dir):
            norms = {os.path.normcase(os.path.normpath(d)) for d in artifact_dirs}
            wnorm = os.path.normcase(os.path.normpath(work_dir))
            if wnorm not in norms:
                artifact_dirs.append(work_dir)
    except Exception:
        pass

    candidates = [
        target_exe + ".previous.exe",
        target_exe + ".updating.tmp",
    ]

    for p in candidates:
        try:
            if os.path.exists(p):
                os.remove(p)
        except Exception:
            pass

    for scan_dir in artifact_dirs:
        try:
            for name in os.listdir(scan_dir):
                lname = name.lower()
                if lname.startswith("snowrunner_editor_updater_") and lname.endswith(".ps1"):
                    p = os.path.join(scan_dir, name)
                    try:
                        os.remove(p)
                    except Exception:
                        pass
                elif lname.startswith("snowrunner_editor_updater_ack_") and lname.endswith(".txt"):
                    p = os.path.join(scan_dir, name)
                    try:
                        os.remove(p)
                    except Exception:
                        pass
                elif lname.startswith("snowrunner_editor_relaunch_") and lname.endswith(".cmd"):
                    p = os.path.join(scan_dir, name)
                    try:
                        os.remove(p)
                    except Exception:
                        pass
                elif lname.startswith("snowrunner_editor_update_payload_") and lname.endswith(".bin"):
                    p = os.path.join(scan_dir, name)
                    try:
                        os.remove(p)
                    except Exception:
                        pass
        except Exception:
            pass


def _start_windows_update_artifact_cleanup_retry(exe_path=None, attempts=80, interval_sec=0.5):
    """Retry cleanup in the background so leftovers disappear shortly after restart."""
    if platform.system() != "Windows":
        return

    try:
        if exe_path:
            target_exe = os.path.abspath(str(exe_path))
        elif getattr(sys, "frozen", False):
            target_exe = os.path.abspath(sys.executable)
        else:
            return
    except Exception:
        return

    def _has_leftovers():
        try:
            base_dir = os.path.dirname(target_exe)
            if not base_dir or not os.path.isdir(base_dir):
                return False
            scan_dirs = []
            if os.path.isdir(base_dir):
                scan_dirs.append(base_dir)
            try:
                work_dir = _resolve_windows_update_work_dir(base_dir)
                if work_dir and os.path.isdir(work_dir):
                    norms = {os.path.normcase(os.path.normpath(d)) for d in scan_dirs}
                    wnorm = os.path.normcase(os.path.normpath(work_dir))
                    if wnorm not in norms:
                        scan_dirs.append(work_dir)
            except Exception:
                pass
            static_paths = [
                target_exe + ".previous.exe",
                target_exe + ".updating.tmp",
            ]
            for p in static_paths:
                if os.path.exists(p):
                    return True
            for scan_dir in scan_dirs:
                for name in os.listdir(scan_dir):
                    lname = str(name).lower()
                    if lname.startswith("snowrunner_editor_updater_") and lname.endswith(".ps1"):
                        return True
                    if lname.startswith("snowrunner_editor_updater_ack_") and lname.endswith(".txt"):
                        return True
                    if lname.startswith("snowrunner_editor_relaunch_") and lname.endswith(".cmd"):
                        return True
                    if lname.startswith("snowrunner_editor_update_payload_") and lname.endswith(".bin"):
                        return True
            return False
        except Exception:
            return False

    def _worker():
        loops = max(1, int(attempts))
        delay = max(0.05, float(interval_sec))
        for _ in range(loops):
            _cleanup_windows_update_artifacts(target_exe)
            if not _has_leftovers():
                break
            time.sleep(delay)

    threading.Thread(target=_worker, daemon=True).start()


def normalize_version(tag: str) -> int:
    """
    Extract numeric part of version string only.
    Example:
      '69a' -> 69
      '69b' -> 69
      '70'  -> 70
    """
    m = re.match(r"(\d+)", str(tag))
    return int(m.group(1)) if m else 0
def check_for_updates_background(root, debug=False):
    """Check GitHub for newer release in a background thread."""
    def log(msg):
        if debug:
            print(f"[UpdateCheck] {msg}")

    result_box = {}
    done = threading.Event()

    def worker():
        system_name = platform.system()
        platform_suffix = _platform_release_suffix(system_name)
        result = {
            "status": None,  # "update", "dev", "none", or None on failure/skip
            "current_num": normalize_version(APP_VERSION),
            "latest_num": None,
            "latest_raw": None,
            "platform_suffix": platform_suffix,
            "download_url": None,
            "download_size": None,
        }
        try:
            log("Trying to reach GitHub API...")
            req = urllib.request.Request(
                GITHUB_RELEASES_API,
                headers={
                    "User-Agent": "SnowRunnerEditor/1.0",
                    "Accept": "application/vnd.github+json",
                },
            )
            try:
                with urllib.request.urlopen(req, timeout=5) as resp:
                    status = int(getattr(resp, "status", 0) or resp.getcode() or 0)
                    body = resp.read()
            except urllib.error.HTTPError as he:
                log(f"GitHub API returned {he.code}, skipping.")
                return
            if status != 200:
                log(f"GitHub API returned {status}, skipping.")
                return
            log("Internet connection OK")

            try:
                releases = json.loads(body.decode("utf-8", errors="replace"))
            except Exception:
                log("Failed to parse GitHub response JSON.")
                return
            if not isinstance(releases, list) or not releases:
                log("No releases found, aborting.")
                return

            selected_release, latest_raw = _select_latest_release_for_platform(releases, platform_suffix)
            if not latest_raw:
                log("No valid tag found for this platform, aborting.")
                return

            tags_preview = [str(rel.get("tag_name", "") or "").lstrip("v") for rel in releases[:15]]
            log(f"Found tags (preview): {tags_preview}")
            log(f"Using suffix '{platform_suffix or '-'}' on {system_name}: selected {latest_raw}")

            latest_num = normalize_version(latest_raw)
            result["latest_raw"] = latest_raw
            result["latest_num"] = latest_num

            log(f"Latest tag after normalization: raw={latest_raw}, numeric={latest_num}")

            if system_name == "Windows" and selected_release is not None:
                pick = _pick_windows_release_download_url(selected_release, latest_raw)
                if isinstance(pick, dict):
                    result["download_url"] = str(pick.get("url", "") or "").strip() or None
                    try:
                        size_val = pick.get("expected_size")
                        result["download_size"] = int(size_val) if size_val is not None else None
                    except Exception:
                        result["download_size"] = None

            current_num = normalize_version(APP_VERSION)
            result["current_num"] = current_num
            log(f"Normalized versions: current={current_num}, latest={latest_num}")

            if latest_num > current_num:
                log("Newer version detected; scheduling popup.")
                result["status"] = "update"
            elif latest_num < current_num:
                log("Current version ahead of latest; dev build.")
                result["status"] = "dev"
            else:
                log("No update available.")
                result["status"] = "none"

        except Exception as e:
            log(f"Update check failed: {e}")
        finally:
            result_box["result"] = result
            done.set()

    def _apply_result_on_main_thread():
        if not done.is_set():
            try:
                root.after(120, _apply_result_on_main_thread)
            except Exception:
                pass
            return

        result = result_box.get("result") or {}
        status = result.get("status")
        current_num = result.get("current_num", normalize_version(APP_VERSION))
        latest_num = result.get("latest_num", current_num)
        latest_raw = str(result.get("latest_raw", "") or latest_num)
        is_windows = platform.system() == "Windows"
        download_url = str(result.get("download_url", "") or "").strip()
        download_size = result.get("download_size")

        try:
            if status in ("update", "dev", "none"):
                globals()["_UPDATE_STATUS"] = status
        except Exception:
            pass

        try:
            footer = globals().get("_VERSION_FOOTER_LABEL")
            if footer is not None:
                if status == "update":
                    footer.config(text=f"Version: {APP_VERSION} (update available)")
                elif status == "dev":
                    footer.config(text=f"Version: {APP_VERSION} (dev build)")
                elif status == "none":
                    footer.config(text=f"Version: {APP_VERSION}")
        except Exception:
            pass

        if status == "update":
            try:
                cfg = _load_config_safe()
                if _cfg_bool(cfg.get("start_with_windows", False), default=False):
                    set_app_status(
                        "Update available. Startup will switch to the newer version after you launch it once.",
                        timeout_ms=10000,
                    )
            except Exception:
                pass

        if status != "update":
            return

        # During startup, root is temporarily withdrawn. If we build the popup too early,
        # some systems may never present it. Defer popup creation until the main window is visible.
        try:
            root_state = str(root.state()).strip().lower()
        except Exception:
            root_state = "normal"
        try:
            root_visible = bool(root.winfo_viewable())
        except Exception:
            root_visible = (root_state != "withdrawn")
        if root_state == "withdrawn" or not root_visible:
            retry_count = int(result_box.get("_update_popup_retry_count", 0) or 0)
            if retry_count < 120:
                result_box["_update_popup_retry_count"] = retry_count + 1
                try:
                    root.after(120, _apply_result_on_main_thread)
                except Exception:
                    pass
                return
            try:
                set_app_status(
                    "Update available, but popup could not be shown automatically. "
                    "Use Settings > Check for Update.",
                    timeout_ms=10000,
                )
            except Exception:
                pass
            return

        try:
            top = _create_themed_toplevel(root)
            top.title("Update Available")
            top.geometry("420x250")
            try:
                top.transient(root)
            except Exception:
                pass

            def _bring_update_popup_to_front():
                try:
                    top.lift()
                    top.focus_force()
                except Exception:
                    pass
                try:
                    # Temporary topmost to prevent startup redraws from hiding it.
                    top.attributes("-topmost", True)
                    top.after(250, lambda: top.attributes("-topmost", False))
                except Exception:
                    pass

            ttk.Label(
                top,
                text=f"A new version is available!\n\n"
                     f"Current: {current_num}\nLatest: {latest_raw}",
                justify="center",
                wraplength=340
            ).pack(pady=10)

            def open_page():
                webbrowser.open(GITHUB_RELEASES_PAGE)

            def copy_link():
                root.clipboard_clear()
                root.clipboard_append(GITHUB_RELEASES_PAGE)
                root.update()
                show_info("Copied", "Releases page link copied to clipboard.")

            btn_frame = ttk.Frame(top)
            btn_frame.pack(pady=10)

            if is_windows:
                status_var = tk.StringVar(value="")
                status_label = ttk.Label(top, textvariable=status_var, justify="center", wraplength=340)
                status_label.pack(pady=(0, 8))
                download_bar = ttk.Progressbar(top, orient="horizontal", length=320, mode="determinate", maximum=100.0)
                _download_bar_state = {"visible": False}

                def _show_download_bar():
                    if _download_bar_state["visible"]:
                        return
                    try:
                        download_bar.pack(pady=(0, 8))
                    except Exception:
                        pass
                    _download_bar_state["visible"] = True

                auto_btn = ttk.Button(btn_frame, text="Auto Update")
                auto_btn.pack(side="left", padx=5)

                def _fmt_size(num_bytes):
                    try:
                        n = float(max(0, int(num_bytes)))
                    except Exception:
                        return "0 B"
                    units = ["B", "KB", "MB", "GB"]
                    idx = 0
                    while n >= 1024.0 and idx < len(units) - 1:
                        n /= 1024.0
                        idx += 1
                    if idx == 0:
                        return f"{int(n)} {units[idx]}"
                    return f"{n:.1f} {units[idx]}"

                def _fmt_eta(seconds):
                    if seconds is None:
                        return ""
                    try:
                        s = int(max(0, round(float(seconds))))
                    except Exception:
                        return ""
                    if s < 60:
                        return f"{s}s"
                    m, s = divmod(s, 60)
                    if m < 60:
                        return f"{m}m {s}s"
                    h, m = divmod(m, 60)
                    return f"{h}h {m}m"

                def _update_download_ui(downloaded, total, speed_bps, eta_sec):
                    def _apply():
                        try:
                            _show_download_bar()
                            if total and int(total) > 0:
                                pct = max(0.0, min(100.0, (float(downloaded) * 100.0) / float(total)))
                                download_bar.stop()
                                download_bar.configure(mode="determinate", maximum=100.0, value=pct)
                                eta_text = _fmt_eta(eta_sec)
                                eta_part = f", ETA {eta_text}" if eta_text else ""
                                status_var.set(
                                    f"Downloading... {pct:.1f}% "
                                    f"({_fmt_size(downloaded)}/{_fmt_size(total)}) "
                                    f"at {_fmt_size(speed_bps)}/s{eta_part}"
                                )
                            else:
                                if str(download_bar.cget("mode")) != "indeterminate":
                                    download_bar.configure(mode="indeterminate")
                                    download_bar.start(12)
                                status_var.set(
                                    f"Downloading... {_fmt_size(downloaded)} "
                                    f"at {_fmt_size(speed_bps)}/s"
                                )
                        except Exception:
                            pass
                    try:
                        root.after(0, _apply)
                    except Exception:
                        pass

                def _finish_auto_update(update_payload=None, err_text=None):
                    global _WINDOWS_UPDATE_IN_PROGRESS
                    try:
                        download_bar.stop()
                    except Exception:
                        pass
                    if err_text:
                        _WINDOWS_UPDATE_IN_PROGRESS = False
                        try:
                            auto_btn.config(state="normal")
                        except Exception:
                            pass
                        status_var.set(err_text)
                        return
                    try:
                        _run_windows_updater_script(update_payload)
                    except Exception as e:
                        _WINDOWS_UPDATE_IN_PROGRESS = False
                        try:
                            auto_btn.config(state="normal")
                        except Exception:
                            pass
                        status_var.set(f"Failed to launch updater: {e}")
                        return

                    status_var.set("Applying update and restarting now...")
                    try:
                        root.update_idletasks()
                    except Exception:
                        pass
                    try:
                        # Short head start for detached updater, then exit quickly.
                        time.sleep(0.10)
                    except Exception:
                        pass
                    try:
                        top.destroy()
                    except Exception:
                        pass
                    try:
                        root.destroy()
                    except Exception:
                        pass
                    # Ensure the running .exe releases its file lock so updater can replace it.
                    os._exit(0)

                def _start_auto_update():
                    global _WINDOWS_UPDATE_IN_PROGRESS
                    if not download_url:
                        status_var.set("No Windows download URL found for this release.")
                        return
                    _WINDOWS_UPDATE_IN_PROGRESS = True
                    try:
                        auto_btn.config(state="disabled")
                    except Exception:
                        pass
                    try:
                        _show_download_bar()
                        download_bar.stop()
                        download_bar.configure(mode="determinate", maximum=100.0, value=0.0)
                    except Exception:
                        pass
                    status_var.set("Downloading latest Windows build...")

                    def _auto_update_worker():
                        update_payload = None
                        err_text = None
                        try:
                            update_payload = _prepare_windows_self_update(
                                download_url,
                                latest_raw,
                                expected_size=download_size,
                                progress_callback=_update_download_ui,
                            )
                        except Exception as e:
                            err_text = f"Auto update failed: {e}"
                        try:
                            root.after(
                                0,
                                lambda payload=update_payload, err=err_text: _finish_auto_update(payload, err),
                            )
                        except Exception:
                            try:
                                globals()["_WINDOWS_UPDATE_IN_PROGRESS"] = False
                            except Exception:
                                pass

                    threading.Thread(target=_auto_update_worker, daemon=True).start()

                auto_btn.config(command=_start_auto_update)
            else:
                ttk.Button(btn_frame, text="Open Page", command=open_page).pack(side="left", padx=5)
                ttk.Button(btn_frame, text="Copy Link", command=copy_link).pack(side="left", padx=5)

            # Raise now and again shortly after, because the main window is still finishing startup.
            _bring_update_popup_to_front()
            top.after(120, _bring_update_popup_to_front)
            top.after(350, _bring_update_popup_to_front)
        except Exception as e:
            log(f"Failed to show update popup: {e}")

    # Start polling from the main thread before worker completion.
    try:
        root.after(120, _apply_result_on_main_thread)
    except Exception:
        pass

    # Run network work in background.
    threading.Thread(target=worker, daemon=True).start()

# -----------------------------------------------------------------------------
# END SECTION: Update Checks
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Dependency Checks + App Launch
# Used In: __main__ entrypoint
# =============================================================================
def check_dependencies():
    """Check for required dependencies and warn if missing."""
    missing = []
    
    # Check tkinter
    try:
        import tkinter
    except ImportError:
        missing.append(
            "tkinter: Install with 'python -m pip install python3-tk' (Linux/macOS) "
            "or use python.org installer (macOS/Windows)"
        )
    
    if missing:
        print("\n⚠️  WARNING: Missing dependencies:")
        for msg in missing:
            print(f"  • {msg}")
        print()
        
        # Only exit if tkinter is missing (critical)
        if "tkinter" in missing[0]:
            print("❌ tkinter is required to run this application.")
            sys.exit(1)


def _log_platform_support_status():
    """
    Print a concise platform-compatibility note.
    The app remains runnable on non-Windows platforms with safe fallbacks.
    """
    system = platform.system()
    if system == "Windows":
        print("[Platform] Windows detected: full feature set enabled.")
    elif system in ("Linux", "Darwin"):
        print(
            f"[Platform] {system} detected: core editor enabled with fallbacks for "
            "Windows-specific integrations (native title-bar theming/AppUserModelID/taskbar tweaks)."
        )
    else:
        print(
            f"[Platform] {system} detected: untested platform. Core editor will attempt to run "
            "with safe fallbacks; some integrations may be unavailable."
        )


# UI helper: hide dotted focus rectangles without disabling focus/clicking
def _apply_focus_outline_fix(root):
    try:
        style = ttk.Style(root)
    except Exception:
        return

    try:
        bg = root.cget("background")
    except Exception:
        try:
            bg = style.lookup("TFrame", "background")
        except Exception:
            bg = ""
    if not bg:
        bg = "SystemButtonFace"

    def _strip_focus(layout):
        if not layout:
            return layout
        new_layout = []
        for elem, opts in layout:
            children = None
            if isinstance(opts, dict):
                children = opts.get("children")

            if "focus" in elem.lower():
                # If focus element wraps children, keep the children (flatten) to avoid
                # removing actual content like labels/indicators.
                if children:
                    new_layout.extend(_strip_focus(children))
                continue

            if children:
                opts = dict(opts)
                opts["children"] = _strip_focus(children)
            new_layout.append((elem, opts))
        return new_layout

    # Only strip focus from specific widget layouts to avoid breaking notebook tabs.
    layout_targets = (
        "TButton",
        "TCheckbutton",
        "TRadiobutton",
        "TNotebook.Tab",
        "Editor.TNotebook.Tab",
    )

    for name in layout_targets:
        try:
            layout = style.layout(name)
            if layout:
                stripped = _strip_focus(layout)
                if stripped and stripped != layout:
                    style.layout(name, stripped)
        except Exception:
            pass

    style_names = layout_targets

    for name in style_names:
        try:
            style.configure(name, focuscolor=bg, focusthickness=0)
        except Exception:
            pass
        try:
            style.map(name, focuscolor=[("focus", bg), ("!focus", bg)])
        except Exception:
            pass

    # Tk widgets (fallback): remove highlight borders without affecting focus
    try:
        root.option_add("*highlightThickness", 0)
        root.option_add("*highlightColor", bg)
        root.option_add("*highlightBackground", bg)
    except Exception:
        pass

    # Prevent focus auto-select for Entry/Combobox (clears only if full text is selected)
    def _clear_full_selection(widget):
        try:
            if not hasattr(widget, "selection_present") or not widget.selection_present():
                return
            first = widget.index("sel.first")
            last = widget.index("sel.last")
            end = widget.index("end")
            if first == 0 and last >= end:
                widget.selection_clear()
        except Exception:
            pass

    def _clear_full_selection_late(event):
        w = event.widget
        def _do():
            _clear_full_selection(w)
        try:
            w.after_idle(_do)
            w.after(1, _do)
        except Exception:
            _do()

    try:
        root.bind_class("TEntry", "<FocusIn>", _clear_full_selection_late, add="+")
        root.bind_class("TCombobox", "<FocusIn>", _clear_full_selection_late, add="+")
        root.bind_class("TCombobox", "<<ComboboxSelected>>", _clear_full_selection_late, add="+")
    except Exception:
        pass


# Main GUI entry (builds all tabs + wires callbacks)
def launch_gui():
    # Capture terminal output into the shared status log file.
    install_status_log_stream_tee()

    # Check for required/optional dependencies first
    check_dependencies()
    _log_platform_support_status()

    # --- Set AppUserModelID early (must happen before creating the Tk root) ---
    if platform.system() == "Windows":
        try:
            MYAPPID = "com.mrboxik.snowrunnereditor"
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(MYAPPID)
            print("[DEBUG] AppUserModelID set:", MYAPPID)
        except Exception as e:
            print("[AppID Warning]", e)
    
    global max_backups_var, make_backup_var, full_backup_var, save_path_var
    global money_var, rank_var, time_preset_var, skip_time_var, time_presets
    global custom_day_var, custom_night_var, other_season_var
    global FACTOR_RULE_VARS, rule_savers, plugin_loaders
    global tyre_var, delete_path_on_close_var, dont_remember_path_var, autosave_var, dark_mode_var, theme_preset_var
    global objectives_safe_fallback_var
    
    # Create root window first
    root = tk.Tk()
    root.title("SnowRunner Editor")
    # Hide during initial layout to avoid size jump on startup
    try:
        root.withdraw()
    except Exception:
        pass
    # Run cleanup again after GUI startup so updater leftovers are removed
    # while the app is open (not only on next restart).
    try:
        _start_windows_update_artifact_cleanup_retry()
    except Exception:
        pass

    def _runtime_update_artifact_cleanup_tick(remaining=240):
        if remaining <= 0:
            return
        try:
            _cleanup_windows_update_artifacts()
        except Exception:
            pass
        try:
            root.after(1000, lambda: _runtime_update_artifact_cleanup_tick(remaining - 1))
        except Exception:
            pass

    try:
        root.after(800, _runtime_update_artifact_cleanup_tick)
    except Exception:
        pass

    # Hide dotted focus rectangles (configurable via config key: hide_focus_outlines)
    try:
        _cfg = load_config() or {}
    except Exception:
        _cfg = {}
    if _cfg.get("hide_focus_outlines", True):
        _apply_focus_outline_fix(root)
    # Try to set a cross-platform application icon (app_icon.ico for Windows, app_icon.png for others).
    try:
        set_app_icon(root)
    except Exception:
        # Non-fatal: icon is optional
        pass

    # Initialize all variables after root window exists
    max_backups_var = tk.StringVar(root, value="20")
    make_backup_var = tk.BooleanVar(root, value=True)
    full_backup_var = tk.BooleanVar(root, value=False)
    save_path_var = tk.StringVar(root)
    money_var = tk.StringVar(root)
    rank_var = tk.StringVar(root)
    xp_var = tk.StringVar(root)
    time_preset_var = tk.StringVar(root)
    skip_time_var = tk.BooleanVar(root)
    custom_day_var = tk.DoubleVar(root, value=1.0)
    custom_night_var = tk.DoubleVar(root, value=1.0)
    other_season_var = tk.StringVar(root)
    tyre_var = tk.StringVar(root, value="default")
    delete_path_on_close_var = tk.BooleanVar(root, value=False)
    dont_remember_path_var = tk.BooleanVar(root, value=False)
    autosave_var = tk.BooleanVar(root, value=False)
    dark_mode_var = tk.BooleanVar(root, value=False)
    theme_preset_var = tk.StringVar(root, value="Light")
    max_autobackups_var = tk.StringVar(root, value="50")
    objectives_safe_fallback_var = tk.BooleanVar(root, value=_get_objectives_safe_fallback_mode())
    # Initialize additional variables
    difficulty_var = tk.StringVar(root)
    truck_avail_var = tk.StringVar(root)
    truck_price_var = tk.StringVar(root)
    addon_avail_var = tk.StringVar(root)
    addon_amount_var = tk.StringVar(root)
    time_day_var = tk.StringVar(root)
    time_night_var = tk.StringVar(root)
    garage_refuel_var = tk.BooleanVar(root)
    app_status_var = tk.StringVar(root, value=_DEFAULT_STATUS_TEXT)
    configure_app_status(root, app_status_var)
    try:
        # Start Objectives+ online refresh immediately so latest data is ready
        # by the time the tab is opened.
        start_objectives_prefetch_background(force=False)
    except Exception:
        pass

    # Ensure global registries exist before building UI
    try:
        FACTOR_RULE_VARS
    except NameError:
        FACTOR_RULE_VARS = []
    try:
        rule_savers
    except NameError:
        rule_savers = []
    try:
        plugin_loaders
    except NameError:
        plugin_loaders = []
    
    plugin_loaders = []

    # Restore from config after variables exist
    try:
        cfg = load_config()
        max_backups_var.set(str(cfg.get("max_backups", "0")))
        max_autobackups_var.set(str(cfg.get("max_autobackups", "50")))
        make_backup_var.set(cfg.get("make_backup", True))
        full_backup_var.set(cfg.get("full_backup", False))
    except Exception:
        pass

    # Load config after variables exist
    config = load_config()
    delete_path_on_close_var.set(config.get("delete_path_on_close", False))
    dont_remember_path_var.set(config.get("dont_remember_path", False))
    enable_legacy_tabs_var = tk.BooleanVar(root, value=bool(config.get("enable_legacy_tabs", False)))
    dark_mode_var.set(bool(config.get("dark_mode", False)))
    try:
        val = config.get("objectives_use_safe_fallback", None)
        if val is None:
            val = config.get("objectives_use_backup", False)
        _set_objectives_safe_fallback_mode(bool(val))
        objectives_safe_fallback_var.set(_get_objectives_safe_fallback_mode())
    except Exception:
        pass
    improve_share_raw = config.get("improve_share_enabled", False)
    if isinstance(improve_share_raw, bool):
        improve_share_enabled = improve_share_raw
    else:
        improve_share_enabled = str(improve_share_raw).strip().lower() in ("1", "true", "yes", "on")
    improve_share_var = tk.BooleanVar(root, value=bool(improve_share_enabled))
    improve_share_state_lock = threading.Lock()
    improve_share_state = {
        "uploading": False,
        "last_uploaded_signature": "",
    }
    try:
        globals()["_THEME_CUSTOM_PRESETS"] = _load_theme_presets_from_config(config)
    except Exception:
        globals()["_THEME_CUSTOM_PRESETS"] = {}
    startup_preset = str(config.get("theme_preset", "") or "").strip()
    if not startup_preset:
        startup_preset = "Dark" if bool(config.get("dark_mode", False)) else "Light"
    resolved_dark = _set_active_theme_preset(startup_preset, persist=False)
    theme_preset_var.set(_ACTIVE_THEME_NAME)
    _set_runtime_theme_constants(bool(resolved_dark))
    _apply_editor_theme(root, dark_mode=resolved_dark, walk_children=False)

    # Keep autosave worker thread independent from tkinter variables.
    try:
        _bind_autosave_runtime_state_traces()
    except Exception as e:
        print("[Autosave] failed to bind state traces:", e)

    # If startup is enabled, keep the Startup shortcut aligned to the currently running build.
    try:
        _sync_windows_startup_registration_if_needed()
    except Exception as e:
        print("[Startup] registration sync failed:", e)

    check_for_updates_background(root, debug=True)

    tyre_var = tk.StringVar(value="default")
    custom_day_var = tk.DoubleVar(value=1.0)
    custom_night_var = tk.DoubleVar(value=1.0)

    # Icon setup removed

    try_autoload_last_save(save_path_var)

    # --- schedule delayed version check so the editor can finish loading first ---
    # Delay (ms) — change to taste (5000 = 5 seconds)
    _VERSION_CHECK_DELAY_MS = 2000

    def _delayed_version_check():
        last = load_last_path()
        if not last or not os.path.exists(last):
            return

        try:
            # Show the non-blocking dialog only once; the dialog's buttons handle persistence/UI updates.
            prompt_save_version_mismatch_and_choose(last, modal=False)
        except Exception as e:
            # Keep editor running even if the delayed check fails
            print("Delayed version check failed:", e)

    try:
        root.after(_VERSION_CHECK_DELAY_MS, _delayed_version_check)
    except Exception:
        try:
            (tk._default_root or root).after(_VERSION_CHECK_DELAY_MS, _delayed_version_check)
        except Exception:
            # as last resort, call directly (will be immediate)
            _delayed_version_check()

    def sync_all_rules(path):
        """
        Read the save file at `path` and update ALL GUI rule widgets:
        - builtin values (money/rank/difficulty/truck availability/price)
        - addon basic fields (kept simple here)
        - tyre dropdowns (sync_rule_dropdowns)
        - factor dropdowns (sync_factor_rule_dropdowns)
        - plugin loaders (plugin_loaders list)
        - time settings (custom_day_var/custom_night_var/time_preset_var/skip_time_var)
        """
        try:
            if not os.path.exists(path):
                return
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()

            # --- Core info from parser you already have ---
            money, rank, xp, difficulty, truck_avail, skip_time, day, night, truck_price = get_file_info(content)

            # update simple builtins if those vars exist
            if "money_var" in globals() and money is not None:
                money_var.set(str(money))
            if "rank_var" in globals() and rank is not None:
                rank_var.set(str(rank))

            # --- robustly read & set experience (will print debug to terminal) ---
            try:
                xp_val = _read_int_key_from_text(content, "experience")
                print(f"[DEBUG] experience read from save: {xp_val}")
            except Exception as e:
                print(f"[DEBUG] error reading experience from save: {e}")
                xp_val = None

            # only set xp_var if the variable actually exists (it is created earlier).
            if "xp_var" in globals() and xp_var is not None:
                try:
                    xp_var.set(str(xp_val) if xp_val is not None else "")
                except Exception as e:
                    print(f"[DEBUG] failed to set xp_var: {e}")


            # set the main builtin rule vars
            if "difficulty_var" in globals():
                difficulty_var.set(difficulty_map.get(difficulty, "Normal"))
            if "truck_avail_var" in globals():
                truck_avail_var.set(truck_avail_map.get(truck_avail, "default"))
            if "truck_price_var" in globals():
                truck_price_var.set(truck_price_map.get(truck_price, "default"))

            # addons: reset to default for now (parsing internal addon details is more elaborate)
            if "addon_avail_var" in globals():
                addon_avail_var.set(addon_avail_map.get(0, "default"))
            if "addon_amount_var" in globals():
                addon_amount_var.set("default")

            # --- Tyres & simple rule dropdowns (re-uses existing helper) ---
            if "sync_rule_dropdowns" in globals():
                try:
                    sync_rule_dropdowns(path)
                except Exception as e:
                    print("sync_rule_dropdowns failed:", e)

            # --- Factor rules (re-uses existing helper) ---
            if "sync_factor_rule_dropdowns" in globals():
                try:
                    sync_factor_rule_dropdowns(path)
                except Exception as e:
                    print("sync_factor_rule_dropdowns failed:", e)

            # --- Call any registered plugin loaders so external rule widgets sync too ---
            if "plugin_loaders" in globals():
                for loader in plugin_loaders:
                    try:
                        loader(path)
                    except Exception as e:
                        print("Plugin loader failed:", e)

            # --- Time settings ---
            _sync_time_ui(day=day, night=night, skip_time=skip_time)
                
            # --- other optional UI flags (if present) ---
            if "other_season_var" in globals():
                # don't force a literal 'default' into the season entry — leave it blank unless the save provides a value
                try:
                    other_season_var.set("")
                except Exception:
                    pass
            if "garage_refuel_var" in globals():
                # some builds look for different string; simple heuristic:
                garage_refuel_var.set('"enableGarageRefuel": true' in content)

        except Exception as e:
            print("Failed to sync all rules:", e)

    def _refresh_all_tabs_from_save(path):
        """Centralized refresh after a save path is selected."""
        try:
            sync_all_rules(path)
        except Exception as e:
            print(f"sync_all_rules failed: {e}")
        # Ensure Tk flushes variable -> widget updates
        try:
            root.update_idletasks()
            root.update()
        except Exception:
            try:
                tk._default_root.update_idletasks()
                tk._default_root.update()
            except Exception:
                pass
        try:
            base = os.path.basename(path) if path else "save file"
            set_app_status(f"Loaded {base} and synchronized all tabs.", timeout_ms=5000)
        except Exception:
            pass

    def _set_improve_share_meta_text(text, timeout_ms=6000):
        message = str(text or "").strip()
        if not message:
            return
        try:
            set_app_status(message, timeout_ms=timeout_ms)
        except Exception:
            pass

    def _update_improve_share_meta(message_override=None, timeout_ms=6000):
        if message_override is not None:
            _set_improve_share_meta_text(message_override, timeout_ms=timeout_ms)
            return
        if not improve_share_var.get():
            _set_improve_share_meta_text("Optional upload: off.", timeout_ms=timeout_ms)
            return
        if not is_improve_upload_endpoint_configured():
            _set_improve_share_meta_text(
                "Optional upload: enabled, but worker URL is not configured.",
                timeout_ms=timeout_ms,
            )
            return
        _set_improve_share_meta_text(
            "Optional upload: on. Only top-level files starting with commonsslsave or completesave are sent anonymously.",
            timeout_ms=timeout_ms,
        )

    def _maybe_upload_improve_samples_from_save_path(save_file_path=None, force=False):
        if not improve_share_var.get():
            return

        endpoint = get_improve_upload_endpoint()
        if not is_improve_upload_endpoint_configured(endpoint):
            msg = "Optional upload skipped: worker URL is not configured in the desktop editor."
            _update_improve_share_meta(msg, timeout_ms=9000)
            return

        file_path = str(save_file_path or save_path_var.get() or "").strip()
        if not file_path or not os.path.isfile(file_path):
            _update_improve_share_meta("Optional upload: on. Select a valid save file to send samples.", timeout_ms=7000)
            return

        folder_path = os.path.dirname(file_path)
        if not folder_path or not os.path.isdir(folder_path):
            msg = "Optional upload skipped: save folder path is not available."
            _update_improve_share_meta(msg, timeout_ms=9000)
            return

        sample_entries = collect_improve_share_entries(folder_path)
        if not sample_entries:
            msg = "Optional upload skipped: no top-level files found in the save folder."
            _update_improve_share_meta(msg, timeout_ms=7000)
            return

        signature = get_improve_share_signature(folder_path, sample_entries)
        with improve_share_state_lock:
            if improve_share_state.get("uploading"):
                msg = "Optional upload already in progress."
                _update_improve_share_meta(msg, timeout_ms=5000)
                return
            if (not force) and signature and signature == improve_share_state.get("last_uploaded_signature"):
                msg = "Optional upload already sent for this loaded folder."
                _update_improve_share_meta(msg, timeout_ms=5000)
                return
            improve_share_state["uploading"] = True

        folder_root = os.path.basename(os.path.normpath(folder_path))
        upload_count = len(sample_entries)
        _update_improve_share_meta(f"Uploading anonymous samples ({upload_count} file(s))...", timeout_ms=0)

        def _worker(entries_snapshot, sig_snapshot, folder_root_snapshot):
            try:
                result = upload_improve_samples_from_entries(
                    entries_snapshot,
                    endpoint=endpoint,
                    source="snowrunner-save-editor-desktop",
                    folder_root=folder_root_snapshot,
                )
                batch_id = str((result or {}).get("batchId") or (result or {}).get("id") or "").strip()
                raw_uploaded_count = (result or {}).get("uploadedCount")
                try:
                    uploaded_count = int(raw_uploaded_count)
                except Exception:
                    uploaded_count = len(entries_snapshot)
                raw_failed_count = (result or {}).get("failedCount")
                try:
                    failed_count = int(raw_failed_count)
                except Exception:
                    failed_count = 0
                raw_ignored_count = (result or {}).get("ignoredCount")
                try:
                    ignored_count = int(raw_ignored_count)
                except Exception:
                    ignored_count = 0
                first_error = str((result or {}).get("error") or "").strip()

                if failed_count > 0:
                    if batch_id:
                        message = (
                            f"Optional upload partial ({uploaded_count} uploaded, {failed_count} failed, "
                            f"{ignored_count} ignored, ID: {batch_id})."
                        )
                    else:
                        message = (
                            f"Optional upload partial ({uploaded_count} uploaded, {failed_count} failed, "
                            f"{ignored_count} ignored)."
                        )
                    if first_error:
                        message = f"{message} {first_error}"
                elif batch_id:
                    message = f"Optional upload complete ({uploaded_count} file(s), {ignored_count} ignored, ID: {batch_id})."
                else:
                    message = f"Optional upload complete ({uploaded_count} file(s), {ignored_count} ignored)."

                if failed_count <= 0:
                    with improve_share_state_lock:
                        improve_share_state["last_uploaded_signature"] = sig_snapshot

                _update_improve_share_meta(message, timeout_ms=9000)
            except Exception as err:
                message = f"Optional upload failed: {err}"
                _update_improve_share_meta(message, timeout_ms=10000)
            finally:
                with improve_share_state_lock:
                    improve_share_state["uploading"] = False

        threading.Thread(
            target=_worker,
            args=(sample_entries, signature, folder_root),
            daemon=True,
        ).start()

    def _on_improve_share_checkbox_changed():
        enabled = bool(improve_share_var.get())
        _update_config_values({"improve_share_enabled": enabled})
        _update_improve_share_meta(timeout_ms=7000)
        if enabled:
            _maybe_upload_improve_samples_from_save_path()

    # Expose refresh helpers to module-level code that uses globals()
    try:
        globals()["sync_all_rules"] = sync_all_rules
        globals()["_refresh_all_tabs_from_save"] = _refresh_all_tabs_from_save
    except Exception:
        pass

    difficulty_map = {0: "Normal", 1: "Hard", 2: "New Game+"}
    reverse_difficulty_map = {v: k for k, v in difficulty_map.items()}
    truck_avail_map = {
        1: "default", 0: "all trucks available", 3: "5–15 trucks/garage",
        4: "locked"
    }
    reverse_truck_avail_map = {v: k for k, v in truck_avail_map.items()}

    truck_price_map = {
        1: "default",
        2: "free",
        3: "2x",
        4: "4x",
        5: "5x"
    }
    reverse_truck_price_map = {v: k for k, v in truck_price_map.items()}

    addon_avail_map = {0: "default", 1: "all internal addons unlocked", 2: "custom range"}
    reverse_addon_avail_map = {v: k for k, v in addon_avail_map.items()}
    addon_amount_ranges = {
        "None": (0, 0),
        "10–50": (10, 50),
        "30–100": (30, 100),
        "50–150": (50, 150),
        "0–100": (0, 100)
    }
    time_presets = {
    "Custom": (1.0, 1.0),
    "Default": (1.0, 1.0),
    "Always Day": (0.0, 1.0),
    "Always Night": (1.0, 0.0),
    "Long Day": (0.01, 1.0),
    "Long Night": (1.0, 0.01),
    "Long Day and Long Night": (0.01, 0.01),
    "Time Stops": (0.0, 0.0),
    "Disco [SEIZURE RISK]": (1000.0, 1000.0),
    "Disco+ [OH GOD WHY]": (10000.0, 10000.0),
    "Disco++ [WILL DESTROY YOUR EYES]": (100000.0, 100000.0),
}
    
    def update_builtin_rule_vars(d, t, p, a, amt_key):
        difficulty_var.set(difficulty_map.get(d, "Normal"))
        truck_avail_var.set(truck_avail_map.get(t, "default"))
        truck_price_var.set(truck_price_map.get(p, "default"))
        addon_avail_var.set(addon_avail_map.get(a, "default"))
        if a == 2 and amt_key in addon_amount_ranges:
            addon_amount_var.set(amt_key)



    # Auto-load values if last path is valid
    last_path = save_path_var.get()
    plugin_loaders.append(sync_factor_rule_dropdowns)
    sync_factor_rule_dropdowns(last_path)

    # Set default values in case no file exists
    day, night = 1.0, 1.0
    if os.path.exists(last_path):
        with open(last_path, 'r', encoding='utf-8') as f:
            content = f.read()
        m, r, xp, d, t, s, day, night, tp = get_file_info(content)
        money_var.set(str(m))
        rank_var.set(str(r))
        difficulty_var.set(difficulty_map.get(d, "Normal"))
        truck_avail_var.set(truck_avail_map.get(t, "default"))
        truck_price_var.set(truck_price_map.get(tp, "default"))
        addon_avail_val = re.search(r'"internalAddonAvailability"\s*:\s*(\d+)', content)
        addon_avail = int(addon_avail_val.group(1)) if addon_avail_val else 0
        addon_avail_var.set(addon_avail_map.get(addon_avail, "default"))

        if addon_avail == 2:
            amount_val = re.search(r'"internalAddonAmount"\s*:\s*(\d+)', content)
            if amount_val:
                amt = int(amount_val.group(1))
                for key, (min_v, max_v) in addon_amount_ranges.items():
                    if min_v <= amt <= max_v:
                        addon_amount_var.set(key)
                        break

        skip_time_var.set(s)
        # Call plugin GUI loaders to refresh their values from file
        for loader in plugin_loaders:
            try:
                loader(save_path_var.get())
            except Exception as e:
                print(f"Plugin failed to update GUI from file: {e}")

        if day is None or night is None:
            time_preset_var.set("Custom")
        else:
            time_preset_var.set(
                next(
                    (k for k, v in time_presets.items()
                     if abs(day - v[0]) < 0.01 and abs(night - v[1]) < 0.01),
                    "Custom"
                )
            )

        # Also sync all rule dropdowns on startup
        sync_rule_dropdowns(last_path)
        for loader in plugin_loaders:
            try:
                loader(last_path)
            except Exception as e:
                print(f"Plugin failed to update GUI on startup: {e}")

    def browse_file():
        file_path = filedialog.askopenfilename(
            filetypes=[("SnowRunner Save", "*.cfg *.dat")]
        )
        if not file_path:
            return

        # Loop so if user chooses "Select different file" we re-validate the newly chosen file
        while True:
            try:
                with open(file_path, "r", encoding="utf-8") as f:
                    content = f.read()

                # Try parsing the save — if it fails or is incomplete, treat as corrupted
                m, r, xp, d, t, s, day, night, tp = get_file_info(content)

                if day is None or night is None:
                    raise ValueError("Missing time settings")

            except Exception:
                messagebox.showerror(
                    "Save File Corrupted",
                    f"Could not load save file:\n{file_path}\n\nThe file appears to be corrupted or incomplete."
                )
                save_path_var.set("")
                return

            # At this point the file parsed OK — check version/missing-key mismatches via the helper.
            action, new_path = prompt_save_version_mismatch_and_choose(file_path)

            if action == "error":
                # safe_load_save (used by the helper) already showed an error dialog
                save_path_var.set("")
                return

            if action == "select" and new_path:
                # User selected a different file from the dialog in the helper:
                # switch to that file and re-run the validation loop.
                file_path = new_path
                # loop continues and will attempt to open & validate the new file
                continue

            # action == "ok": either file matched expected versions or user chose Ignore
            break

        # If we reached here, file_path is accepted (either original or replaced)
        save_path_var.set(file_path)

        # Persist the selection
        save_path(file_path)

        # Centralized refresh
        try:
            _refresh_all_tabs_from_save(file_path)
            if improve_share_var.get():
                _maybe_upload_improve_samples_from_save_path(file_path)
            return
        except Exception as e:
            print(f"_refresh_all_tabs_from_save failed: {e}")

        # FALLBACK: manual UI update (keeps previous behavior if sync_all_rules is not defined)
        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()
            m, r, xp, d, t, s, day, night, tp = get_file_info(content)

            # Money / rank
            if "money_var" in globals() and money_var is not None:
                try:
                    money_var.set(str(m))
                except Exception:
                    pass

            if "rank_var" in globals() and rank_var is not None:
                try:
                    rank_var.set(str(r))
                except Exception:
                    pass

            # XP
            try:
                if "xp_var" in globals() and xp_var is not None:
                    xp_val = xp if xp is not None else _read_int_key_from_text(content, "experience")
                    xp_var.set(str(xp_val) if xp_val is not None else "")
            except Exception:
                try:
                    xp_var.set("")
                except Exception:
                    pass

            # Difficulty / truck availability / price maps (guarded)
            try:
                if "difficulty_var" in globals() and difficulty_var is not None:
                    difficulty_var.set(difficulty_map.get(d, "Normal"))
            except Exception:
                pass

            try:
                if "truck_avail_var" in globals() and truck_avail_var is not None:
                    truck_avail_var.set(truck_avail_map.get(t, "default"))
            except Exception:
                pass

            try:
                if "truck_price_var" in globals() and truck_price_var is not None:
                    truck_price_var.set(truck_price_map.get(tp, "default"))
            except Exception:
                pass

            # Skip time
            try:
                if "skip_time_var" in globals() and skip_time_var is not None:
                    skip_time_var.set(s)
            except Exception:
                pass

            # Time UI (sliders + preset)
            try:
                _sync_time_ui(day=day, night=night, skip_time=s)
            except Exception:
                pass

            if improve_share_var.get():
                _maybe_upload_improve_samples_from_save_path(file_path)

        except Exception:
            # This should be rare because we validated earlier, but handle defensively
            messagebox.showerror(
                "Save File Corrupted",
                f"Could not load save file after selection:\n{file_path}\n\nThe file appears to be corrupted or incomplete."
            )
            save_path_var.set("")
            return


    # -------------------------------------------------------------------------
    # NOTEBOOK + TAB REGISTRY (content is built below)
    # -------------------------------------------------------------------------
    tab_control = ttk.Notebook(root)
    tab_file = ttk.Frame(tab_control)
    tab_money = ttk.Frame(tab_control)
    tab_missions = ttk.Frame(tab_control)
    tab_rules = ttk.Frame(tab_control)
    tab_time = ttk.Frame(tab_control)

    lazy_tab_builders = {}

    def _register_lazy_tab(tab_frame, tab_name, builder):
        lazy_tab_builders[str(tab_frame)] = (tab_name, builder)
        ttk.Label(
            tab_frame,
            text=f"{tab_name} will load when opened.",
            anchor="center",
            justify="center",
        ).pack(fill="both", expand=True, padx=12, pady=12)

    def _ensure_lazy_tab_built(tab_widget):
        payload = lazy_tab_builders.pop(str(tab_widget), None)
        if payload is None:
            return
        tab_name, builder = payload

        try:
            for child in tab_widget.winfo_children():
                child.destroy()
        except Exception:
            pass

        set_app_status(f"Loading {tab_name} tab...", timeout_ms=0)
        try:
            builder()
            set_app_status(f"{tab_name} tab loaded.", timeout_ms=2500)
        except Exception as e:
            ttk.Label(
                tab_widget,
                text=f"Failed to initialize {tab_name} tab:\n{e}",
                style="Warning.TLabel",
                wraplength=600,
                justify="center",
            ).pack(fill="both", expand=True, padx=10, pady=10)
            set_app_status(f"{tab_name} tab failed to load: {e}", timeout_ms=10000)

    # TAB: Save File (inline UI built below)
    tab_control.add(tab_file, text='Save File')

    # TAB: Backups (create_backups_tab)
    tab_backups = ttk.Frame(tab_control)
    tab_control.add(tab_backups, text='Backups')
    _register_lazy_tab(tab_backups, "Backups", lambda: create_backups_tab(tab_backups, save_path_var))

    # TAB: Money & Rank (inline UI built below)
    tab_control.add(tab_money, text='Money & Rank')

    # TAB: Missions (legacy, optional; inline UI built below)
    # Visibility is controlled by the Settings -> Enable legacy tabs option.

    # TAB: Contests (legacy, optional; create_contest_tab)
    tab_contests = ttk.Frame(tab_control)
    _register_lazy_tab(tab_contests, "Contests", lambda: create_contest_tab(tab_contests, save_path_var))

    # TAB: Objectives+ (create_objectives_tab)
    tab_objectives = ttk.Frame(tab_control)
    tab_control.add(tab_objectives, text='Objectives+')
    _register_lazy_tab(tab_objectives, "Objectives+", lambda: create_objectives_tab(tab_objectives, save_path_var))

    def _tab_present(tab_frame):
        try:
            return str(tab_frame) in set(tab_control.tabs())
        except Exception:
            return False

    def _set_legacy_tabs_visibility(show):
        show = bool(show)
        try:
            current_tab = str(tab_control.select())
        except Exception:
            current_tab = ""
        current_is_legacy = current_tab in {str(tab_missions), str(tab_contests)}

        try:
            if _tab_present(tab_missions):
                tab_control.forget(tab_missions)
        except Exception:
            pass
        try:
            if _tab_present(tab_contests):
                tab_control.forget(tab_contests)
        except Exception:
            pass

        if show:
            try:
                tab_control.insert(tab_objectives, tab_missions, text="Missions")
            except Exception:
                pass
            try:
                tab_control.insert(tab_objectives, tab_contests, text="Contests")
            except Exception:
                pass
        elif current_is_legacy:
            try:
                tab_control.select(tab_objectives)
            except Exception:
                pass

    _set_legacy_tabs_visibility(enable_legacy_tabs_var.get())

    # TAB: Trials (create_trials_tab)
    tab_trials = ttk.Frame(tab_control)
    tab_control.add(tab_trials, text='Trials')
    _register_lazy_tab(tab_trials, "Trials", lambda: create_trials_tab(tab_trials, save_path_var, plugin_loaders))

    # TAB: Achievements (create_achievements_tab)
    tab_achievements = ttk.Frame(tab_control)
    tab_control.add(tab_achievements, text='Achievements')
    _register_lazy_tab(
        tab_achievements,
        "Achievements",
        lambda: create_achievements_tab(tab_achievements, save_path_var, plugin_loaders),
    )

    # TAB: PROS (create_pros_tab)
    tab_pros = ttk.Frame(tab_control)
    tab_control.add(tab_pros, text='PROS')
    _register_lazy_tab(tab_pros, "PROS", lambda: create_pros_tab(tab_pros, save_path_var, plugin_loaders))

    # TAB: Upgrades (create_upgrades_tab)
    tab_upgrades = ttk.Frame(tab_control)
    tab_control.add(tab_upgrades, text='Upgrades')
    _register_lazy_tab(tab_upgrades, "Upgrades", lambda: create_upgrades_tab(tab_upgrades, save_path_var))

    # TAB: Watchtowers (create_watchtowers_tab)
    tab_watchtowers = ttk.Frame(tab_control)
    tab_control.add(tab_watchtowers, text="Watchtowers")
    _register_lazy_tab(
        tab_watchtowers,
        "Watchtowers",
        lambda: create_watchtowers_tab(tab_watchtowers, save_path_var),
    )

    # TAB: Discoveries (create_discoveries_tab)
    tab_discoveries = ttk.Frame(tab_control)
    tab_control.add(tab_discoveries, text="Discoveries")
    _register_lazy_tab(
        tab_discoveries,
        "Discoveries",
        lambda: create_discoveries_tab(tab_discoveries, save_path_var),
    )

    # TAB: Levels (create_levels_tab)
    tab_levels = ttk.Frame(tab_control)
    tab_control.add(tab_levels, text="Levels")
    _register_lazy_tab(tab_levels, "Levels", lambda: create_levels_tab(tab_levels, save_path_var))

    # TAB: Garages (create_garages_tab)
    tab_garages = ttk.Frame(tab_control)
    tab_control.add(tab_garages, text="Garages")
    _register_lazy_tab(tab_garages, "Garages", lambda: create_garages_tab(tab_garages, save_path_var))

    # TAB: Vehicles (create_vehicles_tab)
    tab_vehicles = ttk.Frame(tab_control)
    tab_control.add(tab_vehicles, text="Vehicles")
    _register_lazy_tab(tab_vehicles, "Vehicles", lambda: create_vehicles_tab(tab_vehicles, save_path_var))

    # start autosave monitor if autosave enabled in config
    try:
        cfg = load_config()
        if "autosave" in cfg and cfg.get("autosave"):
            # ensure autosave_var exists & set it
            try:
                autosave_var.set(cfg.get("autosave", True))
            except:
                pass
            # start monitor
            start_autosave_monitor()
    except Exception:
        pass


    # TAB: Rules (create_rules_tab)
    _register_lazy_tab(tab_rules, "Rules", lambda: create_rules_tab(tab_rules, save_path_var))
    # End TAB: Rules

    tab_control.add(tab_rules, text='Rules')

    # TAB: Time (inline UI built below)
    tab_control.add(tab_time, text='Time')

    # TAB: Game Stats (create_game_stats_tab)
    tab_stats = ttk.Frame(tab_control)
    tab_control.add(tab_stats, text="Game Stats")
    _register_lazy_tab(
        tab_stats,
        "Game Stats",
        lambda: create_game_stats_tab(tab_stats, save_path_var, plugin_loaders),
    )

    # TAB: Settings (inline UI built below)
    tab_settings = ttk.Frame(tab_control)
    tab_control.add(tab_settings, text='Settings')

    # TAB: Fog Tool (FogToolFrame)
    tab_fog = ttk.Frame(tab_control)

    def _build_fog_tab():
        if FogToolFrame is not None:
            try:
                initial_dir = None
                try:
                    val = save_path_var.get()
                    if val:
                        initial_dir = os.path.dirname(val)
                except Exception:
                    pass

                fog_frame = FogToolFrame(tab_fog, initial_save_dir=initial_dir)
                fog_frame.pack(fill="both", expand=True)
                return
            except Exception as e:
                ttk.Label(
                    tab_fog,
                    text=f"⚠️ Fog Tool failed to load:\n{e}",
                    style="Warning.TLabel",
                    anchor="center",
                    justify="center",
                ).pack(expand=True, fill="both", padx=20, pady=20)
                return
        else:
            ttk.Label(
                tab_fog,
                text="⚠️ Fog Tool not available (fog_tool.py missing)",
                style="Warning.TLabel",
                anchor="center",
                justify="center"
            ).pack(expand=True, fill="both", padx=20, pady=20)

    tab_control.add(tab_fog, text="Fog Tool")
    _register_lazy_tab(tab_fog, "Fog Tool", _build_fog_tab)
    # End TAB: Fog Tool

    tab_control.pack(side="top", expand=1, fill='both')

    def _open_status_logs_file():
        path = get_status_log_path()
        try:
            os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        except Exception:
            pass
        try:
            if not os.path.exists(path):
                with open(path, "w", encoding="utf-8") as f:
                    f.write("")
        except Exception as e:
            return set_app_status(f"Could not create status log file: {e}", timeout_ms=9000)

        try:
            system = platform.system()
            if system == "Windows" and hasattr(os, "startfile"):
                os.startfile(path)
            elif system == "Darwin":
                subprocess.Popen(["open", path])
            else:
                subprocess.Popen(["xdg-open", path])
            set_app_status(f"Opened status logs: {path}", timeout_ms=7000)
        except Exception as e:
            set_app_status(f"Could not open status logs: {e}", timeout_ms=9000)

    status_bar = ttk.Frame(root, style="StatusBar.TFrame")
    status_bar.pack(side="bottom", fill="x")
    ttk.Separator(status_bar, orient="horizontal").pack(fill="x")

    status_row = ttk.Frame(status_bar, style="StatusBar.TFrame")
    status_row.pack(fill="x", padx=8, pady=(4, 6))

    ttk.Label(status_row, text="STATUS", style="StatusBarBadge.TLabel").pack(side="left", padx=(0, 8))
    ttk.Label(status_row, textvariable=app_status_var, style="StatusBarText.TLabel", anchor="w").pack(
        side="left",
        fill="x",
        expand=True,
    )
    ttk.Button(status_row, text="Status logs", width=12, command=_open_status_logs_file).pack(side="right")

    # End NOTEBOOK + TAB REGISTRY
    # ensure Settings is last
    try:
        tab_control.forget(tab_settings)   # remove if already added
    except Exception:
        pass
    tab_control.add(tab_settings, text='Settings')

    # Restore last selected tab if available
    config = load_config() or {}
    last_tab_text = str(config.get("last_tab_text", "") or "").strip()
    # Backward-compat across legacy label naming changes.
    tab_alias = {
        "Missions [Legacy]": "Missions",
        "Contests [Legacy]": "Contests",
        "Missions": "Missions",
        "Contests": "Contests",
    }
    target_text = tab_alias.get(last_tab_text, last_tab_text)
    restored = False
    if target_text:
        try:
            for tab_id in tab_control.tabs():
                try:
                    if str(tab_control.tab(tab_id, "text")) == target_text:
                        tab_control.select(tab_id)
                        restored = True
                        break
                except Exception:
                    continue
        except Exception:
            restored = False

    if not restored:
        last_tab_index = config.get("last_tab", 0)
        try:
            restore_tab_index = int(last_tab_index)
        except Exception:
            restore_tab_index = 0
        try:
            tab_count = max(1, len(tab_control.tabs()))
            restore_tab_index = max(0, min(restore_tab_index, tab_count - 1))
            tab_control.select(restore_tab_index)
        except Exception:
            pass

    # Track tab changes, lazy-load on first open, and save selected tab index.
    def on_tab_change(event):
        try:
            current_tab_id = tab_control.select()
            current_tab_widget = tab_control.nametowidget(current_tab_id)
            _ensure_lazy_tab_built(current_tab_widget)
        except Exception:
            pass
        try:
            config = load_config() or {}
            current_tab_id = tab_control.select()
            config["last_tab"] = tab_control.index(current_tab_id)
            config["last_tab_text"] = str(tab_control.tab(current_tab_id, "text") or "")
            save_config(config)
        except Exception:
            pass

    tab_control.bind("<<NotebookTabChanged>>", on_tab_change)


    # -------------------------------------------------------------------------
    # TAB UI: Settings (tab_settings)
    # -------------------------------------------------------------------------
    minesweeper_app = None
    theme_preset_combo = None

    def apply_selected_theme_preset(preset_name, persist=True):
        enabled = _set_active_theme_preset(preset_name, persist=False)
        theme_preset_var.set(_ACTIVE_THEME_NAME)
        _set_runtime_theme_constants(enabled)
        _apply_editor_theme(root, dark_mode=enabled)
        try:
            if minesweeper_app is not None:
                minesweeper_app.apply_theme()
        except Exception:
            pass
        if persist:
            _persist_theme_selection(_ACTIVE_THEME_NAME, dark_mode=enabled)
        try:
            _fit_window_to_tabs_and_rules()
        except Exception:
            pass

    def refresh_theme_preset_values(selected=None):
        names = _get_theme_preset_names()
        target = str(selected or theme_preset_var.get() or "").strip()
        if target not in names:
            target = _ACTIVE_THEME_NAME if _ACTIVE_THEME_NAME in names else names[0]
        theme_preset_var.set(target)
        try:
            if theme_preset_combo is not None:
                theme_preset_combo.configure(values=names)
        except Exception:
            pass

    def on_theme_preset_changed(_event=None):
        apply_selected_theme_preset(theme_preset_var.get(), persist=True)

    def open_theme_customizer():
        popup = _create_themed_toplevel(root)
        popup.title("Theme Customizer")
        try:
            popup.transient(root)
            popup.grab_set()
        except Exception:
            pass
        screen_h = 900
        basic_popup_h = 820
        advanced_popup_h = 920
        try:
            popup.update_idletasks()
            screen_h = int(popup.winfo_screenheight() or 900)
            basic_popup_h = max(760, min(980, screen_h - 120))
            advanced_popup_h = max(basic_popup_h, min(1140, screen_h - 60))
            popup.geometry(f"760x{basic_popup_h}")
            popup.minsize(700, 720)
        except Exception:
            pass

        body = ttk.Frame(popup, padding=10)
        body.pack(fill="both", expand=True)

        ttk.Label(
            body,
            text="Set colors and save as a named preset.",
        ).pack(anchor="w", pady=(0, 8))

        top_row = ttk.Frame(body)
        top_row.pack(fill="x", pady=(0, 8))
        ttk.Label(top_row, text="Preset Name:").grid(row=0, column=0, sticky="w", padx=(0, 6))
        current_name = str(theme_preset_var.get() or "").strip()
        if current_name.lower() in ("light", "dark"):
            current_name = ""
        preset_name_var_local = tk.StringVar(popup, value=current_name)
        name_entry = ttk.Entry(top_row, textvariable=preset_name_var_local, width=24)
        name_entry.grid(row=0, column=1, sticky="ew", padx=(0, 10))
        top_row.columnconfigure(1, weight=1)

        grid_host = ttk.Frame(body)
        grid_host.pack(fill="x", expand=False)
        canvas = tk.Canvas(grid_host, height=580, bd=0, highlightthickness=0)
        scroll = ttk.Scrollbar(grid_host, orient="vertical", command=canvas.yview)
        rows = ttk.Frame(canvas)
        rows_id = canvas.create_window((0, 0), window=rows, anchor="nw")
        canvas.configure(yscrollcommand=scroll.set)
        canvas.pack(side="left", fill="both", expand=True)
        scroll.pack(side="right", fill="y")

        def _rows_configured(_event=None):
            try:
                canvas.configure(scrollregion=canvas.bbox("all"))
            except Exception:
                pass

        def _canvas_resized(event):
            try:
                canvas.itemconfigure(rows_id, width=event.width)
            except Exception:
                pass

        rows.bind("<Configure>", _rows_configured)
        canvas.bind("<Configure>", _canvas_resized)

        theme_snapshot = _get_effective_theme()
        color_vars = {"warning_color": tk.StringVar(popup, value=theme_snapshot.get("warning_fg", ""))}
        advanced_var = tk.BooleanVar(popup, value=False)
        initial_snapshot = dict(theme_snapshot)
        popup_palette = _get_effective_theme()
        swatch_fallback_bg = popup_palette.get("field_bg", "#2a2a2a")
        swatch_border = popup_palette.get("border", "#505050")
        swatch_invalid_fg = popup_palette.get("warning_fg", "#ffb347")
        instruction = None

        def _resize_customizer_window(force_mode=None):
            try:
                use_advanced = bool(advanced_var.get()) if force_mode is None else bool(force_mode)
            except Exception:
                use_advanced = False

            base_target_h = advanced_popup_h if use_advanced else basic_popup_h
            min_h = 820 if use_advanced else 720
            max_h = max(720, int(screen_h) - 40)
            try:
                popup.update_idletasks()
            except Exception:
                pass
            try:
                req_h = int(popup.winfo_reqheight() or 0) + 18
            except Exception:
                req_h = base_target_h

            target_h = max(base_target_h, req_h)

            # If content exceeds screen height, shrink only the picker canvas first.
            if target_h > max_h:
                try:
                    cur_canvas_h = int(float(canvas.cget("height")))
                except Exception:
                    cur_canvas_h = 0
                if cur_canvas_h > 0:
                    deficit = target_h - max_h
                    canvas_min = 260 if use_advanced else 220
                    new_canvas_h = max(canvas_min, cur_canvas_h - deficit - 8)
                    if new_canvas_h != cur_canvas_h:
                        try:
                            canvas.configure(height=new_canvas_h)
                            popup.update_idletasks()
                            req_h = int(popup.winfo_reqheight() or 0) + 18
                            target_h = max(base_target_h, req_h)
                        except Exception:
                            pass

            target_h = min(max_h, target_h)
            min_h = min(min_h, max_h)
            try:
                width = max(700, int(popup.winfo_width() or 760))
            except Exception:
                width = 760
            try:
                x = int(popup.winfo_x())
                y = int(popup.winfo_y())
                y = max(0, min(y, max(0, screen_h - target_h)))
                popup.geometry(f"{width}x{target_h}+{x}+{y}")
            except Exception:
                popup.geometry(f"{width}x{target_h}")
            try:
                popup.minsize(700, min_h)
            except Exception:
                pass

        def _ensure_color_var(color_key):
            var = color_vars.get(color_key)
            if var is None:
                var = tk.StringVar(popup, value=theme_snapshot.get(color_key, ""))
                color_vars[color_key] = var
            return var

        def _build_draft_theme_colors():
            mode = "dark"
            defaults = _theme_defaults_for_mode(mode)
            raw_colors = {key: _ensure_color_var(key).get().strip() for key in defaults.keys()}
            if not bool(advanced_var.get()):
                warning_color = str(_ensure_color_var("warning_color").get() or "").strip()
                if warning_color:
                    raw_colors["warning_fg"] = warning_color
                    raw_colors["warning_btn_bg"] = warning_color
                    raw_colors["warning_btn_active_bg"] = warning_color
            colors = _sanitize_theme_colors(raw_colors, mode)
            return mode, colors

        def _update_color_swatch(widget, color_value):
            token = str(color_value or "").strip()
            try:
                if token:
                    root.winfo_rgb(token)
                    widget.configure(
                        bg=token,
                        fg=token,
                        text="    ",
                        highlightbackground=swatch_border,
                        highlightcolor=swatch_border,
                    )
                    return
            except Exception:
                pass
            widget.configure(
                bg=swatch_fallback_bg,
                fg=swatch_invalid_fg,
                text=" ?? ",
                highlightbackground=swatch_border,
                highlightcolor=swatch_border,
            )

        def _visible_field_specs():
            if bool(advanced_var.get()):
                return _THEME_CUSTOMIZER_ADVANCED_FIELDS
            return _THEME_CUSTOMIZER_BASIC_FIELDS

        preview_card = tk.Frame(body, relief=tk.SOLID, bd=1, highlightthickness=1)
        preview_header = tk.Label(preview_card, text="Live Preview", anchor="w", font=("TkDefaultFont", 10, "bold"))
        preview_tabs = tk.Frame(preview_card, bd=0, highlightthickness=0)
        preview_tab_save = tk.Label(preview_tabs, text="Save File", padx=8, pady=4)
        preview_tab_obj = tk.Label(preview_tabs, text="Objectives+", padx=8, pady=4)
        preview_tab_set = tk.Label(preview_tabs, text="Settings", padx=8, pady=4)
        preview_tab_save.pack(side="left", padx=(0, 2))
        preview_tab_obj.pack(side="left", padx=(0, 2))
        preview_tab_set.pack(side="left")

        preview_content = tk.Frame(preview_card, bd=0, highlightthickness=0)
        preview_caption = tk.Label(preview_content, text="Selected Save File:", anchor="w")
        preview_entry = tk.Entry(preview_content)
        preview_entry.insert(0, r"C:\Example\CompleteSave.cfg")
        try:
            preview_entry.configure(state="readonly")
        except Exception:
            pass
        preview_check_var = tk.IntVar(value=1)
        preview_check = tk.Checkbutton(
            preview_content,
            text="Don't remember save file path",
            variable=preview_check_var,
            onvalue=1,
            offvalue=0,
            anchor="w",
        )
        preview_btn_row = tk.Frame(preview_content, bd=0, highlightthickness=0)
        preview_btn = tk.Button(preview_btn_row, text="Save Settings")
        preview_warn_btn = tk.Button(preview_btn_row, text="Read warning")
        preview_btn.pack(side="left")
        preview_warn_btn.pack(side="left", padx=(8, 0))
        preview_state_row = tk.Frame(preview_content, bd=0, highlightthickness=0)
        preview_active_btn = tk.Label(preview_state_row, text="Active Button", padx=6, pady=2)
        preview_active_warn_btn = tk.Label(preview_state_row, text="Warning Active", padx=6, pady=2)
        preview_disabled_text = tk.Label(preview_state_row, text="Disabled text preview", padx=6, pady=2, anchor="w")
        preview_mine_cell = tk.Label(preview_state_row, text="Minesweeper cell", padx=6, pady=2)
        preview_active_btn.pack(side="left")
        preview_active_warn_btn.pack(side="left", padx=(8, 0))
        preview_disabled_text.pack(side="left", padx=(8, 0))
        preview_mine_cell.pack(side="left", padx=(8, 0))

        preview_rows = tk.Frame(preview_content, bd=0, highlightthickness=0)
        preview_row_a = tk.Label(preview_rows, text="Row 1 example (Objectives+/Backups)", anchor="w", padx=6, pady=2)
        preview_row_b = tk.Label(preview_rows, text="Row 2 example (Objectives+/Backups)", anchor="w", padx=6, pady=2)
        preview_row_selected = tk.Label(preview_rows, text="Selected row example", anchor="w", padx=6, pady=2)
        preview_row_a.pack(fill="x")
        preview_row_b.pack(fill="x", pady=(2, 0))
        preview_row_selected.pack(fill="x", pady=(2, 0))
        preview_warning_text = tk.Label(
            preview_content,
            text="Warning text preview: this follows your warning color.",
            anchor="w",
            justify="left",
        )

        preview_header.pack(fill="x", padx=8, pady=(6, 4))
        preview_tabs.pack(fill="x", padx=8)
        preview_content.pack(fill="both", expand=True, padx=8, pady=(8, 8))
        preview_caption.pack(fill="x")
        preview_entry.pack(fill="x", pady=(4, 6))
        preview_check.pack(fill="x", pady=(0, 6))
        preview_btn_row.pack(fill="x", pady=(0, 6))
        preview_state_row.pack(fill="x", pady=(0, 6))
        preview_rows.pack(fill="x", pady=(0, 6))
        preview_warning_text.pack(fill="x")
        preview_fog_sample = tk.Label(preview_content, text="Fog Tool background sample", anchor="w", padx=6, pady=4)
        preview_fog_sample.pack(fill="x", pady=(6, 0))
        preview_card.pack(fill="both", expand=True, pady=(8, 2))

        def _safe_preview_color(token, fallback):
            candidate = str(token or "").strip()
            if candidate:
                try:
                    root.winfo_rgb(candidate)
                    return candidate
                except Exception:
                    pass
            return fallback

        def _refresh_live_preview():
            nonlocal instruction
            mode, draft = _build_draft_theme_colors()
            defaults = _theme_defaults_for_mode(mode)

            def _c(key):
                return _safe_preview_color(draft.get(key), defaults.get(key, "#000000"))

            bg = _c("bg")
            fg = _c("fg")
            field_bg = _c("field_bg")
            button_bg = _c("button_bg")
            button_active = _c("button_active_bg")
            border = _c("border")
            accent = _c("accent")
            accent_fg = _c("accent_fg")
            tab_bg = _c("tab_bg")
            tab_active = _c("tab_active_bg")
            notebook_bg = _c("notebook_bg")
            row_a = _c("row_a")
            row_b = _c("row_b")
            mine_closed_bg = _c("mine_closed_bg")
            fog_bg = _c("fog_bg")
            warning_fg = _c("warning_fg")
            warning_btn_bg = _c("warning_btn_bg")
            warning_btn_active = _c("warning_btn_active_bg")
            warning_btn_fg = _c("warning_btn_fg")
            disabled_fg = _c("disabled_fg")

            try:
                preview_card.configure(bg=bg, highlightbackground=border, highlightcolor=border)
                preview_header.configure(bg=bg, fg=fg)
                preview_tabs.configure(bg=notebook_bg)
                preview_tab_save.configure(bg=tab_active, fg=fg, highlightbackground=border, highlightcolor=border)
                preview_tab_obj.configure(bg=tab_bg, fg=fg, highlightbackground=border, highlightcolor=border)
                preview_tab_set.configure(bg=tab_bg, fg=fg, highlightbackground=border, highlightcolor=border)
                preview_content.configure(bg=bg)
                preview_caption.configure(bg=bg, fg=fg)
                preview_entry.configure(
                    readonlybackground=field_bg,
                    disabledbackground=field_bg,
                    bg=field_bg,
                    fg=fg,
                    insertbackground=fg,
                    highlightbackground=border,
                    highlightcolor=border,
                )
                preview_check.configure(
                    bg=bg,
                    fg=fg,
                    activebackground=bg,
                    activeforeground=fg,
                    selectcolor=field_bg,
                    highlightbackground=bg,
                    highlightcolor=bg,
                )
                preview_btn_row.configure(bg=bg)
                preview_btn.configure(
                    bg=button_bg,
                    fg=fg,
                    activebackground=button_active,
                    activeforeground=fg,
                    highlightbackground=border,
                    highlightcolor=border,
                )
                preview_warn_btn.configure(
                    bg=warning_btn_bg,
                    fg=warning_btn_fg,
                    activebackground=warning_btn_active,
                    activeforeground=warning_btn_fg,
                    highlightbackground=border,
                    highlightcolor=border,
                )
                preview_state_row.configure(bg=bg)
                preview_active_btn.configure(bg=button_active, fg=fg, highlightbackground=border, highlightcolor=border)
                preview_active_warn_btn.configure(
                    bg=warning_btn_active,
                    fg=warning_btn_fg,
                    highlightbackground=border,
                    highlightcolor=border,
                )
                preview_disabled_text.configure(bg=bg, fg=disabled_fg)
                preview_mine_cell.configure(bg=mine_closed_bg, fg=fg, highlightbackground=border, highlightcolor=border)
                preview_rows.configure(bg=bg)
                preview_row_a.configure(bg=row_a, fg=fg)
                preview_row_b.configure(bg=row_b, fg=fg)
                preview_row_selected.configure(bg=accent, fg=accent_fg)
                preview_warning_text.configure(bg=bg, fg=warning_fg)
                preview_fog_sample.configure(bg=fog_bg, fg=fg)
                if instruction is not None:
                    instruction.configure(bg=bg, fg=warning_fg)
            except Exception:
                pass

        def _render_color_rows():
            for child in rows.winfo_children():
                child.destroy()

            for idx, (key, label_text) in enumerate(_visible_field_specs()):
                ttk.Label(rows, text=label_text).grid(row=idx, column=0, sticky="w", padx=(0, 8), pady=2)
                color_var = _ensure_color_var(key)
                entry = ttk.Entry(rows, textvariable=color_var, width=18)
                entry.grid(row=idx, column=1, sticky="ew", padx=(0, 8), pady=2)

                swatch = tk.Label(
                    rows,
                    text="    ",
                    width=4,
                    relief=tk.SOLID,
                    bd=1,
                    highlightthickness=1,
                    highlightbackground=swatch_border,
                    highlightcolor=swatch_border,
                )
                try:
                    swatch._skip_theme_retint = True
                except Exception:
                    pass
                swatch.grid(row=idx, column=2, sticky="ew", padx=(0, 8), pady=2)

                def _entry_changed(_event=None, v=color_var, w=swatch):
                    _update_color_swatch(w, v.get())
                    _refresh_live_preview()

                entry.bind("<KeyRelease>", _entry_changed, add="+")
                entry.bind("<FocusOut>", _entry_changed, add="+")
                _update_color_swatch(swatch, color_var.get())

                def _pick_color(k=key, v=color_var, w=swatch):
                    initial = v.get().strip() or None
                    try:
                        _rgb, selected_hex = colorchooser.askcolor(color=initial, parent=popup, title=f"Pick {k}")
                    except Exception:
                        selected_hex = None
                    if selected_hex:
                        v.set(selected_hex)
                        _update_color_swatch(w, v.get())
                        _refresh_live_preview()

                ttk.Button(rows, text="Pick", command=_pick_color).grid(row=idx, column=3, sticky="e", pady=2)

            rows.columnconfigure(1, weight=1)
            field_count = len(_visible_field_specs())
            try:
                rows.update_idletasks()
                requested_h = int(rows.winfo_reqheight() or 0)
            except Exception:
                requested_h = 0
            estimated_h = int(field_count * 25 + 16)
            content_h = max(requested_h, estimated_h)
            max_canvas_h = 560 if bool(advanced_var.get()) else 520
            min_canvas_h = 300 if bool(advanced_var.get()) else 280
            desired_h = max(min_canvas_h, min(max_canvas_h, content_h))
            try:
                canvas.configure(height=desired_h)
            except Exception:
                pass
            _rows_configured()
            _refresh_live_preview()
            _resize_customizer_window(force_mode=advanced_var.get())

        def _collect_theme_payload():
            mode, colors = _build_draft_theme_colors()
            for key, color_token in colors.items():
                try:
                    root.winfo_rgb(color_token)
                except Exception:
                    messagebox.showerror("Invalid Color", f"{key}: '{color_token}' is not a valid Tk color.")
                    return None
            return {"mode": mode, "colors": colors}

        def _save_theme_preset():
            name = str(preset_name_var_local.get() or "").strip()
            if not name:
                messagebox.showerror("Missing Name", "Enter a preset name.")
                return

            # Protect built-in presets: reserved names are redirected to "<name>1".
            requested_lower = name.lower()
            if requested_lower in _reserved_theme_names():
                name = f"{requested_lower}1"

            # Case-insensitive overwrite: if preset already exists with the same logical name,
            # keep that existing key casing and overwrite it.
            save_key = name
            logical = name.lower()
            for existing_key in _THEME_CUSTOM_PRESETS.keys():
                if isinstance(existing_key, str) and existing_key.lower() == logical:
                    save_key = existing_key
                    break

            payload = _collect_theme_payload()
            if payload is None:
                return

            _THEME_CUSTOM_PRESETS[save_key] = payload
            refresh_theme_preset_values(selected=save_key)
            apply_selected_theme_preset(save_key, persist=False)
            _persist_theme_selection(save_key, dark_mode=(payload["mode"] == "dark"))
            try:
                preset_name_var_local.set(save_key)
            except Exception:
                pass
            show_info("Theme Preset", f"Saved preset '{save_key}'.")

        helper_row = ttk.Frame(body)
        helper_row.pack(fill="x", pady=(8, 4))
        instruction = tk.Label(
            helper_row,
            text="Use HEX (#RRGGBB) or English Tk color names (for example: red, orange, white).",
            fg=popup_palette.get("warning_fg", "#ff4d4d"),
            bg=popup_palette.get("bg", "#1f1f1f"),
            anchor="w",
            justify="left",
        )
        try:
            instruction._skip_theme_retint = True
        except Exception:
            pass
        instruction.pack(side="left", fill="x", expand=True)

        def _toggle_advanced():
            advanced_var.set(not bool(advanced_var.get()))
            if bool(advanced_var.get()):
                adv_btn.configure(text="Basic options")
            else:
                adv_btn.configure(text="Advanced options")
            _resize_customizer_window(force_mode=advanced_var.get())
            _render_color_rows()
            _refresh_live_preview()

        def _reset_customizer_values():
            mode = "dark"
            defaults = _theme_defaults_for_mode(mode)
            for key in defaults.keys():
                _ensure_color_var(key).set(str(initial_snapshot.get(key, defaults[key])))
            _ensure_color_var("warning_color").set(str(initial_snapshot.get("warning_fg", defaults["warning_fg"])))
            _render_color_rows()
            _refresh_live_preview()

        adv_btn = None
        reset_btn = None

        _render_color_rows()

        buttons = ttk.Frame(body)
        buttons.pack(fill="x", pady=(4, 0))
        ttk.Button(buttons, text="Save Preset", command=_save_theme_preset).pack(side="left")
        right_actions = ttk.Frame(buttons)
        right_actions.pack(side="right")
        adv_btn = ttk.Button(right_actions, text="Advanced options", command=_toggle_advanced)
        reset_btn = ttk.Button(right_actions, text="Reset", command=_reset_customizer_values)
        adv_btn.pack(side="left", padx=(0, 6))
        reset_btn.pack(side="left", padx=(0, 6))
        ttk.Button(right_actions, text="Close", command=popup.destroy).pack(side="left")

        # Recompute once the bottom action row exists (important for larger non-light widgets).
        try:
            _resize_customizer_window(force_mode=advanced_var.get())
        except Exception:
            pass

        try:
            name_entry.focus_set()
        except Exception:
            pass

    theme_row = ttk.Frame(tab_settings)
    theme_row.pack(anchor="center", pady=(10, 0))
    ttk.Label(theme_row, text="Theme Preset:").pack(side="left")
    theme_preset_combo = ttk.Combobox(theme_row, textvariable=theme_preset_var, state="readonly", width=24)
    theme_preset_combo.pack(side="left", padx=(8, 0))
    theme_preset_combo.bind("<<ComboboxSelected>>", on_theme_preset_changed)
    refresh_theme_preset_values(selected=_ACTIVE_THEME_NAME)

    ttk.Button(tab_settings, text="Theme Customizer", command=open_theme_customizer).pack(pady=(6, 0))
    def _toggle_legacy_tabs_visibility():
        try:
            _set_legacy_tabs_visibility(enable_legacy_tabs_var.get())
        except Exception:
            pass
    ttk.Checkbutton(
        tab_settings,
        text="Enable legacy tabs (Missions/Contests)",
        variable=enable_legacy_tabs_var,
        command=_toggle_legacy_tabs_visibility,
    ).pack(pady=(6, 0))
    ttk.Checkbutton(tab_settings, text="Don't remember save file path", variable=dont_remember_path_var).pack(pady=(5, 0))
    ttk.Checkbutton(tab_settings, text="Delete saved path on close", variable=delete_path_on_close_var).pack(pady=(5, 10))
    def save_settings_silent():
        config = load_config()
        config["enable_legacy_tabs"] = bool(enable_legacy_tabs_var.get())
        config["dont_remember_path"] = dont_remember_path_var.get()
        config["delete_path_on_close"] = delete_path_on_close_var.get()
        config["dark_mode"] = bool(dark_mode_var.get())
        config["theme_preset"] = str(theme_preset_var.get() or _ACTIVE_THEME_NAME or "Light")
        config["theme_presets"] = _serialize_theme_presets()
        config["make_backup"] = make_backup_var.get()
        config["full_backup"] = full_backup_var.get()
        config["max_backups"] = _parse_nonnegative_int(
            max_backups_var.get(),
            _parse_nonnegative_int(config.get("max_backups", 20), 20),
        )
        config["max_autobackups"] = _parse_nonnegative_int(
            max_autobackups_var.get(),
            _parse_nonnegative_int(config.get("max_autobackups", 50), 50),
        )
        config["autosave"] = bool(autosave_var.get() if autosave_var is not None else False)
        try:
            config["objectives_use_safe_fallback"] = bool(objectives_safe_fallback_var.get())
        except Exception:
            pass
        save_config(config)

    def save_settings():
        save_settings_silent()
        show_info("Settings", "Settings have been saved.")

        if delete_path_on_close_var.get():
            _delete_config_keys(["last_save_path"])
        elif not dont_remember_path_var.get():
            save_path(save_path_var.get())

    ttk.Button(tab_settings, text="Save Settings", command=save_settings).pack(pady=(10, 10))
    def create_desktop_shortcut():
        if not getattr(sys, 'frozen', False):
            messagebox.showwarning("Unavailable", "This feature only works in the built version.")
            return

        try:
            exe_path = os.path.abspath(sys.executable)
            desktop = get_desktop_path()
            app_name = "SnowRunner Editor"
            system = platform.system()

            def _run_powershell(ps_command: str):
                for exe in ("powershell", "pwsh"):
                    try:
                        result = subprocess.run(
                            [exe, "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", ps_command],
                            capture_output=True,
                            text=True,
                        )
                        if result.returncode == 0:
                            return
                        last_error = result.stderr.strip() or result.stdout.strip()
                    except FileNotFoundError:
                        last_error = f"{exe} not found"
                        continue
                raise RuntimeError(last_error or "PowerShell failed")

            def _ps_quote(value: str) -> str:
                # PowerShell single-quoted string escaping
                return "'" + value.replace("'", "''") + "'"

            if system == "Windows":
                shortcut_path = os.path.join(desktop, f"{app_name}.lnk")
                ps = (
                    "$W = New-Object -ComObject WScript.Shell; "
                    f"$S = $W.CreateShortcut({_ps_quote(shortcut_path)}); "
                    f"$S.TargetPath = {_ps_quote(exe_path)}; "
                    f"$S.WorkingDirectory = {_ps_quote(os.path.dirname(exe_path))}; "
                    f"$S.IconLocation = {_ps_quote(exe_path)}; "
                    "$S.Save()"
                )
                _run_powershell(ps)
                show_info("Success", f"Shortcut created:\n{shortcut_path}")
                return

            if system == "Darwin":
                # Prefer Finder alias via AppleScript (no extra dependencies)
                alias_path = os.path.join(desktop, f"{app_name}")
                try:
                    def _osa_quote(value: str) -> str:
                        return value.replace('"', '\\"')
                    osa = (
                        'tell application "Finder" to make alias file to POSIX file "'
                        + _osa_quote(exe_path)
                        + '" at POSIX file "'
                        + _osa_quote(desktop)
                        + '"'
                    )
                    result = subprocess.run(
                        ["osascript", "-e", osa],
                        capture_output=True,
                        text=True,
                    )
                    if result.returncode == 0:
                        show_info("Success", f"Alias created on Desktop:\n{alias_path}")
                        return
                except Exception:
                    pass

                # Fallback: create a .command launcher
                command_path = os.path.join(desktop, f"{app_name}.command")
                with open(command_path, "w", encoding="utf-8") as f:
                    f.write("#!/bin/bash\n")
                    f.write(f"\"{exe_path}\" &\n")
                try:
                    os.chmod(command_path, 0o755)
                except Exception:
                    pass
                show_info("Success", f"Launcher created:\n{command_path}")
                return

            # Linux and other Unix-like systems: create a .desktop entry
            desktop_entry_path = os.path.join(desktop, f"{app_name}.desktop")
            exe_path_escaped = exe_path.replace(" ", "\\ ")
            lines = [
                "[Desktop Entry]",
                "Type=Application",
                f"Name={app_name}",
                f"Exec={exe_path_escaped}",
                f"Path={os.path.dirname(exe_path)}",
                "Terminal=false",
                "Categories=Utility;",
            ]
            with open(desktop_entry_path, "w", encoding="utf-8") as f:
                f.write("\n".join(lines) + "\n")
            try:
                os.chmod(desktop_entry_path, 0o755)
            except Exception:
                pass
            show_info("Success", f"Shortcut created:\n{desktop_entry_path}")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to create shortcut:\n{e}")

    ttk.Button(tab_settings, text="Make Desktop Shortcut", command=create_desktop_shortcut).pack(pady=(5, 10))

    def make_backup_now():
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")
        try:
            make_backup_if_enabled(path)
            show_info("Backup", f"Backup created")
        except Exception as e:
            messagebox.showerror("Error", f"Backup failed:\n{e}")

    ttk.Button(tab_settings, text="Make a Backup", command=make_backup_now).pack(pady=(5, 10))

    def manual_update_check():
        check_for_updates_background(root, debug=True)

    ttk.Button(tab_settings, text="Check for Update", command=manual_update_check).pack(pady=(5, 10))

    # Separator and embedded Minesweeper
    if MINESWEEPER_AVAILABLE:
        ttk.Separator(tab_settings, orient='horizontal').pack(fill='x', pady=(10, 5))
        ttk.Label(tab_settings, text="Minesweeper", font=("TkDefaultFont", 11, "bold")).pack(pady=(0, 5))
    
        minesweeper_frame = tk.Frame(
            tab_settings,
            bg=_theme_color_literal("#f0f0f0", role="bg"),
            bd=0,
            highlightthickness=0,
        )
        minesweeper_frame.pack(pady=5)
        minesweeper_app = MinesweeperApp(minesweeper_frame)

    # -------------------------------------------------------------------------
    # END TAB UI: Settings
    # -------------------------------------------------------------------------

    # -------------------------------------------------------------------------
    # TAB UI: Save File (tab_file)
    # -------------------------------------------------------------------------
    ttk.Label(tab_file, text="Selected Save File:").pack(pady=10)

    # Main container for the save-path controls (vertical layout)
    path_container = ttk.Frame(tab_file)
    path_container.pack(fill="x", padx=12, pady=(0, 6))

    # ---- Helpers (defined once here) ----
    def _persist_saved_path(slot_idx: int):
        p = save_path_var.get().strip()
        if not p:
            return messagebox.showerror("Error", "No path in entry to save.")
        cfg = load_config() or {}
        cfg[f"saved_path{slot_idx}"] = p
        save_config(cfg)
        show_info("Saved", f"Saved current path into Saved Path {slot_idx}.")

    def _get_saved_path(slot_idx: int):
        cfg = load_config() or {}
        return cfg.get(f"saved_path{slot_idx}", "")

    def _apply_path_selection(candidate_path: str):
        """Validate candidate_path and, if valid, set save_path_var and run normal sync."""
        if not candidate_path or not os.path.exists(candidate_path):
            return messagebox.showerror("Not found", f"Path not found:\n{candidate_path}")

        file_path = candidate_path

        # Keep the same validation + version-mismatch flow as Browse...
        while True:
            try:
                # quick read + reuse existing parsing/validation
                with open(file_path, "r", encoding="utf-8") as f:
                    content = f.read()
                m, r, xp, d, t, s, day, night, tp = get_file_info(content)
                if day is None or night is None:
                    raise ValueError("Missing time settings")
            except Exception as e:
                return messagebox.showerror("Invalid save", f"Selected file could not be validated:\n{e}")

            # Run version mismatch check (same as Browse)
            action, new_path = prompt_save_version_mismatch_and_choose(file_path)
            if action == "error":
                save_path_var.set("")
                return
            if action == "select" and new_path:
                file_path = new_path
                continue

            # action == "ok"
            break

        # Accept and persist into UI + existing save behavior
        save_path_var.set(file_path)
        try:
            save_path(file_path)
        except Exception:
            pass
        # Centralized refresh (best-effort)
        try:
            _refresh_all_tabs_from_save(file_path)
            set_app_status(f"Selected save file: {os.path.basename(file_path)}", timeout_ms=5000)
            if improve_share_var.get():
                _maybe_upload_improve_samples_from_save_path(file_path)
        except Exception:
            pass

    def _choose_complete_save_in_folder(folder):
        """Find CompleteSave(.cfg/.dat / CompleteSave1..3) and let user pick if multiple."""
        candidates = []
        names = [("CompleteSave", 1), ("CompleteSave1", 2), ("CompleteSave2", 3), ("CompleteSave3", 4)]
        for base, idx in names:
            for ext in (".cfg", ".dat"):
                p = os.path.join(folder, base + ext)
                if os.path.exists(p):
                    candidates.append((idx, p))
        if not candidates:
            return show_info("Not found", f"No CompleteSave*.cfg/.dat files found in:\n{folder}")

        if len(candidates) == 1:
            _apply_path_selection(candidates[0][1])
            return

        # multiple -> popup with only valid numbered buttons
        win = _create_themed_toplevel()
        win.title("Multiple save files found")
        ttk.Label(win, text=f"Found {len(candidates)} save files in:\n{folder}\n\nChoose which slot to open:").pack(padx=12, pady=(8,6))
        btn_frame = ttk.Frame(win)
        btn_frame.pack(padx=12, pady=8)
        for idx, path in candidates:
            def _make_handler(p=path, w=win):
                return lambda: (_apply_path_selection(p), w.destroy())
            ttk.Button(btn_frame, text=f"[{idx}]", command=_make_handler()).pack(side="left", padx=6)

    def _find_steam_saves():
        """Best-effort scan for Steam userdata -> */1465360/remote that contain CompleteSave files."""
        candidates = []
        env_candidates = []
        system = platform.system()
        if system == "Windows":
            pf86 = os.environ.get("PROGRAMFILES(X86)") or os.environ.get("PROGRAMFILES")
            if pf86:
                env_candidates.append(os.path.join(pf86, "Steam", "userdata"))
            env_candidates.append(os.path.join(os.path.expanduser("~"), "AppData", "Local", "Steam", "userdata"))
            env_candidates.append(os.path.join("C:\\", "Program Files (x86)", "Steam", "userdata"))
            env_candidates.append(os.path.join("D:\\", "Program Files (x86)", "Steam", "userdata"))
        elif system == "Darwin":
            env_candidates.append(os.path.join(os.path.expanduser("~"), "Library", "Application Support", "Steam", "userdata"))
        else:
            env_candidates.append(os.path.join(os.path.expanduser("~"), ".local", "share", "Steam", "userdata"))
            env_candidates.append(os.path.join(os.path.expanduser("~"), ".steam", "steam", "userdata"))
            env_candidates.append(os.path.join(os.path.expanduser("~"), ".steam", "root", "userdata"))
            env_candidates.append(os.path.join(os.path.expanduser("~"), ".var", "app", "com.valvesoftware.Steam", "data", "Steam", "userdata"))

        for root in env_candidates:
            if not root or not os.path.isdir(root):
                continue
            try:
                for sid in os.listdir(root):
                    remote = os.path.join(root, sid, "1465360", "remote")
                    if os.path.isdir(remote):
                        for fname in os.listdir(remote):
                            if fname.lower().startswith("completesave") and fname.lower().endswith((".cfg", ".dat")):
                                candidates.append(remote)
                                break
            except Exception:
                continue

        # try parsing libraryfolders.vdf for additional library paths
        def _extract_library_paths(txt):
            paths = []
            if system == "Windows":
                for m in re.finditer(r'\"(.:\\\\[^"]*?)\"', txt):
                    p = m.group(1).replace("\\\\", "\\")
                    paths.append(p)
            else:
                for m in re.finditer(r'\"path\"\\s*\"([^\"]+)\"', txt):
                    paths.append(m.group(1))
                for m in re.finditer(r'\"\\d+\"\\s*\"([^\"]+)\"', txt):
                    paths.append(m.group(1))
            return paths

        steamapps_candidates = []
        if system == "Windows":
            steamapps_candidates.append(os.path.join(os.path.expanduser("~"), "AppData", "Local", "Steam", "steamapps"))
        elif system == "Darwin":
            steamapps_candidates.append(os.path.join(os.path.expanduser("~"), "Library", "Application Support", "Steam", "steamapps"))
        else:
            steamapps_candidates.append(os.path.join(os.path.expanduser("~"), ".local", "share", "Steam", "steamapps"))
            steamapps_candidates.append(os.path.join(os.path.expanduser("~"), ".steam", "steam", "steamapps"))
            steamapps_candidates.append(os.path.join(os.path.expanduser("~"), ".var", "app", "com.valvesoftware.Steam", "data", "Steam", "steamapps"))

        for steam_config in steamapps_candidates:
            library_vdf = os.path.join(steam_config, "libraryfolders.vdf")
            if not os.path.exists(library_vdf):
                continue
            try:
                with open(library_vdf, "r", encoding="utf-8", errors="ignore") as f:
                    txt = f.read()
                for p in _extract_library_paths(txt):
                    userdata = os.path.join(p, "userdata")
                    if os.path.isdir(userdata):
                        try:
                            for sid in os.listdir(userdata):
                                remote = os.path.join(userdata, sid, "1465360", "remote")
                                if os.path.isdir(remote):
                                    for fname in os.listdir(remote):
                                        if fname.lower().startswith("completesave") and fname.lower().endswith((".cfg", ".dat")):
                                            candidates.append(remote)
                                            break
                        except Exception:
                            pass
            except Exception:
                pass

        candidates = list(dict.fromkeys(candidates))
        if not candidates:
            return show_info("Steam not found", "Could not locate Steam save folder automatically.")

        if len(candidates) == 1:
            _choose_complete_save_in_folder(candidates[0])
        else:
            win = _create_themed_toplevel()
            win.title("Multiple Steam save folders found")
            ttk.Label(win, text="Multiple Steam save folders found — pick the folder to inspect:").pack(padx=12, pady=(8,6))
            frame = ttk.Frame(win)
            frame.pack(padx=12, pady=8)
            for p in candidates:
                def _h(pp=p, w=win):
                    return lambda: (_choose_complete_save_in_folder(pp), w.destroy())
                ttk.Button(frame, text=os.path.basename(os.path.dirname(os.path.dirname(p))) + " / " + os.path.basename(p), command=_h()).pack(fill="x", pady=2)

    def _find_epic_saves():
        """Check %USERPROFILE%\\Documents\\My Games\\SnowRunner\\base\\storage\\<id> for CompleteSave files."""
        base = os.path.join(os.path.expanduser("~"), "Documents", "My Games", "SnowRunner", "base", "storage")
        if not os.path.isdir(base):
            return show_info("Epic not found", f"Could not locate Epic storage folder:\n{base}")
        found_folders = []
        try:
            for sub in os.listdir(base):
                subp = os.path.join(base, sub)
                if not os.path.isdir(subp):
                    continue
                for fname in os.listdir(subp):
                    if fname.lower().startswith("completesave") and fname.lower().endswith((".cfg", ".dat")):
                        found_folders.append(subp)
                        break
        except Exception:
            pass

        if not found_folders:
            return show_info("Epic", "No SnowRunner save folders with CompleteSave files found in storage.")

        if len(found_folders) == 1:
            _choose_complete_save_in_folder(found_folders[0])
        else:
            win = _create_themed_toplevel()
            win.title("Multiple Epic storage folders")
            ttk.Label(win, text="Multiple Epic storage folders found — pick one to inspect:").pack(padx=12, pady=(8,6))
            frame = ttk.Frame(win)
            frame.pack(padx=12, pady=8)
            for p in found_folders:
                def _h(pp=p, w=win):
                    return lambda: (_choose_complete_save_in_folder(pp), w.destroy())
                ttk.Button(frame, text=os.path.basename(p), command=_h()).pack(fill="x", pady=2)

    def _load_saved_path(slot_idx: int):
        p = _get_saved_path(slot_idx)
        if not p:
            return show_info("Empty", f"No saved path stored for slot {slot_idx}.")
        _apply_path_selection(p)

    # ---- Layout: Save buttons + Entry + Steam/Epic (row 1) ; Load + Browse (row 2) ----
    row1 = ttk.Frame(path_container)
    row1.pack(fill="x", pady=6)

    # Left column: Save Path 1 / Save Path 2 (stacked)
    left_col = ttk.Frame(row1)
    left_col.pack(side="left", anchor="n")
    ttk.Button(left_col, text="Save Path 1", width=14, command=lambda: _persist_saved_path(1)).pack(pady=2)
    ttk.Button(left_col, text="Save Path 2", width=14, command=lambda: _persist_saved_path(2)).pack(pady=2)

    # Middle: Entry (expands)
    mid_col = ttk.Frame(row1)
    mid_col.pack(side="left", fill="x", expand=True, padx=8)
    entry = ttk.Entry(mid_col, textvariable=save_path_var)
    entry.pack(fill="x", expand=True)

    # Right column: Steam / Epic (stacked)
    right_col = ttk.Frame(row1)
    right_col.pack(side="left", anchor="n")
    ttk.Button(right_col, text="Steam", width=12, command=_find_steam_saves).pack(pady=2)
    ttk.Button(right_col, text="Epic", width=12, command=_find_epic_saves).pack(pady=2)

    # Replace the previous Row 2 block with this centered layout
    row2 = ttk.Frame(path_container)
    row2.pack(fill="x", pady=(4,6))

    center_frame = ttk.Frame(row2)
    center_frame.pack()

    def _attach_simple_hover_tooltip(anchor_widget, tooltip_text):
        tip_state = {"win": None, "job": None}

        def _cancel_job():
            job = tip_state.get("job")
            if job is not None:
                try:
                    anchor_widget.after_cancel(job)
                except Exception:
                    pass
                tip_state["job"] = None

        def _hide(_event=None):
            _cancel_job()
            tip = tip_state.get("win")
            if tip is not None:
                try:
                    tip.destroy()
                except Exception:
                    pass
                tip_state["win"] = None

        def _show_now():
            _hide()
            try:
                tip = tk.Toplevel(anchor_widget)
                tip.wm_overrideredirect(True)
                try:
                    tip.withdraw()
                except Exception:
                    pass
                try:
                    tip.attributes("-topmost", True)
                except Exception:
                    pass
                x = int(anchor_widget.winfo_rootx() + anchor_widget.winfo_width() + 8)
                y = int(anchor_widget.winfo_rooty() + anchor_widget.winfo_height() + 6)
                tip.geometry(f"+{x}+{y}")
                tk.Label(
                    tip,
                    text=str(tooltip_text or ""),
                    justify="left",
                    wraplength=430,
                    bg="#fffbe6",
                    fg="black",
                    relief="solid",
                    bd=1,
                    padx=8,
                    pady=6,
                ).pack()
                tip_state["win"] = tip
                try:
                    tip.deiconify()
                except Exception:
                    pass
            except Exception:
                _hide()

        def _schedule_show(_event=None):
            _cancel_job()
            try:
                tip_state["job"] = anchor_widget.after(260, _show_now)
            except Exception:
                _show_now()

        anchor_widget.bind("<Enter>", _schedule_show, add="+")
        anchor_widget.bind("<Leave>", _hide, add="+")
        anchor_widget.bind("<ButtonPress>", _hide, add="+")
        anchor_widget.bind("<FocusOut>", _hide, add="+")

    ttk.Button(center_frame, text="Load Path 1", width=12, command=lambda: _load_saved_path(1)).pack(side="left", padx=(0,6))
    ttk.Button(center_frame, text="Load Path 2", width=12, command=lambda: _load_saved_path(2)).pack(side="left", padx=(0,12))
    ttk.Button(center_frame, text="Browse...", command=browse_file).pack(side="left")
    improve_share_inline = ttk.Frame(center_frame)
    improve_share_inline.pack(side="left", padx=(12, 0))
    ttk.Checkbutton(
        improve_share_inline,
        text="Make editor better (optional)",
        variable=improve_share_var,
        command=_on_improve_share_checkbox_changed,
    ).pack(side="left")
    improve_share_info_badge = tk.Label(
        improve_share_inline,
        text="i",
        width=2,
        relief="ridge",
        bd=1,
        highlightthickness=0,
        cursor="question_arrow",
        bg=_theme_color_literal("#e9e9e9", role="button_bg"),
        fg=_theme_color_literal("black", role="fg"),
    )
    improve_share_info_badge.pack(side="left", padx=(5, 0))
    _attach_simple_hover_tooltip(
        improve_share_info_badge,
        "If enabled, a copy of your save file will be uploaded anonymously and used only for improving features and fixing bugs. "
        "Files are stored privately and never shared.",
    )

    if improve_share_var.get():
        _update_improve_share_meta(timeout_ms=6000)
        _maybe_upload_improve_samples_from_save_path()

    # Help / hints below (single label)
    ttk.Label(
        tab_file,
        text=(
            "Instructions for loading:\n\n"
            "Slot 1 → CompleteSave.cfg\n"
            "Slot 2 → CompleteSave1.cfg\n"
            "Slot 3 → CompleteSave2.cfg\n"
            "Slot 4 → CompleteSave3.cfg\n\n"
            "Steam saves are typically found at:\n"
            "[Steam install]/userdata/[steam_id]/1465360/remote\n\n"
            "Epic and other platforms:\n"
            "%USERPROFILE%\\Documents\\My Games\\SnowRunner\\base\\storage\\<unique_key_folder>"
        ),
        wraplength=700,
        justify="left",
        font=("TkDefaultFont", 9),
    ).pack(pady=(6, 10))
    # ---------- end replacement block ----------

    ttk.Label(
        tab_file,
        text="⚠️ SnowRunner must be closed before editing the save file. Changes made while the game is running may be lost or cause issues.",
        wraplength=500,
        justify="center",
        style="Warning.TLabel",
        font=("TkDefaultFont", 9, "bold")
    ).pack(pady=(5, 10))

    def _open_save_tab_link(url, label):
        try:
            webbrowser.open(str(url), new=2)
            set_app_status(f"Opened {label}.", timeout_ms=5000)
        except Exception as e:
            set_app_status(f"Failed to open {label}: {e}", timeout_ms=9000)

    save_tab_links_left = ttk.Frame(tab_file)
    save_tab_links_left.place(relx=0.0, rely=1.0, anchor="sw", x=10, y=-10)
    ttk.Button(
        save_tab_links_left,
        text="Buy me a coffee",
        command=lambda: _open_save_tab_link("https://buymeacoffee.com/mrboxik", "Buy me a coffee"),
    ).pack(side="left", padx=(0, 6))
    ttk.Button(
        save_tab_links_left,
        text="Discord Tech Support",
        command=lambda: _open_save_tab_link("https://discord.com/users/638802769393745950", "Discord Tech Support"),
    ).pack(side="left")

    save_tab_links_right = ttk.Frame(tab_file)
    save_tab_links_right.place(relx=1.0, rely=1.0, anchor="se", x=-10, y=-10)
    ttk.Button(
        save_tab_links_right,
        text="GitHub page",
        command=lambda: _open_save_tab_link("https://github.com/MrBoxik/SnowRunner-Save-Editor", "GitHub page"),
    ).pack(side="left", padx=(0, 6))
    ttk.Button(
        save_tab_links_right,
        text="License",
        command=lambda: _open_save_tab_link(
            "https://github.com/MrBoxik/SnowRunner-Save-Editor/blob/main/LICENSE",
            "License",
        ),
    ).pack(side="left")

    # Footer text pinned to bottom center of the Save File tab
    footer_frame = ttk.Frame(tab_file)
    footer_frame.place(relx=0.5, rely=1.0, anchor="s", y=-10)

    ttk.Label(
        footer_frame,
        text="Made with hatred for bugs by: MrBoxik",
        font=("TkDefaultFont", 11, "bold"),
        justify="center"
    ).pack()

    _version_text = f"Version: {APP_VERSION}"
    try:
        status = globals().get("_UPDATE_STATUS")
        if status == "update":
            _version_text = f"Version: {APP_VERSION} (update available)"
        elif status == "dev":
            _version_text = f"Version: {APP_VERSION} (dev build)"
    except Exception:
        pass

    _VERSION_FOOTER_LABEL = ttk.Label(
        footer_frame,
        text=_version_text,
        font=("TkDefaultFont", 9),
        justify="center"
    )
    _VERSION_FOOTER_LABEL.pack()
    try:
        globals()["_VERSION_FOOTER_LABEL"] = _VERSION_FOOTER_LABEL
    except Exception:
        pass

    # -------------------------------------------------------------------------
    # END TAB UI: Save File
    # -------------------------------------------------------------------------

    # -------------------------------------------------------------------------
    # TAB UI: Money & Rank (tab_money)
    # -------------------------------------------------------------------------
    # Money & Rank tab (new layout + helpers)
    def _write_json_key_to_file(path, key, value):
        """Helper: safe replace/insert using _set_key_in_text (uses json.dumps)."""
        try:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            content = _set_key_in_text(content, key, json.dumps(value))
            with open(path, "w", encoding="utf-8") as f:
                f.write(content)
            return True
        except Exception as e:
            print(f"[write_json_key] {e}")
            return False

    def _read_experience_from_file(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                c = f.read()
            val = _read_int_key_from_text(c, "experience")
            print("DEBUG XP READ:", val)
            return val
        except Exception as e:
            print("DEBUG XP ERROR:", e)
            return None


    # ---- UI layout ----
    top_frame = ttk.Frame(tab_money)
    top_frame.pack(pady=4)

    # Money row (editable + update button)
    ttk.Label(top_frame, text="Money:").grid(row=0, column=0, sticky="w")
    ttk.Entry(top_frame, textvariable=money_var, width=22).grid(row=0, column=1, padx=(6, 8))

    # 32-bit money bounds (as requested)
    MONEY_MIN = -2147483647
    MONEY_MAX =  2147483647

    def _parse_and_clamp_money(s: str):
        """
        Parse s as an int (accepts leading +/-). Return (clamped_value, was_clamped, original_value).
        If s is not a valid integer, return (None, False, None).
        """
        try:
            orig = int(s.strip())
        except Exception:
            return None, False, None
        clamped = orig
        if clamped < MONEY_MIN:
            clamped = MONEY_MIN
        elif clamped > MONEY_MAX:
            clamped = MONEY_MAX
        return clamped, (clamped != orig), orig


    def update_money_only():
        make_backup_if_enabled(save_path_var.get())
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")

        v = money_var.get().strip()
        parsed, was_clamped, orig = _parse_and_clamp_money(v)
        if parsed is None:
            return messagebox.showerror("Invalid", "Money must be an integer (e.g. -100 or 12345).")

        money_val = int(parsed)
        if not _write_json_key_to_file(path, "money", money_val):
            return messagebox.showerror("Error", "Failed to write money to file.")

        # Refresh GUI after successful write
        try:
            if "sync_all_rules" in globals():
                sync_all_rules(path)
            else:
                money_var.set(str(money_val))
        except Exception as e:
            print("Warning: failed to refresh GUI after money update:", e)

        if was_clamped:
            show_info("Clamped", f"Entered value {orig} is outside allowed range.\n"
                                           f"Saved value was changed to {money_val}.\n"
                                           f"Value must be between ({MONEY_MIN} and {MONEY_MAX}).")
        else:
            show_info("Success", f"Money updated to {money_val}.")


    ttk.Button(top_frame, text="Update Money", command=update_money_only).grid(row=0, column=2, padx=(4,0))


    # Middle area: left = experience, right = rank
    mid_frame = ttk.Frame(tab_money)
    mid_frame.pack(pady=8)

    # -- left: Experience (fine tuning)
    left = ttk.Frame(mid_frame)
    left.pack(side="left", padx=18, anchor="n")
    ttk.Label(left, text="Experience: (fine tuning)").pack(anchor="w")
    ttk.Entry(left, textvariable=xp_var, width=18).pack(pady=(4,6))

    def update_experience_only():
        make_backup_if_enabled(save_path_var.get())
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")
        v = xp_var.get().strip()
        if not v.isdigit():
            return messagebox.showerror("Invalid", "Experience must be a non-negative integer.")
        val = int(v)

        # compute the rank that corresponds to this XP (highest rank whose requirement <= xp)
        try:
            possible = [k for k, req in RANK_XP_REQUIREMENTS.items() if val >= req]
            computed_rank = max(possible) if possible else None
        except Exception:
            computed_rank = None

        j_xp = json.dumps(val)
        j_rank = json.dumps(computed_rank) if computed_rank is not None else None

        try:
            # read file once
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()

            # primary safe update using existing helper (handles most cases)
            content = _set_key_in_text(content, "experience", j_xp)
            if computed_rank is not None:
                content = _set_key_in_text(content, "rank", j_rank)

            # also patch inside any CompleteSave... blocks (reverse order)
            for match in reversed(list(re.finditer(r'"(CompleteSave\d*)"\s*:\s*{', content))):
                try:
                    block_str, bs, be = extract_brace_block(content, match.end() - 1)
                except Exception:
                    continue
                patched_block = _set_key_in_text(block_str, "experience", j_xp)
                if computed_rank is not None:
                    patched_block = _set_key_in_text(patched_block, "rank", j_rank)
                if patched_block != block_str:
                    content = content[:bs] + patched_block + content[be:]

            # numeric fallback pass to catch plain '"experience": 123' or '"rank": 5' forms
            content = re.sub(r'("experience"\s*:\s*)(-?\d+)',
                             lambda m: m.group(1) + j_xp,
                             content, flags=re.IGNORECASE)
            if computed_rank is not None:
                content = re.sub(r'("rank"\s*:\s*)(-?\d+)',
                                 lambda m: m.group(1) + j_rank,
                                 content, flags=re.IGNORECASE)

            # write once
            with open(path, "w", encoding="utf-8") as f:
                f.write(content)

            # Update GUI immediately (best-effort)
            try:
                if "xp_var" in globals() and xp_var is not None:
                    xp_var.set(str(val))
                if computed_rank is not None and "rank_var" in globals() and rank_var is not None:
                    rank_var.set(str(computed_rank))
            except Exception as e:
                print("Warning: failed to set xp_var/rank_var locally:", e)

            # Full sync (best-effort)
            try:
                if "sync_all_rules" in globals():
                    sync_all_rules(path)
            except Exception as e:
                print("Warning: sync_all_rules failed after experience update:", e)

            show_info("Success", f"Experience updated to {val}.")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to update experience: {e}")


    ttk.Button(left, text="Update Experience", command=update_experience_only).pack()


    # -- right: Rank controls (restored)
    right = ttk.Frame(mid_frame)
    right.pack(side="left", padx=18, anchor="n")
    ttk.Label(right, text="Rank (1 - 30):").pack(anchor="w")

    def update_rank_only():
        make_backup_if_enabled(save_path_var.get())
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")

        rv = rank_var.get().strip()
        if not rv.isdigit():
            return messagebox.showerror("Invalid", "Rank must be numeric.")
        rank_val = int(rv)
        if not (1 <= rank_val <= 30):
            return messagebox.showerror("Invalid", "Rank must be 1–30.")

        xp_val = RANK_XP_REQUIREMENTS.get(rank_val, 0)
        j_rank = json.dumps(rank_val)
        j_xp = json.dumps(xp_val)

        try:
            # read once
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()

            # primary safe update using existing helper (handles most cases)
            content = _set_key_in_text(content, "rank", j_rank)
            content = _set_key_in_text(content, "experience", j_xp)

            # extra pass: replace numeric occurrences explicitly (covers plain "rank": 5 etc.)
            content = re.sub(r'("rank"\s*:\s*)(-?\d+)',
                             lambda m: m.group(1) + j_rank,
                             content, flags=re.IGNORECASE)
            content = re.sub(r'("experience"\s*:\s*)(-?\d+)',
                             lambda m: m.group(1) + j_xp,
                             content, flags=re.IGNORECASE)

            # write once
            with open(path, "w", encoding="utf-8") as f:
                f.write(content)

            # update UI (best-effort)
            try:
                if "xp_var" in globals() and xp_var is not None:
                    xp_var.set(str(xp_val))
                if "rank_var" in globals() and rank_var is not None:
                    rank_var.set(str(rank_val))
            except Exception as e:
                print("Warning: failed to set xp_var/rank_var locally:", e)

            # sync other UI/rules if available
            try:
                if "sync_all_rules" in globals():
                    sync_all_rules(path)
            except Exception as e:
                print("Warning: sync_all_rules failed after rank update:", e)

            show_info("Success", f"Rank set to {rank_val} (experience set to {xp_val}).")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to update rank: {e}")

    ttk.Entry(right, textvariable=rank_var, width=8).pack(pady=(4,6))
    ttk.Button(right, text="Update Rank", command=update_rank_only).pack()

    # Combined update (atomic) — money + rank + xp computed
    def update_money_rank_combined():
        make_backup_if_enabled(save_path_var.get())
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")
        
        m = money_var.get().strip()
        r = rank_var.get().strip()

        # parse and clamp money (allows negatives within 32-bit bounds)
        money_parsed, money_clamped, money_orig = _parse_and_clamp_money(m)
        if money_parsed is None:
            return messagebox.showerror("Invalid", "Money must be an integer (e.g. -100 or 12345).")

        if not r.isdigit():
            return messagebox.showerror("Invalid", "Rank must be numeric.")
        rank_val = int(r)
        if not (1 <= rank_val <= 30):
            return messagebox.showerror("Invalid", "Rank must be 1–30.")

        money_val = int(money_parsed)

        xp_val = RANK_XP_REQUIREMENTS.get(rank_val, 0)

        try:
            okm = _write_json_key_to_file(path, "money", money_val)
            okr = _write_json_key_to_file(path, "rank", rank_val)
            okx = _write_json_key_to_file(path, "experience", xp_val)
            if not (okm and okr and okx):
                raise RuntimeError("One or more writes failed")
            # update UI immediately
            try:
                if "money_var" in globals() and money_var is not None:
                    money_var.set(str(money_val))
                if "rank_var" in globals() and rank_var is not None:
                    rank_var.set(str(rank_val))
                if "xp_var" in globals() and xp_var is not None:
                    xp_var.set(str(xp_val))
            except Exception as e:
                print("Warning: failed to set money/rank/xp locally:", e)
            # full sync
            try:
                if "sync_all_rules" in globals():
                    sync_all_rules(path)
            except Exception as e:
                print("Warning: sync_all_rules failed after combined update:", e)
            show_info("Success", "Money & Rank updated.")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to update money & rank: {e}")

    # XP requirements display (single-column, centered, monospace, aligned columns)
    req_frame = ttk.Frame(tab_money)
    req_frame.pack(fill="x", padx=10, pady=(6,12))

    ttk.Label(
        req_frame,
        text="XP Requirements (Rank : xp)",
        font=("TkDefaultFont", 10, "bold")
    ).pack(anchor="center")

    xp_table_frame = ttk.Frame(req_frame)
    xp_table_frame.pack(pady=6, anchor="center")

    try:
        items = sorted(RANK_XP_REQUIREMENTS.items())
        # Use a monospace font so digits render uniformly
        monospace_font = ("TkFixedFont", 10)

        # build a small grid with two columns: level (right-aligned) and xp (left-aligned)
        for i, (lvl, xp) in enumerate(items):
            lbl_lvl = ttk.Label(xp_table_frame, text=f"{lvl}", font=monospace_font)
            lbl_colon = ttk.Label(xp_table_frame, text=":", font=monospace_font)
            lbl_xp = ttk.Label(xp_table_frame, text=f"{xp}", font=monospace_font)

            # grid them so numbers align neatly
            lbl_lvl.grid(row=i, column=0, sticky="e", padx=(0,6))
            lbl_colon.grid(row=i, column=1, sticky="e")
            lbl_xp.grid(row=i, column=2, sticky="w", padx=(6,0))

        # optional: add a tiny bit of spacing between rows
        for r in range(len(items)):
            xp_table_frame.grid_rowconfigure(r, pad=1)

    except Exception:
        ttk.Label(req_frame, text="No XP table available.").pack(anchor="center")

    # -------------------------------------------------------------------------
    # END TAB UI: Money & Rank
    # -------------------------------------------------------------------------

    # -------------------------------------------------------------------------
    # TAB UI: Missions (tab_missions)
    # -------------------------------------------------------------------------
    seasons = [(name, i) for i, name in enumerate(SEASON_LABELS, start=1)]
    base_maps = [(name, code) for code, name in BASE_MAPS]
    selector = _build_region_selector(
        tab_missions,
        seasons,
        base_maps,
        other_var=other_season_var,
        base_maps_label="Base Game Maps:",
        base_maps_label_font=("TkDefaultFont", 10, "bold"),
        season_pady=10
    )
    season_vars = selector["season_vars"]
    base_map_vars = selector["map_vars"]
    all_check_vars = selector["all_check_vars"]

    def run_complete():
        make_backup_if_enabled(save_path_var.get())
        if not os.path.exists(save_path_var.get()):
            messagebox.showerror("Error", "Save file not found.")
            return
        selected_seasons = _collect_checked_values(season_vars)
        _append_other_season_int(selected_seasons, other_season_var)
        selected_maps = _collect_checked_values(base_map_vars)
        if not selected_seasons and not selected_maps:
            show_info("Info", "No seasons or maps selected.")
            return
        complete_seasons_and_maps(save_path_var.get(), selected_seasons, selected_maps)

    ttk.Button(tab_missions, text="Complete Selected Missions", command=run_complete).pack(pady=10)
    _add_check_all_checkbox(tab_missions, all_check_vars)

    # Disclaimer below the complete button
    ttk.Label(
        tab_missions,
        text="You must accept the task or mission in the game before it can be completed",
        style="Warning.TLabel",
        font=("TkDefaultFont", 10, "bold"),
        wraplength=400,
        justify="center"
    ).pack(pady=(5, 15))


    # -------------------------------------------------------------------------
    # END TAB UI: Missions
    # -------------------------------------------------------------------------

    # -------------------------------------------------------------------------
    # TAB UI: Time (tab_time)
    # -------------------------------------------------------------------------
    ttk.Label(tab_time, text="Time Preset:").pack(pady=10)
    ttk.Combobox(tab_time, textvariable=time_preset_var, values=list(time_presets.keys()), state="readonly", width=30).pack(pady=5)
    ttk.Checkbutton(tab_time, text="Enable Time Skipping", variable=skip_time_var).pack(pady=10)
    ttk.Label(tab_time, text="⚠️ Time settings only apply in New Game+ mode.", style="Warning.TLabel", font=("TkDefaultFont", 9, "bold")).pack(pady=(5, 10))
    ttk.Label(tab_time, text="⚠️ To use custom sliders, select 'Custom' from the Time Presets.", style="Warning.TLabel", font=("TkDefaultFont", 9, "bold")).pack(pady=(5, 10))




    frame_day = ttk.Frame(tab_time)
    frame_day.pack()
    ttk.Label(frame_day, text="Custom Day Time   :").pack(side="left")
    ttk.Scale(
        frame_day,
        command=lambda v: custom_day_var.set(round(float(v), 2)),
        from_=-5.0,
        to=5.0,
        variable=custom_day_var,
        orient="horizontal",
        length=250
    ).pack(side="left", padx=5)
    day_entry = ttk.Entry(frame_day, textvariable=custom_day_var, width=6)
    day_entry.pack(side="left")
    try:
        custom_day_var.set(round(float(day), 2) if day is not None else 1.0)
    except Exception:
        custom_day_var.set(1.0)

    frame_night = ttk.Frame(tab_time)
    frame_night.pack()
    ttk.Label(frame_night, text="Custom Night Time:").pack(side="left")
    ttk.Scale(
        frame_night,
        command=lambda v: custom_night_var.set(round(float(v), 2)),
        from_=-5.0,
        to=5.0,
        variable=custom_night_var,
        orient="horizontal",
        length=250
    ).pack(side="left", padx=5)
    night_entry = ttk.Entry(frame_night, textvariable=custom_night_var, width=6)
    night_entry.pack(side="left")
    try:
        custom_night_var.set(round(float(night), 2) if night is not None else 1.0)
    except Exception:
        custom_night_var.set(1.0)

    # --- Time preset <-> custom sliders sync ---
    def _on_time_preset_change(*_):
        if _TIME_SYNC_GUARD:
            return
        preset = time_preset_var.get()
        if not preset:
            return
        if preset != "Custom":
            day_night = time_presets.get(preset, (1.0, 1.0))
            _sync_time_ui(day=day_night[0], night=day_night[1], preset_name=preset)

    def _on_custom_time_change(*_):
        if _TIME_SYNC_GUARD:
            return
        try:
            if time_preset_var.get() != "Custom":
                _sync_time_ui(
                    day=custom_day_var.get(),
                    night=custom_night_var.get(),
                    preset_name="Custom"
                )
        except Exception:
            pass

    try:
        time_preset_var.trace_add("write", _on_time_preset_change)
    except Exception:
        try:
            time_preset_var.trace("w", _on_time_preset_change)
        except Exception:
            pass

    for _v in (custom_day_var, custom_night_var):
        try:
            _v.trace_add("write", _on_custom_time_change)
        except Exception:
            try:
                _v.trace("w", _on_custom_time_change)
            except Exception:
                pass


    ttk.Label(tab_time, text="""ℹ️ Time Speed Settings:
2.0 = Twice as fast
1.0 = normal speed
0.0 = time stops
-1.0 = Rewinds time
-2.0 = Twice as fast in reverse

⚠️ If one value is positive and the other is negative,
time will freeze at the transition (day to night or night to day).""", wraplength=400, justify="left").pack(pady=(10, 20))

    def update_time_btn():
        make_backup_if_enabled(save_path_var.get())
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")

        if time_preset_var.get() == "Custom":
            day = round(custom_day_var.get(), 2)
            night = round(custom_night_var.get(), 2)
        else:
            day, night = time_presets.get(time_preset_var.get(), (1.0, 1.0))

        st = skip_time_var.get()
        modify_time(path, day, night, st)

    ttk.Button(tab_time, text="Apply Time Settings", command=update_time_btn).pack(pady=20)

    # -------------------------------------------------------------------------
    # END TAB UI: Time
    # -------------------------------------------------------------------------

    if os.path.exists(save_path_var.get()):
        sync_rule_dropdowns(save_path_var.get())

    
    # --- Final Sync After GUI is Built ---
    if os.path.exists(save_path_var.get()):
        for loader in plugin_loaders:
            try:
                loader(save_path_var.get())
            except Exception as e:
                print(f"Plugin failed to update GUI on startup: {e}")


    # External rules/extensions no longer mounted into the Rules tab (tab intentionally left empty).

    
    if delete_path_on_close_var.get():
        try:
            _delete_config_keys(["last_save_path"])
        except Exception as e:
            print("[Warning] Could not delete save path:", e)

    # --- Auto-sync on startup if a valid save file is remembered ---
    if save_path_var.get() and os.path.exists(save_path_var.get()):
        try:
            sync_all_rules(save_path_var.get())
            print("[DEBUG] Auto-sync applied on startup.")
        except Exception as e:
            print("[Warning] Auto-sync failed:", e)

    _close_guard = {"done": False}

    def _shutdown_editor():
        if _close_guard["done"]:
            return
        _close_guard["done"] = True
        try:
            save_settings_silent()
        except Exception:
            pass
        try:
            stop_autosave_monitor()
        except Exception:
            pass
        try:
            root.destroy()
        except Exception:
            pass

    try:
        root.protocol("WM_DELETE_WINDOW", _shutdown_editor)
    except Exception:
        pass

    _apply_editor_theme(root, dark_mode=dark_mode_var.get())

    # --- Auto-size window to show all tabs and full Rules tab content ---
    def _fit_window_to_tabs_and_rules():
        try:
            root.update_idletasks()
            try:
                tab_count = tab_control.index("end")
            except Exception:
                tab_count = 0

            nb_req_w = tab_control.winfo_reqwidth()
            nb_req_h = tab_control.winfo_reqheight()
            rules_req_w = tab_rules.winfo_reqwidth() if 'tab_rules' in locals() else 0
            rules_req_h = tab_rules.winfo_reqheight() if 'tab_rules' in locals() else 0

            # Use full rules content height if available (so all rules are visible)
            rules_frame = globals().get("_RULES_CONTENT_FRAME")
            if rules_frame is not None:
                try:
                    rules_req_w = max(rules_req_w, rules_frame.winfo_reqwidth())
                    rules_req_h = max(rules_req_h, rules_frame.winfo_reqheight())
                except Exception:
                    pass

            header_width = 0
            if tab_count > 0:
                try:
                    x, y, w, h = tab_control.bbox(tab_count - 1)
                    header_width = x + w
                except Exception:
                    header_width = 0
            if not header_width and tab_count > 0:
                try:
                    font = tkfont.nametofont("TkDefaultFont")
                except Exception:
                    font = tkfont.Font()
                tab_texts = []
                for i in range(tab_count):
                    try:
                        tab_texts.append(tab_control.tab(i, "text"))
                    except Exception:
                        pass
                text_width = sum(font.measure(t) for t in tab_texts)
                header_width = text_width + (12 * tab_count) + 20

            target_w = int(max(header_width, nb_req_w, rules_req_w) + 16)
            status_h = 0
            try:
                status_h = status_bar.winfo_reqheight() if "status_bar" in locals() else 0
            except Exception:
                status_h = 0
            target_h = int(max(nb_req_h, rules_req_h) + 60 + status_h)
            if target_w > 0 and target_h > 0:
                root.geometry(f"{target_w}x{target_h}")
        except Exception as e:
            print("[Warning] auto-size failed:", e)

    # Size before showing the window (avoid visible resize jump)
    _fit_window_to_tabs_and_rules()
    try:
        root.update_idletasks()
        _fit_window_to_tabs_and_rules()
    except Exception:
        pass
    try:
        root.deiconify()
    except Exception:
        pass
    try:
        root.after(40, lambda: _apply_windows_titlebar_theme(root, dark_mode=dark_mode_var.get()))
        root.after(180, lambda: _apply_windows_titlebar_theme(root, dark_mode=dark_mode_var.get()))
    except Exception:
        pass
    try:
        root.after(60, _fit_window_to_tabs_and_rules)
    except Exception:
        pass
    try:
        root.after(
            120,
            lambda: _ensure_lazy_tab_built(tab_control.nametowidget(tab_control.select())),
        )
    except Exception:
        pass

    root.mainloop()

# -----------------------------------------------------------------------------
# END SECTION: Dependency Checks + App Launch
# -----------------------------------------------------------------------------

FogToolFrame = FogToolApp
if __name__ == "__main__":
    try:
        argv_flags = {str(a).strip().lower() for a in sys.argv[1:] if str(a).strip()}
        _cleanup_windows_update_artifacts()
        _start_windows_update_artifact_cleanup_retry()
        if "--self-test" in argv_flags:
            # Lightweight startup probe for the auto-updater:
            # process must launch and exit cleanly without opening the GUI.
            sys.exit(0)
        launch_gui()
    except Exception as e:
        print("[Fatal] Editor failed to launch:", e)
        traceback.print_exc()
        try:
            _NATIVE_SHOWERROR(
                "Startup Error",
                f"The editor failed to launch cleanly.\n\n{e}\n\n"
                "See console output for details."
            )
        except Exception:
            pass


