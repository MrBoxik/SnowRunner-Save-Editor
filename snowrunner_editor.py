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
from datetime import datetime

# Guard optional imports to prevent crashes when dependencies missing
try:
    import requests  # type: ignore
except Exception:
    requests = None

try:
    from PIL import Image, ImageDraw, ImageTk  # type: ignore
except Exception:
    Image = ImageDraw = ImageTk = None

import webbrowser
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, PhotoImage
import tkinter.font as tkfont

# =============================================================================
# APP VERSION (manual)
# =============================================================================
APP_VERSION = 96
_UPDATE_STATUS = None  # "update", "dev", "none"

# Pillow resampling compatibility (handle both old and new Pillow API)
if Image is not None:
    try:
        RESAMPLE_LANCZOS = Image.Resampling.LANCZOS
    except Exception:
        RESAMPLE_LANCZOS = getattr(Image, "LANCZOS", getattr(Image, "ANTIALIAS", Image.NEAREST))
else:
    RESAMPLE_LANCZOS = None

# Flag to enable/disable image-dependent features
IMAGE_ENABLED = Image is not None and ImageTk is not None

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
_AUTOSAVE_THREAD = None
_AUTOSAVE_STOP_EVENT = None
_TIME_SYNC_GUARD = False

SAVE_FILE_NAME = "snowrunner_editor_save.json"
_SAVE_FILE_PATH = None

# -----------------------------------------------------------------------------
# END SECTION: Global Tk/Editor State
# -----------------------------------------------------------------------------

# =============================================================================
# SECTION: Local Save-Data Path Helpers
# Used In: Minesweeper mini-game + app settings persistence
# =============================================================================

def _ensure_dir(path):
    try:
        os.makedirs(path, exist_ok=True)
        return True
    except Exception:
        return False

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
    """Return a writable path for Minesweeper progress data."""
    global _SAVE_FILE_PATH
    if _SAVE_FILE_PATH:
        return _SAVE_FILE_PATH

    base_dir = None
    try:
        system = platform.system()
    except Exception:
        system = None

    if system == "Windows":
        base_dir = os.getenv("LOCALAPPDATA") or os.getenv("APPDATA")
        if base_dir:
            base_dir = os.path.join(base_dir, "SnowRunnerEditor")
    elif system == "Darwin":
        base_dir = os.path.expanduser("~/Library/Application Support/SnowRunnerEditor")
    else:
        base_dir = os.getenv("XDG_DATA_HOME")
        if base_dir:
            base_dir = os.path.join(base_dir, "snowrunner_editor")
        else:
            base_dir = os.path.expanduser("~/.local/share/snowrunner_editor")

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
    """Return list of PhotoImage objects loaded from a .ico (best effort)."""
    try:
        if not ico_path or not os.path.exists(ico_path):
            return []
        if Image is None or ImageTk is None:
            return []
        ico_img = Image.open(ico_path)
        icons = []
        try:
            n_frames = getattr(ico_img, "n_frames", 1)
        except Exception:
            n_frames = 1
        if n_frames > 1:
            for i in range(n_frames):
                try:
                    ico_img.seek(i)
                    icons.append(ImageTk.PhotoImage(ico_img.copy()))
                except Exception:
                    pass
        else:
            icons.append(ImageTk.PhotoImage(ico_img))
        return icons
    except Exception:
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

    Prefers app_icon.ico on Windows and app_icon.png elsewhere. Uses Pillow's
    ImageTk when available, falls back to tkinter.PhotoImage. Non-fatal.
    """
    try:
        system = platform.system()
        # Windows: prefer .ico and explicitly set taskbar icon
        if system == "Windows":
            ico = resource_path("app_icon.ico")
            if os.path.exists(ico):
                did_set = False
                # Try using ImageTk to load multi-size .ico for iconphoto (best results on taskbar)
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

        # Try PNG via Pillow ImageTk (preferred)
        png = resource_path("app_icon.png")
        if os.path.exists(png):
            try:
                if 'ImageTk' in globals() and ImageTk is not None:
                    tkimg = ImageTk.PhotoImage(Image.open(png))
                    try:
                        root.iconphoto(False, tkimg)
                    except Exception:
                        try:
                            root.iconphoto(tkimg)
                        except Exception:
                            pass
                    try:
                        setattr(root, "_app_icon_image", tkimg)
                    except Exception:
                        pass
                    return
            except Exception:
                # try tkinter PhotoImage fallback
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
        # Non-Windows fallback: if no PNG but ICO exists, try using ICO via Pillow
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
CELL_COLORS = {"default": "#bdbdbd", "empty": "white", "flagged": "#e0e0e0"}
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

        self.title_label = tk.Label(root, font=("Arial", 16))
        self.title_label.pack(pady=10)
        self.frame = tk.Frame(root)
        self.frame.pack()

        self.start_level()

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

        self.cells, self.mine_locations = [], set()
        for r in range(self.size):
            row = []
            for c in range(self.size):
                btn = tk.Button(
                    self.frame, width=2, height=1, font=("Arial", 12),
                    bg=CELL_COLORS["default"], activebackground=CELL_COLORS["default"],
                    command=lambda r=r, c=c: self.reveal(r, c)
                )
                # Cross-platform right-click support
                btn.bind("<Button-3>", lambda e, r=r, c=c: self.toggle_flag(r, c))
                btn.bind("<Button-2>", lambda e, r=r, c=c: self.toggle_flag(r, c))
                btn.grid(row=r, column=c)
                row.append(Cell(r, c, btn))
            self.cells.append(row)

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
            messagebox.showinfo("Boom!", "You hit a mine! Restarting level...")
            return self.start_level()

        self._reveal_recursive(r, c)
        if self.check_win():
            self.win_level()

    def _reveal_recursive(self, r, c):
        if not (0 <= r < self.size and 0 <= c < self.size): return
        cell = self.cells[r][c]
        if cell.revealed or cell.flagged: return

        cell.revealed = True
        cell.btn.config(relief=tk.SUNKEN, state=tk.DISABLED, bg=CELL_COLORS["empty"])
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
            cell.btn.config(text=EMOJI_FLAG, bg=CELL_COLORS["flagged"])
        else:
            cell.btn.config(text="", bg=CELL_COLORS["default"])

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
        self.current_image_L = None  # Pillow L image (editor orientation)
        self.footer = b""
        self.scale = 1.0
        self.offset_x = 0
        self.offset_y = 0
        self.brush_gray = 1
        self.brush_size = 4
        self.drawing = False
        self.last_x = None
        self.last_y = None

        # Overlay state (RGBA)
        self.overlay_img = None
        self.overlay_scale = 1.0
        self.overlay_offset = (0, 0)   # in fog-image pixels (editor orientation)
        self.overlaytk = None
        self.dragging_overlay = False
        self.last_drag = (0, 0)

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
        ttk.Button(top, text="Load Overlay PNG", command=self.load_overlay).pack(side="left", padx=6)
        ttk.Button(top, text="Apply Overlay", command=self.apply_overlay).pack(side="left", padx=2)
        ttk.Button(top, text="Clear Overlay", command=self.clear_overlay).pack(side="left", padx=2)
        ttk.Button(top, text="Tutorial / Info", command=self.show_info).pack(side="right", padx=6)

        # status + canvas
        self.status = tk.StringVar(value="Ready")
        ttk.Label(parent, textvariable=self.status).pack(fill="x")
        self.canvas = tk.Canvas(parent, bg="#d4bf98")
        self.canvas.pack(fill="both", expand=True)
        self.canvas.bind("<Configure>", lambda e: self.show_preview())

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

Step 4: Overlay a PNG (optional)  
- Click Load Overlay PNG to place an image over the fog map.  
- Supported only in PNG format (use online converters if needed).  
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
        win = tk.Toplevel(self)
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

    # ---------------- Editor functions ----------------
    def open_cfg(self):
        if not IMAGE_ENABLED:
            messagebox.showerror("Missing dependency", "Pillow is required for fog editing.\nRun: pip install Pillow")
            return
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
            imgL = Image.frombytes("L", (w, h), pix)
            # vertical flip in editor to match in-game orientation
            imgL = imgL.transpose(Image.FLIP_TOP_BOTTOM)
            self.current_image_L = imgL.copy()

            # If overlay is loaded, center it by default on load
            if self.overlay_img:
                iw, ih = self.current_image_L.size
                ow, oh = self.overlay_img.size
                # center overlay in image coordinates
                self.overlay_offset = (max(0, (iw - int(ow * self.overlay_scale)) // 2),
                                       max(0, (ih - int(oh * self.overlay_scale)) // 2))

            self.log(f"Loaded {os.path.basename(path)} — {w}x{h}")
            self.show_preview()
        except Exception as e:
            with open(self.cfg_path + ".decode_debug.log", "a", encoding="utf-8") as f:
                f.write("Open parse error:\n")
                f.write(repr(e) + "\n")
                f.write(traceback.format_exc() + "\n")
            messagebox.showerror("Error parsing payload", str(e))

    def show_preview(self):
        if not IMAGE_ENABLED:
            messagebox.showerror("Missing dependency", "Pillow is required for this feature.\nRun: pip install Pillow")
            return
        if not self.current_image_L:
            return
        cw = self.canvas.winfo_width(); ch = self.canvas.winfo_height()
        iw, ih = self.current_image_L.size
        if cw <= 0 or ch <= 0:
            return
        scale = min(cw / iw, ch / ih)
        self.scale = scale
        self.offset_x = (cw - iw * scale) / 2
        self.offset_y = (ch - ih * scale) / 2

        disp = self.current_image_L.convert("RGB").resize((max(1, int(iw * scale)), max(1, int(ih * scale))), Image.NEAREST)
        self.tk_preview = ImageTk.PhotoImage(disp)
        self.canvas.delete("all")
        self.canvas.create_rectangle(0, 0, cw, ch, fill="#d4bf98", outline="")
        self.canvas.create_image(self.offset_x, self.offset_y, anchor="nw", image=self.tk_preview)

        # Draw overlay if present (preview scaled)
        if self.overlay_img:
            ow, oh = self.overlay_img.size
            sw = max(1, int(ow * self.overlay_scale * self.scale))
            sh = max(1, int(oh * self.overlay_scale * self.scale))
            overlay_resized = self.overlay_img.resize((sw, sh), RESAMPLE_LANCZOS).convert("RGBA")
            self.overlaytk = ImageTk.PhotoImage(overlay_resized)
            ox = self.offset_x + int(self.overlay_offset[0] * self.scale)
            oy = self.offset_y + int(self.overlay_offset[1] * self.scale)
            self.canvas.create_image(ox, oy, anchor="nw", image=self.overlaytk)

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
        iw, ih = self.current_image_L.size
        x = max(0, min(iw - 1, x)); y = max(0, min(ih - 1, y))
        draw = ImageDraw.Draw(self.current_image_L)
        x0, y0 = self.last_x, self.last_y
        dx, dy = x - x0, y - y0
        dist = max(1, int((dx * dx + dy * dy) ** 0.5))
        for i in range(dist + 1):
            xi = int(round(x0 + dx * (i / dist))); yi = int(round(y0 + dy * (i / dist)))
            bbox = [xi - self.brush_size // 2, yi - self.brush_size // 2,
                    xi + (self.brush_size - 1) // 2, yi + (self.brush_size - 1) // 2]
            draw.ellipse(bbox, fill=self.brush_gray)
        self.last_x, self.last_y = x, y
        self.show_preview()

    def stop_draw(self, e):
        self.drawing = False
        self.last_x = self.last_y = None

    def save_back(self):
        if not self.cfg_path or not self.current_image_L:
            messagebox.showerror("Error", "Open a .cfg or .dat first")
            return

        # flip back vertically before saving (reverse of editor flip)
        img_to_save = self.current_image_L.transpose(Image.FLIP_TOP_BOTTOM)
        w, h = img_to_save.size
        pix = img_to_save.tobytes()
        payload = bytearray(struct.pack("<II", w, h) + pix + (self.footer or b""))

        try:
            self._write_stored_block_file(self.cfg_path, payload)
            self.log(f"Saved: {self.cfg_path}")
            messagebox.showinfo("Saved", f"Patched file:\n{self.cfg_path}")
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
                messagebox.showinfo("No files", "No files matched the selected seasons/maps.")
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
        if not IMAGE_ENABLED:
            messagebox.showerror("Missing dependency", "Pillow is required for overlays.\nRun: pip install Pillow")
            return
        startdir = self.last_dir if self.last_dir and os.path.isdir(self.last_dir) else os.getcwd()
        path = filedialog.askopenfilename(initialdir=startdir, filetypes=[("Image files", "*.png;*.jpg;*.jpeg"), ("All", "*.*")])
        if not path:
            return
        try:
            img = Image.open(path).convert("RGBA")
            self.overlay_img = img
            # center overlay on current fog image if available
            if self.current_image_L:
                iw, ih = self.current_image_L.size
                ow, oh = img.size
                self.overlay_scale = 1.0
                self.overlay_offset = (max(0, (iw - ow) // 2), max(0, (ih - oh) // 2))
            else:
                self.overlay_scale = 1.0
                self.overlay_offset = (0, 0)
            self.show_preview()
            self.log(f"Overlay loaded: {os.path.basename(path)} (drag with right mouse, scroll to zoom)")
        except Exception as e:
            messagebox.showerror("Overlay error", str(e))

    def clear_overlay(self):
        self.overlay_img = None
        self.show_preview()

    def apply_overlay(self):
        """
        Rasterizes the overlay onto the fog map (self.current_image_L).
        Any overlay pixel with alpha < 128 is ignored.
        Color mapping: nearest of 0->1, 128->128, 255->255
        """
        if not IMAGE_ENABLED:
            messagebox.showerror("Missing dependency", "Pillow is required for overlays.\nRun: pip install Pillow")
            return
        if not self.overlay_img or not self.current_image_L:
            return
        base = self.current_image_L.copy()
        bw, bh = base.size
        ow, oh = self.overlay_img.size
        new_w = max(1, int(ow * self.overlay_scale))
        new_h = max(1, int(oh * self.overlay_scale))
        overlay_resized = self.overlay_img.resize((new_w, new_h), RESAMPLE_LANCZOS)
        ox, oy = self.overlay_offset
        for y in range(overlay_resized.height):
            ty = y + oy
            if ty < 0 or ty >= bh:
                continue
            for x in range(overlay_resized.width):
                tx = x + ox
                if tx < 0 or tx >= bw:
                    continue
                r, g, b, a = overlay_resized.getpixel((x, y))
                if a < 128:
                    continue
                brightness = (r + g + b) // 3
                choices = [(1, abs(brightness - 0)), (128, abs(brightness - 128)), (255, abs(brightness - 255))]
                closest_val = min(choices, key=lambda v: v[1])[0]
                base.putpixel((tx, ty), closest_val)
        self.current_image_L = base
        self.overlay_img = None
        self.show_preview()
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
        self.show_preview()

    def stop_overlay_drag(self, e):
        self.dragging_overlay = False

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
        self.show_preview()

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

SAVE_PATH_FILE = os.path.join(os.path.expanduser("~"), ".snowrunner_save_path.txt")  # legacy
CONFIG_FILE = os.path.join(os.path.expanduser("~"), ".snowrunner_editor_config.json")
def load_config():
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, "r") as f:
                return json.load(f)
        except Exception:
            pass
    return {}
def save_config(data):
    try:
        with open(CONFIG_FILE, "w") as f:
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



def _create_autobackup(save_dir):
    """
    Copy all .cfg/.dat files from save_dir into backup/autobackup-<timestamp>[_full] preserving subpaths.
    Uses the same skip logic as make_backup_if_enabled (skips the backup folder itself).
    """
    try:
        if not save_dir or not os.path.isdir(save_dir):
            print("[Autosave] Save dir missing or invalid:", save_dir)
            return
        timestamp = datetime.now().strftime("autobackup-%d.%m.%Y %H-%M-%S")
        backup_dir = os.path.join(save_dir, "backup")
        os.makedirs(backup_dir, exist_ok=True)
        folder_name = timestamp + ("_full" if full_backup_var.get() else "")
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
    except Exception as e:
        print("[Autosave] Failed:", e, flush=True)


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

def _autosave_monitor_loop(get_save_path_callable, stop_event, poll_interval=60):
    """
    Monitor loop (one-minute cadence):
      - If autosave disabled -> sleep poll_interval between checks (so toggle is checked every minute).
      - If save folder invalid -> sleep poll_interval and re-check.
      - If game not running -> reset baseline and sleep poll_interval (only check again after interval).
      - If game running -> check folder mtimes every poll_interval seconds and create autobackup on change.
    """
    last_seen_mtimes = {}
    while not stop_event.is_set():
        try:
            # Respect the poll interval consistently
            if not autosave_var or not autosave_var.get():
                print(f"[Autosave] disabled - will re-check every {poll_interval}s.", flush=True)
                # Sleep full interval before checking again
                for _ in range(poll_interval):
                    if stop_event.is_set():
                        break
                    time.sleep(1)
                continue

            # Obtain full save file path from provided callable
            full_path = ""
            try:
                full_path = (get_save_path_callable() or "") if get_save_path_callable else ""
            except Exception as e:
                full_path = ""
                print(f"[Autosave] get_save_path_callable() raised: {e}", flush=True)

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
                for _ in range(poll_interval):
                    if stop_event.is_set():
                        break
                    time.sleep(1)
                continue

            # Check whether SnowRunner is running (once per interval)
            running = _is_snowrunner_running()
            print(f"[Autosave] process running: {running}", flush=True)

            # If not running -> reset baseline and wait one interval before checking again
            if not running:
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
                for _ in range(poll_interval):
                    if stop_event.is_set():
                        break
                    time.sleep(1)
                continue

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
                print(f"[Autosave] initialized baseline while running; next check in {poll_interval}s", flush=True)
                for _ in range(poll_interval):
                    if stop_event.is_set():
                        break
                    time.sleep(1)
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
                    _create_autobackup(save_dir)
                except Exception as e:
                    print("[Autosave] failed to create autobackup:", e, flush=True)
                last_seen_mtimes = current_mtimes
            else:
                print("[Autosave] no changes detected.", flush=True)

            # Wait exactly poll_interval seconds (split into 1s steps so stop_event wakes quickly)
            for _ in range(poll_interval):
                if stop_event.is_set():
                    break
                time.sleep(1)

        except Exception as e:
            print("[Autosave] monitor exception:", e, flush=True)
            # On error, sleep one interval before retrying
            for _ in range(poll_interval):
                if stop_event.is_set():
                    break
                time.sleep(1)

    print("[Autosave] monitor exiting", flush=True)


def start_autosave_monitor(get_save_path_callable):
    global _AUTOSAVE_THREAD, _AUTOSAVE_STOP_EVENT
    if _AUTOSAVE_THREAD and _AUTOSAVE_THREAD.is_alive():
        return
    _AUTOSAVE_STOP_EVENT = threading.Event()
    _AUTOSAVE_THREAD = threading.Thread(target=_autosave_monitor_loop, args=(get_save_path_callable, _AUTOSAVE_STOP_EVENT), daemon=True)
    _AUTOSAVE_THREAD.start()
    print("[Autosave] monitor started")


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


def make_backup_if_enabled(path):
    try:
        if not os.path.exists(path):
            print("[Backup] Skipped (path invalid).")
            return

        save_dir = os.path.dirname(path)
        timestamp = datetime.now().strftime("backup-%d.%m.%Y %H-%M-%S")
        backup_dir = os.path.join(save_dir, "backup")
        os.makedirs(backup_dir, exist_ok=True)

        # FULL BACKUP: copy all .cfg/.dat files (skip backup folder itself)
        if full_backup_var.get():
            full_dir = os.path.join(backup_dir, timestamp + "_full")
            os.makedirs(full_dir, exist_ok=True)
            for root, _, files in os.walk(save_dir):
                if os.path.abspath(root).startswith(os.path.abspath(backup_dir)):
                    continue  # skip backups of backups
                for file in files:
                    if file.lower().endswith((".cfg", ".dat")):
                        src_path = os.path.join(root, file)
                        rel_path = os.path.relpath(src_path, save_dir)
                        dst_path = os.path.join(full_dir, rel_path)
                        os.makedirs(os.path.dirname(dst_path), exist_ok=True)
                        shutil.copy2(src_path, dst_path)
            print(f"[Backup] Full backup created at: {full_dir}")

        # SINGLE BACKUP: only current save
        elif make_backup_var.get():
            single_dir = os.path.join(backup_dir, timestamp)
            os.makedirs(single_dir, exist_ok=True)
            backup_file_path = os.path.join(single_dir, os.path.basename(path))
            shutil.copy2(path, backup_file_path)
            print(f"[Backup] Backup created at: {backup_file_path}")
        else:
            print("[Backup] Skipped (disabled).")

        # --- Auto cleanup old backups ---
        try:
            max_backups = int(max_backups_var.get())
        except Exception:
            max_backups = 20
        try:
            max_autobackups = int(max_autobackups_var.get())
        except Exception:
            max_autobackups = 50

        # list contents in backup_dir, keep them sorted (oldest first because name contains date)
        all_entries = sorted(os.listdir(backup_dir))

        # normal backups: names starting with "backup-"
        normal_backups = [n for n in all_entries if n.startswith("backup-")]
        # autobackups: names starting with "autobackup-"
        auto_backups = [n for n in all_entries if n.startswith("autobackup-")]

        # delete oldest normal backups if over limit
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

        # delete oldest autobackups if over limit
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

    except Exception as e:
        print(f"[Backup Error] Failed to create backup: {e}")
        
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
    top = tk.Toplevel()
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
    messagebox.showinfo("Success", "Time updated.")

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
        messagebox.showinfo("Notice", "No matching missions found.")
        return

    new_block_str = json.dumps(obj_states, separators=(",", ":"))
    content = content[:block_start] + new_block_str + content[block_end:]
    with open(file_path, 'w', encoding='utf-8') as out_file:
        out_file.write(content)

    messagebox.showinfo("Success", "Selected missions marked complete.")

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
            messagebox.showinfo("Info", "No new contests were modified.")
        else:
            messagebox.showinfo("Success", f"{total_added} contests marked as completed.")

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
        messagebox.showinfo("Success", msg)
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
        messagebox.showinfo("Success", msg)
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
        messagebox.showinfo("Success", msg)
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
        messagebox.showinfo("Success", msg)
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
_MR_CHUNK_MAX = 80
_MR_ENGLISH_TARGET = 20000
_MR_DATA_SIGNATURE = "const _=JSON.parse('[{\"name\":\"RU_02_01_SERVHUB_GAS\""
_MR_DESC_SIGNATURE = "const t={UI_TRUCK_TYPE_HEAVY_DUTY:{t:0,b:{t:2,i:[{t:3}],s:\"HEAVY DUTY\""
_MR_DEBUG = False

# Language preference helpers (favor English when multiple locales exist)
_MR_ENGLISH_WORDS = {
    "the", "and", "to", "of", "in", "on", "for", "with", "from", "at", "by",
    "you", "your", "we", "our", "deliver", "find", "task", "contract", "contest",
    "lost", "trailer", "truck", "cargo", "repair", "bridge", "road", "house",
    "watchtower", "explore", "exploration", "mission"
}
_MR_DIACRITICS = set("ąćęłńóśźżĄĆĘŁŃÓŚŹŻàáâäãåæçèéêëìíîïñòóôöõøùúûüýÿßčďěňřšťůž")

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
    # Penalize ID-like strings
    if re.fullmatch(r"[A-Z0-9_]+", s):
        score -= 2.0
    return score

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
        import chardet  # type: ignore
        det = chardet.detect(bs)
        enc = det.get("encoding") or "utf-8"
        return bs.decode(enc, errors="replace")
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
        # Retry with certifi if SSL verification fails (common in frozen apps)
        if isinstance(e, ssl.SSLCertVerificationError) or "CERTIFICATE_VERIFY_FAILED" in str(e):
            try:
                import certifi  # type: ignore
                ctx = ssl.create_default_context(cafile=certifi.where())
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
            # Last resort: unverified TLS (best-effort to avoid total failure)
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

    # Probe all chunks lightly to find localization candidates.
    loc_candidates: List[str] = []
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
            loc_candidates.append(ch)
        # Limit probe list to a reasonable size
        if len(loc_candidates) >= 120 and len(data_candidates) >= 3:
            break

    # Download chunks; aim to capture enough English localization coverage.
    best_data_score = 0
    best_desc_score = 0
    english_entries = 0
    english_chunks = 0
    downloaded = 0
    ok = 0
    fail = 0

    # Prioritize localization + description candidates (likely contain strings)
    download_queue = desc_candidates + loc_candidates + [ch for ch in chunk_names if ch not in loc_candidates and ch not in desc_candidates]
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
                            sample_vals = list(parsed.values())[:120]
                            if sample_vals:
                                avg = sum(_mr_text_english_score(v) for v in sample_vals) / max(1, len(sample_vals))
                            else:
                                avg = -999.0
                            if avg >= 1.0:
                                english_chunks += 1
                                english_entries += len(parsed)
                                if _MR_DEBUG:
                                    _mr_log(f"expand_chunks: english_chunk={ch} entries={len(parsed)} avg={avg:.2f}")
                    except Exception:
                        pass
                if _MR_DEBUG and (ds >= 10 or cs >= 10):
                    _mr_log(f"expand_chunks: {ch} ds={ds} cs={cs}")
                if english_chunks >= 2 and english_entries >= _MR_ENGLISH_TARGET:
                    break
        except Exception:
            fail += 1
            continue

    # Re-select best roles from the expanded set
    if _MR_DEBUG:
        _mr_log(f"expand_chunks: downloaded ok={ok} fail={fail} english_chunks={english_chunks} english_entries={english_entries}")
    _mr_choose_best_js_roles()

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

def _mr_download_js_step() -> None:
    _MR_IN_MEM_FILES.clear()
    _MR_IN_MEM_META.clear()
    found = set()

    # Fast-path: try known endpoints directly (no Playwright needed)
    try:
        if _MR_DEBUG:
            _mr_log("download_js_step: trying direct endpoints")
        if _mr_try_direct_js_endpoints():
            if _MR_DEBUG:
                _mr_log("download_js_step: direct endpoints success")
            return
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
        if _MR_DEBUG:
            _mr_log(f"download_js_step: fallback html ok; mem_files={list(_MR_IN_MEM_FILES.keys())[:6]}")
        return
    except Exception:
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
    merged: Dict[str, str] = {}
    seen_files: Set[str] = set()

    def _merge_value(key: str, val: str) -> None:
        if key not in merged:
            merged[key] = val
            return
        old = merged.get(key, "")
        # Prefer the value that looks more English / less mojibake
        new_score = _mr_text_english_score(val)
        old_score = _mr_text_english_score(old)
        if new_score > old_score + 0.2:
            merged[key] = val

    def _add_from_text(txt: Optional[str]) -> None:
        if not txt:
            return
        # quick filter to avoid heavy parsing for unrelated files
        if ("s:\"") not in txt and ("s:'") not in txt and ("s :") not in txt:
            return
        parsed = _mr_parse_localization_from_desc_text(txt)
        if parsed:
            for k, v in parsed.items():
                _merge_value(k, v)

    # First try the chosen desc file (if any)
    if desc_js_file:
        try:
            txt = _mr_decode_bytes_to_text(_mr_get_file_bytes_or_mem(desc_js_file))
            _add_from_text(txt)
            if desc_js_file:
                seen_files.add(desc_js_file)
        except Exception:
            pass

    # Then scan other in-memory JS files likely to contain localization.
    for name, bs in list(_MR_IN_MEM_FILES.items()):
        if name in seen_files:
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
            # Skip chunks unlikely to contain localization
            continue
        _add_from_text(txt)
        seen_files.add(name)
        # stop early if we already have a large localization table
        if len(merged) >= 12000:
            break

    if _MR_DEBUG:
        try:
            _mr_log(f"collect_localization: files={len(seen_files)} entries={len(merged)}")
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
            return best.strip()

        def _collect_desc_text_blobs(current_desc: Optional[str]) -> List[str]:
            blobs: List[str] = []
            seen: Set[str] = set()
            if current_desc:
                try:
                    txt = _mr_decode_bytes_to_text(_mr_get_file_bytes_or_mem(current_desc))
                    if txt:
                        blobs.append(txt)
                        seen.add(current_desc)
                except Exception:
                    pass
            for name, bs in list(_MR_IN_MEM_FILES.items()):
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

def _load_csv_to_simpleframe(csv_path: str) -> Optional[SimpleFrame]:
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

    for path in candidates:
        df = _load_csv_to_simpleframe(path)
        if df is not None:
            return df

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
            self._tip_label = tk.Label(
                self._tip,
                text=tip,
                justify="left",
                background="#fefecd",
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

            info.bind("<Enter>", lambda e, it=item: self._show_tooltip_for_item(it, e))
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
                    self.load_data_thread(allow_build=False, preserve_changes=True, keep_existing_items=True)
                if built:
                    self._set_status_temp("Updated to latest data", 2000)
                else:
                    if self.items:
                        self._set_status_temp("Update failed — using cached data", 3000)
                    else:
                        self._set_status_temp("No data available (offline)", 3000)

            try:
                if hasattr(self.parent, "after"):
                    self.parent.after(0, finish)
                else:
                    finish()
            except Exception:
                finish()

        threading.Thread(target=worker, daemon=True).start()

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
            foreground="red",
            font=("TkDefaultFont", 9, "bold"),
            wraplength=500,
            justify="left"
        )
        warn_label.pack(side="left", padx=(0, 8))

        read_btn = tk.Button(
            bottom,
            text="Read warning",
            command=_show_objectives_warning,
            bg="#c62828",
            fg="white",
            activebackground="#b71c1c",
            relief="raised"
        )
        read_btn.pack(side="left", padx=(0, 8))

        # Status centered between left warning and right action buttons
        self.status_label = ttk.Label(
            bottom,
            textvariable=self.status_var,
            foreground="red",
            width=36,
            anchor="center",
            justify="center",
            font=("TkFixedFont", 9)
        )
        self.status_label.pack(side="left", padx=(8, 8), expand=True, fill="x")

        ttk.Button(bottom, text="Check filtered", command=self.check_filtered).pack(side="right", padx=4)
        ttk.Button(bottom, text="Uncheck filtered", command=self.uncheck_filtered).pack(side="right", padx=4)
        ttk.Button(bottom, text="Apply Changes", command=self.apply_changes_thread).pack(side="right")

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
                    self._show_tooltip_for_pool(pool_index, e)
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

    def _hide_tooltip(self):
        if self._tip is not None and tk.Toplevel.winfo_exists(self._tip):
            try:
                self._tip.withdraw()
            except Exception:
                pass

    # ---------------- data loading & filtering ----------------
    def load_data_thread(self, allow_build: bool = True, preserve_changes: bool = False, keep_existing_items: bool = False):
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
                display = g("displayname") or g("name") or key
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
                    "desc": g("descriptiontext") or "",
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
                self.session_locked = set(pre)
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
                self.selected_changes[iid] = False
                cnt += 1
        log(f"Uncheck filtered: marked {cnt} items (matching current filters)")
        self._refresh_visible_checkbox_vars()

    # ---------------- applying changes ----------------
    def apply_changes_thread(self):
        sp = self.tk_var_get(self.save_var)
        if not sp or not os.path.exists(sp):
            try:
                messagebox.showinfo("Info", "No valid save file provided; Apply Changes will only print actions to console.")
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

        if not changes:
            log("ApplyChanges: nothing to do")
            return

        log(f"ApplyChanges: batch-applying {len(changes)} changes")

        def worker():
            try:
                id_to_type = {it["id"]: (it.get("type") or "TASK").upper() for it in self.items}
                contest_changes = {k: v for k, v in changes.items() if id_to_type.get(k, "TASK") == "CONTEST"}
                mission_changes = {k: v for k, v in changes.items() if id_to_type.get(k, "TASK") != "CONTEST"}

                if not sp or not os.path.exists(sp):
                    log("[BATCH WRITE] no save file; printing planned changes:")
                    log(f"  contests: {len(contest_changes)} missions: {len(mission_changes)}")
                else:
                    with open(sp, "r", encoding="utf-8") as f:
                        content = f.read()
                        
                    # Use central folder-based backup instead of creating a .bak file
                    try:
                        if 'make_backup_if_enabled' in globals() and callable(make_backup_if_enabled):
                            make_backup_if_enabled(sp)
                    except Exception:
                        log("[BATCH WRITE] folder backup failed/ignored")


                    if mission_changes:
                        start = content.find('"objectiveStates"')
                        if start != -1:
                            try:
                                block, bs, be = extract_brace_block(content, start)
                                try:
                                    obj_states = json.loads(block)
                                except Exception:
                                    obj_states = {}
                                for kid, kval in mission_changes.items():
                                    cur = obj_states.get(kid)
                                    if not isinstance(cur, dict):
                                        cur = {}
                                    cur["isFinished"] = bool(kval)
                                    obj_states[kid] = cur
                                new_block = json.dumps(obj_states, indent=4, ensure_ascii=False)
                                content = content[:bs] + new_block + content[be:]
                            except Exception as e:
                                log(f"[BATCH WRITE] failed to patch objectiveStates: {e}")
                        else:
                            log("[BATCH WRITE] objectiveStates block not found; mission changes skipped")

                    if contest_changes:
                        try:
                            # collect global contestTimes entries that we add while patching CompleteSave blocks
                            global_contest_times_new = {}
                            added_total = 0
                            removed_total = 0

                            # Find all CompleteSave* occurrences and process each (use reversed so replacing doesn't break earlier offsets)
                            matches = list(re.finditer(r'"(CompleteSave\d*)"\s*:\s*{', content))
                            for match in reversed(matches):
                                save_key = match.group(1)
                                try:
                                    # extract the value block ({ ... }) after the key
                                    value_block_str, val_block_start, val_block_end = extract_brace_block(content, match.end() - 1)
                                    try:
                                        value_data = json.loads(value_block_str)
                                    except Exception:
                                        # skip malformed block
                                        continue

                                    # SslValue may be directly present or nested
                                    ssl = value_data.get("SslValue") or value_data.get(save_key, {}).get("SslValue") or {}

                                    # Normalize finishedObjs shape
                                    orig_finished = ssl.get("finishedObjs", [])
                                    finished_is_dict = isinstance(orig_finished, dict)
                                    if isinstance(orig_finished, dict):
                                        finished_set = set(orig_finished.keys())
                                    elif isinstance(orig_finished, list):
                                        finished_set = set(orig_finished)
                                    else:
                                        finished_set = set()

                                    # Ensure contestTimes is a dict
                                    contest_times = ssl.get("contestTimes", {})
                                    if not isinstance(contest_times, dict):
                                        contest_times = {}

                                    added_here = []
                                    removed_here = []

                                    # Apply the explicit contest_changes mapping (key -> bool)
                                    for k, v in contest_changes.items():
                                        if v:
                                            if k not in finished_set:
                                                finished_set.add(k)
                                                added_here.append(k)
                                            if k not in contest_times:
                                                contest_times[k] = 1
                                                global_contest_times_new[k] = 1
                                        else:
                                            if k in finished_set:
                                                finished_set.remove(k)
                                                removed_here.append(k)
                                            if k in contest_times:
                                                del contest_times[k]

                                    # If anything changed for this block, write it back
                                    if added_here or removed_here:
                                        if finished_is_dict:
                                            ssl["finishedObjs"] = {kk: True for kk in finished_set}
                                        else:
                                            ssl["finishedObjs"] = list(finished_set)

                                        ssl["contestTimes"] = contest_times

                                        viewed = ssl.get("viewedUnactivatedObjectives", [])
                                        if isinstance(viewed, list) and added_here:
                                            ssl["viewedUnactivatedObjectives"] = [v for v in viewed if v not in added_here]

                                        # Put SslValue back and replace the value block in content
                                        value_data["SslValue"] = ssl
                                        new_value_block_str = json.dumps(value_data, separators=(",", ":"))
                                        content = content[:val_block_start] + new_value_block_str + content[val_block_end:]

                                        added_total += len(added_here)
                                        removed_total += len(removed_here)

                                except Exception:
                                    # skip this CompleteSave block on any unexpected error
                                    continue

                            # Merge new contestTimes entries into any other contestTimes blocks in the file
                            if global_contest_times_new and 'update_all_contest_times_blocks' in globals():
                                try:
                                    content = update_all_contest_times_blocks(content, global_contest_times_new)
                                except Exception:
                                    # non-fatal: ignore if merge fails
                                    pass

                            log(f"[BATCH WRITE] Contests updated: +{added_total} / -{removed_total}")
                        except Exception as e:
                            log(f"[BATCH WRITE] Failed to patch CompleteSave blocks: {e}")

                    try:
                        with open(sp, "w", encoding="utf-8") as f:
                            f.write(content)
                        log(f"[BATCH WRITE] applied {len(changes)} changes to {sp}")
                    except Exception as e:
                        log(f"[BATCH WRITE] write failed: {e}")
            except Exception as ex:
                log(f"[BATCH WRITE][ERROR] {ex}")

            try:
                new_checked = _read_finished_contests(sp) | _read_finished_missions(sp) if sp and os.path.exists(sp) else set()
            except Exception:
                new_checked = set()
            self.original_checked = new_checked
            log(f"ApplyChanges: finished; original_checked now {len(self.original_checked)} items")

            self._refresh_visible_checkbox_vars()
            self._update_visible_rows()

            try:
                if changes:
                    messagebox.showinfo(
                        "Objectives+",
                        f"Successfully applied {len(changes)} change(s) to your save file."
                    )
                else:
                    messagebox.showinfo(
                        "Objectives+",
                        "No changes were applied (nothing selected)."
                    )
            except Exception as e:
                log(f"[BATCH WRITE][POPUP ERROR] {e}")

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
        self.session_locked = set(new_checked)
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
        Robust Backup Settings popup: uses globals if present, otherwise local fallbacks.
        Persists settings into CONFIG_FILE via save_config(). Ensures the global autosave_var
        is used (so toggles take effect immediately) and attaches a single trace to it.
        """
        # Determine parent safely
        try:
            parent = tab_backups.winfo_toplevel() if 'tab_backups' in globals() and hasattr(tab_backups, 'winfo_toplevel') else (tk._default_root if getattr(tk, "_default_root", None) is not None else None)
        except Exception:
            parent = None

        win = tk.Toplevel(parent) if parent else tk.Toplevel()
        win.title("Backup Settings")
        win.geometry("480x260")
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
        ttk.Checkbutton(frm, text="Enable Autosave (create autobackup when game autosaves)", variable=autosave_var).pack(anchor="w", pady=(0,8))
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

        # Buttons
        btn_row = ttk.Frame(frm)
        btn_row.pack(fill="x", pady=(14, 0))

        def _cfg_bool(v):
            if isinstance(v, bool):
                return v
            if isinstance(v, str):
                return v.strip().lower() in ("1", "true", "yes", "on")
            try:
                return bool(int(v))
            except Exception:
                return False

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
                    autosave_var.set(_cfg_bool(autosave_var.get()))
            except Exception:
                pass

            # Persist to config file as canonical source of truth
            try:
                new_cfg = load_config() or {}
            except Exception:
                new_cfg = {}
            try:
                new_cfg["make_backup"] = _cfg_bool(make_backup_var_local.get())
                new_cfg["full_backup"] = _cfg_bool(full_backup_var_local.get())
                new_cfg["max_backups"] = int(max_backups_var_local.get()) if str(max_backups_var_local.get()).isdigit() else int(new_cfg.get("max_backups", 20))
                new_cfg["max_autobackups"] = int(max_autobackups_var_local.get()) if str(max_autobackups_var_local.get()).isdigit() else int(new_cfg.get("max_autobackups", 50))
                new_cfg["autosave"] = _cfg_bool(autosave_var.get())
            except Exception:
                # fallbacks
                new_cfg.setdefault("max_backups", 20)
                new_cfg.setdefault("max_autobackups", 50)
            try:
                save_config(new_cfg)
            except Exception as e:
                print("[Backup Settings] Failed to save config:", e)

            messagebox.showinfo("Settings", "Backup settings saved.")
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

        # ---- autosave toggle wiring: remove old traces and attach a single one ----
        def _autosave_toggled(*a):
            """Start/stop the autosave monitor to match the checkbox state."""
            try:
                if autosave_var.get():
                    # pass callable returning full save-file path (monitor resolves folder)
                    start_autosave_monitor(lambda: save_path_var.get() if save_path_var is not None else "")
                else:
                    stop_autosave_monitor()
            except Exception as e:
                print("[Autosave] toggle error:", e)

        # --- remove any previous traces to avoid duplication (handle different trace_info shapes) ---
        try:
            traces = autosave_var.trace_info() or []
            for t in traces:
                try:
                    # trace_info entries vary by Tk version. Try common tuple shapes.
                    if isinstance(t, (list, tuple)):
                        if len(t) >= 2:
                            autosave_var.trace_vdelete(t[0], t[1])
                        else:
                            # older shape: single token
                            autosave_var.trace_vdelete("w", t[0])
                    else:
                        # fallback: attempt to remove write traces
                        autosave_var.trace_vdelete("w", t)
                except Exception:
                    # ignore failures to delete an individual trace
                    pass
        except Exception:
            pass

        # --- add trace (use trace_add when available) ---
        try:
            autosave_var.trace_add("write", _autosave_toggled)
        except Exception:
            try:
                autosave_var.trace("w", _autosave_toggled)
            except Exception:
                # if we can't attach the callback, still try to set monitor to current state below
                pass

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

    # --- treeview / table with additional columns and matching colours and size ---
    # Use exact hex colours you chose for Objectives+ so visuals line up
    even_bg = "#f8f8f8"
    odd_bg = "#e0e0e0"

    # Use a plain tk.Frame so the visible background behind the Treeview rows matches exactly
    tree_frame = tk.Frame(container, bg=even_bg)
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
                        background=even_bg,
                        fieldbackground=even_bg,
                        bordercolor=even_bg,
                        relief="flat",
                        borderwidth=0,
                        rowheight=30,       # MATCH Objectives+ row height
                        font=item_font)     # MATCH Objectives+ font size
        style.configure("Backups.Treeview.Heading",
                        background=even_bg,
                        relief="flat",
                        borderwidth=0,
                        font=heading_font)
        # selection appearance (tweak as desired)
        style.map("Backups.Treeview",
                  background=[("selected", "#cfe8ff")],
                  foreground=[("selected", "black")])
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

    def list_backup_folders():
        """Populate the backups treeview with folders from the backup directory.
        Rows get alternating 'even'/'odd' tags so the Treeview can display two-tone rows.
        """
        # clear existing rows
        tree.delete(*tree.get_children())

        backup_dir = _get_backup_dir()
        if not backup_dir or not os.path.exists(backup_dir):
            tree.insert("", "end", values=("No backups found (set save path or create backups first)", ""))
            recall_btn.config(state="disabled")
            return

        try:
            items = sorted(os.listdir(backup_dir), reverse=True)
            if not items:
                tree.insert("", "end", values=("No backups found", ""))
                recall_btn.config(state="disabled")
                return

            # Ensure alternating-row tags exist (some themes may ignore these but it's harmless)
            odd_bg = "#e0e0e0"
            even_bg = "#f8f8f8"
            try:
                tree.tag_configure("odd", background=odd_bg)
                tree.tag_configure("even", background=even_bg)
            except Exception:
                # some ttk themes or environments may not allow tag styling — ignore safely
                pass

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

            # operate in folder-only mode; ensure recall disabled until selection
            recall_btn.config(state="disabled")

        except Exception as e:
            tree.insert("", "end", values=(f"Error listing backups: {e}", ""))
            recall_btn.config(state="disabled")



    # list_files_in_backup removed: per-file recall and folder drilling disabled

    def _selected_item():
        sel = tree.selection()
        if not sel:
            return None
        vals = tree.item(sel[0], "values")
        if not vals:
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
        vals = tree.item(sel[0], "values")
        if not vals:
            recall_btn.config(state="disabled")
            return
        # Only folder-level rows are shown; enable recall when an item is selected
        recall_btn.config(state="normal")

    def on_refresh():
        # Always show folder-level listing; disable drilling into backup folders.
        list_backup_folders()
    

    def on_recall_selected():
        """
        If in folders mode: restore the entire selected backup folder into save folder.
        If in files mode: restore the selected CompleteSave file + matching companions (existing logic).
        """
        sel = _selected_item()
        if not sel:
            messagebox.showinfo("Recall", "No item selected.")
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
        messagebox.showinfo("Recall", f"Recalled {copied} files from backup '{folder_name}'.")
        # refresh listing
        list_backup_folders()

    # Bindings
    tree.bind("<Double-1>", on_tree_double_click)
    tree.bind("<<TreeviewSelect>>", on_tree_select)
    refresh_btn.config(command=on_refresh)
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
        if hasattr(save_path_var, "trace_info"):
            for t in (save_path_var.trace_info() or []):
                try:
                    save_path_var.trace_vdelete(t[0], t[1])
                except Exception:
                    pass
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
            v.load_data_thread(allow_build=False, preserve_changes=False, keep_existing_items=False)
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
            return messagebox.showinfo("Info", "No seasons or maps selected.")
        mark_discovered_contests_complete(path, selected_seasons, selected_maps)

    ttk.Button(tab, text="Mark Contests Complete", command=on_click).pack(pady=10)
    _add_check_all_checkbox(tab, all_check_vars)

    ttk.Label(
        tab,
        text="You must accepted (discovered) the contests for them to be marked as completed.",
        foreground="red",
        font=("TkDefaultFont", 9, "bold"),
        wraplength=400,
        justify="center"
    ).pack(pady=(5, 10))

    ttk.Label(
        tab,
        text="also completes all unfinished tasks found on the map",
        foreground="red",
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
        messagebox.showinfo("Success", msg)
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
    ttk.Style().configure("RedWarning.TLabel", foreground="red")
    ttk.Label(tab, text="Steam achievements will also be unlocked, but they can’t be removed with this editor. It’s meant mainly for the in-game Achievements tab.", wraplength=1000, justify="left", style="RedWarning.TLabel").pack(fill="x", padx=10, pady=(6, 8))

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
                messagebox.showinfo("Saved", "Achievements saved to file (rewrote file).")
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

            messagebox.showinfo("Saved", "Achievements saved to file.")
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
            messagebox.showinfo("Copied", "PROS link copied to clipboard.")
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

            messagebox.showinfo("Saved", "PROS entitlements saved successfully.")
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
            messagebox.showinfo("Saved", "Trials saved successfully.")
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
            messagebox.showinfo("Info", "No seasons or maps selected.")
            return
        find_and_modify_upgrades(path, selected_regions)

    ttk.Button(tab, text="Unlock Upgrades", command=on_apply).pack(pady=(10, 5))
    _add_check_all_checkbox(tab, all_check_vars)

    ttk.Label(tab, text="At least one upgrade must be marked or collected in-game for this to work.",
              foreground="red").pack(pady=(0, 2))
    ttk.Label(tab, text="If a new season is added, you may need to mark or collect one new upgrade.",
              foreground="red").pack()
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

        messagebox.showinfo("Success", "Stats and distances updated.")
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
            return messagebox.showinfo("Info", "No seasons or maps selected.")
        unlock_watchtowers(path, selected_regions)

    ttk.Button(tab, text="Unlock Watchtowers", command=on_apply).pack(pady=(10, 5))
    _add_check_all_checkbox(tab, all_check_vars)
    ttk.Label(tab, text="It will mark them as found but wont reveal the map use the Fog Tool for that.",
              foreground="red").pack()

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
            return messagebox.showinfo("Info", "No seasons or maps selected.")
        unlock_discoveries(path, selected_regions)

    ttk.Button(tab, text="Unlock Discoveries", command=on_apply).pack(pady=(10, 5))
    _add_check_all_checkbox(tab, all_check_vars)
    ttk.Label(tab, text="Sets discovered trucks to their max for selected regions but won't add them to garage.",
              foreground="red").pack()

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
            return messagebox.showinfo("Info", "No seasons or maps selected.")
        unlock_levels(path, selected_regions)

    ttk.Button(tab, text="Unlock Levels", command=on_apply).pack(pady=(10, 5))
    _add_check_all_checkbox(tab, all_check_vars)
    ttk.Label(
        tab,
        text="Lets you view regions you haven't visited yet.",
        foreground="red"
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
            return messagebox.showinfo("Info", "No seasons or maps selected.")
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
        foreground="red",
        wraplength=1000,
        justify="left"
    ).pack(pady=(6, 0), padx=12)

# ---------- FACTOR_RULE_DEFINITIONS (use your exact names/keys) ----------
FACTOR_RULE_DEFINITIONS = [
    ("Addon Selling Price", "addonSellingFactor", {"normal": 1.0, "10%": 0.1, "30%": 0.3, "50%": 0.5, "no refunds": 0}),
    ("Trailer selling price", "trailerSellingFactor", {"normal price": 1, "50%": 0.5, "30%": 0.3, "10%": 0.1, "cant be sold": -1}),
    ("Trailer availability", "trailerAvailability", {"default": 0, "all trailers available": 1}),
    ("truck switching price (Over Minimap)", "teleportationPrice", {"free": 0, "500": 500, "1000": 1000, "2000": 2000, "5000": 5000}),
    ("Tire availability", "tyreAvailability", {"default": 1, "all tires available": 0, "highway , allraod": 2, "highway, allroad, offroad": 3, "no mudtires": 4, "no chained tires": 5, "random per garage": 6}),
    ("truck availibility", "truckAvailability", {"default": 1, "all trucks are available from the start": 0, "5-15 trucks in each garage": 3, "store unlocks at rank 10": 2, "store unlocks at rank 20": 2, "store unlocks at rank 30": 2, "store is locked": 4}),
    ("truck pricing", "truckPricingFactor", {"default": 1, "free": 0, "2 times": 2, "4 times": 4, "6 times": 6}),
    ("Internal addon availability", "internalAddonAvailability", {"default": 0, "all internal addons unlocked": 1}),
    ("Fuel price", "fuelPriceFactor", {"normal price": 1, "free": 0, "2times": 2, "4times": 4, "6times": 6}),
    ("Garage repair price", "garageRepairePriceFactor", {"free": 0, "normal price": 1, "2times": 2, "4time": 4, "6times": 6}),
    ("Map marker style", "isMapMarkerAsInHardMode", {"default": False, "hard mode": True}),
    ("Truck selling price", "truckSellingFactor", {"normal price": 1, "50%": 0.5, "30%": 0.3, "10%": 0.1, "cant be sold": -1}),
    ("Vehicle addon pricing", "addonPricingFactor", {"default": 1, "free": 0, "2times": 2, "4times": 4, "6times": 6}),
    ("Game difficulty", "gameDifficultyMode", {"Normal": 0, "Hard": 1, "New Game+": 2}),
    ("Vehicle damage", "vehicleDamageFactor", {"default": 1, "no damage": 0, "2x": 2, "3x": 3, "5x": 5}),
    ("Vehicle storage slots", "vehicleStorageSlots", {"default": 0, "only 3": 3, "only 5": 5, "only 10": 10, "only scouts": -1}),
    ("Trailer pricing", "trailerPricingFactor", {"free": 0, "normal price": 1, "2x": 2, "4x": 4, "6x": 6}),
    ("External addon availability", "externalAddonAvailability", {"default": 0, "all addons unlocked": 1, "random 5": 2, "random 10": 3, "each garage random 10": 4}),
    ("Garage refuelling", "isGarageRefuelAvailable", {"True": True, "False": False}),
    ("Max contest attempts", "maxContestAttempts", {"default": -1, "1 attempt": 1, "3 attempt": 3, "5 attempt": 5}),
    ("Repair points required", "repairPointsRequiredFactor", {"default": 1, "2x less": 0.5, "2x": 2, "4x": 4, "6x": 6}),
    ("Repair points cost", "repairPointsCostFactor", {"free": 0, "default": 1, "2x": 2, "4x": 4, "6x": 6}),
    ("Region repair price", "regionRepaireMoneyFactor", {"free": 0, "default": 1, "2x": 2, "4x": 4, "6x": 6}),
    ("Recovery price", "recoveryPriceFactor", {"free": 0, "default": 1, "2x": 2, "4x": 4, "6x": 6}),
    ("Automatic cargo loading", "loadingPriceFactor", {"free": 0, "paid": 1, "2x": 2, "4x": 4, "6x": 6}),
    ("Region traveling price", "regionTravellingPriceFactor", {"free": 0, "default": 1, "2x": 2, "4x": 4, "6x": 6}),
    ("Task and contest payouts", "tasksAndContestsPayoutsFactor", {"normal": 1, "50%": 0.5, "150%": 1.5, "200%": 2, "300%": 3}),
    ("Contracts payouts", "contractsPayoutsFactor", {"normal": 1, "50%": 0.5, "150%": 1.5, "200%": 2, "300%": 3}),
]

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
        var = tk.StringVar(value=list(options.keys())[0])
        FACTOR_RULE_VARS.append((label, key, options, var))
        entries.append((label, key, options, var))

    COLS = 3
    for ci in range(COLS):
        center_frame.columnconfigure(ci, weight=1, uniform="rulecol")

    r = 0
    c = 0
    for label_text, key, opts, var in entries:
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
            # 1) run per-key savers on tmp
            for saver in rule_savers:
                try:
                    saver(tmp)
                except Exception as se:
                    print("rule saver error:", se)

            # 2) Set isHardMode based on gameDifficultyMode UI selection
            gd_val = None
            for lbl, ikey, opts, var in FACTOR_RULE_VARS:
                if ikey == "gameDifficultyMode":
                    sel_label = var.get()
                    gd_val = opts.get(sel_label, _choose_safe_default(opts))
                    break
            with open(tmp, "r", encoding="utf-8") as f:
                content = f.read()
            if gd_val is not None:
                try:
                    is_hard_bool = True if int(gd_val) == 1 else False
                except Exception:
                    is_hard_bool = False
                content = _set_key_in_text(content, "isHardMode", json.dumps(is_hard_bool))
                with open(tmp, "w", encoding="utf-8") as f:
                    f.write(content)

            # 3) Read back and sanitize
            with open(tmp, "r", encoding="utf-8") as f:
                text = f.read()

            # Ensure each rule key exists and not null (use defaults)
            for _, internal_key, options, _ in FACTOR_RULE_VARS:
                safe = _choose_safe_default(options)
                text = _ensure_key_with_default_text(text, internal_key, safe, treat_zero_as_missing=False)

            # Ensure autoloadPrice > 0 (treat 0 as missing)
            text = _ensure_key_with_default_text(text, "autoloadPrice", _DEFAULT_AUTOLOAD_PRICE, treat_zero_as_missing=True)

            # Ensure special arrays
            text = _ensure_array_key(text, "recoveryPrice", _DEFAULT_RECOVERY_PRICE)
            text = _ensure_array_key(text, "fullRepairPrice", _DEFAULT_FULL_REPAIR_PRICE)

            # settingsDictionaryForNGPScreen fix
            text = _ensure_settings_dictionary(text, _DEFAULT_SETTINGS_DICT)

            # deployPrice ensure object with Region/Map
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

            # 4) Compare & write
            with open(path, "r", encoding="utf-8") as f:
                original = f.read()

            if text == original:
                try:
                    os.remove(tmp)
                except Exception:
                    pass
                messagebox.showinfo("No changes", "No rule changes detected.")
                return

            _make_backup(path)
            with open(path, "w", encoding="utf-8") as f:
                f.write(text)
            try:
                os.remove(tmp)
            except Exception:
                pass
            messagebox.showinfo("Success", "Rules applied successfully.")
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
            for display_label, internal_key, options, var in FACTOR_RULE_VARS:
                m = re.search(rf'"{re.escape(internal_key)}"\s*:\s*(".*?"|\[[^\]]*\]|\{{[^}}]*\}}|[-]?\d+(\.\d+)?|true|false|null)', content, flags=re.IGNORECASE)
                if not m:
                    continue
                raw = m.group(1).strip()
                # quoted values
                if raw.startswith('"') and raw.endswith('"'):
                    rawv = raw[1:-1]
                else:
                    rawv = raw
                # ignore arrays/objects for comboboxes
                if rawv.startswith('[') or rawv.startswith('{'):
                    continue
                matched = False
                for lab, val in options.items():
                    if str(val) == str(rawv):
                        var.set(lab)
                        matched = True
                        break
                if not matched and rawv in options:
                    var.set(rawv)
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
    ttk.Frame(bottom).pack(side="left", expand=True)
    ttk.Button(bottom, text="Save Rules to Save File", command=apply_all_rules, width=30).pack(side="left")
    ttk.Frame(bottom).pack(side="left", expand=True)

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
    if requests is None:
        if debug:
            print("[UpdateCheck] requests not installed; skipping update check.")
        return

    def log(msg):
        if debug:
            print(f"[UpdateCheck] {msg}")

    def worker():
        try:
            log("Trying to reach GitHub API...")
            r = requests.get(GITHUB_RELEASES_API, timeout=5)
            if r.status_code != 200:
                log(f"GitHub API returned {r.status_code}, skipping.")
                return
            log("Internet connection OK ✅")

            releases = r.json()
            if not isinstance(releases, list) or not releases:
                log("No releases found, aborting.")
                return

            # collect all tags
            tags = [rel.get("tag_name", "").lstrip("v") for rel in releases if rel.get("tag_name")]
            log(f"Found tags: {tags}")

            # pick the raw tag with the highest numeric part
            tags_sorted = sorted(tags, key=lambda t: normalize_version(t), reverse=True)
            latest_raw = tags_sorted[0]
            latest_num = normalize_version(latest_raw)

            log(f"Latest tag after normalization: raw={latest_raw}, numeric={latest_num}")

            if not latest_raw:
                log("No valid tag found, aborting.")
                return

            current_num = normalize_version(APP_VERSION)
            log(f"Normalized versions → current: {current_num}, latest: {latest_num}")

            if latest_num > current_num:
                log("Newer version detected → scheduling popup.")
                try:
                    globals()["_UPDATE_STATUS"] = "update"
                except Exception:
                    pass

                def popup():
                    top = tk.Toplevel(root)
                    top.title("Update Available")
                    top.geometry("380x200")

                    # ✅ Cleaner label: no extra newlines or text
                    ttk.Label(
                        top,
                        text=f"A new version is available!\n\n"
                             f"Current: {current_num}\nLatest: {latest_num}",
                        justify="center",
                        wraplength=340
                    ).pack(pady=10)

                    def open_page():
                        webbrowser.open(GITHUB_RELEASES_PAGE)

                    def copy_link():
                        root.clipboard_clear()
                        root.clipboard_append(GITHUB_RELEASES_PAGE)
                        root.update()
                        messagebox.showinfo("Copied", "Releases page link copied to clipboard.")

                    btn_frame = ttk.Frame(top)
                    btn_frame.pack(pady=10)

                    ttk.Button(btn_frame, text="Open Page", command=open_page).pack(side="left", padx=5)
                    ttk.Button(btn_frame, text="Copy Link", command=copy_link).pack(side="left", padx=5)

                # show popup in main thread
                root.after(0, popup)
                # update footer version label if present
                try:
                    if "_VERSION_FOOTER_LABEL" in globals() and globals()["_VERSION_FOOTER_LABEL"] is not None:
                        globals()["_VERSION_FOOTER_LABEL"].config(
                            text=f"Version: {APP_VERSION} (update available)"
                        )
                except Exception:
                    pass
            elif latest_num < current_num:
                log("Current version ahead of latest → dev build.")
                try:
                    globals()["_UPDATE_STATUS"] = "dev"
                except Exception:
                    pass
                try:
                    if "_VERSION_FOOTER_LABEL" in globals() and globals()["_VERSION_FOOTER_LABEL"] is not None:
                        globals()["_VERSION_FOOTER_LABEL"].config(
                            text=f"Version: {APP_VERSION} (dev build)"
                        )
                except Exception:
                    pass
            else:
                log("No update available.")
                try:
                    globals()["_UPDATE_STATUS"] = "none"
                except Exception:
                    pass
                try:
                    if "_VERSION_FOOTER_LABEL" in globals() and globals()["_VERSION_FOOTER_LABEL"] is not None:
                        globals()["_VERSION_FOOTER_LABEL"].config(
                            text=f"Version: {APP_VERSION}"
                        )
                except Exception:
                    pass

        except Exception as e:
            log(f"Update check failed: {e}")

    # run worker in background thread
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
    
    # Check for optional dependencies
    if Image is None:
        missing.append(
            "Pillow: Install with 'pip install Pillow' (image loading/overlay features will be disabled)"
        )
    
    if requests is None:
        missing.append(
            "requests: Install with 'pip install requests' (some network features will be disabled)"
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
    # Check for required/optional dependencies first
    check_dependencies()

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
    global tyre_var, delete_path_on_close_var, dont_remember_path_var, autosave_var
    
    # Create root window first
    root = tk.Tk()
    root.title("SnowRunner Editor")
    # Hide during initial layout to avoid size jump on startup
    try:
        root.withdraw()
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
    max_autobackups_var = tk.StringVar(root, value="50")
    # Initialize additional variables
    difficulty_var = tk.StringVar(root)
    truck_avail_var = tk.StringVar(root)
    truck_price_var = tk.StringVar(root)
    addon_avail_var = tk.StringVar(root)
    addon_amount_var = tk.StringVar(root)
    time_day_var = tk.StringVar(root)
    time_night_var = tk.StringVar(root)
    garage_refuel_var = tk.BooleanVar(root)

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

    check_for_updates_background(root, debug=True)

    # Load config after variables exist
    config = load_config()
    delete_path_on_close_var.set(config.get("delete_path_on_close", False))
    dont_remember_path_var.set(config.get("dont_remember_path", False))

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
            dummy = tk._default_root or tk.Toplevel()
            dummy.after(_VERSION_CHECK_DELAY_MS, _delayed_version_check)
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

    # TAB: Save File (inline UI built below)
    tab_control.add(tab_file, text='Save File')

    # TAB: Backups (create_backups_tab)
    tab_backups = ttk.Frame(tab_control)
    tab_control.add(tab_backups, text='Backups')
    create_backups_tab(tab_backups, save_path_var)

    # TAB: Money & Rank (inline UI built below)
    tab_control.add(tab_money, text='Money & Rank')

    # TAB: Missions (inline UI built below)
    tab_control.add(tab_missions, text='Missions')

    # TAB: Contests (create_contest_tab)
    tab_contests = ttk.Frame(tab_control)
    tab_control.add(tab_contests, text='Contests')
    create_contest_tab(tab_contests, save_path_var)

    # TAB: Objectives+ (create_objectives_tab)
    tab_objectives = ttk.Frame(tab_control)
    tab_control.add(tab_objectives, text='Objectives+')
    create_objectives_tab(tab_objectives, save_path_var)

    # TAB: Trials (create_trials_tab)
    tab_trials = ttk.Frame(tab_control)
    tab_control.add(tab_trials, text='Trials')
    create_trials_tab(tab_trials, save_path_var, plugin_loaders)

    # TAB: Achievements (create_achievements_tab)
    tab_achievements = ttk.Frame(tab_control)
    tab_control.add(tab_achievements, text='Achievements')
    create_achievements_tab(tab_achievements, save_path_var, plugin_loaders)

    # TAB: PROS (create_pros_tab)
    tab_pros = ttk.Frame(tab_control)
    tab_control.add(tab_pros, text='PROS')
    create_pros_tab(tab_pros, save_path_var, plugin_loaders)

    # TAB: Upgrades (create_upgrades_tab)
    tab_upgrades = ttk.Frame(tab_control)
    tab_control.add(tab_upgrades, text='Upgrades')
    create_upgrades_tab(tab_upgrades, save_path_var)

    # TAB: Watchtowers (create_watchtowers_tab)
    tab_watchtowers = ttk.Frame(tab_control)
    tab_control.add(tab_watchtowers, text="Watchtowers")
    create_watchtowers_tab(tab_watchtowers, save_path_var)

    # TAB: Discoveries (create_discoveries_tab)
    tab_discoveries = ttk.Frame(tab_control)
    tab_control.add(tab_discoveries, text="Discoveries")
    create_discoveries_tab(tab_discoveries, save_path_var)

    # TAB: Levels (create_levels_tab)
    tab_levels = ttk.Frame(tab_control)
    tab_control.add(tab_levels, text="Levels")
    create_levels_tab(tab_levels, save_path_var)

    # TAB: Garages (create_garages_tab)
    tab_garages = ttk.Frame(tab_control)
    tab_control.add(tab_garages, text="Garages")
    create_garages_tab(tab_garages, save_path_var)


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
            start_autosave_monitor(lambda: save_path_var.get() if save_path_var is not None else "")
    except Exception:
        pass


    # TAB: Rules (create_rules_tab)
    try:
        create_rules_tab(tab_rules, save_path_var)
    except Exception as e:
        ttk.Label(tab_rules, text=f"Failed to initialize Rules tab:\n{e}", foreground="red", wraplength=600, justify="center").pack(fill="both", expand=True, padx=10, pady=10)
    # End TAB: Rules

    tab_control.add(tab_rules, text='Rules')

    # TAB: Time (inline UI built below)
    tab_control.add(tab_time, text='Time')

    # TAB: Game Stats (create_game_stats_tab)
    tab_stats = ttk.Frame(tab_control)
    tab_control.add(tab_stats, text="Game Stats")
    create_game_stats_tab(tab_stats, save_path_var, plugin_loaders)

    # TAB: Settings (inline UI built below)
    tab_settings = ttk.Frame(tab_control)
    tab_control.add(tab_settings, text='Settings')

    # TAB: Fog Tool (FogToolFrame)
    tab_fog = ttk.Frame(tab_control)

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
        except Exception as e:
            ttk.Label(
                tab_fog,
                text=f"⚠️ Fog Tool failed to load:\n{e}",
                foreground="red",
                anchor="center",
                justify="center"
            ).pack(expand=True, fill="both", padx=20, pady=20)
    else:
        ttk.Label(
            tab_fog,
            text="⚠️ Fog Tool not available (fog_tool.py missing)",
            foreground="red",
            anchor="center",
            justify="center"
        ).pack(expand=True, fill="both", padx=20, pady=20)

    tab_control.add(tab_fog, text="Fog Tool")
    # End TAB: Fog Tool

    tab_control.pack(expand=1, fill='both')
    # End NOTEBOOK + TAB REGISTRY
    # ensure Settings is last
    try:
        tab_control.forget(tab_settings)   # remove if already added
    except Exception:
        pass
    tab_control.add(tab_settings, text='Settings')


    # Track tab changes and save selected tab index
    def on_tab_change(event):
        config = load_config()
        config["last_tab"] = tab_control.index(tab_control.select())
        save_config(config)
    tab_control.bind("<<NotebookTabChanged>>", on_tab_change)

    # Restore last selected tab if available
    config = load_config()
    last_tab_index = config.get("last_tab", 0)
    try:
        tab_control.select(last_tab_index)
    except Exception:
        pass


    # -------------------------------------------------------------------------
    # TAB UI: Settings (tab_settings)
    # -------------------------------------------------------------------------
    ttk.Checkbutton(tab_settings, text="Don't remember save file path", variable=dont_remember_path_var).pack(pady=(10, 0))
    ttk.Checkbutton(tab_settings, text="Delete saved path on close", variable=delete_path_on_close_var).pack(pady=(5, 10))
    def save_settings_silent():
        config = load_config()
        config["dont_remember_path"] = dont_remember_path_var.get()
        config["delete_path_on_close"] = delete_path_on_close_var.get()
        config["make_backup"] = make_backup_var.get()
        config["full_backup"] = full_backup_var.get()
        config["max_backups"] = int(max_backups_var.get())
        config["max_autobackups"] = int(max_autobackups_var.get())
        config["autosave"] = bool(autosave_var.get() if autosave_var is not None else False)
        save_config(config)

    def save_settings():
        save_settings_silent()
        messagebox.showinfo("Settings", "Settings have been saved.")

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
                messagebox.showinfo("Success", f"Shortcut created:\n{shortcut_path}")
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
                        messagebox.showinfo("Success", f"Alias created on Desktop:\n{alias_path}")
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
                messagebox.showinfo("Success", f"Launcher created:\n{command_path}")
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
            messagebox.showinfo("Success", f"Shortcut created:\n{desktop_entry_path}")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to create shortcut:\n{e}")

    ttk.Button(tab_settings, text="Make Desktop Shortcut", command=create_desktop_shortcut).pack(pady=(5, 10))

    def make_backup_now():
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")
        try:
            make_backup_if_enabled(path)
            messagebox.showinfo("Backup", f"Backup created")
        except Exception as e:
            messagebox.showerror("Error", f"Backup failed:\n{e}")

    ttk.Button(tab_settings, text="Make a Backup", command=make_backup_now).pack(pady=(5, 10))

    def manual_update_check():
        if requests is None:
            messagebox.showwarning(
                "Missing dependency",
                "requests is required to check for updates.\nRun: pip install requests"
            )
            return
        check_for_updates_background(root, debug=True)

    ttk.Button(tab_settings, text="Check for Update", command=manual_update_check).pack(pady=(5, 10))

    # Separator and embedded Minesweeper
    if MINESWEEPER_AVAILABLE:
        ttk.Separator(tab_settings, orient='horizontal').pack(fill='x', pady=(10, 5))
        ttk.Label(tab_settings, text="Minesweeper", font=("TkDefaultFont", 11, "bold")).pack(pady=(0, 5))
    
        minesweeper_frame = tk.Frame(tab_settings)
        minesweeper_frame.pack(pady=5)
        MinesweeperApp(minesweeper_frame)

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
        messagebox.showinfo("Saved", f"Saved current path into Saved Path {slot_idx}.")

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
            return messagebox.showinfo("Not found", f"No CompleteSave*.cfg/.dat files found in:\n{folder}")

        if len(candidates) == 1:
            _apply_path_selection(candidates[0][1])
            return

        # multiple -> popup with only valid numbered buttons
        win = tk.Toplevel()
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
            return messagebox.showinfo("Steam not found", "Could not locate Steam save folder automatically.")

        if len(candidates) == 1:
            _choose_complete_save_in_folder(candidates[0])
        else:
            win = tk.Toplevel()
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
            return messagebox.showinfo("Epic not found", f"Could not locate Epic storage folder:\n{base}")
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
            return messagebox.showinfo("Epic", "No SnowRunner save folders with CompleteSave files found in storage.")

        if len(found_folders) == 1:
            _choose_complete_save_in_folder(found_folders[0])
        else:
            win = tk.Toplevel()
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
            return messagebox.showinfo("Empty", f"No saved path stored for slot {slot_idx}.")
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

    ttk.Button(center_frame, text="Load Path 1", width=12, command=lambda: _load_saved_path(1)).pack(side="left", padx=(0,6))
    ttk.Button(center_frame, text="Load Path 2", width=12, command=lambda: _load_saved_path(2)).pack(side="left", padx=(0,12))
    ttk.Button(center_frame, text="Browse...", command=browse_file).pack(side="left")

    # Help / hints below (single label)
    ttk.Label(
        tab_file,
        text=(
            "⚠️ It's recommended to create a backup of your save file before editing even tho the checkbox above should do them.\n\n"
            "Instructions for loading:\n"
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
        foreground="black"
    ).pack(pady=(6, 10))
    # ---------- end replacement block ----------

    ttk.Label(
        tab_file,
        text="⚠️ SnowRunner must be closed before editing the save file. Changes made while the game is running may be lost or cause issues.",
        wraplength=500,
        justify="center",
        foreground="red",
        font=("TkDefaultFont", 9, "bold")
    ).pack(pady=(5, 10))

    # Footer text pinned to bottom center of the Save File tab
    footer_frame = ttk.Frame(tab_file)
    footer_frame.place(relx=0.5, rely=1.0, anchor="s", y=-10)

    ttk.Label(
        footer_frame,
        text="Made with hatred for bugs by: MrBoxik",
        foreground="black",
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
        foreground="black",
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
            messagebox.showinfo("Clamped", f"Entered value {orig} is outside allowed range.\n"
                                           f"Saved value was changed to {money_val}.\n"
                                           f"Value must be between ({MONEY_MIN} and {MONEY_MAX}).")
        else:
            messagebox.showinfo("Success", f"Money updated to {money_val}.")


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

            messagebox.showinfo("Success", f"Experience updated to {val}.")
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

            messagebox.showinfo("Success", f"Rank set to {rank_val} (experience set to {xp_val}).")
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
            messagebox.showinfo("Success", "Money & Rank updated.")
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
            messagebox.showinfo("Info", "No seasons or maps selected.")
            return
        complete_seasons_and_maps(save_path_var.get(), selected_seasons, selected_maps)

    ttk.Button(tab_missions, text="Complete Selected Missions", command=run_complete).pack(pady=10)
    _add_check_all_checkbox(tab_missions, all_check_vars)

    # Disclaimer below the complete button
    ttk.Label(
        tab_missions,
        text="You must accept the task or mission in the game before it can be completed",
        foreground="red",
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
    ttk.Label(tab_time, text="⚠️ Time settings only apply in New Game+ mode.", foreground="red", font=("TkDefaultFont", 9, "bold")).pack(pady=(5, 10))
    ttk.Label(tab_time, text="⚠️ To use custom sliders, select 'Custom' from the Time Presets.", foreground="red", font=("TkDefaultFont", 9, "bold")).pack(pady=(5, 10))




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
time will freeze at the transition (day to night or night to day).""", wraplength=400, justify="left", foreground="darkblue").pack(pady=(10, 20))

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

    # --- Auto-size window to show all tabs and full Rules tab content ---
    def _fit_window_to_tabs_and_rules():
        try:
            root.update_idletasks()
            # Compute actual tab header width from the last tab bbox (more accurate)
            header_width = 0
            try:
                tab_count = tab_control.index("end")
            except Exception:
                tab_count = 0
            if tab_count > 0:
                try:
                    x, y, w, h = tab_control.bbox(tab_count - 1)
                    header_width = x + w
                except Exception:
                    header_width = 0

            if not header_width:
                # Fallback: text width estimate with smaller padding
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

            target_w = int(max(header_width, nb_req_w, rules_req_w) + 16)
            target_h = int(max(nb_req_h, rules_req_h) + 60)
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

    root.mainloop()

# -----------------------------------------------------------------------------
# END SECTION: Dependency Checks + App Launch
# -----------------------------------------------------------------------------

FogToolFrame = FogToolApp
if __name__ == "__main__":
    check_dependencies()  # Run dependency checks before UI
    launch_gui()
