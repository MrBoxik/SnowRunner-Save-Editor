import os
import sys
import platform
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, PhotoImage

make_backup_var = None

import os, sys, platform
if platform.system() == "Windows":
    import ctypes
    from ctypes import wintypes
    
try:
    from fog_tool import FogToolFrame
except ImportError:
    FogToolFrame = None

wintypes.HRESULT = ctypes.c_long  # Fix missing HRESULT

import sys, os, platform, ctypes
from ctypes import wintypes

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

    def guid_from_str(guid_str):
        import uuid
        u = uuid.UUID(guid_str)
        return GUID(
            u.time_low,
            u.time_mid,
            u.time_hi_version,
            (ctypes.c_ubyte * 8).from_buffer_copy(u.bytes[8:])
        )

    SHGetKnownFolderPath = ctypes.windll.shell32.SHGetKnownFolderPath
    SHGetKnownFolderPath.argtypes = [ctypes.POINTER(GUID), wintypes.DWORD, wintypes.HANDLE, ctypes.POINTER(ctypes.c_wchar_p)]
    SHGetKnownFolderPath.restype = wintypes.HRESULT

    path_ptr = ctypes.c_wchar_p()
    desktop_guid = guid_from_str('{B4BFCC3A-DB2C-424C-B029-7FE99A87C641}')
    result = SHGetKnownFolderPath(ctypes.byref(desktop_guid), 0, 0, ctypes.byref(path_ptr))
    if result != 0:
        raise ctypes.WinError(result)
    return path_ptr.value


import ctypes
from ctypes import wintypes

import platform
import sys
import os

def resource_path(relative_path):
    """ Get absolute path to resource, works for dev and for PyInstaller """
    try:
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)
dropdown_widgets = {}
import json
import tkinter as tk
try:
    from minesweeper_patched import MinesweeperApp
    MINESWEEPER_AVAILABLE = True
except ImportError:
    MINESWEEPER_AVAILABLE = False  # patched to work in embedded frame

from tkinter import filedialog, messagebox, simpledialog, ttk
import os
import re
import importlib.util
import glob

def set_var(var, val_map, actual_val):
    for label, value in val_map.items():
        if value == actual_val:
            var.set(label)
            return
    if actual_val is not None:
        var.set(f"[unknown: {actual_val}]")


SAVE_PATH_FILE = os.path.join(os.path.expanduser("~"), ".snowrunner_save_path.txt")

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


RANK_XP_REQUIREMENTS = {
    1: 0, 2: 700, 3: 1700, 4: 2900, 5: 4100, 6: 5400, 7: 6900,
    8: 8500, 9: 10100, 10: 11800, 11: 13700, 12: 15700, 13: 17800,
    14: 20100, 15: 22500, 16: 25000, 17: 27500, 18: 30100,
    19: 32700, 20: 35500, 21: 38300, 22: 41300, 23: 44300,
    24: 47500, 25: 50700, 26: 54100, 27: 57500, 28: 61100,
    29: 64900, 30: 69000
}

# --- Global Factor Rules Config ---
external_addon_map = {
    "default": (0, 0),
    "all addons unlocked": (1, 0),
    "random 5": (2, 5),
    "random 10": (3, 10),
    "each garage random 10": (4, 10)
}
FACTOR_RULE_DEFINITIONS = [
    ("Region Repair Price", "regionRepaireMoneyFactor", {"default": 1, "2x outside home region": 2, "3x outside home region": 3, "4x outside home region": 4}),
    ("Recovery Price", "recoveryPriceFactor", {"free": 0, "paid": 1, "2x": 2, "4x": 4, "6x": 6}),
    ("Automatic Cargo Loading Price", "loadingPriceFactor", {"free": 0, "paid": 1, "2x": 2, "4x": 4, "6x": 6}),
    ("Region Travelling Price", "regionTravellingPriceFactor", {"free": 0, "paid": 1, "2x": 2, "4x": 4, "6x": 6}),
    ("Tasks and Contests Payouts", "tasksAndContestsPayoutsFactor", {"normal": 1, "50%": 0.5, "150%": 1.5, "200%": 2.0, "300%": 3.0}),
    ("Contracts Payouts", "contractsPayoutsFactor", {"normal": 1, "50%": 0.5, "150%": 1.5, "200%": 2.0, "300%": 3.0})
]
FACTOR_RULE_VARS = []


import shutil
from datetime import datetime

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
                    if file.endswith((".cfg", ".dat")):
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
            max_backups = 0

        if max_backups > 0:
            all_backups = sorted(os.listdir(backup_dir))
            if len(all_backups) > max_backups:
                to_delete = all_backups[:len(all_backups) - max_backups]
                for old in to_delete:
                    old_path = os.path.join(backup_dir, old)
                    if os.path.isdir(old_path):
                        shutil.rmtree(old_path)
                    else:
                        os.remove(old_path)
                print(f"[Cleanup] Removed {len(to_delete)} old backup(s).")

    except Exception as e:
        print(f"[Backup Error] Failed to create backup: {e}")

        
def recall_backup(path):
    try:
        save_dir = os.path.dirname(path)
        backup_dir = os.path.join(save_dir, "backup")
        if not os.path.exists(backup_dir):
            messagebox.showerror("Recall Backup", "No backups found.")
            return

        backups = sorted(os.listdir(backup_dir), reverse=True)
        if not backups:
            messagebox.showerror("Recall Backup", "No backups available.")
            return

        # Create popup window
        recall_win = tk.Toplevel()
        recall_win.title("Recall Backup")
        recall_win.geometry("400x300")

        # Scrollable frame
        canvas = tk.Canvas(recall_win)
        scrollbar = ttk.Scrollbar(recall_win, orient="vertical", command=canvas.yview)
        scroll_frame = ttk.Frame(canvas)

        scroll_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )

        canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)

        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        # Create one button per backup
        def do_restore(choice):
            chosen_backup = os.path.join(backup_dir, choice)
            for root, _, files in os.walk(chosen_backup):
                for file in files:
                    src_path = os.path.join(root, file)
                    rel_path = os.path.relpath(src_path, chosen_backup)
                    dst_path = os.path.join(save_dir, rel_path)
                    os.makedirs(os.path.dirname(dst_path), exist_ok=True)
                    shutil.copy2(src_path, dst_path)

            messagebox.showinfo("Recall Backup", f"Backup {choice} restored successfully!")
            recall_win.destroy()

        for backup in backups:
            ttk.Button(scroll_frame, text=backup, command=lambda b=backup: do_restore(b)).pack(fill="x", pady=2, padx=5)

    except Exception as e:
        messagebox.showerror("Recall Backup", f"Failed to recall backup: {e}")



def load_last_path():
    if os.path.exists(SAVE_PATH_FILE):
        with open(SAVE_PATH_FILE, "r") as f:
            return f.read().strip()
    return ""

def save_path(path):
    if "dont_remember_path_var" in globals() and dont_remember_path_var.get():
        return
    with open(SAVE_PATH_FILE, "w") as f:
        f.write(path)

def get_file_info(content):
    truck_price = int(re.search(r'"truckPricingFactor"\s*:\s*(\d+)', content).group(1)) if re.search(r'"truckPricingFactor"\s*:\s*(\d+)', content) else 1
    def search_num(key):
        match = re.search(rf'"{key}"\s*:\s*(-?\d+(\.\d+)?(e[-+]?\d+)?)', content)
        return float(match.group(1)) if match else None
    money = int(re.search(r'"money"\s*:\s*(\d+)', content).group(1)) if re.search(r'"money"\s*:\s*(\d+)', content) else 0
    rank = int(re.search(r'"rank"\s*:\s*(\d+)', content).group(1)) if re.search(r'"rank"\s*:\s*(\d+)', content) else 0
    difficulty = int(re.search(r'"gameDifficultyMode"\s*:\s*(\d+)', content).group(1)) if re.search(r'"gameDifficultyMode"\s*:\s*(\d+)', content) else 0
    truck_avail = int(re.search(r'"truckAvailability"\s*:\s*(\d+)', content).group(1)) if re.search(r'"truckAvailability"\s*:\s*(\d+)', content) else 0
    skip_time = 'true' in re.search(r'"isAbleToSkipTime"\s*:\s*(true|false)', content).group(1) if re.search(r'"isAbleToSkipTime"\s*:\s*(true|false)', content) else False
    day = search_num("timeSettingsDay")
    night = search_num("timeSettingsNight")
    return money, rank, difficulty, truck_avail, skip_time, day, night, truck_price

def modify_rules(file_path, difficulty, truck_avail, truck_price, internal_avail, internal_amount=None):
    with open(file_path, 'r', encoding='utf-8') as file:
        content = file.read()

    is_hard_mode = "true" if difficulty == 1 else "false"
    content = re.sub(r'("gameDifficultyMode"\s*:\s*)\d+', lambda m: m.group(1) + str(difficulty), content)
    content = re.sub(r'("isHardMode"\s*:\s*)(true|false)', lambda m: m.group(1) + is_hard_mode, content)
    content = re.sub(r'("truckAvailability"\s*:\s*)\d+', lambda m: m.group(1) + str(truck_avail), content)
    content = re.sub(r'("truckPricingFactor"\s*:\s*)\d+', lambda m: m.group(1) + str(truck_price), content)

    # Apply internalAddonAvailability
    content = re.sub(r'("internalAddonAvailability"\s*:\s*)\d+', lambda m: m.group(1) + str(internal_avail), content)

    # Apply internalAddonAmount logic
    if internal_avail == 2 and internal_amount is not None:
        content = re.sub(r'("internalAddonAmount"\s*:\s*)\d+', lambda m: m.group(1) + str(internal_amount), content)
    else:
        content = re.sub(r'("internalAddonAmount"\s*:\s*)\d+', lambda m: m.group(1) + '0', content)

    with open(file_path, 'w', encoding='utf-8') as out_file:
        out_file.write(content)

def modify_time(file_path, time_day, time_night, skip_time):
    with open(file_path, 'r', encoding='utf-8') as file:
        content = file.read()
    content = re.sub(r'("timeSettingsDay"\s*:\s*)-?\d+(\.\d+)?(e[-+]?\d+)?', lambda m: f'{m.group(1)}{time_day}', content)
    content = re.sub(r'("timeSettingsNight"\s*:\s*)-?\d+(\.\d+)?(e[-+]?\d+)?', lambda m: f'{m.group(1)}{time_night}', content)
    content = re.sub(r'("isAbleToSkipTime"\s*:\s*)(true|false)', lambda m: f'{m.group(1)}{"true" if skip_time else "false"}', content)
    with open(file_path, 'w', encoding='utf-8') as out_file:
        out_file.write(content)
    messagebox.showinfo("Success", "Time updated.")

def extract_brace_block(s, start_index):
    open_braces = 0
    in_string = False
    escape = False
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
                if open_braces == 0:
                    return s[block_start:i + 1], block_start, i + 1
        escape = (char == '\\' and not escape)
    raise ValueError("Matching closing brace not found.")

# Season to Map ID mapping
SEASON_ID_MAP = {
    1: "RU_03",  # Season 1: Kola Peninsula
    2: "US_04",  # Season 2: Yukon
    3: "US_03",  # Season 3: Wisconsin
    4: "RU_04",  # Season 4: Amur
    5: "RU_05",  # Season 5: Don
    6: "US_06",  # Season 6: Maine
    7: "US_07",  # Season 7: Tennessee
    8: "RU_08",  # Season 8: Glades
    9: "US_09",  # Season 9: Ontario
    10: "US_10", # Season 10: British Columbia
    11: "US_11", # Season 11: Scandinavia
    12: "US_12", # Season 12: North Carolina
    13: "RU_13", # Season 13: Almaty
    14: "US_14", # Season 14: Austria
    15: "US_15", # Season 15: Quebec
    16: "US_16", # Season 16: Washington
}

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


def sync_rule_dropdowns(path):
    try:
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()

        def extract_int(key):
            match = re.search(rf'"{key}"\s*:\s*(-?\d+)', content)
            return int(match.group(1)) if match else None

        def extract_float(key):
            match = re.search(rf'"{key}"\s*:\s*(-?\d+(\.\d+)?(e[-+]?\d+)?)', content)
            return float(match.group(1)) if match else None

        def extract_bool(key):
            match = re.search(rf'"{key}"\s*:\s*(true|false)', content)
            return match.group(1) == "true" if match else None

        def set_var(var, val_map, actual_val):
            for label, value in val_map.items():
                if value == actual_val:
                    var.set(label)
                    return

        
        tyre_val = extract_int("tyreAvailability")
        set_var(tyre_var, {
            "all tires available": 0,
            "default": 1,
            "highway, allroad": 2,
            "highway, allroad, offroad": 3,
            "no mudtires": 4,
            "no chained tires": 5,
            "random per garage": 6
        }, tyre_val)
        if tyre_val is not None:
            for label, val in {
                "all tires available": 0,
                "default": 1,
                "highway, allroad": 2,
                "highway, allroad, offroad": 3,
                "no mudtires": 4,
                "no chained tires": 5,
                "random per garage": 6
            }.items():
                if val == tyre_val and "tyreAvailability" in dropdown_widgets:
                    dropdown_widgets["tyreAvailability"].set(label)
                    break
    

    except Exception as e:
        print("Error syncing rule dropdowns:", e)



def sync_factor_rule_dropdowns(file_path):
        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()
            def extract_value(key):
                match = re.search(r'"{}"\s*:\s*([^,\n]+)'.format(key), content)
                return match.group(1) if match else None

            for label, key, options, var in FACTOR_RULE_VARS:
                val = extract_value(key)
                if val is not None:
                    for name, num in options.items():
                        if str(num) == val:
                            var.set(name)
                            break
        except Exception as e:
            print("Failed to sync factor rules:", e)


def extend_rules_tab(tab, context):
    var = tk.StringVar(value="default")

    def save(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()

        except Exception as e:
            context["messagebox"].showerror("Rule Error", f"Failed to apply rule: {e}")

    
    def sync(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()

            match_avail = re.search(r'"jhagsdvcyjghaSVDCJYVASRFBGADRRBF"\s*:\s*(\d+)', content)
            if not match_avail:
                return

            avail = int(match_avail.group(1))

            for label, (a_val, a_amt) in external_addon_map.items():

                    break
        except Exception as e:
            print(f"[External Addon Rule Sync Error]: {e}")


def run_complete():
    make_backup_if_enabled(save_path_var.get())

    save_file = save_path_var.get()
    if not save_file or not os.path.exists(save_file):
        messagebox.showerror("Error", "Save file not found.")
        return

    selected_seasons = [i for i, var in season_vars if var.get() == 1]
    if other_season_var.get().isdigit():
        selected_seasons.append(int(other_season_var.get()))
    selected_maps = [map_ids[i] for i, var in enumerate(map_vars) if var.get()]

    complete_seasons_and_maps(save_file, selected_seasons, selected_maps)

    try:
        with open(save_file, "r", encoding="utf-8") as f:
            content = f.read()

        discovered_match = re.search(r'"discoveredObjectives"\s*:\s*{', content)
        finished_match = re.search(r'"finishedObjs"\s*:\s*{', content)
        times_match = re.search(r'"contestTimes"\s*:\s*{', content)

        if discovered_match:
            disc_block_str, disc_start, disc_end = extract_brace_block(content, discovered_match.start())
            discovered = json.loads(disc_block_str)
        else:
            discovered, disc_start, disc_end = {}, -1, -1

        if finished_match:
            fin_block_str, fin_start, fin_end = extract_brace_block(content, finished_match.start())
            finished = json.loads(fin_block_str)
        else:
            finished, fin_start, fin_end = {}, -1, -1

        if times_match:
            times_block_str, times_start, times_end = extract_brace_block(content, times_match.start())
            contest_times = json.loads(times_block_str)
        else:
            contest_times, times_start, times_end = {}, -1, -1

        for key in discovered:
            if any(part in key for part in ("A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "P", "O", "Q", "R", "T", "S", "U", "V", "W", "X", "Y", "Z")):
                for season in selected_seasons:
                    if f"_{season:02}_" in key:
                        finished[key] = {}
                        contest_times[key] = 1
                for map_id in selected_maps:
                    if map_id in key:
                        finished[key] = {}
                        contest_times[key] = 1

        if fin_start != -1:
            content = content[:fin_start] + json.dumps(finished, separators=(",", ":")) + content[fin_end:]
        if times_start != -1:
            content = content[:times_start] + json.dumps(contest_times, separators=(",", ":")) + content[times_end:]

        with open(save_file, "w", encoding="utf-8") as f:
            f.write(content)

    except Exception as e:
        messagebox.showerror("Contest Completion Error", str(e))




# ---- Contests Tab Logic ----
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import json
import os
import re

def extract_brace_block(s, start_index):
    open_braces = 0
    in_string = False
    escape = False
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
                if open_braces == 0:
                    return s[block_start:i+1], block_start, i+1
        escape = (char == '\\' and not escape)
    raise ValueError("Matching closing brace not found")

def extract_json_block_by_key(text, key):
    key_start = text.find(f'"{key}"')
    if key_start == -1:
        raise ValueError(f"Key '{key}' not found")
    while key_start > 0 and text[key_start] != '{':
        key_start -= 1
    return extract_brace_block(text, key_start)

def update_all_contest_times_blocks(content, new_entries):
    matches = list(re.finditer(r'"contestTimes"\s*:\s*{', content))
    updated_content = content
    for match in reversed(matches):  # Process from end to preserve indexes
        json_block, block_start, block_end = extract_brace_block(content, match.end() - 1)
        parsed = json.loads(json_block)
        for key in new_entries:
            if key not in parsed:
                parsed[key] = 1
        new_block_str = json.dumps(parsed, separators=(",", ":"))
        updated_content = updated_content[:block_start] + new_block_str + updated_content[block_end:]
    return updated_content

def mark_discovered_contests_complete(save_path, selected_seasons, selected_maps):
    make_backup_if_enabled(save_path)
    if not os.path.exists(save_path):
        messagebox.showerror("Error", "Save file not found.")
        return

    with open(save_path, "r", encoding="utf-8") as f:
        content = f.read()

    try:
        save_key_match = re.search(r'"(CompleteSave\d*)"\s*:\s*{', content)
        if not save_key_match:
            messagebox.showerror("Error", "No valid CompleteSave* block found.")
            return
        save_key = save_key_match.group(1)
        json_block, start, end = extract_json_block_by_key(content, save_key)
        data = json.loads(json_block)
        ssl_value = data[save_key]["SslValue"]

        discovered = ssl_value.get("discoveredObjectives", {})
        finished = ssl_value.get("finishedObjs", [])
        if not isinstance(finished, list):
            messagebox.showerror("Error", "finishedObjs is not a list")
            return

        contest_times = ssl_value.get("contestTimes", {})
        if not isinstance(contest_times, dict):
            contest_times = {}

        
        season_region_map = {
            1: "RU_03",  # Season 1: Kola Peninsula
            2: "US_04",  # Season 2: Yukon
            3: "US_03",  # Season 3: Wisconsin
            4: "RU_04",  # Season 4: Amur
            5: "RU_05",  # Season 5: Don
            6: "US_06",  # Season 6: Maine
            7: "US_07",  # Season 7: Tennessee
            8: "RU_08",  # Season 8: Glades
            9: "US_09",  # Season 9: Ontario
            10: "US_10", # Season 10: British Columbia
            11: "US_11", # Season 11: Scandinavia
            12: "US_12", # Season 12: North Carolina
            13: "RU_13", # Season 13: Almaty
            14: "US_14", # Season 14: Austria
            15: "US_15", # Season 15: Quebec
            16: "US_16", # Season 16: Washington
        }
        selected_region_codes = [season_region_map[s] for s in selected_seasons if s in season_region_map]

        added_keys = []
        for key in discovered:
            if any(part in key for part in ("A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "P", "O", "Q", "R", "T", "S", "U", "V", "W", "X", "Y", "Z")):
                if any(code in key for code in selected_region_codes + selected_maps):
                    if key not in finished:
                        finished.append(key)
                        added_keys.append(key)
                    if key not in contest_times:
                        contest_times[key] = 1

        if not added_keys:
            messagebox.showinfo("Info", "No new contests were modified.")
            return

        ssl_value["finishedObjs"] = finished
        ssl_value["contestTimes"] = contest_times

        
        
        # Remove from viewedUnactivatedObjectives if present
        viewed = ssl_value.get("viewedUnactivatedObjectives", [])
        if isinstance(viewed, list):
            before = len(viewed)
            viewed = [v for v in viewed if v not in added_keys]
            ssl_value["viewedUnactivatedObjectives"] = viewed

        # Replace the original JSON block in the file with the updated one
        updated_json_block = json.dumps(data, separators=(",", ":"))
        updated_content = content[:start] + updated_json_block + content[end:]

        # Now update all contestTimes blocks inside updated_content
        updated_content = update_all_contest_times_blocks(updated_content, contest_times)
    

        with open(save_path, "w", encoding="utf-8") as f:
            f.write(updated_content)

        messagebox.showinfo("Success", f"{len(added_keys)} contests marked as completed.")

    except Exception as e:
        messagebox.showerror("Error", str(e))

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
        updated = 0

        for map_key, towers in wp_data["data"].items():
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

        messagebox.showinfo("Success", f"Unlocked {updated} watchtowers.")
    except Exception as e:
        messagebox.showerror("Error", str(e))


def create_contest_tab(tab, save_path_var):

    season_vars = []
    map_vars = []
    other_season_var = tk.StringVar()

    seasons = [
        "Season 1: Search & Recover (Kola Peninsula)",
        "Season 2: Explore & Expand (Yukon)",
        "Season 3: Locate & Deliver (Wisconsin)",
        "Season 4: New Frontiers (Amur)",
        "Season 5: Build & Dispatch (Don)",
        "Season 6: Haul & Hustle (Maine)",
        "Season 7: Compete & Conquer (Tennessee)",
        "Season 8: Grand Harvest (Glades)",
        "Season 9: Renew & Rebuild (Ontario)",
        "Season 10: Fix & Connect (British Columbia)",
        "Season 11: Lights & Cameras (Scandinavia)",
        "Season 12: Public Energy (North Carolina)",
        "Season 13: Dig & Drill (Almaty)",
        "Season 14: Reap & Sow (Austria)",
        "Season 15: Oil & Dirt (Quebec)",
        "Season 16: High Voltage (Washington)"
    ]

    maps = [("Michigan", "US_01"), ("Alaska", "US_02"), ("Taymyr", "RU_02")]

    season_frame = ttk.Frame(tab)
    season_frame.pack(pady=5)

    left_column = ttk.Frame(season_frame)
    left_column.pack(side="left", padx=10, anchor="n")

    right_column = ttk.Frame(season_frame)
    right_column.pack(side="left", padx=10, anchor="n")

    for i, name in enumerate(seasons, 1):
        var = tk.IntVar()
        season_vars.append((i, var))
        column = left_column if i <= len(seasons) / 2 else right_column
        ttk.Checkbutton(column, text=name, variable=var).pack(anchor="w", pady=2)

    ttk.Label(tab, text="Other Season number (e.g. 17, 18, 19)").pack()
    ttk.Entry(tab, textvariable=other_season_var).pack(pady=5)

    ttk.Label(tab, text="Base Maps:").pack()
    map_frame = ttk.Frame(tab)
    map_frame.pack()
    for name, code in maps:
        var = tk.IntVar()
        ttk.Checkbutton(map_frame, text=name, variable=var).pack(anchor="w")
        map_vars.append((code, var))

    def on_click():
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")
        selected_seasons = [i for i, var in season_vars if var.get() == 1]
        if other_season_var.get().isdigit():
            selected_seasons.append(int(other_season_var.get()))
        selected_maps = [code for code, var in map_vars if var.get() == 1]
        if not selected_seasons and not selected_maps:
            return messagebox.showinfo("Info", "No seasons or maps selected.")
        mark_discovered_contests_complete(path, selected_seasons, selected_maps)

    ttk.Button(tab, text="Mark Contests Complete", command=on_click).pack(pady=10)

    ttk.Label(
        tab,
        text="You must accepted (discovered) the contests for them to be marked as completed.",
        foreground="black",
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
    16: ("US_16", "Season 16: High Voltage (Washington)")
}

BASE_MAPS = [
    ("US_01", "Michigan"),
    ("US_02", "Alaska"),
    ("RU_02", "Taymyr")
]

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
        updated = 0

        for map_key, upgrades in upgrades_data.items():
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

        messagebox.showinfo("Success", f"Updated {updated} upgrades.")
    except Exception as e:
        messagebox.showerror("Error", str(e))

def extract_brace_block(s, start_index):
    open_braces = 0
    in_string = False
    escape = False
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
                if open_braces == 0:
                    return s[block_start:i + 1], block_start, i + 1
        escape = (char == '\\' and not escape)
    raise ValueError("Matching closing brace not found.")



def create_upgrades_tab(tab, save_path_var):
    season_vars = []
    map_vars = []
    other_season_var = tk.StringVar()

    season_frame = ttk.Frame(tab)
    season_frame.pack(pady=(0, 10))

    # Two columns: left and right
    left_column = ttk.Frame(season_frame)
    left_column.pack(side="left", padx=10, anchor="n")

    right_column = ttk.Frame(season_frame)
    right_column.pack(side="left", padx=10, anchor="n")

    for idx, (season_num, (code, label)) in enumerate(SEASON_REGION_MAP.items(), start=1):
        var = tk.IntVar()
        column = left_column if idx <= len(SEASON_REGION_MAP) / 2 else right_column
        cb = ttk.Checkbutton(column, text=label, variable=var)
        cb.pack(anchor="w", pady=2)
        season_vars.append((code, var))

    # Add Other Season number entry
    ttk.Label(tab, text="Other Season number (e.g. 17, 18, 19)").pack(pady=5)
    ttk.Entry(tab, textvariable=other_season_var).pack(pady=5)

    ttk.Label(tab, text="Base Maps:").pack(pady=(5, 0))

    map_frame = ttk.Frame(tab)
    map_frame.pack(anchor="center", pady=5)

    for code, name in BASE_MAPS:
        var = tk.IntVar()
        cb = ttk.Checkbutton(map_frame, text=name, variable=var)
        cb.pack(anchor="w")
        map_vars.append((code, var))

    def on_apply():
        path = save_path_var.get()
        if not os.path.exists(path):
            messagebox.showerror("Error", "Save file not found.")
            return
        selected_regions = [code for code, var in season_vars if var.get()]
        selected_regions += [code for code, var in map_vars if var.get()]
        if other_season_var.get().isdigit():
            selected_regions.append(f"US_{int(other_season_var.get()):02}")
        if not selected_regions:
            messagebox.showinfo("Info", "No seasons or maps selected.")
            return
        find_and_modify_upgrades(path, selected_regions)

    ttk.Button(tab, text="Unlock Upgrades", command=on_apply).pack(pady=(10, 5))

    ttk.Label(tab, text="At least one upgrade must be marked or collected in-game for this to work.",
              foreground="red").pack(pady=(0, 2))
    ttk.Label(tab, text="If a new season is added, you may need to mark or collect one new upgrade.",
              foreground="red").pack()
    
def create_game_stats_tab(tab, save_path_var, plugin_loaders):
    import json

    stats_vars = {}
    distance_vars = {}

    # Full mapping for region codes -> full names (uppercase keys)
    REGION_NAME_MAP = {
        "US_01": "Michigan",
        "US_02": "Alaska",
        "RU_02": "Taymyr",
        "RU_03": "Season 1: Search & Recover (Kola Peninsula)",
        "US_03": "Season 3: Locate & Deliver (Wisconsin)",
        "US_04": "Season 2: Explore & Expand (Yukon)",
        "RU_04": "Season 4: New Frontiers (Amur)",
        "RU_05": "Season 5: Build & Dispatch (Don)",
        "US_06": "Season 6: Haul & Hustle (Maine)",
        "US_07": "Season 7: Compete & Conquer (Tennessee)",
        "RU_08": "Season 8: Grand Harvest (Glades)",
        "US_09": "Season 9: Renew & Rebuild (Ontario)",
        "US_10": "Season 10: Fix & Connect (British Columbia)",
        "US_11": "Season 11: Lights & Cameras (Scandinavia)",
        "US_12": "Season 12: Public Energy (North Carolina)",
        "RU_13": "Season 13: Dig & Drill (Almaty)",
        "US_14": "Season 14: Reap & Sow (Austria)",
        "US_15": "Season 15: Oil & Dirt (Quebec)",
        "US_16": "Season 16: High Voltage (Washington)",
        "TRIALS": "Trials"
    }
    REGION_ORDER = list(REGION_NAME_MAP.keys())

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
            label_text = REGION_NAME_MAP.get(region_up, region)
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


def create_watchtowers_tab(tab, save_path_var):
    season_vars = []
    map_vars = []
    other_season_var = tk.StringVar()

    season_frame = ttk.Frame(tab)
    season_frame.pack(pady=(0, 10))

    # Two columns: left and right
    left_column = ttk.Frame(season_frame)
    left_column.pack(side="left", padx=10, anchor="n")

    right_column = ttk.Frame(season_frame)
    right_column.pack(side="left", padx=10, anchor="n")

    for idx, (season_num, (code, label)) in enumerate(SEASON_REGION_MAP.items(), start=1):
        var = tk.IntVar()
        column = left_column if idx <= len(SEASON_REGION_MAP) / 2 else right_column
        cb = ttk.Checkbutton(column, text=label, variable=var)
        cb.pack(anchor="w", pady=2)
        season_vars.append((code, var))

    ttk.Label(tab, text="Other Season number (e.g. 17, 18, 19)").pack(pady=5)
    ttk.Entry(tab, textvariable=other_season_var).pack(pady=5)

    ttk.Label(tab, text="Base Maps:").pack(pady=(5, 0))

    map_frame = ttk.Frame(tab)
    map_frame.pack(anchor="center", pady=5)

    for code, name in BASE_MAPS:
        var = tk.IntVar()
        cb = ttk.Checkbutton(map_frame, text=name, variable=var)
        cb.pack(anchor="w")   # align left inside block
        map_vars.append((code, var))

    def on_apply():
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")
        selected_regions = [code for code, var in season_vars if var.get()]
        selected_regions += [code for code, var in map_vars if var.get()]
        if other_season_var.get().isdigit():
            selected_regions.append(f"US_{int(other_season_var.get()):02}")
        if not selected_regions:
            return messagebox.showinfo("Info", "No seasons or maps selected.")
        unlock_watchtowers(path, selected_regions)

    ttk.Button(tab, text="Unlock Watchtowers", command=on_apply).pack(pady=(10, 5))
    ttk.Label(tab, text="It will mark them as found but wont reveal the map use the Fog Tool for that.",
              foreground="red").pack()
    
import threading, requests, webbrowser, re

GITHUB_RELEASES_API = "https://api.github.com/repos/MrBoxik/SnowRunner-Save-Editor/releases"
GITHUB_RELEASES_PAGE = "https://github.com/MrBoxik/SnowRunner-Save-Editor/releases"
GITHUB_MAIN_PAGE = "https://github.com/MrBoxik/SnowRunner-Save-Editor"


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

    def worker():
        cfg = load_config()
        current_version = cfg.get("current_version", None)

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

            latest_num = normalize_version(latest_raw)

            # First launch → save numeric version once
            if current_version is None:
                numeric_latest = str(normalize_version(latest_raw))
                cfg["current_version"] = numeric_latest
                save_config(cfg)
                log(f"No version in config → writing {numeric_latest} as first launch version.")
                return

            log(f"User version from config: {current_version}")

            current_num = normalize_version(current_version)
            log(f"Normalized versions → current: {current_num}, latest: {latest_num}")

            if latest_num > current_num:
                log("Newer version detected → scheduling popup.")

                def popup():
                    top = tk.Toplevel(root)
                    top.title("Update Available")
                    top.geometry("380x200")

                    # ✅ Cleaner label: no extra newlines or text
                    ttk.Label(
                        top,
                        text=f"A new version is available!\n\n"
                             f"Current: {current_version}\nLatest: {latest_num}",
                        justify="center",
                        wraplength=340
                    ).pack(pady=10)

                    def confirm_update():
                        numeric_latest = str(latest_num)   # ✅ always numeric
                        cfg["current_version"] = numeric_latest
                        save_config(cfg)
                        log(f"User confirmed update → saved version {numeric_latest} to config.")
                        top.destroy()

                    updated_var = tk.BooleanVar(value=False)
                    chk = ttk.Checkbutton(
                        top,
                        text="I updated",
                        variable=updated_var,
                        command=lambda: confirm_update() if updated_var.get() else None
                    )
                    chk.pack(pady=(0, 5))  # ✅ tighten space above

                    def open_page():
                        webbrowser.open(GITHUB_MAIN_PAGE)

                    def copy_link():
                        root.clipboard_clear()
                        root.clipboard_append(GITHUB_MAIN_PAGE)
                        root.update()
                        messagebox.showinfo("Copied", "Main page link copied to clipboard.")

                    btn_frame = ttk.Frame(top)
                    btn_frame.pack(pady=10)

                    ttk.Button(btn_frame, text="Open Page", command=open_page).pack(side="left", padx=5)
                    ttk.Button(btn_frame, text="Copy Link", command=copy_link).pack(side="left", padx=5)

                # show popup in main thread
                root.after(0, popup)
            else:
                log("No update available.")

        except Exception as e:
            log(f"Update check failed: {e}")

    # run worker in background thread
    threading.Thread(target=worker, daemon=True).start()


def launch_gui():
    global max_backups_var

    # Restore from config
    try:
        cfg = load_config()
        max_backups_var.set(str(cfg.get("max_backups", "0")))
    except Exception:
        pass

    plugin_loaders = []
    root = tk.Tk()
    check_for_updates_background(root, debug=True)
    # --- Remove ugly dotted focus rings globally ---
    root.option_add("*TEntry.highlightThickness", 0)
    root.option_add("*TEntry.highlightColor", "SystemWindowBackground")
    root.option_add("*TEntry.highlightBackground", "SystemWindowBackground")
    root.option_add("*TButton.takeFocus", 0)
    root.option_add("*TCheckbutton.takeFocus", 0)
    root.option_add("*TRadiobutton.takeFocus", 0)
    global tyre_var, custom_day_var, custom_night_var

    max_backups_var = tk.StringVar(value="0")  # default 0 = unlimited


    global delete_path_on_close_var, dont_remember_path_var
    delete_path_on_close_var = tk.BooleanVar(value=False)
    dont_remember_path_var = tk.BooleanVar(value=False)
    config = load_config()
    config = load_config()
    max_backups_var.set(str(config.get("max_backups", "0")))
    delete_path_on_close_var.set(config.get("delete_path_on_close", False))
    dont_remember_path_var.set(config.get("dont_remember_path", False))

    global tyre_var
    tyre_var = tk.StringVar(value="default")
    global custom_day_var, custom_night_var
    custom_day_var = tk.DoubleVar(value=1.0)
    custom_night_var = tk.DoubleVar(value=1.0)

    import sys
    # inside your GUI initialization
    icon_path_ico = resource_path("app_icon.ico")
    icon_path_png = resource_path("app_icon.png")

    try:
        if platform.system() == "Windows" and os.path.exists(icon_path_ico):
            # .ico works only on Windows
            root.iconbitmap(icon_path_ico)
        elif os.path.exists(icon_path_png):
            # use PNG everywhere else
            icon_img = PhotoImage(file=icon_path_png)
            root.iconphoto(True, icon_img)
        else:
            print("No suitable icon found, skipping icon setup.")
    except Exception as e:
        print("Failed to set window icon:", e)

    root.title("SnowRunner Save Editor")

     
    def on_close():
        # Save settings before closing
        save_settings()

        if delete_path_on_close_var.get():
            config = load_config()
            if "last_opened_path" in config:
                del config["last_opened_path"]
                save_config(config)

        root.destroy()


    save_path_var = tk.StringVar(value=load_last_path())
    money_var = tk.StringVar()
    rank_var = tk.StringVar()
    difficulty_var = tk.StringVar()
    truck_avail_var = tk.StringVar()
    truck_price_var = tk.StringVar()
    skip_time_var = tk.BooleanVar()
    addon_avail_var = tk.StringVar()
    addon_amount_var = tk.StringVar()
    time_preset_var = tk.StringVar()
    other_season_var = tk.StringVar()

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
        m, r, d, t, s, day, night, tp = get_file_info(content)
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

        time_preset_var.set(next((k for k, v in time_presets.items() if abs(day - v[0]) < 0.01 and abs(night - v[1]) < 0.01), "Custom"))
        # Also sync all rule dropdowns on startup
        sync_rule_dropdowns(last_path)
        for loader in plugin_loaders:
            try:
                loader(last_path)
            except Exception as e:
                print(f"Plugin failed to update GUI on startup: {e}")

    def browse_file():
        file_path = filedialog.askopenfilename(filetypes=[("SnowRunner Save", "*.cfg *.dat")])
        if file_path:
            save_path_var.set(file_path)
        # Call plugin GUI loaders to refresh their values from file
        for loader in plugin_loaders:
            try:
                loader(save_path_var.get())
            except Exception as e:
                print(f"Plugin failed to update GUI from file: {e}")

            save_path(file_path)
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                m, r, d, t, s, day, night, tp = get_file_info(content)
                money_var.set(str(m))
                rank_var.set(str(r))
                difficulty_var.set(difficulty_map.get(d, "Normal"))
                truck_avail_var.set(truck_avail_map.get(t, "default"))
                truck_price_var.set(truck_price_map.get(tp, "default"))
                skip_time_var.set(s)
    match = next((k for k, v in time_presets.items() if abs(day - v[0]) < 0.01 and abs(night - v[1]) < 0.01), "Custom")
    time_preset_var.set(match)
    

    tab_control = ttk.Notebook(root)
    tab_file = ttk.Frame(tab_control)
    tab_money = ttk.Frame(tab_control)
    tab_missions = ttk.Frame(tab_control)
    tab_rules = ttk.Frame(tab_control)
    tab_time = ttk.Frame(tab_control)
    tab_control.add(tab_file, text='Save File')
    tab_control.add(tab_money, text='Money & Rank')
    tab_control.add(tab_missions, text='Missions')
    tab_contests = ttk.Frame(tab_control)
    tab_control.add(tab_contests, text='Contests')
    create_contest_tab(tab_contests, save_path_var)
    tab_upgrades = ttk.Frame(tab_control)
    tab_control.add(tab_upgrades, text='Upgrades')
    create_upgrades_tab(tab_upgrades, save_path_var)
    tab_watchtowers = ttk.Frame(tab_control)
    tab_control.add(tab_watchtowers, text="Watchtowers")
    create_watchtowers_tab(tab_watchtowers, save_path_var)
    tab_control.add(tab_rules, text='Rules')
    tab_control.add(tab_time, text='Time')
    tab_stats = ttk.Frame(tab_control)
    tab_control.add(tab_stats, text="Game Stats")
    create_game_stats_tab(tab_stats, save_path_var, plugin_loaders)
    tab_settings = ttk.Frame(tab_control)
    tab_control.add(tab_settings, text='Settings')

    # Create Fog Tool tab
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

    tab_control.pack(expand=1, fill='both')
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


    ttk.Checkbutton(tab_settings, text="Don't remember save file path", variable=dont_remember_path_var).pack(pady=(10, 0))
    ttk.Checkbutton(tab_settings, text="Delete saved path on close", variable=delete_path_on_close_var).pack(pady=(5, 10))
    def save_settings_silent():
        config = load_config()
        config["dont_remember_path"] = dont_remember_path_var.get()
        config["delete_path_on_close"] = delete_path_on_close_var.get()
        config["make_backup"] = make_backup_var.get()
        config["full_backup"] = full_backup_var.get()
        config["max_backups"] = int(max_backups_var.get())
        save_config(config)

    def save_settings():
        save_settings_silent()
        messagebox.showinfo("Settings", "Settings have been saved.")

        if delete_path_on_close_var.get():
            if os.path.exists(SAVE_PATH_FILE):
                os.remove(SAVE_PATH_FILE)
        elif not dont_remember_path_var.get():
            save_path(save_path_var.get())

    ttk.Button(tab_settings, text="Save Settings", command=save_settings).pack(pady=(10, 10))
    def create_desktop_shortcut():
        if not getattr(sys, 'frozen', False):
            messagebox.showwarning("Unavailable", "This feature only works in the built version.")
            return

        if platform.system() != "Windows":
            messagebox.showwarning("Unsupported", "This feature is only available on Windows.")
            return

        try:
            import pythoncom
            from win32com.client import Dispatch

            exe_path = sys.executable
            desktop = get_desktop_path()
            shortcut_path = os.path.join(desktop, "SnowRunner Editor.lnk")

            shell = Dispatch('WScript.Shell')
            shortcut = shell.CreateShortcut(shortcut_path)
            shortcut.TargetPath = exe_path
            shortcut.WorkingDirectory = os.path.dirname(exe_path)
            shortcut.IconLocation = exe_path
            shortcut.save()

            messagebox.showinfo("Success", f"Shortcut created:\n{shortcut_path}")
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
        check_for_updates_background(root, debug=True)

    ttk.Button(tab_settings, text="Check for Update", command=manual_update_check).pack(pady=(5, 10))



    # Separator and embedded Minesweeper
    if MINESWEEPER_AVAILABLE:
        ttk.Separator(tab_settings, orient='horizontal').pack(fill='x', pady=(10, 5))
        ttk.Label(tab_settings, text="Minesweeper", font=("TkDefaultFont", 11, "bold")).pack(pady=(0, 5))
    
        minesweeper_frame = tk.Frame(tab_settings)
        minesweeper_frame.pack(pady=5)
        MinesweeperApp(minesweeper_frame)





    # Save file tab
    ttk.Label(tab_file, text="Selected Save File:").pack(pady=10)
    ttk.Entry(tab_file, textvariable=save_path_var, width=60).pack(pady=5)
    ttk.Button(tab_file, text="Browse...", command=browse_file).pack(pady=10)
        # Info text about backup and file paths
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
        wraplength=500,
        justify="left",
        font=("TkDefaultFont", 9),
        foreground="black"
    ).pack(pady=(5, 10))

    ttk.Label(
        tab_file,
        text="⚠️ SnowRunner must be closed before editing the save file. Changes made while the game is running may be lost or cause issues.",
        wraplength=500,
        justify="center",
        foreground="red",
        font=("TkDefaultFont", 9, "bold")
    ).pack(pady=(5, 10))
    global make_backup_var, full_backup_var
    make_backup_var = tk.BooleanVar(value=True)
    full_backup_var = tk.BooleanVar(value=False)

    # Restore from config if available
    try:
        cfg = load_config()
        make_backup_var.set(cfg.get("make_backup", True))
        full_backup_var.set(cfg.get("full_backup", False))
    except Exception:
        pass

    ttk.Checkbutton(
        tab_file,
        text="Small Backup (only the 1 main save file, ~200kB per backup)",
        variable=make_backup_var,
        command=save_settings_silent
    ).pack(pady=(0, 10))

    ttk.Checkbutton(
        tab_file,
        text="Full Backup (entire save folder, ~30MB per backup) Recommended",
        variable=full_backup_var,
        command=save_settings_silent
    ).pack(pady=(0, 10))

    ttk.Button(
        tab_file,
        text="Recall Backup",
        command=lambda: recall_backup(save_path_var.get())
    ).pack(pady=(5, 10))

    ttk.Label(
        tab_file,
        text="⚠️ Full backups are much safer but take much more space. Delete old ones regularly.",
        wraplength=500,
        justify="center",
        foreground="red",
        font=("TkDefaultFont", 9, "bold")
    ).pack(pady=(0, 10))

    ttk.Label(tab_file, text="Auto Cleanup (max backups, 0 = unlimited):").pack(pady=(5, 0))
    ttk.Entry(tab_file, textvariable=max_backups_var).pack(pady=(0, 10))

    ttk.Button(
        tab_file,
        text="Save Settings",
        command=lambda: save_settings_silent() or messagebox.showinfo("Settings", "Settings saved.")
    ).pack(pady=(0, 10))



    # Footer text at the bottom of the Save File tab
    ttk.Label(
        tab_file,
        text="Made with hatred for bugs by: MrBoxik",
        foreground="black",
        font=("TkDefaultFont", 9),
        justify="center"
    ).pack(pady=(200, 5))

    # Money tab
    ttk.Label(tab_money, text="Desired Money:").pack()
    ttk.Entry(tab_money, textvariable=money_var).pack()
    ttk.Label(tab_money, text="Desired Rank (1–30):").pack(pady=10)
    ttk.Entry(tab_money, textvariable=rank_var).pack()

    def update_money_rank():
        make_backup_if_enabled(save_path_var.get())
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")
        if not (money_var.get().isdigit() and rank_var.get().isdigit()):
            return messagebox.showerror("Invalid", "Money and rank must be numeric.")
        rank_val = int(rank_var.get())
        if not (1 <= rank_val <= 30):
            return messagebox.showerror("Invalid", "Rank must be 1–30.")
        xp_val = RANK_XP_REQUIREMENTS[rank_val]
        with open(path, 'r', encoding='utf-8') as f:
            content = f.read()
        content = re.sub(r'"money"\s*:\s*\d+', f'"money": {int(money_var.get())}', content)
        content = re.sub(r'"rank"\s*:\s*\d+', f'"rank": {rank_val}', content)
        content = re.sub(r'"experience"\s*:\s*\d+', f'"experience": {xp_val}', content)
        with open(path, 'w', encoding='utf-8') as f:
            f.write(content)
        messagebox.showinfo("Success", f"Money and experience for rank {rank_val} updated.")

    ttk.Button(tab_money, text="Update Money & Rank", command=update_money_rank).pack(pady=20)
    # Missions tab
    seasons = [
        "Season 1: Search & Recover (Kola Peninsula)",
        "Season 2: Explore & Expand (Yukon)",
        "Season 3: Locate & Deliver (Wisconsin)",
        "Season 4: New Frontiers (Amur)",
        "Season 5: Build & Dispatch (Don)",
        "Season 6: Haul & Hustle (Maine)",
        "Season 7: Compete & Conquer (Tennessee)",
        "Season 8: Grand Harvest (Glades)",
        "Season 9: Renew & Rebuild (Ontario)",
        "Season 10: Fix & Connect (British Columbia)",
        "Season 11: Lights & Cameras (Scandinavia)",
        "Season 12: Public Energy (North Carolina)",
        "Season 13: Dig & Drill (Almaty)",
        "Season 14: Reap & Sow (Austria)",
        "Season 15: Oil & Dirt (Quebec)",
        "Season 16: High Voltage (Washington)"
    ]
    season_vars = []
    season_frame = ttk.Frame(tab_missions)
    season_frame.pack(pady=10)
    left_column = ttk.Frame(season_frame)
    left_column.pack(side='left', padx=10, anchor='n')
    right_column = ttk.Frame(season_frame)
    right_column.pack(side='left', padx=10, anchor='n')
    for i, name in enumerate(seasons, 1):
        var = tk.IntVar()
        season_vars.append((i, var))
        column = left_column if i <= len(seasons) / 2 else right_column
        ttk.Checkbutton(column, text=name, variable=var).pack(anchor='w', pady=2)

    ttk.Label(tab_missions, text="Other Season number (e.g. 17, 18, 19)").pack(pady=5)
    ttk.Entry(tab_missions, textvariable=other_season_var).pack(pady=5)

    ttk.Label(tab_missions, text="Base Game Maps:", font=("TkDefaultFont", 10, "bold")).pack(pady=5)

    map_frame = ttk.Frame(tab_missions)              # new frame
    map_frame.pack(anchor="center", pady=5)          # center the block

    base_maps = [("Michigan", "US_01"), ("Alaska", "US_02"), ("Taymyr", "RU_02")]
    base_map_vars = []

    for name, map_id in base_maps:
        var = tk.IntVar()
        base_map_vars.append((map_id, var))
        ttk.Checkbutton(map_frame, text=name, variable=var).pack(anchor="w")  # left align


    def run_complete():
        make_backup_if_enabled(save_path_var.get())
        if not os.path.exists(save_path_var.get()):
            messagebox.showerror("Error", "Save file not found.")
            return
        selected_seasons = [i for i, var in season_vars if var.get() == 1]
        if other_season_var.get().isdigit():
            selected_seasons.append(int(other_season_var.get()))
        selected_maps = [map_id for map_id, var in base_map_vars if var.get() == 1]
        if not selected_seasons and not selected_maps:
            messagebox.showinfo("Info", "No seasons or maps selected.")
            return
        complete_seasons_and_maps(save_path_var.get(), selected_seasons, selected_maps)

    ttk.Button(tab_missions, text="Complete Selected Missions", command=run_complete).pack(pady=10)

    # Disclaimer below the complete button
    ttk.Label(
        tab_missions,
        text="You must accept the task or mission in the game before it can be completed",
        foreground="black",
        font=("TkDefaultFont", 10, "bold"),
        wraplength=400,
        justify="center"
    ).pack(pady=(5, 15))



    # -- Begin improved layout for all rules --
    rules_grid_frame = ttk.Frame(tab_rules)
    rules_grid_frame.pack(pady=10)

    # Helper to place a labeled dropdown in a grid cell
    def add_labeled_combobox(parent, label_text, variable, values, row, col):
        frame = ttk.Frame(parent, relief="groove", padding=5)
        frame.grid(row=row, column=col, padx=5, pady=5, sticky="nw")
        ttk.Label(frame, text=label_text).pack(anchor="w")
        ttk.Combobox(frame, textvariable=variable, values=values, state="readonly").pack(fill="x")

    # Add built-in rule settings
    built_in_rules = [
        ("Game Difficulty Modes:", difficulty_var, list(reverse_difficulty_map.keys())),
        ("Truck Availability:", truck_avail_var, list(reverse_truck_avail_map.keys())),
        ("Truck Pricing:", truck_price_var, list(reverse_truck_price_map.keys())),
        ("Internal Addon Availability:", addon_avail_var, list(reverse_addon_avail_map.keys())),
        ("Internal Addon Amount (if custom):", addon_amount_var, list(addon_amount_ranges.keys()))
    ]

    num_columns = 3
    for i, (label, var, options) in enumerate(built_in_rules):
        row = i // num_columns
        col = i % num_columns
        add_labeled_combobox(rules_grid_frame, label, var, options, row, col)


    
    # --- Begin: Loaders for Rule Dropdown Sync ---
    def load_all_custom_rule_vars(file_path):
        print('[DEBUG] Custom rule loader triggered:', file_path)
        if not os.path.exists(file_path):
            return
        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()

            def extract_int(key):
                match = re.search(rf'"{key}"\s*:\s*(-?\d+)', content)
                return int(match.group(1)) if match else None

            def extract_float(key):
                match = re.search(rf'"{key}"\s*:\s*(-?\d+(\.\d+)?(e[-+]?\d+)?)', content)
                return float(match.group(1)) if match else None

            def extract_bool(key):
                match = re.search(rf'"{key}"\s*:\s*(true|false)', content)
                return match.group(1) == "true" if match else None

            def set_var(var, val_map, actual_val):
                for label, value in val_map.items():
                    if value == actual_val:
                        var.set(label)
                        return

            # Sync logic
            set_var(damage_var, damage_options, extract_int("vehicleDamageFactor"))
            set_var(storage_var, storage_options, extract_int("vehicleStorageSlots"))
            set_var(teleport_var, teleport_map, extract_int("teleportationPrice"))
            set_var(trailer_var, trailer_map, extract_int("trailerPricingFactor"))
            set_var(sell_var, sell_map, extract_float("truckSellingFactor"))
            set_var(addon_var, addon_map, extract_int("addonPricingFactor"))
            set_var(fuel_var, fuel_map, extract_int("fuelPriceFactor"))
            refuel_val = extract_bool("isGarageRefuelAvailable")
            if refuel_val is not None: refuel_var.set(refuel_val)
            set_var(repair_var, repair_map, extract_int("garageRepairePriceFactor"))
            marker_val = extract_bool("isMapMarkerAsInHardMode")
            if marker_val is not None: marker_var.set("hard mode" if marker_val else "default")
            set_var(contest_var, contest_map, extract_int("maxContestAttempts"))
            set_var(repair_cost_var, repair_cost_map, extract_int("repairPointsCostFactor"))
            set_var(repair_req_var, repair_req_map, extract_float("repairPointsRequiredFactor"))
            set_var(trailer_avail_var, trailer_avail_map, extract_int("trailerAvailability"))
            set_var(trailer_sell_var, trailer_sell_map, extract_float("trailerSellingFactor"))
            set_var(addon_sell_var, addon_sell_map, extract_float("addonSellingFactor"))
            set_var(tyre_var, {
                "all tires available": 0,
                "default": 1,
                "highway, allroad": 2,
                "highway, allroad, offroad": 3,
                "no mudtires": 4,
                "no chained tires": 5,
                "random per garage": 6
            }, extract_int("tyreAvailability"))

        except Exception as e:
            print("Rule loader failed:", e)

    plugin_loaders.append(load_all_custom_rule_vars)
    # --- End: Loaders for Rule Dropdown Sync ---


    # Collect plugin rule savers
    rule_savers = []
# plugin_loaders = []  # Removed duplicate to preserve earlier plugin loader

    # Create a frame with grid layout for modular rule widgets
    rules_grid_frame = ttk.Frame(tab_rules)
    rules_grid_frame.pack(pady=10)

    # Track widget position in grid
    rule_col_count = 3  # Number of columns you want
    rule_index = 0

    
    # --- Embedded: Vehicle Damage Factor ---
    damage_var = tk.StringVar(value="default")
    damage_options = {'default': 1, 'no damage': 0, '2x': 2, '3x': 3, '5x': 5}
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="Vehicle Damage:").pack(anchor="w", pady=2)
    ttk.Combobox(subframe, textvariable=damage_var, values=list(damage_options.keys()), state="readonly").pack(fill="x")
    def save_damage(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            val = damage_options[damage_var.get()]
            if '"vehicleDamageFactor"' in content:
                content = re.sub(r'"vehicleDamageFactor"\s*:\s*-?\d+(\.\d+)?(e[-+]?\d+)?', f'"vehicleDamageFactor": {val}', content)
            else:
                content = content.replace("{", f'"vehicleDamageFactor": {val}, ', 1)
            with open(path, "w", encoding="utf-8") as f:
                f.write(content)
        except Exception as e:
            messagebox.showerror("Rule Error", f"Failed to apply Vehicle Damage Factor: {e}")
    rule_savers.append(save_damage)
    rule_index += 1

    # --- Embedded: Vehicle Storage Slots ---
    storage_var = tk.StringVar(value="default")
    storage_options = {'default': 0, 'only 3': 3, 'only 5': 5, 'only 10': 10, 'only scouts': -1}
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="Vehicle Storage Slots:").pack(anchor="w", pady=2)
    ttk.Combobox(subframe, textvariable=storage_var, values=list(storage_options.keys()), state="readonly").pack(fill="x")
    def save_storage(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            val = storage_options[storage_var.get()]
            if '"vehicleStorageSlots"' in content:
                content = re.sub(r'"vehicleStorageSlots"\s*:\s*-?\d+(\.\d+)?(e[-+]?\d+)?', f'"vehicleStorageSlots": {val}', content)
            else:
                content = content.replace("{", f'"vehicleStorageSlots": {val}, ', 1)
            with open(path, "w", encoding="utf-8") as f:
                f.write(content)
        except Exception as e:
            messagebox.showerror("Rule Error", f"Failed to apply Vehicle Storage Slots: {e}")
    rule_savers.append(save_storage)
    rule_index += 1

    # --- Embedded: Truck Switching (Teleportation) ---
    teleport_var = tk.StringVar(value="free")
    teleport_values = ["free", "500", "1000", "2000", "5000"]
    teleport_map = {"free": 0, "500": 500, "1000": 1000, "2000": 2000, "5000": 5000}
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="Truck Switching (Over Minimap):").pack(anchor="w", pady=2)
    ttk.Combobox(subframe, textvariable=teleport_var, values=teleport_values, state="readonly").pack(fill="x")
    def save_teleport(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            val = teleport_map[teleport_var.get()]
            if '"teleportationPrice"' in content:
                content = re.sub(r'"teleportationPrice"\s*:\s*\d+', f'"teleportationPrice": {val}', content)
            else:
                content = content.replace("{", f'"teleportationPrice": {val}, ', 1)
            with open(path, "w", encoding="utf-8") as f:
                f.write(content)
        except Exception as e:
            messagebox.showerror("Rule Error", f"Failed to apply Truck Teleportation Price rule: {e}")
    rule_savers.append(save_teleport)
    rule_index += 1

    # --- Embedded: Trailer Pricing Factor ---
    trailer_var = tk.StringVar(value="normal price")
    trailer_map = {"free": 0, "normal price": 1, "2x": 2, "4x": 4, "6x": 6}
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="Trailer Price:").pack(anchor="w", pady=2)
    ttk.Combobox(subframe, textvariable=trailer_var, values=list(trailer_map.keys()), state="readonly").pack(fill="x")
    def save_trailer(path):
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        val = trailer_map[trailer_var.get()]
        if '"trailerPricingFactor"' in content:
            content = re.sub(r'"trailerPricingFactor"\s*:\s*\d+', f'"trailerPricingFactor": {val}', content)
        else:
            content = content.replace("{", f'"trailerPricingFactor": {val}, ', 1)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
    rule_savers.append(save_trailer)
    rule_index += 1

    # --- Embedded: Truck Selling Price ---
    sell_var = tk.StringVar(value="normal price")
    sell_map = {"normal price": 1, "50%": 0.5, "30%": 0.3, "10%": 0.1, "can't be sold": -1}
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="Truck Selling Price:").pack(anchor="w", pady=2)
    ttk.Combobox(subframe, textvariable=sell_var, values=list(sell_map.keys()), state="readonly").pack(fill="x")
    def save_sell(path):
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        val = sell_map[sell_var.get()]
        if '"truckSellingFactor"' in content:
            content = re.sub(r'"truckSellingFactor"\s*:\s*-?\d+(\.\d+)?(e[-+]?\d+)?', f'"truckSellingFactor": {val}', content)
        else:
            content = content.replace("{", f'"truckSellingFactor": {val}, ', 1)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
    rule_savers.append(save_sell)
    rule_index += 1


    # --- Upgraded: Tyre Availability Rule with Styled Frame ---
    
    
    
    
    # --- External Addon Availability (modifies externalAddonsAmount automatically) ---
    external_addon_var = tk.StringVar(value="default")
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="External Addon Availability:").pack(anchor="w", pady=2)
    ttk.Combobox(subframe, textvariable=external_addon_var, values=list(external_addon_map.keys()), state="readonly").pack(fill="x")
    def save_external_addons(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            val, amt = external_addon_map[external_addon_var.get()]
            content = re.sub(r'"externalAddonAvailability"\s*:\s*\d+', f'"externalAddonAvailability": {val}', content) if '"externalAddonAvailability"' in content else content.replace("{", f'"externalAddonAvailability": {val}, ', 1)
            content = re.sub(r'"externalAddonsAmount"\s*:\s*\d+', f'"externalAddonsAmount": {amt}', content) if '"externalAddonsAmount"' in content else content.replace("{", f'"externalAddonsAmount": {amt}, ', 1)
            with open(path, "w", encoding="utf-8") as f:
                f.write(content)
        except Exception as e:
            messagebox.showerror("Rule Error", f"Failed to apply External Addon rule: {e}")
    rule_savers.append(save_external_addons)
    rule_index += 1

    def sync_external_addon_var(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            match = re.search(r'"externalAddonAvailability"\s*:\s*(\d+)', content)
            if match:
                value = int(match.group(1))
                for k, (v, _) in external_addon_map.items():
                    if v == value:
                        external_addon_var.set(k)
                        break
        except Exception as e:
            print(f"Sync error (externalAddonAvailability): {e}")

    plugin_loaders.append(sync_external_addon_var)

    # --- Embedded: Addon Pricing Factor ---
    addon_var = tk.StringVar(value="default")
    addon_map = {"default": 1, "free": 0, "2x": 2, "4x": 4, "6x": 6}
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="Vehicle Addon Price:").pack(anchor="w", pady=2)
    ttk.Combobox(subframe, textvariable=addon_var, values=list(addon_map.keys()), state="readonly").pack(fill="x")
    def save_addon(path):
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        val = addon_map[addon_var.get()]
        content = re.sub(r'"addonPricingFactor"\s*:\s*\d+', f'"addonPricingFactor": {val}', content) if '"addonPricingFactor"' in content else content.replace("{", f'"addonPricingFactor": {val}, ', 1)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
    rule_savers.append(save_addon)
    rule_index += 1

    # --- Embedded: Fuel Price ---
    fuel_var = tk.StringVar(value="normal price")
    fuel_map = {"free": 0, "normal price": 1, "2x": 2, "4x": 4, "6x": 6}
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="Fuel Price:").pack(anchor="w", pady=2)
    ttk.Combobox(subframe, textvariable=fuel_var, values=list(fuel_map.keys()), state="readonly").pack(fill="x")
    def save_fuel(path):
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        val = fuel_map[fuel_var.get()]
        content = re.sub(r'"fuelPriceFactor"\s*:\s*\d+', f'"fuelPriceFactor": {val}', content) if '"fuelPriceFactor"' in content else content.replace("{", f'"fuelPriceFactor": {val}, ', 1)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
    rule_savers.append(save_fuel)
    rule_index += 1

    # --- Embedded: Garage Refuel ---
    refuel_var = tk.BooleanVar(value=True)
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="Garage Refueling:").pack(anchor="w", pady=2)
    ttk.Checkbutton(subframe, text="Enable garage refueling", variable=refuel_var).pack()
    def save_refuel(path):
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        val = "true" if refuel_var.get() else "false"
        content = re.sub(r'"isGarageRefuelAvailable"\s*:\s*(true|false)', f'"isGarageRefuelAvailable": {val}', content) if '"isGarageRefuelAvailable"' in content else content.replace("{", f'"isGarageRefuelAvailable": {val}, ', 1)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
    rule_savers.append(save_refuel)
    rule_index += 1

    # --- Embedded: Garage Repair Price ---
    repair_var = tk.StringVar(value="normal price")
    repair_map = {"auto repair": 0, "paid": 1, "2x": 2, "4x": 4, "6x": 6}
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="Garage Repair Price:").pack(anchor="w", pady=2)
    ttk.Combobox(subframe, textvariable=repair_var, values=list(repair_map.keys()), state="readonly").pack(fill="x")
    def save_repair(path):
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        val = repair_map[repair_var.get()]
        content = re.sub(r'"garageRepairePriceFactor"\s*:\s*[^,\n]+', f'"garageRepairePriceFactor": {val}', content) if '"garageRepairePriceFactor"' in content else content.replace("{", f'"garageRepairePriceFactor": {val}, ', 1)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
    rule_savers.append(save_repair)
    rule_index += 1

    
    # --- Embedded: Map Marker Mode ---
    marker_var = tk.StringVar(value="default")
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="Map Marker Style:").pack(anchor="w", pady=2)
    ttk.Combobox(subframe, textvariable=marker_var, values=["default", "hard mode"], state="readonly").pack(fill="x")
    def save_marker(path):
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        val = "true" if marker_var.get() == "hard mode" else "false"
        content = re.sub(r'"isMapMarkerAsInHardMode"\s*:\s*(true|false)', f'"isMapMarkerAsInHardMode": {val}', content) if '"isMapMarkerAsInHardMode"' in content else content.replace("{", f'"isMapMarkerAsInHardMode": {val}, ', 1)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
    rule_savers.append(save_marker)
    rule_index += 1

    # --- Embedded: Max Contest Attempts ---
    contest_var = tk.StringVar(value="default")
    contest_map = {'default': -1, '1 attempt': 1, '3 attempts': 3, '5 attempts': 5}
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="Max Contest Attempts:").pack(anchor="w", pady=2)
    ttk.Combobox(subframe, textvariable=contest_var, values=list(contest_map.keys()), state="readonly").pack(fill="x")
    def save_contest(path):
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        val = contest_map[contest_var.get()]
        content = re.sub(r'"maxContestAttempts"\s*:\s*-?\d+(\.\d+)?(e[-+]?\d+)?', f'"maxContestAttempts": {val}', content) if '"maxContestAttempts"' in content else content.replace("{", f'"maxContestAttempts": {val}, ', 1)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
    rule_savers.append(save_contest)
    rule_index += 1

    # --- Embedded: Repair Points Cost ---
    repair_cost_var = tk.StringVar(value="free")
    repair_cost_map = {'free': 0, 'paid': 1, '2x': 2, '4x': 4, '6x': 6}
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="Repair Points Cost:").pack(anchor="w", pady=2)
    ttk.Combobox(subframe, textvariable=repair_cost_var, values=list(repair_cost_map.keys()), state="readonly").pack(fill="x")
    def save_repair_cost(path):
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        val = repair_cost_map[repair_cost_var.get()]
        content = re.sub(r'"repairPointsCostFactor"\s*:\s*-?\d+(\.\d+)?(e[-+]?\d+)?', f'"repairPointsCostFactor": {val}', content) if '"repairPointsCostFactor"' in content else content.replace("{", f'"repairPointsCostFactor": {val}, ', 1)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
    rule_savers.append(save_repair_cost)
    rule_index += 1

    # --- Embedded: Repair Points Required ---
    repair_req_var = tk.StringVar(value="default")
    repair_req_map = {'default': 1, '2x less': 0.5, '2x': 2, '4x': 4, '6x': 6}
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="Repair Points Required:").pack(anchor="w", pady=2)
    ttk.Combobox(subframe, textvariable=repair_req_var, values=list(repair_req_map.keys()), state="readonly").pack(fill="x")
    def save_repair_req(path):
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        val = repair_req_map[repair_req_var.get()]
        content = re.sub(r'"repairPointsRequiredFactor"\s*:\s*-?\d+(\.\d+)?(e[-+]?\d+)?', f'"repairPointsRequiredFactor": {val}', content) if '"repairPointsRequiredFactor"' in content else content.replace("{", f'"repairPointsRequiredFactor": {val}, ', 1)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
    rule_savers.append(save_repair_req)
    rule_index += 1

    # --- Embedded: Trailer Availability ---
    trailer_avail_var = tk.StringVar(value="default")
    trailer_avail_map = {"default": 0, "all trailers available": 1}
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="Trailer Availability:").pack(anchor="w", pady=2)
    ttk.Combobox(subframe, textvariable=trailer_avail_var, values=list(trailer_avail_map.keys()), state="readonly").pack(fill="x")
    def save_trailer_avail(path):
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        val = trailer_avail_map[trailer_avail_var.get()]
        content = re.sub(r'"trailerAvailability"\s*:\s*\d+', f'"trailerAvailability": {val}', content) if '"trailerAvailability"' in content else content.replace("{", f'"trailerAvailability": {val}, ', 1)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
    rule_savers.append(save_trailer_avail)
    rule_index += 1

    # --- Embedded: Trailer Selling Price ---
    trailer_sell_var = tk.StringVar(value="normal price")
    trailer_sell_map = {"normal price": 1, "50%": 0.5, "30%": 0.3, "10%": 0.1, "can't be sold": -1}
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="Trailer Selling Price:").pack(anchor="w", pady=2)
    ttk.Combobox(subframe, textvariable=trailer_sell_var, values=list(trailer_sell_map.keys()), state="readonly").pack(fill="x")
    def save_trailer_sell(path):
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        val = trailer_sell_map[trailer_sell_var.get()]
        content = re.sub(r'"trailerSellingFactor"\s*:\s*-?\d+(\.\d+)?(e[-+]?\d+)?', f'"trailerSellingFactor": {val}', content) if '"trailerSellingFactor"' in content else content.replace("{", f'"trailerSellingFactor": {val}, ', 1)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
    rule_savers.append(save_trailer_sell)
    rule_index += 1


    # (placeholder for actual code, injected in the next step)


    # --- Embedded: Addon Selling Price ---
    addon_sell_var = tk.StringVar(value="normal price")
    addon_sell_map = {
        "normal price":1.0,
        "50%":0.5,
        "30%":0.3,
        "10%":0.1,
        "no refunds":0.0
    }
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count,
                  padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="Addon Selling Price:").pack(anchor="w", pady=2)
    ttk.Combobox(subframe, textvariable=addon_sell_var,
             values=list(addon_sell_map.keys()), state="readonly").pack(fill="x")

    def save_addon_sell(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            val = addon_sell_map[addon_sell_var.get()]
            if '"addonSellingFactor"' in content:
                content = re.sub(
                    r'"addonSellingFactor"\s*:\s*-?\d+(\.\d+)?(e[-+]?\d+)?',
                    f'"addonSellingFactor": {val}', content)
            else:
                content = content.replace("{", f'"addonSellingFactor": {val}, ', 1)
            with open(path, "w", encoding="utf-8") as f:
                f.write(content)
        except Exception as e:
            messagebox.showerror("Rule Error", f"Failed to apply Addon Selling Factor: {e}")

    rule_savers.append(save_addon_sell)
    rule_index += 1


    # --- Final Tire Availability Rule with Save + Sync ---
    
    def save_tyre_rule(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            label_to_value = {
                "all tires available": 0,
                "default": 1,
                "highway, allroad": 2,
                "highway, allroad, offroad": 3,
                "no mudtires": 4,
                "no chained tires": 5,
                "random per garage": 6
            }
            value = label_to_value[tyre_var.get()]
            if '"tyreAvailability"' in content:
                content = re.sub(r'"tyreAvailability"\s*:\s*\d+', f'"tyreAvailability": {value}', content)
            else:
                content = content.replace("{", f'"tyreAvailability": {value}, ', 1)
            with open(path, "w", encoding="utf-8") as f:
                f.write(content)
        except Exception as e:
            messagebox.showerror("Rule Error", f"Failed to apply Tire Availability rule: {e}")

    rule_savers.append(save_tyre_rule)


    
    
    
    # --- Embedded: Factor Rules ---

    for label, key, options in FACTOR_RULE_DEFINITIONS:
        var = tk.StringVar(value=list(options.keys())[0])
        FACTOR_RULE_VARS.append((label, key, options, var))
        subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
        subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
        ttk.Label(subframe, text=label + ":").pack(anchor="w", pady=2)
        combo = ttk.Combobox(subframe, textvariable=var, values=list(options.keys()), state="readonly")
        combo.pack(fill="x")
        def make_saver(k=key, m=options, v=var):
            def save(path):
                try:
                    with open(path, "r", encoding="utf-8") as f:
                        content = f.read()
                    value = m[v.get()]
                    if f'"{k}"' in content:
                        content = re.sub(fr'"{k}"\s*:\s*[^,\n]+', f'"{k}": {value}', content)
                    else:
                        content = content.replace("{", f'"{k}": {value}, ', 1)
                    with open(path, "w", encoding="utf-8") as f:
                        f.write(content)
                except Exception as e:
                    messagebox.showerror("Rule Error", f"Failed to apply rule for {k}: {e}")
            return save
        rule_savers.append(make_saver())
        rule_index += 1


    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    ttk.Label(subframe, text="Tire Availability:").pack(anchor="w", pady=2)
    tyre_combo = ttk.Combobox(
        subframe,
        textvariable=tyre_var,
        values=[
            "all tires available",
            "default",
            "highway, allroad",
            "highway, allroad, offroad",
            "no mudtires",
            "no chained tires",
            "random per garage"
        ],
        state="readonly"
    )
    tyre_combo.pack(fill="x")
    rule_index += 1

    def save_tyre_rule(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            label_to_value = {
                "all tires available": 0,
                "default": 1,
                "highway, allroad": 2,
                "highway, allroad, offroad": 3,
                "no mudtires": 4,
                "no chained tires": 5,
                "random per garage": 6
            }
            value = label_to_value[tyre_var.get()]
            if '"tyreAvailability"' in content:
                content = re.sub(r'"tyreAvailability"\s*:\s*\d+', f'"tyreAvailability": {value}', content)
            else:
                content = content.replace("{", f'"tyreAvailability": {value}, ', 1)
            with open(path, "w", encoding="utf-8") as f:
                f.write(content)
        except Exception as e:
            messagebox.showerror("Rule Error", f"Failed to apply Tire Availability rule: {e}")

    rule_savers.append(save_tyre_rule)

    dropdown_widgets["tyreAvailability"] = tyre_combo

    # Load all rule extensions from folder

    rules_folder = os.path.join(os.path.dirname(__file__), "rules_extensions")
    if os.path.isdir(rules_folder):
        for file in glob.glob(os.path.join(rules_folder, "*.py")):
            module_name = os.path.splitext(os.path.basename(file))[0]
            spec = importlib.util.spec_from_file_location(module_name, file)
            if spec and spec.loader:
                module = importlib.util.module_from_spec(spec)
                try:
                    spec.loader.exec_module(module)
                    if hasattr(module, "extend_rules_tab"):
                            # Create a subframe for each module's UI
                            subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
                            subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")

                            module.extend_rules_tab(subframe, {
                                "save_path_var": save_path_var,
                                "messagebox": messagebox,
                                "register_saver": rule_savers.append,
                                "register_file_loader": plugin_loaders.append
                            })

                            rule_index += 1
                except Exception as e:
                    print(f"Error loading rule extension '{module_name}':", e)
    def apply_all_rules():
        make_backup_if_enabled(save_path_var.get())
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")
        d = reverse_difficulty_map.get(difficulty_var.get(), 0)
        t = reverse_truck_avail_map.get(truck_avail_var.get(), 0)
        p = reverse_truck_price_map.get(truck_price_var.get(), 1)
        a = reverse_addon_avail_map.get(addon_avail_var.get(), 0)
        selected_range = addon_amount_var.get()
        amt = None
        if a == 2 and selected_range in addon_amount_ranges:
            min_a, max_a = addon_amount_ranges[selected_range]
            amt = (min_a + max_a) // 2
        modify_rules(path, d, t, p, a, amt)

        for saver in rule_savers:
            saver(path)

        messagebox.showinfo("Success", "All rules applied.")

    ttk.Button(tab_rules, text="Apply All Rules", command=apply_all_rules).pack(pady=20)
    # Add note below Apply All Rules button
    ttk.Label(
        tab_rules,
        text="⚠️ The rules above are only applied if you select 'New Game+' in Game Difficulty Modes.",
        wraplength=500,
        justify="center",
        font=("TkDefaultFont", 9, "bold"),
        foreground="black"
    ).pack(pady=(5, 15))

    # Time tab
    ttk.Label(tab_time, text="Time Preset:").pack(pady=10)
    ttk.Combobox(tab_time, textvariable=time_preset_var, values=list(time_presets.keys()), state="readonly", width=30).pack(pady=5)
    ttk.Checkbutton(tab_time, text="Enable Time Skipping", variable=skip_time_var).pack(pady=10)
    ttk.Label(tab_time, text="⚠️ Time settings only apply in New Game+ mode.", foreground="red", font=("TkDefaultFont", 9, "bold")).pack(pady=(5, 10))
    ttk.Label(tab_time, text="⚠️ To use custom sliders, select 'Custom' from the Time Presets.", foreground="red", font=("TkDefaultFont", 9, "bold")).pack(pady=(5, 10))




    frame_day = ttk.Frame(tab_time)
    frame_day.pack()
    ttk.Label(frame_day, text="Custom Day Time   :").pack(side="left")
    ttk.Scale(frame_day, command=lambda v: custom_day_var.set(round(float(v), 2)), from_=-5.0, to=5.0, variable=custom_day_var, orient="horizontal", length=250).pack(side="left", padx=5)
    day_entry = ttk.Entry(frame_day, textvariable=custom_day_var, width=6)
    day_entry.pack(side="left")
    custom_day_var.set(round(day, 2))

    frame_night = ttk.Frame(tab_time)
    frame_night.pack()
    ttk.Label(frame_night, text="Custom Night Time:").pack(side="left")
    ttk.Scale(frame_night, command=lambda v: custom_night_var.set(round(float(v), 2)), from_=-5.0, to=5.0, variable=custom_night_var, orient="horizontal", length=250).pack(side="left", padx=5)
    night_entry = ttk.Entry(frame_night, textvariable=custom_night_var, width=6)
    night_entry.pack(side="left")
    custom_night_var.set(round(night, 2))

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

    
    if os.path.exists(save_path_var.get()):
        sync_rule_dropdowns(save_path_var.get())
    load_all_custom_rule_vars(save_path_var.get())  # Moved to safe location

    
    # --- Final Sync After GUI is Built ---
    if os.path.exists(save_path_var.get()):
        for loader in plugin_loaders:
            try:
                loader(save_path_var.get())
            except Exception as e:
                print(f"Plugin failed to update GUI on startup: {e}")


    # --- External Addon Rule Integration ---
    subframe = ttk.Frame(rules_grid_frame, relief="groove", padding=5)
    subframe.grid(row=rule_index // rule_col_count, column=rule_index % rule_col_count, padx=5, pady=5, sticky="n")
    extend_rules_tab(subframe, {
        "save_path_var": save_path_var,
        "messagebox": messagebox,
        "register_saver": rule_savers.append,
        "register_file_loader": plugin_loaders.append
    })
    rule_index += 1

    
    if delete_path_on_close_var.get() and os.path.exists(SAVE_PATH_FILE):
        try:
            os.remove(SAVE_PATH_FILE)
        except Exception as e:
            print("[Warning] Could not delete save path:", e)

    root.mainloop()


if __name__ == "__main__":
    launch_gui()
def write_save_file(path, content):
    try:
        with open(path, 'w', encoding='utf-8') as f:
            f.write(content)
    except Exception as e:
        messagebox.showerror("Write Error", f"Failed to save file: {e}")

