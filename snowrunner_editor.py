
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
from tkinter import filedialog, messagebox, ttk
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
    if "make_backup_var" in globals() and make_backup_var.get() and os.path.exists(path):
        save_dir = os.path.dirname(path)
        timestamp = datetime.now().strftime("backup-%d.%m.%Y %H-%M-%S")
        backup_dir = os.path.join(save_dir, "backup", timestamp)
        os.makedirs(backup_dir, exist_ok=True)
        backup_file_path = os.path.join(backup_dir, os.path.basename(path))
        shutil.copy2(path, backup_file_path)


import shutil
from datetime import datetime

def make_backup_if_enabled(path):
    try:
        if os.path.exists(path) and make_backup_var.get():
            save_dir = os.path.dirname(path)
            timestamp = datetime.now().strftime("backup-%d.%m.%Y %H-%M-%S")
            backup_dir = os.path.join(save_dir, "backup", timestamp)
            os.makedirs(backup_dir, exist_ok=True)
            backup_file_path = os.path.join(backup_dir, os.path.basename(path))
            shutil.copy2(path, backup_file_path)
            print(f"[Backup] Backup created at: {backup_file_path}")
        else:
            print("[Backup] Skipped (either disabled or path invalid).")
    except Exception as e:
        print(f"[Backup Error] Failed to create backup: {e}")


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
            if f"_{season:02}_" in key:
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

    ttk.Label(tab, text="External Addon Availbility:").pack(pady=5)
    ttk.Combobox(
        tab,
        textvariable=var,
        values=[
            "default",
            "all addons unlocked",
            "random 5",
            "random 10",
            "each garage random 10"
        ],
        state="readonly"
    ).pack(pady=2)

    label_to_values = {
        "default": {
            "externalAddonAvailability": 0,
            "externalAddonsAmount": 0
        },
        "all addons unlocked": {
            "externalAddonAvailability": 1,
            "externalAddonsAmount": 0
        },
        "random 5": {
            "externalAddonAvailability": 2,
            "externalAddonsAmount": 5
        },
        "random 10": {
            "externalAddonAvailability": 3,
            "externalAddonsAmount": 10
        },
        "each garage random 10": {
            "externalAddonAvailability": 4,
            "externalAddonsAmount": 10
        },
    }

    def save(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()

            values = label_to_values[var.get()]
            for key, val in values.items():
                if f'"{key}"' in content:
                    content = re.sub(
                        rf'"{key}"\s*:\s*[^,\n]+',
                        f'"{key}": {val}',
                        content
                    )
                else:
                    content = content.replace("{", f'"{key}": {val}, ', 1)

            with open(path, "w", encoding="utf-8") as f:
                f.write(content)

        except Exception as e:
            context["messagebox"].showerror("Rule Error", f"Failed to apply rule: {e}")

    
    def sync(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()

            match_avail = re.search(r'"externalAddonAvailability"\s*:\s*(\d+)', content)
            match_amount = re.search(r'"externalAddonsAmount"\s*:\s*(\d+)', content)
            if not match_avail or not match_amount:
                return

            avail = int(match_avail.group(1))
            amount = int(match_amount.group(1))

            for label, (a_val, a_amt) in external_addon_map.items():
                if a_val == avail and a_amt == amount:
                    var.set(label)
                    break
        except Exception as e:
            print(f"[External Addon Rule Sync Error]: {e}")

    context["register_file_loader"](sync)
    sync(context["save_path_var"].get())

    context["register_saver"](save)

def launch_gui():
    global tyre_var, custom_day_var, custom_night_var
    
    plugin_loaders = []
    root = tk.Tk()
    global delete_path_on_close_var, dont_remember_path_var
    delete_path_on_close_var = tk.BooleanVar(value=False)
    dont_remember_path_var = tk.BooleanVar(value=False)
    global tyre_var
    tyre_var = tk.StringVar(value="default")
    global custom_day_var, custom_night_var
    custom_day_var = tk.DoubleVar(value=1.0)
    custom_night_var = tk.DoubleVar(value=1.0)
    # Load icon after root is initialized
    import sys
    if getattr(sys, 'frozen', False):
        base_path = sys._MEIPASS
    else:
        base_path = os.path.abspath('.')
    icon_path = resource_path('app_icon.ico')
    try:
        root.iconbitmap(icon_path)
    except Exception as e:
        print('Failed to set icon:', e)
    try:
        root.iconbitmap(icon_path)
    except Exception as e:
        print('Failed to set icon:', e)
    root.title("SnowRunner Save Editor")

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
        1: "default", 2: "all trucks available", 3: "5–15 trucks/garage",
        4: "unlock rank 10", 5: "unlock rank 20", 6: "unlock rank 30", 7: "locked"
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
    "Always Day": (0.0, -1.0),
    "Always Night": (-1.0, 0.0),
    "Long Day": (0.3, 1.0),
    "Long Night": (1.0, 0.3),
    "Long Day and Long Night": (0.3, 0.3),
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
        file_path = filedialog.askopenfilename(filetypes=[("SnowRunner Save", "*.cfg")])
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
    tab_control.add(tab_rules, text='Rules')
    tab_control.add(tab_time, text='Time')
    tab_settings = ttk.Frame(tab_control)
    tab_control.add(tab_settings, text='Settings')

    tab_control.pack(expand=1, fill='both')

    ttk.Checkbutton(tab_settings, text="Don't remember save file path", variable=dont_remember_path_var).pack(pady=(10, 0))
    ttk.Checkbutton(tab_settings, text="Delete saved path on close", variable=delete_path_on_close_var).pack(pady=(5, 10))


    # Save file tab
    ttk.Label(tab_file, text="Selected Save File:").pack(pady=10)
    ttk.Entry(tab_file, textvariable=save_path_var, width=60).pack(pady=5)
    ttk.Button(tab_file, text="Browse...", command=browse_file).pack(pady=10)
    ttk.Label(
        tab_file,
        text="⚠️ SnowRunner must be closed before editing the save file. Changes made while the game is running may be lost or cause issues.",
        wraplength=500,
        justify="center",
        foreground="red",
        font=("TkDefaultFont", 9, "bold")
    ).pack(pady=(5, 10))
    make_backup_var = tk.BooleanVar(value=True)

    def make_backup_if_enabled(path):
        try:
            if os.path.exists(path) and make_backup_var.get():
                save_dir = os.path.dirname(path)
                timestamp = datetime.now().strftime("backup-%d.%m.%Y %H-%M-%S")
                backup_dir = os.path.join(save_dir, "backup", timestamp)
                os.makedirs(backup_dir, exist_ok=True)
                backup_file_path = os.path.join(backup_dir, os.path.basename(path))
                shutil.copy2(path, backup_file_path)
                print(f"[Backup] Backup created at: {backup_file_path}")
            else:
                print("[Backup] Skipped (either disabled or path invalid).")
        except Exception as e:
            print(f"[Backup Error] Failed to create backup: {e}")


    ttk.Checkbutton(tab_file, text="Make a Backup", variable=make_backup_var).pack(pady=(0, 10))
    ttk.Label(tab_file, text="Backups are created in the same directory as the save file in a folder named 'backup'.", font=("TkDefaultFont", 9), foreground="black").pack(pady=(0, 10))

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
        "Season 15: Oil & Dirt (Quebec)"
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

    ttk.Label(tab_missions, text="Other Season (e.g. 16, 17...):").pack(pady=5)
    ttk.Entry(tab_missions, textvariable=other_season_var).pack(pady=5)

    ttk.Label(tab_missions, text="Base Game Maps:", font=("TkDefaultFont", 10, "bold")).pack(pady=5)
    base_maps = [("Michigan", "US_01"), ("Alaska", "US_02"), ("Taymyr", "RU_02")]
    base_map_vars = []
    for name, map_id in base_maps:
        var = tk.IntVar()
        base_map_vars.append((map_id, var))
        ttk.Checkbutton(tab_missions, text=name, variable=var).pack(anchor='w', padx=30)

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
    sell_map = {"normal price": 1, "50%": 0.5, "30%": 0.30000001192092896, "10%": 0.10000000149011612, "can't be sold": -1}
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
    repair_map = {"free": -1, "normal price": 0, "2x": 2, "4x": 4, "6x": 6}
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
    ttk.Label(tab_time, text="👉 To use custom sliders, select 'Custom' from the Time Presets.", foreground="red", font=("TkDefaultFont", 9, "bold")).pack(pady=(5, 10))




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
