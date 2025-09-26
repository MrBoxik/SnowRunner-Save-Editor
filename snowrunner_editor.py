# Combined SnowRunner Editor with Minesweeper and Fog Tool in one file

# --- Inlined: minesweeper_patched.py ---

import tkinter as tk
from tkinter import ttk
from tkinter import messagebox
import requests


SAVE_FILE = "minesweeper_save.json"

def load_progress():
    if not os.path.exists(SAVE_FILE):
        return {"level": 1, "title": "", "has_bronze": False, "has_silver": False, "has_gold": False}
    with open(SAVE_FILE, "r") as f:
        return json.load(f)

def save_progress(data):
    with open(SAVE_FILE, "w") as f:
        json.dump(data, f, indent=4)

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
                btn.bind("<Button-3>", lambda e, r=r, c=c: self.toggle_flag(r, c))
                btn.grid(row=r, column=c)
                row.append(Cell(r, c, btn))
            self.cells.append(row)

    def place_mines(self, safe_r, safe_c):
        exclude = {(safe_r + dr, safe_c + dc) for dr in (-1, 0, 1) for dc in (-1, 0, 1)}
        while len(self.mine_locations) < self.mines:
            r, c = random.randrange(self.size), random.randrange(self.size)
            if (r, c) not in exclude and not self.cells[r][c].has_mine:
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
        if self.level == 1: self.data["has_bronze"] = True; self.level = 2
        elif self.level == 2: self.data["has_silver"] = True; self.level = 3
        elif self.level == 3: self.data["has_gold"] = True
        self.data["level"] = self.level
        save_progress(self.data)
        self.start_level()

MINESWEEPER_AVAILABLE = True

import os
import struct
import zlib
import traceback
from PIL import Image, ImageTk, ImageDraw

# ---------- BitWriter ----------
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


# ---------- Path handling ----------
def load_editor_last_path():
    """Load last used save path from SnowRunner Editor (.snowrunner_save_path.txt).
    .snowrunner_save_path.txt traditionally contains a full path to CompleteSave.cfg,
    so we return dirname(full_path) (the folder)."""
    cfg_file = os.path.join(os.path.expanduser('~'), '.snowrunner_save_path.txt')
    if os.path.exists(cfg_file):
        try:
            with open(cfg_file, 'r', encoding='utf-8') as f:
                full_path = f.read().strip()
            if full_path:
                return os.path.dirname(full_path)
        except Exception:
            pass
    return None

def load_initial_path():
    """Priority:
      1) .snowrunner_save_path.txt (if exists and points to existing folder)
      2) last_dir.txt (in tool folder)
      3) os.getcwd()
    """
    # 1) SnowRunner editor path first
    editor_path = load_editor_last_path()
    if editor_path and os.path.isdir(editor_path):
        return editor_path

    # 2) FogTool last_dir.txt
    last_dir_file = os.path.join(os.path.dirname(__file__), "last_dir.txt")
    if os.path.exists(last_dir_file):
        try:
            with open(last_dir_file, "r", encoding="utf-8") as f:
                ld = f.read().strip()
            if ld and os.path.isdir(ld):
                return ld
        except:
            pass

    # 3) Fallback
    return os.getcwd()


# ---------- Main App ----------
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
        self.last_dir_file = os.path.join(os.path.dirname(__file__), "last_dir.txt")

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
        self.overlay_tk = None
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
        self.notebook.pack(fill="both", expand=True)

        self.editor_frame = ttk.Frame(self.notebook)
        self._build_editor_ui(self.editor_frame)
        self.notebook.add(self.editor_frame, text="Editor")

        self.automation_frame = ttk.Frame(self.notebook)
        self._build_automation_ui(self.automation_frame)
        self.notebook.add(self.automation_frame, text="Automation")

    # ---------- Helpers for saving paths ----------
    def _update_last_paths(self, folder_path):
        """Update both FogTool's last_dir.txt (folder only) and the SnowRunner
        .snowrunner_save_path.txt (writes folder/CompleteSave.cfg so editor expects full-file entry)."""
        # Write last_dir.txt (folder only)
        try:
            with open(self.last_dir_file, "w", encoding="utf-8") as f:
                f.write(folder_path)
        except Exception:
            # don't crash if unable to write (permissions, read-only location)
            pass

        # Write .snowrunner_save_path.txt in user's home; write full path with filename to be compatible with SnowRunner
        try:
            editor_cfg = os.path.join(os.path.expanduser("~"), ".snowrunner_save_path.txt")
            # write a representative path to CompleteSave.cfg inside the folder
            example_savefile = os.path.join(folder_path, "CompleteSave.cfg")
            with open(editor_cfg, "w", encoding="utf-8") as f:
                f.write(example_savefile)
        except Exception:
            # fail silently; writing to Program Files may require elevation
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
        seasons = [
            ("us_01", "Michigan"),
            ("us_02", "Alaska"),
            ("ru_02", "Taymyr"),
            ("ru_03", "Season 1: Search & Recover (Kola Peninsula)"),
            ("us_04", "Season 2: Explore & Expand (Yukon)"),
            ("us_03", "Season 3: Locate & Deliver (Wisconsin)"),
            ("ru_04", "Season 4: New Frontiers (Amur)"),
            ("ru_05", "Season 5: Build & Dispatch (Don)"),
            ("us_06", "Season 6: Haul & Hustle (Maine)"),
            ("us_07", "Season 7: Compete & Conquer (Tennessee)"),
            ("ru_08", "Season 8: Grand Harvest (Glades)"),
            ("us_09", "Season 9: Renew & Rebuild (Ontario)"),
            ("us_10", "Season 10: Fix & Connect (British Columbia)"),
            ("us_11", "Season 11: Lights & Cameras (Scandinavia)"),
            ("us_12", "Season 12: Public Energy (North Carolina)"),
            ("ru_13", "Season 13: Dig & Drill (Almaty)"),
            ("us_14", "Season 14: Reap & Sow (Austria)"),
            ("us_15", "Season 15: Oil & Dirt (Quebec)"),
            ("us_16", "Season 16: High Voltage (Washington)"),
        ]
        for code, name in seasons:
            v = tk.IntVar(value=0)
            ttk.Checkbutton(self.season_frame, text=name, variable=v).pack(anchor="w")
            self.season_checks[code] = v

        ttk.Label(self.season_frame, text="Other Season number (e.g., 17,18,19):").pack(anchor="w")
        self.extra_season_var = tk.StringVar()
        ttk.Entry(self.season_frame, textvariable=self.extra_season_var).pack(anchor="w", fill="x")

        # Show the currently chosen save folder (derived at startup or selected later)
        self.auto_status_var = tk.StringVar(value=f"Save folder (auto): {self.save_dir}")
        ttk.Label(parent, textvariable=self.auto_status_var).pack(fill="x", pady=6)

    # ---------------- Info popup ----------------
    def show_info(self):
        info_text = """Fog Image Tool — Tutorial

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
- US_01 → Michigan  
- US_02 → Alaska  
- RU_02 → Taymyr  
- RU_03 → Season 1: Search & Recover (Kola Peninsula)  
- US_03 → Season 3: Locate & Deliver (Wisconsin)  
- US_04 → Season 2: Explore & Expand (Yukon)  
- RU_04 → Season 4: New Frontiers (Amur)  
- RU_05 → Season 5: Build & Dispatch (Don)  
- US_06 → Season 6: Haul & Hustle (Maine)  
- US_07 → Season 7: Compete & Conquer (Tennessee)  
- RU_08 → Season 8: Grand Harvest (Glades)  
- US_09 → Season 9: Renew & Rebuild (Ontario)  
- US_10 → Season 10: Fix & Connect (British Columbia)  
- US_11 → Season 11: Lights & Cameras (Scandinavia)  
- US_12 → Season 12: Public Energy (North Carolina)  
- RU_13 → Season 13: Dig & Drill (Almaty)  
- US_14 → Season 14: Reap & Sow (Austria)  
- US_15 → Season 15: Oil & Dirt (Quebec)  
- US_16 → Season 16: High Voltage (Washington)
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
            overlay_resized = self.overlay_img.resize((sw, sh), Image.Resampling.LANCZOS).convert("RGBA")
            self.overlay_tk = ImageTk.PhotoImage(overlay_resized)
            ox = self.offset_x + int(self.overlay_offset[0] * self.scale)
            oy = self.offset_y + int(self.overlay_offset[1] * self.scale)
            self.canvas.create_image(ox, oy, anchor="nw", image=self.overlay_tk)

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
        if not self.overlay_img or not self.current_image_L:
            return
        base = self.current_image_L.copy()
        bw, bh = base.size
        ow, oh = self.overlay_img.size
        new_w = max(1, int(ow * self.overlay_scale))
        new_h = max(1, int(oh * self.overlay_scale))
        overlay_resized = self.overlay_img.resize((new_w, new_h), Image.Resampling.LANCZOS)
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

class FogToolFrame(ttk.Frame):
    def __init__(self, parent, initial_save_dir=None):
        super().__init__(parent)
        self.app = FogToolApp(self, initial_save_dir=initial_save_dir)
        self.app.pack(fill="both", expand=True)


# ---------------- Run standalone ----------------

# --- Original editor (snowrunner_editor.py) ---

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
            max_backups = 20

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
        money, rank, difficulty, truck_avail, skip_time, day, night, truck_price = get_file_info(content)

        # If day or night is None → treat as corruption
        if day is None or night is None:
            raise ValueError("Missing time settings")

        # If parsing succeeds fully → save path is valid
        save_path_var.set(last_path)

    except Exception:
        messagebox.showerror(
            "Save File Corrupted",
            f"Could not load save file:\n{last_path}\n\nThe file appears to be corrupted or incomplete."
        )
        save_path_var.set("")


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
            # Match integers, floats, booleans, or null
            match = re.search(rf'"{re.escape(key)}"\s*:\s*("?[\w\.\-]+"?)', content)
            if match:
                return match.group(1).strip('"')
            return None

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
    global FACTOR_RULE_VARS, rule_savers, plugin_loaders

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


    save_path_var = tk.StringVar()
    try_autoload_last_save(save_path_var)
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
    time_day_var = tk.StringVar()   
    time_night_var = tk.StringVar()

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
            money, rank, difficulty, truck_avail, skip_time, day, night, truck_price = get_file_info(content)

            # update simple builtins if those vars exist
            if "money_var" in globals() and money is not None:
                money_var.set(str(money))
            if "rank_var" in globals() and rank is not None:
                rank_var.set(str(rank))

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

            # --- Time settings (use the actual GUI var names used in your time tab) ---
            if "custom_day_var" in globals():
                try:
                    custom_day_var.set(round(float(day), 2) if day is not None else 1.0)
                except Exception:
                    custom_day_var.set(1.0)

            if "custom_night_var" in globals():
                try:
                    custom_night_var.set(round(float(night), 2) if night is not None else 1.0)
                except Exception:
                    custom_night_var.set(1.0)

            if "skip_time_var" in globals():
                skip_time_var.set(bool(skip_time))

            # also push values to the raw stringvars so they're in sync too
            if "time_day_var" in globals() and day is not None:
                time_day_var.set(str(day))
            if "time_night_var" in globals() and night is not None:
                time_night_var.set(str(night))

            # detect matching preset
            if "time_preset_var" in globals():
                matched_preset = None
                try:
                    for preset_name, (p_day, p_night) in time_presets.items():
                        if (
                            day is not None and night is not None
                            and float(day) == float(p_day)
                            and float(night) == float(p_night)
                        ):
                            matched_preset = preset_name
                            break
                except Exception:
                    matched_preset = None
                time_preset_var.set(matched_preset if matched_preset else "Custom")
                
            # --- other optional UI flags (if present) ---
            if "other_season_var" in globals():
                other_season_var.set("default")
            if "garage_refuel_var" in globals():
                # some builds look for different string; simple heuristic:
                garage_refuel_var.set('"enableGarageRefuel": true' in content)

        except Exception as e:
            print("Failed to sync all rules:", e)

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
        file_path = filedialog.askopenfilename(filetypes=[("SnowRunner Save", "*.cfg *.dat")])
        if not file_path:
            return

        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()

            # Try parsing the save — if it fails or is incomplete, treat as corrupted
            m, r, d, t, s, day, night, tp = get_file_info(content)

            if day is None or night is None:
                raise ValueError("Missing time settings")

            # ✅ Only reach this point if file is valid
            save_path_var.set(file_path)

            # Call plugin GUI loaders to refresh their values from file
            for loader in plugin_loaders:
                try:
                    loader(save_path_var.get())
                except Exception as e:
                    print(f"Plugin failed to update GUI from file: {e}")

            save_path(file_path)

            # Update GUI with parsed values
            money_var.set(str(m))
            rank_var.set(str(r))
            difficulty_var.set(difficulty_map.get(d, "Normal"))
            truck_avail_var.set(truck_avail_map.get(t, "default"))
            truck_price_var.set(truck_price_map.get(tp, "default"))
            skip_time_var.set(s)

            match = next(
                (k for k, v in time_presets.items()
                 if abs(day - v[0]) < 0.01 and abs(night - v[1]) < 0.01),
                "Custom"
            )
            time_preset_var.set(match)

        except Exception:
            messagebox.showerror(
                "Save File Corrupted",
                f"Could not load save file:\n{file_path}\n\nThe file appears to be corrupted or incomplete."
            )
            save_path_var.set("")


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
        full_backup_var.set(cfg.get("full_backup", True))
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
        foreground="red",
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
        path = save_path_var.get()
        if not os.path.exists(path):
            return messagebox.showerror("Error", "Save file not found.")

        # Load original save
        with open(path, "r", encoding="utf-8") as f:
            original_content = f.read()

        # Resolve dropdown values
        d = reverse_difficulty_map.get(difficulty_var.get(), 0)
        t = reverse_truck_avail_map.get(truck_avail_var.get(), 0)
        p = reverse_truck_price_map.get(truck_price_var.get(), 1)
        a = reverse_addon_avail_map.get(addon_avail_var.get(), 0)
        selected_range = addon_amount_var.get()
        amt = None
        if a == 2 and selected_range in addon_amount_ranges:
            min_a, max_a = addon_amount_ranges[selected_range]
            amt = (min_a + max_a) // 2

        # --- Apply rules to a copy in memory ---

        tmp_path = path + ".tmpcheck"
        shutil.copy2(path, tmp_path)  # copy original for safe in-memory edit

        # apply main rules
        modify_rules(tmp_path, d, t, p, a, amt)
        # apply all extra rule savers
        for saver in rule_savers:
            saver(tmp_path)

        # read modified content
        with open(tmp_path, "r", encoding="utf-8") as f:
            modified_content = f.read()
        os.remove(tmp_path)  # cleanup

        # --- Diff check ---
        if original_content == modified_content:
            messagebox.showinfo("Notice", "No changes to apply.")
            return

        def strip_difficulty(text):
            """
            Normalize all keys that are considered 'difficulty-related' so
            changes to them don't count as 'other' changes.
            """
            keys = [
                "gameDifficultyMode",
                "isHardMode",
                "isMapMarkerAsInHardMode",   # optional: ignore other difficulty-linked flags
            ]
            out = text
            val_pattern = r'(?:-?\d+(\.\d+)?(e[-+]?\d+)?|true|false|null)'
            for key in keys:
                out = re.sub(
                    rf'"{key}"\s*:\s*{val_pattern}',
                    f'"{key}":X',
                    out,
                    flags=re.IGNORECASE
                )
            return out

        if strip_difficulty(original_content) == strip_difficulty(modified_content):
            # Only difficulty-related keys changed → allow silently
            make_backup_if_enabled(path)
        elif d != 2:  # not New Game+
            proceed = messagebox.askyesno(
                "Proceed Anyway?",
                "Changing rules when Game Difficulty is not set to 'New Game+' "
                "is not recommended and might cause issues.\n\n"
                "Do you want to continue and save anyway?"
            )
            if not proceed:
                # user cancelled — restore GUI controls to what's in the save file
                try:
                    sync_all_rules(path)
                except Exception as e:
                    print("Failed to sync all rules after cancel:", e)
                return
            make_backup_if_enabled(path)
        else:
            # New Game+ → always safe
            make_backup_if_enabled(path)

        # --- Write real changes ---
        with open(path, "w", encoding="utf-8") as f:
            f.write(modified_content)

        messagebox.showinfo("Success", "All rules applied.")


    ttk.Button(tab_rules, text="Apply All Rules", command=apply_all_rules).pack(pady=20)
    # Add note below Apply All Rules button
    ttk.Label(
        tab_rules,
        text="⚠️ The rules above are only applied if you select 'New Game+' in Game Difficulty Modes.",
        wraplength=500,
        justify="center",
        font=("TkDefaultFont", 9, "bold"),
        foreground="red"
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

    # --- Auto-sync on startup if a valid save file is remembered ---
    if save_path_var.get() and os.path.exists(save_path_var.get()):
        try:
            sync_all_rules(save_path_var.get())
            print("[DEBUG] Auto-sync applied on startup.")
        except Exception as e:
            print("[Warning] Auto-sync failed:", e)

    root.mainloop()



if __name__ == "__main__":
    launch_gui()
def write_save_file(path, content):
    try:
        with open(path, 'w', encoding='utf-8') as f:
            f.write(content)
    except Exception as e:
        messagebox.showerror("Write Error", f"Failed to save file: {e}")


# Alias for compatibility with editor code
FogToolFrame = FogToolApp
