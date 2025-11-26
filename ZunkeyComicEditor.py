import tkinter as tk
from tkinter import filedialog, colorchooser, messagebox, ttk, scrolledtext
from PIL import Image, ImageTk, ImageDraw, ImageFont
import sys
import os
import traceback
import copy
import json
import base64
import io

# =========================================================
#  設定・定数
# =========================================================

APP_NAME = "Zunkey Comic Editor"
APP_VERSION = "0.1 Beta"

FONT_Config = {
    "メイリオ": {"tk": "Meiryo", "file": "meiryo.ttc"},
    "MS ゴシック": {"tk": "MS Gothic", "file": "msgothic.ttc"},
    "MS 明朝": {"tk": "MS Mincho", "file": "msmincho.ttc"},
    "游ゴシック": {"tk": "Yu Gothic", "file": "YuGothB.ttc"},
    "Arial": {"tk": "Arial", "file": "arial.ttf"}
}
FONT_NAMES = list(FONT_Config.keys())

ALIGN_H_OPTIONS = ["右寄せ (Right)", "中央 (Center)", "左寄せ (Left)"]
ALIGN_V_OPTIONS = ["上寄せ (Top)", "中央 (Middle)", "下寄せ (Bottom)"]

# Pillowのバージョン互換対応
try:
    RESAMPLE_LANCZOS = Image.Resampling.LANCZOS
    RESAMPLE_BICUBIC = Image.Resampling.BICUBIC
    RESAMPLE_BILINEAR = Image.Resampling.BILINEAR
except AttributeError:
    RESAMPLE_LANCZOS = Image.LANCZOS
    RESAMPLE_BICUBIC = Image.BICUBIC
    RESAMPLE_BILINEAR = Image.BILINEAR

# =========================================================
#  メインアプリケーションクラス
# =========================================================

class ZunComiApp:
    def __init__(self, root):
        self.root = root
        self.root.title(f"{APP_NAME} v{APP_VERSION}")
        self.root.geometry("1280x850")
        self.root.state('zoomed') 

        # --- データ管理 ---
        self.original_image = None
        self.display_image = None
        self.img_scale = 1.0
        self.offset_x = 0
        self.offset_y = 0
        
        self.cache_bg_image = None
        self.cache_canvas_size = (0, 0)
        self.hit_targets = [] 
        
        self.brush_active = False
        self.brush_color = "#ffffff"
        self.text_color = "#000000"
        self.text_outline_color = "#ffffff"
        
        self.dropper_active = False
        self.strokes = [] 

        self.text_objects = [] 
        self.placed_images = [] 
        
        self.asset_images = [] 
        self.asset_thumbnails = [] 
        self.asset_frames = []
        
        self.selected_item = None 
        self.placing_text_content = None 
        self.placing_image_id = None 
        
        self.drag_data = {"x": 0, "y": 0, "item": None}
        self.font_names = list(FONT_Config.keys())

        self.history_stack = []
        self.redo_stack = []
        self.max_history = 20

        self._setup_ui()
        self._bind_shortcuts()

    def _bind_shortcuts(self):
        self.root.bind("<Control-z>", self.undo)
        self.root.bind("<Control-y>", self.redo)

    # --- スマートスライダー ---
    def create_smart_slider(self, parent, label_text, from_, to, initial_val, callback):
        container = tk.Frame(parent, bg="#f0f0f0", pady=2)
        container.pack(fill=tk.X)
        top_row = tk.Frame(container, bg="#f0f0f0"); top_row.pack(fill=tk.X)
        tk.Label(top_row, text=label_text, bg="#f0f0f0", font=("Meiryo", 9)).pack(side=tk.LEFT)
        var = tk.IntVar(value=initial_val)
        entry = tk.Entry(top_row, textvariable=var, width=5, justify="right"); entry.pack(side=tk.RIGHT)
        def on_entry_commit(e): callback(); return "break"
        entry.bind("<Return>", on_entry_commit); entry.bind("<FocusOut>", lambda e: callback())
        bot_row = tk.Frame(container, bg="#f0f0f0"); bot_row.pack(fill=tk.X)
        def increment():
            if var.get() < to: var.set(var.get() + 1); callback()
        def decrement():
            if var.get() > from_: var.set(var.get() - 1); callback()
        def on_scale_move(val):
            var.set(int(float(val))); callback()
        tk.Button(bot_row, text="-", command=decrement, width=2, bg="white", relief="solid", bd=1).pack(side=tk.LEFT)
        tk.Scale(bot_row, from_=from_, to=to, orient=tk.HORIZONTAL, variable=var, showvalue=0, command=on_scale_move, bg="#f0f0f0", bd=0, highlightthickness=0).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
        tk.Button(bot_row, text="+", command=increment, width=2, bg="white", relief="solid", bd=1).pack(side=tk.LEFT)
        return var

    # --- スマートスクロール ---
    def setup_mouse_scroll(self, widget):
        def _on_mousewheel(event): widget.yview_scroll(int(-1*(event.delta/120)), "units")
        def _bind_wheel(event): self.root.bind_all("<MouseWheel>", _on_mousewheel)
        def _unbind_wheel(event): self.root.unbind_all("<MouseWheel>")
        widget.bind("<Enter>", _bind_wheel); widget.bind("<Leave>", _unbind_wheel)

    # ---------------------------------------------------------
    # UI構築
    # ---------------------------------------------------------
    def _setup_ui(self):
        left_container = tk.Frame(self.root, width=360, bg="#f0f0f0")
        left_container.pack(side=tk.LEFT, fill=tk.Y)
        left_container.pack_propagate(False)
        self.left_canvas = tk.Canvas(left_container, bg="#f0f0f0", highlightthickness=0)
        left_scrollbar = tk.Scrollbar(left_container, orient="vertical", command=self.left_canvas.yview)
        self.left_scrollable_frame = tk.Frame(self.left_canvas, bg="#f0f0f0", padx=10, pady=10)
        self.left_scrollable_frame.bind("<Configure>", lambda e: self.left_canvas.configure(scrollregion=self.left_canvas.bbox("all")))
        self.left_canvas.create_window((0, 0), window=self.left_scrollable_frame, anchor="nw", width=340)
        self.left_canvas.configure(yscrollcommand=left_scrollbar.set)
        self.left_canvas.pack(side="left", fill="both", expand=True); left_scrollbar.pack(side="right", fill="y")
        self.setup_mouse_scroll(self.left_canvas)

        right_container = tk.Frame(self.root, width=220, bg="#e0e0e0", padx=5, pady=5)
        right_container.pack(side=tk.RIGHT, fill=tk.Y)
        right_container.pack_propagate(False)
        self.canvas_frame = tk.Frame(self.root, bg="#333")
        self.canvas_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.canvas = tk.Canvas(self.canvas_frame, bg="#333", highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True)

        sidebar = self.left_scrollable_frame

        # 1. ファイル操作
        tk.Label(sidebar, text="1. ファイル操作", font=("Meiryo", 10, "bold"), bg="#f0f0f0").pack(anchor="w", pady=(0, 5))
        btn_proj_frame = tk.Frame(sidebar, bg="#f0f0f0"); btn_proj_frame.pack(fill=tk.X, pady=2)
        tk.Button(btn_proj_frame, text="プロジェクトを開く", command=self.load_project, bg="#ffdddd").pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 2))
        tk.Button(btn_proj_frame, text="プロジェクト保存", command=self.save_project, bg="#ffdddd").pack(side=tk.RIGHT, fill=tk.X, expand=True, padx=(2, 0))
        btn_file_frame = tk.Frame(sidebar, bg="#f0f0f0"); btn_file_frame.pack(fill=tk.X, pady=2)
        tk.Button(btn_file_frame, text="画像を開く (新規)", command=self.load_image, bg="#add8e6").pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 2))
        tk.Button(btn_file_frame, text="画像書出 (PNG)", command=self.save_image, bg="#90ee90").pack(side=tk.RIGHT, fill=tk.X, expand=True, padx=(2, 0))
        undo_frame = tk.Frame(sidebar, bg="#f0f0f0"); undo_frame.pack(fill=tk.X, pady=2)
        tk.Button(undo_frame, text="↶ 戻す (Ctrl+Z)", command=lambda: self.undo(None), bg="white").pack(side=tk.LEFT, fill=tk.X, expand=True)
        tk.Button(undo_frame, text="↷ 進む (Ctrl+Y)", command=lambda: self.redo(None), bg="white").pack(side=tk.RIGHT, fill=tk.X, expand=True)

        # 2. 消しゴム
        tk.Label(sidebar, text="2. 消しゴム", font=("Meiryo", 10, "bold"), bg="#f0f0f0").pack(anchor="w", pady=(10,0))
        eraser_frame = tk.Frame(sidebar, bg="#f0f0f0"); eraser_frame.pack(fill=tk.X, pady=2)
        color_info = tk.Frame(eraser_frame, bg="#f0f0f0"); color_info.pack(fill=tk.X)
        tk.Label(color_info, text="色:", bg="#f0f0f0").pack(side=tk.LEFT)
        self.lbl_eraser_preview = tk.Label(color_info, bg=self.brush_color, width=4, relief="solid", borderwidth=1); self.lbl_eraser_preview.pack(side=tk.LEFT, padx=5)
        self.btn_dropper = tk.Button(eraser_frame, text="スポイト", bg="lightgray", command=self.toggle_dropper_mode); self.btn_dropper.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=2)
        self.btn_brush_mode = tk.Button(eraser_frame, text="消しゴムON", bg="lightgray", command=self.toggle_brush_mode); self.btn_brush_mode.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=2)
        self.var_brush_size = self.create_smart_slider(eraser_frame, "太さ:", 1, 100, 20, lambda: None)

        # 3. 文字入力
        tk.Label(sidebar, text="3. 文字入力", font=("Meiryo", 10, "bold"), bg="#f0f0f0").pack(anchor="w", pady=(10,0))
        self.input_text_box = scrolledtext.ScrolledText(sidebar, height=5, width=30, wrap=tk.WORD); self.input_text_box.pack(pady=5)
        btn_input_frame = tk.Frame(sidebar, bg="#f0f0f0"); btn_input_frame.pack(fill=tk.X)
        self.btn_register = tk.Button(btn_input_frame, text="リストに登録", command=self.register_text, bg="#ddd"); self.btn_register.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.btn_update = tk.Button(btn_input_frame, text="内容更新", command=self.update_placed_object_text, bg="#ffebcd", state=tk.DISABLED); self.btn_update.pack(side=tk.RIGHT, fill=tk.X, expand=True)

        # 4. 登録テキスト
        tk.Label(sidebar, text="4. 登録テキスト", font=("Meiryo", 10, "bold"), bg="#f0f0f0").pack(anchor="w", pady=(10,0))
        list_frame = tk.Frame(sidebar, bg="#f0f0f0"); list_frame.pack(fill=tk.X, pady=5)
        sb = tk.Scrollbar(list_frame, orient=tk.VERTICAL)
        self.text_listbox = tk.Listbox(list_frame, height=4, yscrollcommand=sb.set, exportselection=False)
        sb.config(command=self.text_listbox.yview); self.text_listbox.pack(side=tk.LEFT, fill=tk.X, expand=True); sb.pack(side=tk.RIGHT, fill=tk.Y)
        self.text_listbox.bind('<<ListboxSelect>>', self.on_list_select)
        list_btn_frame = tk.Frame(sidebar, bg="#f0f0f0"); list_btn_frame.pack(fill=tk.X)
        self.btn_list_update = tk.Button(list_btn_frame, text="リスト更新", command=self.update_list_text, bg="#ffebcd", state=tk.DISABLED, width=10); self.btn_list_update.pack(side=tk.LEFT, padx=2)
        tk.Button(list_btn_frame, text="リスト削除", command=self.delete_list_text, bg="#ffcccc", width=10).pack(side=tk.RIGHT, padx=2)

        # 5. テキスト設定
        tk.Label(sidebar, text="5. テキスト設定 (選択中)", font=("Meiryo", 10, "bold"), bg="#f0f0f0").pack(anchor="w", pady=(10,0))
        prop_row1 = tk.Frame(sidebar, bg="#f0f0f0"); prop_row1.pack(fill=tk.X)
        self.lbl_text_color_preview = tk.Label(prop_row1, bg=self.text_color, width=3, relief="solid", borderwidth=1); self.lbl_text_color_preview.pack(side=tk.LEFT, padx=2)
        tk.Button(prop_row1, text="色", command=self.choose_text_color, width=3).pack(side=tk.LEFT, padx=2)
        self.lbl_outline_color_preview = tk.Label(prop_row1, bg=self.text_outline_color, width=3, relief="solid", borderwidth=1); self.lbl_outline_color_preview.pack(side=tk.LEFT, padx=(10, 2))
        tk.Button(prop_row1, text="縁色", command=self.choose_outline_color, width=4).pack(side=tk.LEFT, padx=2)
        prop_row_font = tk.Frame(sidebar, bg="#f0f0f0"); prop_row_font.pack(fill=tk.X, pady=2)
        self.combo_font = ttk.Combobox(prop_row_font, values=self.font_names, state="readonly", width=18); self.combo_font.current(0); self.combo_font.pack(side=tk.LEFT, padx=2)
        self.combo_font.bind("<<ComboboxSelected>>", self.on_property_change)
        tk.Button(prop_row_font, text="+", command=self.add_custom_font, width=2).pack(side=tk.LEFT)
        self.var_font_size = self.create_smart_slider(sidebar, "サイズ:", 10, 300, 40, self.on_property_change)
        self.var_line_spacing = self.create_smart_slider(sidebar, "行間(%):", 0, 300, 20, self.on_property_change)
        self.var_char_spacing = self.create_smart_slider(sidebar, "文字間(%):", -50, 200, 0, self.on_property_change)
        self.var_outline_width = self.create_smart_slider(sidebar, "縁太さ:", 0, 20, 0, self.on_property_change)
        self.var_text_angle = self.create_smart_slider(sidebar, "回転(°):", -180, 180, 0, self.on_property_change)
        self.var_vertical = tk.BooleanVar(value=True)
        tk.Checkbutton(sidebar, text="縦書き", variable=self.var_vertical, command=self.on_property_change, bg="#f0f0f0").pack(anchor="w")
        align_f = tk.Frame(sidebar, bg="#f0f0f0"); align_f.pack(fill=tk.X)
        self.combo_align_h = ttk.Combobox(align_f, values=ALIGN_H_OPTIONS, state="readonly", width=13); self.combo_align_h.current(0); self.combo_align_h.pack(side=tk.LEFT)
        self.combo_align_h.bind("<<ComboboxSelected>>", self.on_property_change)
        self.combo_align_v = ttk.Combobox(align_f, values=ALIGN_V_OPTIONS, state="readonly", width=13); self.combo_align_v.current(0); self.combo_align_v.pack(side=tk.LEFT)
        self.combo_align_v.bind("<<ComboboxSelected>>", self.on_property_change)

        # 6. 画像設定
        tk.Label(sidebar, text="6. 画像設定 (選択中)", font=("Meiryo", 10, "bold"), bg="#f0f0f0").pack(anchor="w", pady=(15,0))
        self.var_img_scale = self.create_smart_slider(sidebar, "倍率(%):", 10, 500, 100, self.on_image_property_change)
        self.var_img_angle = self.create_smart_slider(sidebar, "回転(°):", -180, 180, 0, self.on_image_property_change)
        tk.Button(sidebar, text="選択アイテムを削除", command=self.delete_selected_item, bg="#ffcccc").pack(fill=tk.X, pady=10)

        # 右サイドバー
        right_header = tk.Frame(right_container, bg="#e0e0e0", padx=5, pady=5); right_header.pack(side=tk.TOP, fill=tk.X)
        tk.Label(right_header, text="画像素材 (描き文字)", font=("Meiryo", 9, "bold"), bg="#e0e0e0").pack(anchor="w")
        tk.Button(right_header, text="＋ 画像を追加", command=self.add_asset_image, bg="white").pack(fill=tk.X, pady=5)
        self.asset_canvas = tk.Canvas(right_container, bg="#e0e0e0", highlightthickness=0)
        right_scrollbar = tk.Scrollbar(right_container, orient="vertical", command=self.asset_canvas.yview)
        self.scrollable_frame = tk.Frame(self.asset_canvas, bg="#e0e0e0")
        self.scrollable_frame.bind("<Configure>", lambda e: self.asset_canvas.configure(scrollregion=self.asset_canvas.bbox("all")))
        self.asset_canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw", width=200)
        self.asset_canvas.configure(yscrollcommand=right_scrollbar.set)
        self.asset_canvas.pack(side="left", fill="both", expand=True); right_scrollbar.pack(side="right", fill="y")
        self.setup_mouse_scroll(self.asset_canvas)

        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<B1-Motion>", self.on_canvas_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_canvas_release)
        self.root.bind("<Configure>", self.on_resize_window)

    # ---------------------------------------------------------
    # ロジック
    # ---------------------------------------------------------
    def add_asset_image(self):
        file_paths = filedialog.askopenfilenames(filetypes=[("Image files", "*.png;*.jpg;*.jpeg")])
        if not file_paths: return
        for path in file_paths:
            try:
                img = Image.open(path).convert("RGBA")
                self.asset_images.append(img)
                asset_id = len(self.asset_images) - 1
                thumb_w = 140; aspect = img.height / img.width; thumb_h = int(thumb_w * aspect)
                if thumb_h > 140: thumb_h = 140
                thumb_pil = img.resize((thumb_w, thumb_h), RESAMPLE_LANCZOS)
                thumb_tk = ImageTk.PhotoImage(thumb_pil)
                self.asset_thumbnails.append(thumb_tk)
                item_frame = tk.Frame(self.scrollable_frame, bg="#e0e0e0", bd=2, relief="flat")
                item_frame.pack(pady=5, padx=5, fill=tk.X)
                self.asset_frames.append(item_frame)
                btn_del = tk.Button(item_frame, text="×", font=("Arial", 8), bg="#ffcccc", command=lambda i=asset_id, f=item_frame: self.remove_asset_image(i, f), width=2, relief="flat")
                btn_del.pack(anchor="ne")
                btn_img = tk.Button(item_frame, image=thumb_tk, command=lambda i=asset_id: self.select_asset_to_place(i), bg="white", relief="flat")
                btn_img.pack(padx=2, pady=2)
            except Exception as e: print(f"Failed to load {path}: {e}")

    def remove_asset_image(self, asset_id, frame_widget):
        if 0 <= asset_id < len(self.asset_images):
            self.asset_images[asset_id] = None; self.asset_frames[asset_id] = None
            frame_widget.destroy(); self.update_canvas_image()

    def update_asset_highlight(self, target_id):
        for i, frame in enumerate(self.asset_frames):
            if frame: frame.config(bg="#ff4500" if i == target_id else "#e0e0e0")

    def select_asset_to_place(self, asset_id):
        if self.asset_images[asset_id] is None: return
        self._reset_modes(); self.placing_image_id = asset_id; self.update_asset_highlight(asset_id); self.deselect_all(); self.root.config(cursor="hand2")

    def _reset_modes(self):
        self.brush_active = False; self.dropper_active = False; self.placing_text_content = None; self.placing_image_id = None
        self.update_asset_highlight(None)
        self.btn_brush_mode.config(text="消しゴムON", bg="lightgray")
        self.btn_dropper.config(text="スポイト", bg="lightgray")
        self.root.config(cursor="")

    def deselect_all(self):
        self.selected_item = None; self.btn_update.config(state=tk.DISABLED, bg="#ffebcd"); self.update_canvas_image()

    def delete_selected_item(self):
        if self.selected_item is None: return
        self.save_history(); idx = self.selected_item['index']
        if self.selected_item['type'] == 'text': del self.text_objects[idx]
        elif self.selected_item['type'] == 'image': del self.placed_images[idx]
        self.deselect_all()

    def on_property_change(self, *args):
        if self.selected_item and self.selected_item['type'] == 'text':
            if len(args) == 0: self.save_history()
            idx = self.selected_item['index']; obj = self.text_objects[idx]
            obj['size'] = self.var_font_size.get()
            obj['line_spacing'] = self.var_line_spacing.get()
            obj['char_spacing'] = self.var_char_spacing.get()
            obj['outline_width'] = self.var_outline_width.get()
            obj['angle'] = self.var_text_angle.get()
            obj['vertical'] = self.var_vertical.get()
            obj['font_key'] = self.combo_font.get()
            obj['align_h'] = self.combo_align_h.get() 
            obj['align_v'] = self.combo_align_v.get() 
            self.update_canvas_image()

    def on_image_property_change(self, *args):
        if self.selected_item and self.selected_item['type'] == 'image':
            if len(args) > 0: self.save_history()
            idx = self.selected_item['index']; obj = self.placed_images[idx]
            obj['scale'] = self.var_img_scale.get() / 100.0
            obj['angle'] = self.var_img_angle.get()
            self.update_canvas_image()

    def reflect_selection_to_ui(self):
        if self.selected_item is None: return
        idx = self.selected_item['index']
        if self.selected_item['type'] == 'text':
            obj = self.text_objects[idx]
            self.input_text_box.delete("1.0", tk.END); self.input_text_box.insert(tk.END, obj['text'])
            self.var_font_size.set(obj['size'])
            self.var_line_spacing.set(obj.get('line_spacing', 20))
            self.var_char_spacing.set(obj.get('char_spacing', 0))
            self.var_outline_width.set(obj.get('outline_width', 0))
            self.var_text_angle.set(obj.get('angle', 0))
            self.var_vertical.set(obj['vertical'])
            self.combo_font.set(obj['font_key'])
            self.combo_align_h.set(obj.get('align_h', ALIGN_H_OPTIONS[0]))
            self.combo_align_v.set(obj.get('align_v', ALIGN_V_OPTIONS[0]))
            self.text_color = obj['color']; self.lbl_text_color_preview.config(bg=self.text_color)
            self.text_outline_color = obj.get('outline_color', '#ffffff'); self.lbl_outline_color_preview.config(bg=self.text_outline_color)
            self.btn_update.config(state=tk.NORMAL, bg="#ffa500"); self.text_listbox.selection_clear(0, tk.END); self.btn_list_update.config(state=tk.DISABLED, bg="#ffebcd")
        elif self.selected_item['type'] == 'image':
            obj = self.placed_images[idx]
            self.var_img_scale.set(int(obj['scale'] * 100)); self.var_img_angle.set(obj['angle']); self.btn_update.config(state=tk.DISABLED, bg="#ffebcd")

    def toggle_dropper_mode(self):
        if self.dropper_active: self._reset_modes()
        else: self._reset_modes(); self.dropper_active = True; self.btn_dropper.config(text="色を取得...", bg="#add8e6"); self.root.config(cursor="crosshair")

    def toggle_brush_mode(self):
        if self.brush_active: self._reset_modes()
        else: self._reset_modes(); self.brush_active = True; self.deselect_all(); self.btn_brush_mode.config(text="消しゴムON", bg="orange"); self.root.config(cursor="dot")

    def set_brush_color(self, hex_color):
        self.brush_color = hex_color; self.lbl_eraser_preview.config(bg=hex_color)

    def pick_color_from_image(self, x, y):
        if self.original_image:
            try:
                p = self.original_image.getpixel((int(x), int(y)))
                self.set_brush_color('#{:02x}{:02x}{:02x}'.format(p[0],p[1],p[2]))
                self.toggle_brush_mode()
            except: pass

    def choose_text_color(self):
        c = colorchooser.askcolor(color=self.text_color)[1]
        if c:
            self.save_history(); self.text_color = c; self.lbl_text_color_preview.config(bg=c)
            if self.selected_item and self.selected_item['type'] == 'text':
                self.text_objects[self.selected_item['index']]['color'] = c; self.update_canvas_image()

    def choose_outline_color(self):
        c = colorchooser.askcolor(color=self.text_outline_color)[1]
        if c:
            self.save_history(); self.text_outline_color = c; self.lbl_outline_color_preview.config(bg=c)
            if self.selected_item and self.selected_item['type'] == 'text':
                self.text_objects[self.selected_item['index']]['outline_color'] = c; self.update_canvas_image()

    def add_custom_font(self):
        path = filedialog.askopenfilename(filetypes=[("Font", "*.ttf;*.ttc;*.otf")])
        if path:
            name = os.path.splitext(os.path.basename(path))[0]
            FONT_Config[name] = {"tk": "Arial", "file": path}
            self.font_names = list(FONT_Config.keys()); self.combo_font['values'] = self.font_names; self.combo_font.set(name)
            if self.selected_item and self.selected_item['type'] == 'text': self.save_history(); self.on_property_change()

    def register_text(self):
        text = self.input_text_box.get("1.0", "end-1c")
        if text.strip(): self.text_listbox.insert(tk.END, text); self.input_text_box.delete("1.0", tk.END)

    def update_list_text(self):
        sel = self.text_listbox.curselection()
        if sel:
            idx = sel[0]; new_text = self.input_text_box.get("1.0", "end-1c")
            if new_text.strip(): self.text_listbox.delete(idx); self.text_listbox.insert(idx, new_text); self.text_listbox.select_set(idx); self.placing_text_content = new_text

    def delete_list_text(self):
        sel = self.text_listbox.curselection()
        if sel: self.text_listbox.delete(sel[0]); self.input_text_box.delete("1.0", tk.END); self.btn_list_update.config(state=tk.DISABLED, bg="#ffebcd"); self.placing_text_content = None

    def update_placed_object_text(self):
        if self.selected_item and self.selected_item['type'] == 'text':
            self.save_history(); text = self.input_text_box.get("1.0", "end-1c")
            if text.strip(): self.text_objects[self.selected_item['index']]['text'] = text; self.update_canvas_image()

    def on_list_select(self, event):
        sel = self.text_listbox.curselection()
        if sel:
            self._reset_modes(); self.deselect_all()
            text = self.text_listbox.get(sel[0]); self.placing_text_content = text
            self.input_text_box.delete("1.0", tk.END); self.input_text_box.insert(tk.END, text)
            self.btn_list_update.config(state=tk.NORMAL, bg="#ffa500"); self.root.config(cursor="hand2")

    def load_image(self):
        path = filedialog.askopenfilename(filetypes=[("Image", "*.jpg;*.png;*.jpeg")])
        if not path: return
        try:
            self.original_image = Image.open(path).convert("RGBA")
            self.cache_bg_image = None; self.strokes = []; self.text_objects = []; self.placed_images = []; self.history_stack = []; self.redo_stack = []; self._reset_modes(); self.hit_targets = []; self.update_canvas_image()
        except Exception as e: messagebox.showerror("Err", str(e))

    def img_to_base64(self, img):
        if img is None: return None
        b = io.BytesIO(); img.save(b, format="PNG"); return base64.b64encode(b.getvalue()).decode('utf-8')

    def base64_to_img(self, s):
        if not s: return None
        try: return Image.open(io.BytesIO(base64.b64decode(s))).convert("RGBA")
        except: return None

    def save_project(self):
        if self.original_image is None: messagebox.showwarning("警告", "データなし"); return
        path = filedialog.asksaveasfilename(defaultextension=".zmm", filetypes=[("ZMM Project", "*.zmm")])
        if not path: return
        data = {
            "version": "1.0", "background_image": self.img_to_base64(self.original_image),
            "asset_images": [self.img_to_base64(i) for i in self.asset_images],
            "registered_texts": self.text_listbox.get(0, tk.END),
            "text_objects": self.text_objects, "placed_images": self.placed_images, "strokes": self.strokes,
            "brush_color": self.brush_color, "text_color": self.text_color, "text_outline_color": self.text_outline_color,
            "custom_fonts": {k: v["file"] for k, v in FONT_Config.items() if k not in ["メイリオ", "MS ゴシック", "MS 明朝", "游ゴシック", "Arial"]}
        }
        try:
            with open(path, 'w', encoding='utf-8') as f: json.dump(data, f, ensure_ascii=False, indent=2)
            messagebox.showinfo("完了", "保存しました")
        except Exception as e: messagebox.showerror("エラー", f"{e}")

    def load_project(self):
        path = filedialog.askopenfilename(filetypes=[("ZMM Project", "*.zmm")])
        if not path: return
        try:
            with open(path, 'r', encoding='utf-8') as f: d = json.load(f)
            self._reset_modes(); self.history_stack = []; self.redo_stack = []
            self.original_image = self.base64_to_img(d.get("background_image"))
            self.cache_bg_image = None; self.asset_images = []; self.asset_thumbnails = []; self.asset_frames = []
            for w in self.scrollable_frame.winfo_children(): w.destroy()
            for b64 in d.get("asset_images", []):
                img = self.base64_to_img(b64)
                if img:
                    self.asset_images.append(img); aid = len(self.asset_images)-1
                    tw=140; aspect=img.height/img.width; th=int(tw*aspect); th=140 if th>140 else th
                    tk_img = ImageTk.PhotoImage(img.resize((tw, th), RESAMPLE_LANCZOS))
                    self.asset_thumbnails.append(tk_img)
                    fr = tk.Frame(self.scrollable_frame, bg="#e0e0e0", bd=2, relief="flat"); fr.pack(pady=5, padx=5, fill=tk.X)
                    self.asset_frames.append(fr)
                    tk.Button(fr, text="×", font=("Arial", 8), bg="#ffcccc", command=lambda i=aid, f=fr: self.remove_asset_image(i, f), width=2, relief="flat").pack(anchor="ne")
                    tk.Button(fr, image=tk_img, command=lambda i=aid: self.select_asset_to_place(i), bg="white", relief="flat").pack(padx=2, pady=2)
                else: self.asset_images.append(None); self.asset_frames.append(None)
            self.text_listbox.delete(0, tk.END)
            for t in d.get("registered_texts", []): self.text_listbox.insert(tk.END, t)
            self.text_objects = d.get("text_objects", []); self.placed_images = d.get("placed_images", []); self.strokes = d.get("strokes", [])
            self.brush_color = d.get("brush_color", "#ffffff"); self.text_color = d.get("text_color", "#000000"); self.text_outline_color = d.get("text_outline_color", "#ffffff")
            self.lbl_eraser_preview.config(bg=self.brush_color); self.lbl_text_color_preview.config(bg=self.text_color); self.lbl_outline_color_preview.config(bg=self.text_outline_color)
            for n, p in d.get("custom_fonts", {}).items(): 
                if os.path.exists(p): FONT_Config[n] = {"tk": "Arial", "file": p}
            self.font_names = list(FONT_Config.keys()); self.combo_font['values'] = self.font_names
            self.update_canvas_image(); messagebox.showinfo("完了", "読み込みました")
        except Exception as e: messagebox.showerror("エラー", f"{e}")

    def save_history(self):
        if not self.original_image: return
        st = {'image': self.original_image.copy(), 'text_objects': copy.deepcopy(self.text_objects),
              'placed_images': copy.deepcopy(self.placed_images), 'strokes': copy.deepcopy(self.strokes)}
        self.history_stack.append(st)
        if len(self.history_stack) > self.max_history: self.history_stack.pop(0)
        self.redo_stack.clear()

    def undo(self, e=None):
        if not self.history_stack: return
        cur = {'image': self.original_image.copy(), 'text_objects': copy.deepcopy(self.text_objects), 'placed_images': copy.deepcopy(self.placed_images), 'strokes': copy.deepcopy(self.strokes)}
        self.redo_stack.append(cur); self._restore_state(self.history_stack.pop())

    def redo(self, e=None):
        if not self.redo_stack: return
        cur = {'image': self.original_image.copy(), 'text_objects': copy.deepcopy(self.text_objects), 'placed_images': copy.deepcopy(self.placed_images), 'strokes': copy.deepcopy(self.strokes)}
        self.history_stack.append(cur); self._restore_state(self.redo_stack.pop())

    def _restore_state(self, s):
        self.original_image = s['image']; self.cache_bg_image = None
        self.text_objects = s['text_objects']; self.placed_images = s['placed_images']; self.strokes = s['strokes']
        self.selected_item = None; self.update_canvas_image(); self.input_text_box.delete("1.0", tk.END); self.btn_update.config(state=tk.DISABLED, bg="#ffebcd")

    def on_canvas_click(self, event):
        if not self.original_image: return
        ix = (event.x - self.offset_x) / self.img_scale; iy = (event.y - self.offset_y) / self.img_scale
        if self.dropper_active: self.pick_color_from_image(ix, iy); return
        if self.placing_text_content or self.placing_image_id is not None or self.brush_active: self.save_history()

        if self.placing_text_content:
            self.text_objects.append({
                'text': self.placing_text_content, 'x': ix, 'y': iy,
                'size': self.var_font_size.get(), 'line_spacing': self.var_line_spacing.get(), 'char_spacing': self.var_char_spacing.get(),
                'outline_width': self.var_outline_width.get(), 'outline_color': self.text_outline_color,
                'angle': self.var_text_angle.get(), 
                'color': self.text_color, 'vertical': self.var_vertical.get(), 'font_key': self.combo_font.get(),
                'align_h': self.combo_align_h.get(), 'align_v': self.combo_align_v.get()
            })
            self.placing_text_content = None; self.text_listbox.selection_clear(0, tk.END); self.btn_list_update.config(state=tk.DISABLED, bg="#ffebcd"); self.root.config(cursor="")
            self.selected_item = {'type': 'text', 'index': len(self.text_objects)-1}
            self.reflect_selection_to_ui(); self.update_canvas_image(); return

        if self.placing_image_id is not None:
            if self.asset_images[self.placing_image_id] is None: return
            self.placed_images.append({'src_id': self.placing_image_id, 'x': ix, 'y': iy, 'scale': 1.0, 'angle': 0.0})
            self.placing_image_id = None; self.update_asset_highlight(None); self.root.config(cursor="")
            self.selected_item = {'type': 'image', 'index': len(self.placed_images)-1}
            self.reflect_selection_to_ui(); self.update_canvas_image(); return

        if self.brush_active: self._add_stroke(ix, iy); return

        clicked = self.canvas.find_closest(event.x, event.y); tags = self.canvas.gettags(clicked); new_sel = None
        for tag in tags:
            if tag.startswith("text_hit_"): new_sel = {'type': 'text', 'index': int(tag.split("_")[-1])}; break
            if tag.startswith("img_hit_"): new_sel = {'type': 'image', 'index': int(tag.split("_")[-1])}; break
        
        found = None
        for item in reversed(self.hit_targets):
            x0, y0, x1, y1 = item['bbox']
            if x0 <= event.x <= x1 and y0 <= event.y <= y1:
                found = {'type': item['type'], 'index': item['index']}
                break
        
        self.selected_item = found
        if self.selected_item:
            self.save_history()
            self.drag_data["item"] = self.selected_item; self.drag_data["x"] = event.x; self.drag_data["y"] = event.y; self.reflect_selection_to_ui()
        else: self.deselect_all()
        self.update_canvas_image()

    def on_canvas_drag(self, event):
        if not self.original_image: return
        ix = (event.x - self.offset_x) / self.img_scale; iy = (event.y - self.offset_y) / self.img_scale
        if self.brush_active: self._add_stroke(ix, iy)
        elif self.drag_data["item"]:
            sel = self.drag_data["item"]; idx = sel['index']
            if sel['type'] == 'text': self.text_objects[idx]['x'] = ix; self.text_objects[idx]['y'] = iy
            elif sel['type'] == 'image': self.placed_images[idx]['x'] = ix; self.placed_images[idx]['y'] = iy
            self.update_canvas_image()

    def on_canvas_release(self, event):
        self.drag_data["item"] = None; 
        if self.brush_active:
            self.cache_bg_image = None; self.update_canvas_image()

    def _add_stroke(self, x, y):
        sz = self.var_brush_size.get(); self.strokes.append((x, y, sz, self.brush_color))
        sx = x*self.img_scale+self.offset_x; sy = y*self.img_scale+self.offset_y; r = (sz*self.img_scale)/2
        self.canvas.create_oval(sx-r, sy-r, sx+r, sy+r, fill=self.brush_color, outline=self.brush_color)

    def on_resize_window(self, event):
        if self.original_image: self.update_canvas_image()

    def _get_pil_font(self, font_key, size):
        f = FONT_Config.get(font_key, {"file": "arial.ttf"})["file"]
        p = f if os.path.isabs(f) else os.path.join("C:/Windows/Fonts", f)
        if not os.path.exists(p) and os.path.exists(f): p = f
        try: return ImageFont.truetype(p, size)
        except: return ImageFont.load_default()

    def _calculate_text_geometry(self, draw, obj):
        text = obj['text']; x = obj['x']; y = obj['y']; size = obj['size']
        ls_px = size * (obj.get('line_spacing', 20)/100.0); cs_px = size * (obj.get('char_spacing', 0)/100.0)
        outline_w = obj.get('outline_width', 0)
        angle = obj.get('angle', 0) 
        vertical = obj['vertical']; font = self._get_pil_font(obj['font_key'], size)
        ah = obj.get('align_h', "Right"); av = obj.get('align_v', "Top")
        instr = []; mx, my, Mx, My = float('inf'), float('inf'), float('-inf'), float('-inf')

        if not text: return [], (x, y, x, y), (0,0,0,0)

        if draw is None:
             dummy_img = Image.new("RGBA", (1, 1))
             draw = ImageDraw.Draw(dummy_img)
        
        if not vertical:
            lines = text.split('\n'); line_data = []; total_h = 0
            for l in lines:
                if not l: line_data.append((0, size, [])); total_h += size + ls_px; continue
                chrs = []; lw = 0; mh = 0
                for c in l:
                    bb = draw.textbbox((0,0), c, font=font); w = bb[2]-bb[0]; h = bb[3]-bb[1]
                    chrs.append((c, w)); lw += w + cs_px; mh = max(mh, h)
                if lw>0: lw-=cs_px
                line_data.append((lw, mh, chrs)); total_h += mh + ls_px
            if total_h > 0: total_h -= ls_px
            
            if "Top" in av: sy = 0
            elif "Bottom" in av: sy = -total_h
            else: sy = -total_h / 2
            
            cy = sy
            for lw, lh, chrs in line_data:
                if "Right" in ah: sx = -lw
                elif "Left" in ah: sx = 0
                else: sx = -lw / 2
                cx = sx
                for c, cw in chrs:
                    instr.append({'x':cx, 'y':cy, 'text':c, 'anchor':'lt'})
                    mx=min(mx,cx); my=min(my,cy); Mx=max(Mx,cx+cw); My=max(My,cy+lh)
                    cx += cw + cs_px
                cy += lh + ls_px
        else:
            lines = text.split('\n'); cols = []; tw = 0; cgap = size * 0.05
            for l in lines:
                if not l: cols.append((size/2, 0, [])); tw += size/2 + ls_px; continue
                cdata = []; ch = 0; mcw = 0
                for c in l:
                    bb = draw.textbbox((0,0), c, font=font); w = bb[2]-bb[0]; h = bb[3]-bb[1]
                    cdata.append((c, w, h)); ch += h + cgap + cs_px; mcw = max(mcw, w)
                if ch>0: ch -= (cgap + cs_px)
                cols.append((mcw, ch, cdata)); tw += mcw + ls_px
            if tw>0: tw-=ls_px
            
            if "Right" in ah: sx = 0
            elif "Center" in ah: sx = tw / 2
            else: sx = tw
            
            cr = sx
            for cw, ch, chrs in cols:
                ccx = cr - (cw / 2)
                if "Top" in av: cy = 0
                elif "Bottom" in av: cy = -ch
                else: cy = -ch / 2
                for c, w, h in chrs:
                    instr.append({'x':ccx, 'y':cy, 'text':c, 'anchor':'mt'})
                    l = ccx-w/2; t = cy; r = ccx+w/2; b = cy+h
                    mx=min(mx,l); my=min(my,t); Mx=max(Mx,r); My=max(My,b)
                    cy += h + cgap + cs_px
                cr -= (cw + ls_px)

        if mx == float('inf'): return [], (x, y, x, y), (0,0,0,0)

        block_w = int(Mx - mx + outline_w*2 + 10)
        block_h = int(My - my + outline_w*2 + 10)
        offset_x = -mx + outline_w + 5
        offset_y = -my + outline_w + 5
        
        return instr, (mx, my, Mx, My), (block_w, block_h, offset_x, offset_y)

    def update_canvas_image(self):
        if not self.original_image: return
        cw, ch = self.canvas.winfo_width(), self.canvas.winfo_height()
        if cw<10 or ch<10: return
        iw, ih = self.original_image.size; sc = min(cw/iw, ch/ih)
        nw, nh = int(iw*sc), int(ih*sc); self.img_scale = sc
        self.offset_x, self.offset_y = (cw-nw)//2, (ch-nh)//2
        self.hit_targets = []
        
        dummy_img = Image.new('RGBA', (1, 1))
        dummy_draw = ImageDraw.Draw(dummy_img)

        try:
            if self.cache_bg_image is None or self.cache_canvas_size != (nw, nh):
                self.cache_bg_image = self.original_image.resize((nw, nh), RESAMPLE_BILINEAR)
                self.cache_canvas_size = (nw, nh)
                if self.strokes:
                    d = ImageDraw.Draw(self.cache_bg_image)
                    for sx, sy, sz, c in self.strokes:
                        rsx = sx * sc; rsy = sy * sc; rsz = sz * sc; r = rsz/2
                        d.ellipse((rsx-r, rsy-r, rsx+r, rsy+r), fill=c)

            base = self.cache_bg_image.copy()
            
            for i, o in enumerate(self.placed_images):
                src = self.asset_images[o['src_id']]
                if src:
                    w = int(src.width*o['scale'] * sc); h = int(src.height*o['scale'] * sc)
                    if w>0 and h>0:
                        rot = src.resize((w, h), RESAMPLE_BILINEAR).rotate(o['angle'], expand=True, resample=RESAMPLE_BILINEAR)
                        dx = int(o['x']*sc - rot.width/2); dy = int(o['y']*sc - rot.height/2)
                        base.paste(rot, (dx, dy), rot)
                        
                        c0 = dx + self.offset_x; r0 = dy + self.offset_y
                        c1 = c0 + rot.width; r1 = r0 + rot.height
                        self.hit_targets.append({'type': 'image', 'index': i, 'bbox': (c0, r0, c1, r1)})
            
            for i, o in enumerate(self.text_objects):
                p_obj = o.copy(); p_obj['size'] = int(o['size'] * sc); p_obj['outline_width'] = int(o.get('outline_width', 0) * sc)
                p_obj['x'] = 0; p_obj['y'] = 0
                
                res = self._calculate_text_geometry(dummy_draw, p_obj)
                if not res: continue
                instr, bounds, (bw, bh, offx, offy) = res
                
                txt_img = Image.new('RGBA', (bw, bh), (0,0,0,0))
                d_txt = ImageDraw.Draw(txt_img)
                
                out_w = p_obj['outline_width']; out_c = o.get('outline_color', '#ffffff')
                font = self._get_pil_font(p_obj['font_key'], p_obj['size'])
                
                for x in instr:
                    d_txt.text((x['x'] + offx, x['y'] + offy), x['text'], font=font, fill=o['color'], anchor=x.get('anchor', 'lt'), stroke_width=out_w, stroke_fill=out_c)
                
                angle = o.get('angle', 0)
                if angle != 0: rotated_txt = txt_img.rotate(angle, expand=True, resample=RESAMPLE_BILINEAR)
                else: rotated_txt = txt_img
                
                bx = o['x']*sc; by = o['y']*sc
                final_x = int(bx - rotated_txt.width/2)
                final_y = int(by - rotated_txt.height/2)
                base.paste(rotated_txt, (final_x, final_y), rotated_txt)
                
                c0 = final_x + self.offset_x; r0 = final_y + self.offset_y
                c1 = c0 + rotated_txt.width; r1 = r0 + rotated_txt.height
                self.hit_targets.append({'type': 'text', 'index': i, 'bbox': (c0, r0, c1, r1)})

            self.display_pil = base
            self.display_image = ImageTk.PhotoImage(self.display_pil)
            self.canvas.delete("all")
            self.canvas.create_image(self.offset_x, self.offset_y, anchor=tk.NW, image=self.display_image)

            if self.selected_item:
                sel_idx = self.selected_item['index']; sel_type = self.selected_item['type']
                for item in reversed(self.hit_targets):
                    if item['type'] == sel_type and item['index'] == sel_idx:
                        c0, r0, c1, r1 = item['bbox']
                        self.canvas.create_rectangle(c0, r0, c1, r1, outline="blue", dash=(4,4), width=2)
                        if sel_type == 'text': obj=self.text_objects[sel_idx]
                        else: obj=self.placed_images[sel_idx]
                        ax = obj['x']*sc+self.offset_x; ay = obj['y']*sc+self.offset_y
                        if sel_type == 'text':
                             self.canvas.create_line(ax-10, ay, ax+10, ay, fill="red", width=2)
                             self.canvas.create_line(ax, ay-10, ax, ay+10, fill="red", width=2)
                        else:
                             self.canvas.create_oval(ax-5, ay-5, ax+5, ay+5, fill="red")
                        break
        except: traceback.print_exc()

    def save_image(self):
        if not self.original_image: return
        path = filedialog.asksaveasfilename(defaultextension=".png", filetypes=[("PNG", "*.png")])
        if not path: return
        final = self.original_image.copy(); d = ImageDraw.Draw(final)
        dummy_draw = ImageDraw.Draw(Image.new("RGBA", (1, 1)))
        for sx, sy, sz, c in self.strokes: r=sz/2; d.ellipse((sx-r, sy-r, sx+r, sy+r), fill=c)
        for o in self.placed_images:
            src = self.asset_images[o['src_id']]
            if src:
                w = int(src.width*o['scale']); h = int(src.height*o['scale'])
                if w>0 and h>0:
                    rot = src.resize((w, h), RESAMPLE_LANCZOS).rotate(o['angle'], expand=True, resample=RESAMPLE_BICUBIC)
                    dx = int(o['x']-rot.width/2); dy = int(o['y']-rot.height/2)
                    final.paste(rot, (dx, dy), rot)
        for o in self.text_objects:
            p_obj = o.copy(); p_obj['x']=0; p_obj['y']=0
            res = self._calculate_text_geometry(dummy_draw, p_obj)
            if not res: continue
            instr, bounds, (bw, bh, offx, offy) = res
            txt_img = Image.new('RGBA', (bw, bh), (0,0,0,0)); d_txt = ImageDraw.Draw(txt_img)
            out_w = p_obj.get('outline_width', 0); out_c = o.get('outline_color', '#ffffff')
            font = self._get_pil_font(p_obj['font_key'], p_obj['size'])
            for x in instr:
                d_txt.text((x['x'] + offx, x['y'] + offy), x['text'], font=font, fill=o['color'], anchor=x.get('anchor', 'lt'), stroke_width=out_w, stroke_fill=out_c)
            angle = o.get('angle', 0)
            if angle != 0: rotated_txt = txt_img.rotate(angle, expand=True, resample=RESAMPLE_BICUBIC)
            else: rotated_txt = txt_img
            final_x = int(o['x'] - rotated_txt.width/2); final_y = int(o['y'] - rotated_txt.height/2)
            final.paste(rotated_txt, (final_x, final_y), rotated_txt)
        final.save(path); messagebox.showinfo("OK", "保存しました")

if __name__ == "__main__":
    root = tk.Tk()
    app = ZunComiApp(root)
    root.mainloop()