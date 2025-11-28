import tkinter as tk
from tkinter import filedialog, colorchooser, messagebox, ttk, scrolledtext
from PIL import Image, ImageTk, ImageDraw, ImageFont, ImageOps
import sys
import os
import traceback
import copy
import json
import base64
import io
import math
import numpy as np
import shutil
import glob
import subprocess

# ★ Skiaのインポートチェック
try:
    import skia
except ImportError:
    messagebox.showerror("エラー", "skia-python がインストールされていません。\npip install skia-python numpy を実行してください。")
    sys.exit(1)

# =========================================================
#  設定・定数
# =========================================================

APP_NAME = "Zunkey Comic Editor"
APP_VERSION = "0.9 (Real Path Fix)"

# --- パス解決ロジック（Nuitka Onefile 完全対応版）---
def get_base_dir():
    """
    実行ファイルのディレクトリを確実に取得する。
    Nuitka --onefile の場合、__file__ はTempフォルダを指すが、
    sys.argv[0] は元のEXEファイルを指すことが多い。
    """
    # 1. PyInstallerなどでfrozenされている場合
    if getattr(sys, 'frozen', False):
        return os.path.dirname(sys.executable)
    
    # 2. Nuitkaなどでコンパイルされている場合 (__compiled__が存在する)
    # または通常のスクリプト実行の場合も含め、sys.argv[0]が最も信頼性が高い
    try:
        # sys.argv[0] の絶対パスを取得
        path = os.path.abspath(sys.argv[0])
        return os.path.dirname(path)
    except:
        # 万が一取得できない場合はカレントディレクトリ
        return os.getcwd()

BASE_DIR = get_base_dir()
FONTS_DIR = os.path.join(BASE_DIR, "fonts")

# システムフォント
SYSTEM_FONTS = {
    "メイリオ": "C:/Windows/Fonts/meiryo.ttc",
    "游ゴシック": "C:/Windows/Fonts/YuGothB.ttc",
    "MS ゴシック": "C:/Windows/Fonts/msgothic.ttc",
    "MS Pゴシック": "C:/Windows/Fonts/msgothic.ttc",
    "MS 明朝": "C:/Windows/Fonts/msmincho.ttc",
    "Arial": "arial.ttf"
}

# 実行時に動的に構築するフォントリスト
FONT_MAP = SYSTEM_FONTS.copy()

# 縦書き用 文字置換マップ
VERTICAL_CHAR_MAP = {
    '、': '︑', '。': '︒', 
    '「': '﹁', '」': '﹂', 
    '『': '﹃', '』': '﹄',
    '（': '︵', '）': '︶', '(': '︵', ')': '︶',
    '[': '︻', ']': '︼', '{': '︷', '}': '︸',
    '＜': '︿', '＞': '﹀', '＝': '‖', '〜': '⌇', '~': '⌇',
    '！': '！', '？': '？', '!': '！', '?': '？'
}

ROTATE_CHARS = {'…', '‥', 'ー', '-', ':', ';', '＝', '='}

# 位置補正を行う小書き文字
SMALL_KANA = {'っ', 'ゃ', 'ゅ', 'ょ', 'ぁ', 'ぃ', 'ぅ', 'ぇ', 'ぉ', 
              'ッ', 'ャ', 'ュ', 'ョ', 'ァ', 'ィ', 'ゥ', 'ェ', 'ォ'}

ALIGN_H_OPTIONS = ["左寄せ (Left)", "中央 (Center)", "右寄せ (Right)"]
ALIGN_V_OPTIONS = ["上寄せ (Top)", "中央 (Middle)", "下寄せ (Bottom)"]

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
        self.root.geometry("1400x950")
        
        # --- フォント初期化 ---
        self._init_fonts_dir()

        # --- データ管理 ---
        self.original_image = None
        self.display_image = None
        self.img_scale = 1.0
        self.offset_x = 0
        self.offset_y = 0
        
        self.cache_bg_image = None
        self.cache_canvas_size = (0, 0)
        self.hit_targets = [] 
        
        # ツール状態
        self.brush_active = False
        self.brush_color = "#ffffff"
        self.text_color = "#000000"
        self.text_outline_color = "#ffffff"
        self.dropper_active = False
        
        # オブジェクトデータ
        self.strokes = [] 
        self.text_objects = [] 
        self.placed_images = [] 
        
        # アセット管理
        self.asset_images = [] 
        self.asset_thumbnails = [] 
        self.asset_frames = []
        
        # 選択・操作状態
        self.selected_item = None 
        self.placing_text_content = None 
        self.placing_image_id = None 
        self.drag_data = {"x": 0, "y": 0, "item": None}
        
        # フォントキャッシュ (Skia Typeface)
        self.skia_typeface_cache = {}

        # 履歴管理
        self.history_stack = []
        self.redo_stack = []
        self.max_history = 20

        self._setup_ui()
        self._bind_shortcuts()

    def _init_fonts_dir(self):
        """fontsフォルダを確認し、なければ作成"""
        if not os.path.exists(FONTS_DIR):
            try:
                os.makedirs(FONTS_DIR)
            except Exception as e:
                # エラー時も動作は継続する
                print(f"Font dir creation failed: {e}")
        self.refresh_font_list()

    def refresh_font_list(self):
        """ローカルのfontsフォルダを再スキャンしてリストを更新"""
        global FONT_MAP
        FONT_MAP = SYSTEM_FONTS.copy()
        
        if os.path.exists(FONTS_DIR):
            exts = ['*.ttf', '*.ttc', '*.otf', '*.TTF', '*.TTC', '*.OTF'] 
            files = []
            for ext in exts:
                files.extend(glob.glob(os.path.join(FONTS_DIR, ext)))
            
            for f in files:
                filename = os.path.basename(f)
                FONT_MAP[filename] = f
        
        self.font_names = list(FONT_MAP.keys())

    def open_fonts_folder(self):
        """OSのエクスプローラーでフォントフォルダを開く"""
        try:
            if not os.path.exists(FONTS_DIR):
                os.makedirs(FONTS_DIR)
            os.startfile(FONTS_DIR)
        except Exception as e:
            messagebox.showerror("エラー", f"フォルダを開けませんでした。\n{e}")

    def _bind_shortcuts(self):
        self.root.bind("<Control-z>", self.undo)
        self.root.bind("<Control-y>", self.redo)

    # --- UI Helper ---
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
        self.combo_font = ttk.Combobox(prop_row_font, values=self.font_names, state="readonly", width=16); self.combo_font.current(0); self.combo_font.pack(side=tk.LEFT, padx=2)
        self.combo_font.bind("<<ComboboxSelected>>", self.on_property_change)
        
        tk.Button(prop_row_font, text="＋", command=self.import_font_to_local, width=2, bg="#ddffdd", cursor="hand2").pack(side=tk.LEFT, padx=1)
        tk.Button(prop_row_font, text="📂", command=self.open_fonts_folder, width=2, bg="#ffebcd", cursor="hand2").pack(side=tk.LEFT, padx=1)
        
        self.var_font_size = self.create_smart_slider(sidebar, "サイズ:", 10, 400, 40, self.on_property_change)
        self.var_line_spacing = self.create_smart_slider(sidebar, "行間(%):", -50, 300, 20, self.on_property_change)
        self.var_char_spacing = self.create_smart_slider(sidebar, "文字間(%):", -50, 200, 0, self.on_property_change)
        self.var_outline_width = self.create_smart_slider(sidebar, "縁太さ:", 0, 30, 2, self.on_property_change)
        self.var_text_angle = self.create_smart_slider(sidebar, "回転(°):", -180, 180, 0, self.on_property_change)
        
        self.var_vertical = tk.BooleanVar(value=True) 
        tk.Checkbutton(sidebar, text="縦書き (Vertical)", variable=self.var_vertical, command=self.on_property_change, bg="#f0f0f0").pack(anchor="w")
        
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
    # ロジック: Skiaフォント・描画
    # ---------------------------------------------------------
    def _get_skia_typeface(self, font_key):
        if font_key in self.skia_typeface_cache:
            return self.skia_typeface_cache[font_key]
        
        path = FONT_MAP.get(font_key)
        typeface = None
        if path and os.path.exists(path):
            try: typeface = skia.Typeface.MakeFromFile(path)
            except: pass
        
        if not typeface:
            try: typeface = skia.Typeface.MakeFromName(font_key, skia.FontStyle.Normal())
            except: pass
            
        if not typeface:
            try: typeface = skia.Typeface.MakeFromName("Meiryo", skia.FontStyle.Normal())
            except: pass
            if not typeface: typeface = skia.Typeface.MakeDefault()

        self.skia_typeface_cache[font_key] = typeface
        return typeface

    def _render_text_skia(self, obj):
        try:
            text = obj['text']
            if not text: return None
            
            size = obj['size']
            color = obj['color']
            outline_color = obj.get('outline_color', '#ffffff')
            outline_width = obj.get('outline_width', 0)
            
            vertical = obj['vertical']
            line_spacing_ratio = obj.get('line_spacing', 20) / 100.0
            char_spacing_ratio = obj.get('char_spacing', 0) / 100.0
            
            angle_deg = obj.get('angle', 0)
            
            font_key = obj.get('font_key', 'メイリオ')
            typeface = self._get_skia_typeface(font_key)
            
            paint_fill = skia.Paint(
                AntiAlias=True,
                Color=int(color.replace("#", "0xFF"), 16)
            )
            
            paint_stroke = None
            if outline_width > 0:
                paint_stroke = skia.Paint(
                    AntiAlias=True,
                    Style=skia.Paint.kStroke_Style,
                    StrokeWidth=outline_width * 2,
                    Color=int(outline_color.replace("#", "0xFF"), 16),
                    StrokeJoin=skia.Paint.kRound_Join,
                    StrokeCap=skia.Paint.kRound_Cap
                )
            
            font = skia.Font(typeface, size)
            
            if vertical:
                text = text.replace("...", "…").replace("。。。", "…")
            lines = text.split('\n')
            
            ls_px = size * line_spacing_ratio
            cs_px = size * char_spacing_ratio
            
            max_len = max([len(l) for l in lines]) if lines else 0
            padding = size * 2 + outline_width * 2
            
            content_w = len(lines) * (size + ls_px)
            content_h = max_len * (size + cs_px)
            
            est_width = int(content_w + padding * 2)
            est_height = int(content_h + padding * 2)
            
            if not vertical:
                content_w_h = max_len * (size + cs_px)
                content_h_h = len(lines) * (size + ls_px)
                est_width = int(content_w_h + padding * 2)
                est_height = int(content_h_h + padding * 2)
            
            surface = skia.Surface(est_width, est_height)
            
            with surface as canvas:
                if vertical:
                    # 縦書き
                    cursor_x = est_width - padding - (size / 2)
                    for line in lines:
                        cursor_y = padding + (size / 2)
                        for char in line:
                            d_char = VERTICAL_CHAR_MAP.get(char, char)
                            need_rotate = (char in ROTATE_CHARS)
                            if need_rotate: d_char = char
                            
                            is_small = (char in SMALL_KANA)
                            
                            char_w = font.measureText(d_char)
                            metrics = font.getMetrics()
                            vertical_center_offset = (metrics.fAscent + metrics.fDescent) / 2
                            
                            canvas.save()
                            canvas.translate(cursor_x, cursor_y)
                            
                            draw_x = -(char_w / 2)
                            draw_y = -vertical_center_offset
                            
                            if is_small:
                                draw_x += size * 0.12 
                                draw_y -= size * 0.12 

                            if need_rotate:
                                canvas.rotate(90)
                                if not is_small:
                                    draw_x = -(char_w / 2)
                                    draw_y = -vertical_center_offset

                            if paint_stroke:
                                canvas.drawString(d_char, draw_x, draw_y, font, paint_stroke)
                            canvas.drawString(d_char, draw_x, draw_y, font, paint_fill)
                            
                            canvas.restore()
                            cursor_y += size + cs_px
                        cursor_x -= (size + ls_px)
                else:
                    # 横書き
                    cursor_y = padding + (size / 2)
                    for line in lines:
                        cursor_x = padding + (size / 2)
                        for char in line:
                            char_w = font.measureText(char)
                            metrics = font.getMetrics()
                            vertical_center_offset = (metrics.fAscent + metrics.fDescent) / 2
                            
                            canvas.save()
                            canvas.translate(cursor_x, cursor_y)
                            draw_x = -(char_w / 2)
                            draw_y = -vertical_center_offset
                            
                            if paint_stroke:
                                canvas.drawString(char, draw_x, draw_y, font, paint_stroke)
                            canvas.drawString(char, draw_x, draw_y, font, paint_fill)
                            canvas.restore()
                            cursor_x += char_w + cs_px + (outline_width/2)
                        cursor_y += size + ls_px

            # PIL変換
            image = surface.makeImageSnapshot()
            if image:
                w, h = image.width(), image.height()
                data = image.tobytes()
                try:
                    pil_img = Image.frombytes("RGBA", (w, h), data, "raw", "BGRA")
                except:
                    pil_img = Image.frombytes("RGBA", (w, h), data)

                bbox = pil_img.getbbox()
                if bbox:
                    pil_img = pil_img.crop(bbox)
                    if angle_deg != 0:
                        pil_img = pil_img.rotate(angle_deg, expand=True, resample=Image.BICUBIC)
                    return pil_img
            return None
        except Exception as e:
            traceback.print_exc()
            return None

    def _render_image_item(self, obj):
        try:
            src = self.asset_images[obj['src_id']]
            if not src: return None
            w = int(src.width * obj['scale']); h = int(src.height * obj['scale'])
            if w<=0 or h<=0: return None
            angle = obj['angle']
            img = src.resize((w, h), RESAMPLE_LANCZOS)
            if angle != 0: img = img.rotate(angle, expand=True, resample=RESAMPLE_BICUBIC)
            return img
        except Exception:
            return None

    # ---------------------------------------------------------
    # UI更新
    # ---------------------------------------------------------
    def update_canvas_image(self):
        if not self.original_image: return
        try:
            cw, ch = self.canvas.winfo_width(), self.canvas.winfo_height()
            if cw<10 or ch<10: return
            iw, ih = self.original_image.size
            sc = min(cw/iw, ch/ih)
            self.img_scale = sc
            nw, nh = int(iw*sc), int(ih*sc)
            self.offset_x, self.offset_y = (cw-nw)//2, (ch-nh)//2
            
            self.hit_targets = []

            if self.cache_bg_image is None or self.cache_canvas_size != (nw, nh):
                self.cache_bg_image = self.original_image.resize((nw, nh), RESAMPLE_BILINEAR)
                self.cache_canvas_size = (nw, nh)
                if self.strokes:
                    d = ImageDraw.Draw(self.cache_bg_image)
                    for sx, sy, sz, c in self.strokes:
                        rsx=sx*sc; rsy=sy*sc; rsz=sz*sc; r=rsz/2
                        d.ellipse((rsx-r, rsy-r, rsx+r, rsy+r), fill=c)
            
            base = self.cache_bg_image.copy()

            for i, o in enumerate(self.placed_images):
                img_obj = self._render_image_item(o)
                if img_obj:
                    cx = o['x']*sc; cy = o['y']*sc
                    px = int(cx - img_obj.width/2); py = int(cy - img_obj.height/2)
                    base.paste(img_obj, (px, py), img_obj)
                    c0 = px + self.offset_x; r0 = py + self.offset_y
                    c1 = c0 + img_obj.width; r1 = r0 + img_obj.height
                    self.hit_targets.append({'type': 'image', 'index': i, 'bbox': (c0, r0, c1, r1)})

            for i, o in enumerate(self.text_objects):
                p_obj = o.copy()
                p_obj['size'] = int(o['size'] * sc)
                p_obj['outline_width'] = int(o.get('outline_width', 0) * sc)
                
                img_obj = self._render_text_skia(p_obj)
                
                if img_obj:
                    cx = o['x']*sc; cy = o['y']*sc
                    px = int(cx - img_obj.width/2)
                    py = int(cy - img_obj.height/2)
                    base.paste(img_obj, (px, py), img_obj)
                    c0 = px + self.offset_x; r0 = py + self.offset_y
                    c1 = c0 + img_obj.width; r1 = r0 + img_obj.height
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
                        self.canvas.create_rectangle(c0, r0, c1, r1, outline="cyan", dash=(4,4), width=2)
                        if sel_type == 'text': obj=self.text_objects[sel_idx]
                        else: obj=self.placed_images[sel_idx]
                        ax = obj['x']*sc+self.offset_x; ay = obj['y']*sc+self.offset_y
                        self.canvas.create_oval(ax-4, ay-4, ax+4, ay+4, fill="red", outline="white")
                        break
        except Exception:
            traceback.print_exc()

    # ---------------------------------------------------------
    # 操作系
    # ---------------------------------------------------------
    def import_font_to_local(self):
        paths = filedialog.askopenfilenames(filetypes=[("Font files", "*.ttf;*.ttc;*.otf")])
        if not paths: return
        imported_count = 0
        for src_path in paths:
            try:
                filename = os.path.basename(src_path)
                dest_path = os.path.join(FONTS_DIR, filename)
                shutil.copy2(src_path, dest_path)
                imported_count += 1
            except Exception as e:
                print(f"Error copying font {src_path}: {e}")
        
        if imported_count > 0:
            self.refresh_font_list()
            self.combo_font['values'] = self.font_names
            messagebox.showinfo("成功", f"{imported_count}個のフォントを追加しました。\nリストから選択可能です。")
        else:
            messagebox.showwarning("失敗", "フォントの追加に失敗しました。")

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
            
            current_font = obj.get('font_key', 'メイリオ')
            if current_font in self.font_names:
                self.combo_font.set(current_font)
            else:
                self.combo_font.set(self.font_names[0])

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
            "version": APP_VERSION, "background_image": self.img_to_base64(self.original_image),
            "asset_images": [self.img_to_base64(i) for i in self.asset_images],
            "registered_texts": self.text_listbox.get(0, tk.END),
            "text_objects": self.text_objects, "placed_images": self.placed_images, "strokes": self.strokes,
            "brush_color": self.brush_color, "text_color": self.text_color, "text_outline_color": self.text_outline_color
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
            self.update_canvas_image(); messagebox.showinfo("完了", "読み込みました")
        except Exception as e: messagebox.showerror("エラー", f"{e}")

    def save_history(self):
        if not self.original_image: return
        st = {
            'text_objects': copy.deepcopy(self.text_objects),
            'placed_images': copy.deepcopy(self.placed_images), 
            'strokes': copy.deepcopy(self.strokes)
        }
        self.history_stack.append(st)
        if len(self.history_stack) > self.max_history: self.history_stack.pop(0)
        self.redo_stack.clear()

    def undo(self, e=None):
        if not self.history_stack: return
        cur = {'text_objects': copy.deepcopy(self.text_objects), 'placed_images': copy.deepcopy(self.placed_images), 'strokes': copy.deepcopy(self.strokes)}
        self.redo_stack.append(cur); self._restore_state(self.history_stack.pop())

    def redo(self, e=None):
        if not self.redo_stack: return
        cur = {'text_objects': copy.deepcopy(self.text_objects), 'placed_images': copy.deepcopy(self.placed_images), 'strokes': copy.deepcopy(self.strokes)}
        self.history_stack.append(cur); self._restore_state(self.redo_stack.pop())

    def _restore_state(self, s):
        self.text_objects = s['text_objects']; self.placed_images = s['placed_images']; self.strokes = s['strokes']
        self.cache_bg_image = None
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
                'color': self.text_color, 'vertical': self.var_vertical.get(), 
                'font_key': self.combo_font.get(),
                'use_custom': False, 
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
            dx = event.x - self.drag_data["x"]; dy = event.y - self.drag_data["y"]
            if sel['type'] == 'text':
                self.text_objects[idx]['x'] += dx / self.img_scale
                self.text_objects[idx]['y'] += dy / self.img_scale
            elif sel['type'] == 'image':
                self.placed_images[idx]['x'] += dx / self.img_scale
                self.placed_images[idx]['y'] += dy / self.img_scale
            self.drag_data["x"] = event.x; self.drag_data["y"] = event.y
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

    def save_image(self):
        if not self.original_image: return
        path = filedialog.asksaveasfilename(defaultextension=".png", filetypes=[("PNG", "*.png")])
        if not path: return
        final = self.original_image.copy(); d = ImageDraw.Draw(final)
        for sx, sy, sz, c in self.strokes: r=sz/2; d.ellipse((sx-r, sy-r, sx+r, sy+r), fill=c)
        
        for o in self.placed_images:
            img_obj = self._render_image_item(o)
            if img_obj:
                dx = int(o['x']-img_obj.width/2); dy = int(o['y']-img_obj.height/2)
                final.paste(img_obj, (dx, dy), img_obj)
        
        for o in self.text_objects:
            img_obj = self._render_text_skia(o)
            if img_obj:
                final_x = int(o['x'] - img_obj.width/2); final_y = int(o['y'] - img_obj.height/2)
                final.paste(img_obj, (final_x, final_y), img_obj)
        
        final.save(path); messagebox.showinfo("OK", "保存しました")

if __name__ == "__main__":
    try:
        root = tk.Tk()
        app = ZunComiApp(root)
        root.mainloop()
    except Exception:
        traceback.print_exc()