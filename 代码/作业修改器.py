import tkinter as tk
from tkinter import ttk, colorchooser, font, messagebox
from PIL import Image, ImageTk, ImageDraw, ImageFont
import os
import copy
import json
import sys
import math
import time
import threading
import queue
import platform
from concurrent.futures import ThreadPoolExecutor

# 导入公共模块（目录结构配置与工具函数）
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (BASE_DIR, IMAGE_EXTENSIONS, GRADING_DIR, is_exam_or_checkin,
                    normalize_lecture, parse_filename, get_grading_filename,
                    open_in_file_manager, clear_filename_cache,
                    check_filename_format, smart_rename_folder,
                    scan_dir_incremental, clear_dir_scan_cache,
                    LECTURES, LECTURE_SUB_TYPES, is_student_folder,
                    PROJECT_VERSION, atomic_write_json,
                    PARALLEL_WORKERS, seq_sort_key, collect_student_options,
                    MONITOR_SEARCH_FILE, read_monitor_search_state,
                    write_modifier_changed, window_geometry, config_file_path)

# ---------- 配置文件 ----------
CONFIG_FILE = config_file_path('image_tool_config.json')
DEFAULT_CONFIG = {
    'last_lecture': '全部', 'last_cat': '全部', 'last_class': '全部', 
    'last_seq': '全部', 'last_status': '全部',
    'shortcuts': {'prev': '<Left>', 'next': '<Right>', 'save': '<Up>', 'tile': '<Control-t>'},
    'tools': {
        'check': {'color': 'red', 'width': 3}, 'cross': {'color': 'red', 'width': 3},
        'line': {'color': 'red', 'width': 3},
        'text': {'color': 'red', 'font': 'SimHei', 'size': 20, 'weight': 'bold'}
    },
    # 联排多图模式（默认无缝拼接、无标签，像一张大图）
    # fill_mode: 'contain'=等比缩放留白(不裁内容)  'cover'=等比缩放居中裁剪(填满格子)
    'tile': {'columns': 2, 'spacing': 0, 'show_labels': False, 'max_count': 50,
             'fill_mode': 'contain'},
    # 文本框（无边框，默认红色楷体20号加粗；内容在设置中配置）
    'textbox': {'text': '', 'font': 'KaiTi', 'size': 20, 'color': 'red', 'weight': 'bold',
                'align': 'left', 'valign': 'top', 'fill': False,
                'fill_color': '#ffffff', 'padding': 6},
    # 评分文字（固定 60 号加粗）
    'grading': {'font': 'SimHei', 'size': 60, 'color': 'red'},
    # 方向：所有自动旋转/摆正已取消（2026-08-06），仅保留手动"旋转主图"；
    # orient 节保留仅为兼容旧配置（不再生效）
    'orient': {'auto': False, 'ocr': False},
    'presets': {'check': {}, 'cross': {}, 'line': {}, 'text': {}},
    'layout': {'left_pane_width': 240, 'right_pane_width': 160}
}

# ---------- 全局变量 ----------
elements = []
selected_index = None
scale = 1.0
bg_image = None
bg_photo = None
bg_path = None
left_click_mode = 'select'   # select/check/cross/line/text
# 画布就地编辑文本框（无对话框）：直接输入到画布上的文本框
editing_box = None           # 正在编辑的 BoxTextElement
editing_text = None          # 嵌入画布的 tk.Text 输入控件
editing_window = None        # canvas.create_window 返回的 id
_edit_focus_after = None     # 延迟聚焦回调 id（防旧回调抢焦点）
canvas = None
root = None
scale_slider = None
grading_frame = None
grading_data = {}

undo_stack = []
redo_stack = []
is_undoing = False

search_result_list = []
cached_nav_list = []
tool_config = {}
tool_buttons = {}
preset_frame_inner = None

# ---------- 联排多图模式状态 ----------
tile_mode = False            # 是否开启联排
tile_entries = []            # [{'path','image','elements','name'}] 当前组（文件夹）的图片
tile_active = 0              # 当前编辑的图索引
tile_layout = []             # [(ox, oy, w, h)] 平铺布局
tile_scale = 1.0             # 平铺显示缩放（由 fit_scale * tile_zoom 得出）
tile_zoom = 1.0              # 用户手动缩放系数（Ctrl+滚轮 / 滑块）
drag_state = None            # 拖动状态（移动/调整大小）
tile_btn = None              # 联排开关按钮（用于高亮显示状态）
tile_folder_list = []        # 所有含图片的文件夹（按路径排序），一个文件夹=一组
tile_folder_idx = 0          # 当前组（文件夹）索引
tile_drafts = {}             # {path: {'elements': 标注, 'rot90': 旋转次数}} 各图未保存状态暂存（切组不丢失）
tile_show_mode = 'orig'      # 组内显示状态：'orig'=原图  'modified'=-改(已批改结果)
nav_prev_btn = None          # "上一张/上一组"按钮引用
nav_next_btn = None          # "下一张/下一组"按钮引用

search_lecture_var = None
search_cat_var = None
search_class_var = None
search_seq_var = None
search_status_var = None
search_listbox = None
seq_combo_box = None

# ---------- 姓名-类别 检索模式状态（与内容检索独立，共用同一修改器） ----------
search_mode = 'content'          # 'content'=讲次内容-学生检索  'student'=姓名-类别检索
search_student_var = None        # 姓名下拉：'2024-01-张三' 或 '全部'
student_seq_var = None           # 学生序号过滤（辅助定位学生）
student_combo_box = None
student_seq_combo_box = None
_content_mode_frames = []        # 内容模式专属面板（讲次/图片序号）
_student_mode_frames = []        # 学生模式专属面板（学生序号/姓名）

paned_window = None
left_pane = None
left_content = None
canvas_frame = None
top_spacer = None
toggle_btn = None
is_left_expanded = True
right_pane = None
right_canvas = None   # 右栏滚动容器（_global_wheel 访问，须模块级）

active_danmakus = []

# ---------- 性能缓存（低配机器友好） ----------
# 目录增量扫描缓存已统一在 common（scan_dir_incremental / clear_dir_scan_cache）
# 显示用 PhotoImage 缓存: {(id(bg_image), w, h): PhotoImage}
_display_photo_cache = {}

# ---------- 配置读写 ----------
# 配置内存缓存：get_cfg/get_section 高频调用（每帧重绘）不再反复读磁盘；
# 通过 load_config/save_config 保持同步。
_config_cache = None


def _config_bool(value, default=False):
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return bool(value)
    if isinstance(value, str):
        value = value.strip().lower()
        if value in ('true', '1', 'yes', 'on', '是'):
            return True
        if value in ('false', '0', 'no', 'off', '否', ''):
            return False
    return default


def _config_int(value, default, minimum, maximum):
    try:
        return max(minimum, min(maximum, int(value)))
    except (TypeError, ValueError):
        return default


def _normalize_config(config):
    """规范化会参与运算/绑定的配置值，同时保留未知扩展字段。"""
    shortcuts = config['shortcuts']
    for key, default in DEFAULT_CONFIG['shortcuts'].items():
        value = shortcuts.get(key)
        shortcuts[key] = value if isinstance(value, str) and value.strip() else default
    for key in ('check', 'cross', 'line'):
        tool = config['tools'].get(key)
        if not isinstance(tool, dict):
            tool = copy.deepcopy(DEFAULT_CONFIG['tools'][key])
            config['tools'][key] = tool
        tool['color'] = str(tool.get('color', 'red'))
        tool['width'] = _config_int(tool.get('width'), 3, 1, 20)
    tile = config['tile']
    tile['columns'] = _config_int(tile.get('columns'), 2, 1, 6)
    tile['spacing'] = _config_int(tile.get('spacing'), 0, 0, 100)
    tile['max_count'] = _config_int(tile.get('max_count'), 50, 5, 200)
    tile['show_labels'] = _config_bool(tile.get('show_labels'))
    tile['keep_drafts_on_group_switch'] = _config_bool(
        tile.get('keep_drafts_on_group_switch'), True)
    if tile.get('fill_mode') not in ('contain', 'cover'):
        tile['fill_mode'] = 'contain'
    textbox = config['textbox']
    textbox['size'] = _config_int(textbox.get('size'), 20, 8, 200)
    textbox['padding'] = _config_int(textbox.get('padding'), 6, 0, 100)
    textbox['fill'] = _config_bool(textbox.get('fill'))
    if textbox.get('align') not in ('left', 'center', 'right'):
        textbox['align'] = 'left'
    if textbox.get('valign') not in ('top', 'middle', 'bottom'):
        textbox['valign'] = 'top'
    grading = config['grading']
    grading['size'] = _config_int(grading.get('size'), 60, 16, 200)
    config['danmaku_ms'] = _config_int(config.get('danmaku_ms'), 3000, 1000, 10000)
    return config


def load_config():
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, 'r', encoding='utf-8') as f:
                config = json.load(f)
                if not isinstance(config, dict):
                    raise ValueError('配置根节点不是对象')
                for key in DEFAULT_CONFIG:
                    if key not in config:
                        # deepcopy：避免缺失节直接引用 DEFAULT_CONFIG 的嵌套 dict，
                        # 后续原地修改（如应用预设）会污染全局默认值
                        config[key] = copy.deepcopy(DEFAULT_CONFIG[key])
                    elif isinstance(DEFAULT_CONFIG[key], dict):
                        if not isinstance(config.get(key), dict):
                            config[key] = copy.deepcopy(DEFAULT_CONFIG[key])
                            continue
                        for sub_key in DEFAULT_CONFIG[key]:
                            if sub_key not in config[key]:
                                config[key][sub_key] = copy.deepcopy(DEFAULT_CONFIG[key][sub_key])
                return _normalize_config(config)
        except (OSError, json.JSONDecodeError, ValueError, TypeError):
            return _normalize_config(copy.deepcopy(DEFAULT_CONFIG))
    return _normalize_config(copy.deepcopy(DEFAULT_CONFIG))

def save_config(config):
    global _config_cache
    try:
        atomic_write_json(CONFIG_FILE, config, indent=4, ensure_ascii=False)
        _config_cache = config   # 保存成功后同步内存缓存
    except Exception as e: print(f"配置保存失败: {e}")

def _ensure_config_cache():
    """确保配置内存缓存已加载（惰性；返回配置 dict）"""
    global _config_cache
    if _config_cache is None:
        _config_cache = load_config()
    return _config_cache

def _is_image_file(name):
    """是否为图片文件（按扩展名；小写比较）"""
    return os.path.splitext(name)[1].lower() in IMAGE_EXTENSIONS

def get_tool_config(mode):
    """获取绘图工具配置（勾/叉/直线：颜色+线宽；文本框样式走 get_section('textbox')）"""
    cfg = tool_config.get(mode, {})
    return {'color': cfg.get('color', 'red'), 'width': cfg.get('width', 3)}

def get_cfg(section, key, default=None):
    """读取配置的便捷函数（内存缓存，毫秒级）"""
    return _ensure_config_cache().get(section, {}).get(key, default)

def get_section(section):
    """读取整个配置节（内存缓存；不存在则用默认值）"""
    return _ensure_config_cache().get(section, DEFAULT_CONFIG.get(section, {}))

# ---------- 文本渲染工具（Tk 与 PIL 像素单位统一，实现所见即所得） ----------
# 系统字体族名 -> 系统字体文件（在 Windows 字体目录中查找，不依赖代码所在位置）
_SYSTEM_FONT_FILES = {
    'KaiTi': 'simkai.ttf', '楷体': 'simkai.ttf', '楷体_GB2312': 'simkai.ttf',
    'SimHei': 'simhei.ttf', '黑体': 'simhei.ttf',
    'SimSun': 'simsun.ttc', '宋体': 'simsun.ttc',
    'Microsoft YaHei': 'msyh.ttc', '微软雅黑': 'msyh.ttc',
    'Arial': 'arial.ttf', 'Times New Roman': 'times.ttf',
}

# 字体对象缓存（每帧重绘会大量创建字体，缓存后仅首次创建）：
# Tk 字体 {(family, px, weight): tkfont}；PIL 字体 {(family, px): pilfont}
_tk_font_cache = {}
_pil_font_cache = {}

def get_pil_font(family, px):
    """获取 PIL 字体（像素单位）；按系统字体名查找字体文件（楷体→simkai.ttf 等）"""
    px = max(1, int(px))
    key = (family, px)
    f = _pil_font_cache.get(key)
    if f is not None:
        return f
    fname = _SYSTEM_FONT_FILES.get(family, family)
    for fn in [fname, family, 'simkai.ttf', 'simhei.ttf', 'simsun.ttc',
               'msyh.ttc', 'arial.ttf', 'Microsoft YaHei']:
        try:
            f = ImageFont.truetype(fn, px)
            break
        except Exception:
            continue
    if f is None:
        f = ImageFont.load_default()
    # 缓存上限保护：只保留最近 64 个（不同字号/字体组合）
    if len(_pil_font_cache) > 64:
        _pil_font_cache.pop(next(iter(_pil_font_cache)))
    _pil_font_cache[key] = f
    return f

def get_tk_font(family, px, weight='normal'):
    """获取 Tk 字体；size 取负值表示像素（Windows 支持），与 PIL 像素单位一致"""
    px = max(1, int(px))
    key = (family, px, weight)
    f = _tk_font_cache.get(key)
    if f is not None:
        return f
    try:
        f = font.Font(family=family, size=-px, weight=weight)
    except Exception:
        try:
            f = font.Font(size=-px, weight=weight)
        except Exception:
            f = font.Font(size=12)
    # 缓存上限保护：只保留最近 128 个
    if len(_tk_font_cache) > 128:
        _tk_font_cache.pop(next(iter(_tk_font_cache)))
    _tk_font_cache[key] = f
    return f

def wrap_text_by_width(text, measurer, max_width):
    """按显示宽度逐字换行（中英文通用）；measurer(str)->像素宽度"""
    if max_width <= 0: return text.split('\n')
    lines = []
    for para in str(text).split('\n'):
        if not para:
            lines.append(''); continue
        cur = ''
        for ch in para:
            if measurer(cur + ch) <= max_width:
                cur += ch
            else:
                if cur: lines.append(cur)
                cur = ch
        lines.append(cur)
    return lines

def text_line_height(font_obj, line_spacing=1.4):
    """估算单行文字高度（像素）；乘 1.4 为标准行距。
    兼容 Tk 字体（metrics('linespace')）与 PIL 字体（getbbox）：
    历史 bug——tkinter.font.Font 没有 getbbox 也没有 .size 属性，
    原实现恒回退 return 12，导致画布上多行文本框行高错误、各行重叠
    （保存走 PIL 字体行高正确，画布预览与成图不一致）。"""
    try:
        # Tk 字体：metrics('linespace') 返回单行行高
        return int(font_obj.metrics('linespace') * line_spacing)
    except Exception:
        pass
    try:
        b = font_obj.getbbox('中')   # PIL 字体
        return int((b[3] - b[1]) * line_spacing)
    except Exception:
        pass
    return 12

# ---------- 弹幕提示系统 ----------
class WrapFrame(tk.Frame):
    """
    可自动换行的容器：子控件（按钮/单选/勾选等）超过容器宽度时自动换到下一行，
    保证筛选条件（分类/班级等）在窄栏中显示完整。
    """
    def __init__(self, master, wrap=True, start_col=0, **kw):
        super().__init__(master, **kw)
        self._items = []
        self._wrap = wrap
        self._start_col = start_col
        self.bind('<Configure>', self._relayout)

    def add(self, w):
        self._items.append(w)
        self._relayout()

    def set_wrap(self, on):
        self._wrap = on
        self._relayout()

    def _relayout(self, e=None):
        if not self._items:
            return
        for w in self._items:
            w.grid_forget()
        width = self.winfo_width()
        if width < 30:
            return
        row = col = self._start_col
        used = 0
        for w in self._items:
            try:
                # 注意：不能在此调用 update_idletasks()——本函数由 <Configure> 事件触发，
                # 处理事件队列会级联触发兄弟 WrapFrame 的 <Configure>，形成事件风暴递归
                # （RecursionError）。winfo_reqwidth() 同步返回请求宽度，无需处理事件队列。
                ww = w.winfo_reqwidth() + 4
            except Exception:
                ww = 30
            if self._wrap and col > self._start_col and used + ww > width:
                row += 1; col = self._start_col; used = 0
            w.grid(row=row, column=col, sticky='w')
            col += 1
            used += ww

def show_danmaku(text):
    # 长文本截断（弹幕单行显示，避免撑出窗口）
    text = str(text)
    if len(text) > 60:
        text = text[:57] + '…'
    while len(active_danmakus) >= 3:
        old = active_danmakus.pop()
        if old.winfo_exists(): old.destroy()
    for i in range(len(active_danmakus)-1, -1, -1):
        lbl = active_danmakus[i]
        if lbl.winfo_exists():
            lbl.place_configure(y=10 + (i+1) * 40)
    win_h = root.winfo_height()
    dm_height = max(20, int(win_h / 30))
    lbl = tk.Label(root, text=text, bg='#333333', fg='white', font=('微软雅黑', 10), bd=0, highlightthickness=0)
    lbl.place(relx=0.5, y=10, anchor='n', height=dm_height)
    active_danmakus.insert(0, lbl)
    def remove_danmaku(l=lbl):
        if l.winfo_exists(): l.destroy()
        if l in active_danmakus:
            idx = active_danmakus.index(l)
            active_danmakus.pop(idx)
            for i in range(idx, len(active_danmakus)):
                ml = active_danmakus[i]
                if ml.winfo_exists(): ml.place_configure(y=10 + i * 40)
    # 弹幕时长（设置中心可调，默认 3 秒）。
    # 修复历史 bug：get_cfg('danmaku_ms', 3000) 把 int 当 key 查、
    # 'danmaku_ms' 当 section——实际该键存在配置**顶层**，返回 int 后
    # int.get() 抛 AttributeError 被吞，弹幕时长设置永远不生效。
    try:
        dm_ms = max(500, int((_config_cache or {}).get('danmaku_ms', 3000)))
    except Exception:
        dm_ms = 3000
    root.after(dm_ms, remove_danmaku)

# ---------- 评分数据持久化 ----------
# 分类输出顺序（作业→课前小测→错题再练，其他排后）
def _cat_order_key(c):
    try:
        return LECTURE_SUB_TYPES.index(c)
    except ValueError:
        return 99

def _sorted_grading(lec_data):
    """
    评价数据规范化排序：分类按固定顺序；分类内按 班级→学生序号→姓名 排序。
    key 格式 2024-02-李四（班级-序号-姓名），sorted 即按 班级→序号→姓名。
    """
    if not isinstance(lec_data, dict):
        return lec_data
    out = {}
    for cat in sorted(lec_data.keys(), key=_cat_order_key):
        inner = lec_data[cat]
        if isinstance(inner, dict):
            out[cat] = {k: inner[k] for k in sorted(inner.keys())}
        else:
            out[cat] = inner
    return out

def load_all_grading_data():
    if os.path.exists(GRADING_DIR):
        for fname in os.listdir(GRADING_DIR):
            if not fname.endswith('.json'):
                continue
            # 解析 lecture 键（统一规范化：'第02讲'/'第2讲' → '2'，
            # 兼容旧版本补零文件名，避免历史成绩因键不匹配而"消失"）
            lecture = fname.replace('.json', '')
            if lecture.startswith('第') and lecture.endswith('讲'):
                lecture = normalize_lecture(lecture)
            try:
                with open(os.path.join(GRADING_DIR, fname), 'r', encoding='utf-8') as f:
                    grading_data[lecture] = json.load(f)
            except Exception:
                pass

def save_grading_json(lecture):
    if not os.path.exists(GRADING_DIR): os.makedirs(GRADING_DIR)
    file_path = os.path.join(GRADING_DIR, get_grading_filename(lecture))
    atomic_write_json(file_path, _sorted_grading(grading_data.get(lecture, {})),
                      indent=4, ensure_ascii=False)

def sync_grading_data_to_disk(lecture, category):
    if lecture not in grading_data: grading_data[lecture] = {}
    if category not in grading_data[lecture]: grading_data[lecture][category] = {}
    if not bg_path: return
    current_dir = os.path.dirname(bg_path)
    if not os.path.exists(current_dir): return
    updated = False
    for f in os.listdir(current_dir):
        if _is_image_file(f):
            meta = parse_filename(f)
            if meta and normalize_lecture(meta.get('lecture', '')) == str(lecture):
                cat = meta.get('category', '')
                if str(cat) == str(category):
                    key = _grading_ctx(meta)[0]
                    if key not in grading_data[lecture][category]:
                        grading_data[lecture][category][key] = ""
                        updated = True
    if updated: save_grading_json(lecture)

def open_grading_dir():
    if not os.path.exists(GRADING_DIR): os.makedirs(GRADING_DIR)
    if not open_in_file_manager(GRADING_DIR):
        show_danmaku(f"无法打开目录: {GRADING_DIR}")

# ---------- 预设管理逻辑 ----------
active_preset_name = None   # 当前激活的预设名（删除预设时按它删，无需输入弹窗）

def apply_preset_direct(name):
    global active_preset_name
    mode_presets = load_config().get('presets', {}).get(left_click_mode, {})
    if name in mode_presets:
        tool_config[left_click_mode] = copy.deepcopy(mode_presets[name])
        active_preset_name = name
        for btn in preset_frame_inner.winfo_children():
            btn.config(relief=tk.SUNKEN if btn.cget("text") == name else tk.RAISED)

def open_preset_editor():
    win = tk.Toplevel(root); win.title(f"新增 '{left_click_mode}' 预设"); win.geometry("300x250")
    tk.Label(win, text="预设名称:").pack(pady=5); name_entry = tk.Entry(win); name_entry.pack(fill=tk.X, padx=10)
    tk.Label(win, text="颜色:").pack(pady=5); color_var = tk.StringVar(value='red')
    tk.Entry(win, textvariable=color_var).pack(fill=tk.X, padx=10)
    tk.Button(win, text="选色", command=lambda: color_var.set(colorchooser.askcolor()[1] or color_var.get())).pack(pady=2)
    if left_click_mode == 'text':
        tk.Label(win, text="字号:").pack(pady=5); size_var = tk.IntVar(value=16); tk.Spinbox(win, from_=8, to=72, textvariable=size_var).pack()
    else:
        tk.Label(win, text="线宽:").pack(pady=5); width_var = tk.IntVar(value=2); tk.Spinbox(win, from_=1, to=20, textvariable=width_var).pack()
    def save_new_preset():
        name = name_entry.get()
        if not name:
            show_danmaku("请输入预设名称")
            return
        c = load_config()
        if left_click_mode not in c['presets']: c['presets'][left_click_mode] = {}
        d = {'color': color_var.get()}
        if left_click_mode == 'text':
            try:
                size = max(8, size_var.get())
            except (ValueError, TypeError, tk.TclError):
                size = 16   # 字号被输入非数字：用默认值
            d.update(size=size, font='SimHei', weight='normal')
        else:
            try:
                d['width'] = max(1, width_var.get())
            except (ValueError, TypeError, tk.TclError):
                d['width'] = 2
        c['presets'][left_click_mode][name] = d; save_config(c); refresh_preset_buttons(); win.destroy()
        show_danmaku(f"预设 '{name}' 已保存")
    tk.Button(win, text="保存", command=save_new_preset, bg='lightgreen').pack(pady=10)

def delete_selected_preset():
    """删除当前激活的预设（点击预设应用后即激活，无需输入名称弹窗）"""
    global active_preset_name
    name = active_preset_name
    if not name:
        show_danmaku("请先点选要删除的预设（应用后自动记录）")
        return
    c = load_config()
    if left_click_mode in c.get('presets', {}) and name in c['presets'][left_click_mode]:
        del c['presets'][left_click_mode][name]; save_config(c); refresh_preset_buttons()
        active_preset_name = None
        show_danmaku(f"预设 '{name}' 已删除")
    else:
        show_danmaku("预设不存在或已删除")

def refresh_preset_buttons():
    for w in preset_frame_inner.winfo_children(): w.destroy()
    presets = load_config().get('presets', {}).get(left_click_mode, {})
    if not presets: tk.Label(preset_frame_inner, text="无预设", fg='grey').pack()
    else:
        for name in presets:
            tk.Button(preset_frame_inner, text=name, command=lambda n=name: apply_preset_direct(n), relief=tk.RAISED).pack(side=tk.LEFT, padx=2, pady=2, fill=tk.X, expand=True)

# ---------- 文件名解析与数据处理 ----------
# normalize_lecture / parse_filename / is_exam_or_checkin
# 已统一由 common 模块提供（见文件头部 import）

def _grading_ctx(meta):
    """评分定位三元组：(学生key, 规范化讲次, 分类)——多处评分读写共用"""
    return (f"{meta['class_prefix']}-{meta['class_full']}-{meta['name']}",
            str(normalize_lecture(meta.get('lecture', ''))),
            str(meta.get('category', '')))

def get_current_grade(meta):
    key, norm_lec, cat = _grading_ctx(meta)
    if norm_lec in grading_data and cat in grading_data[norm_lec]:
        return grading_data[norm_lec][cat].get(key, "")
    return ""

def update_grading_ui(meta):
    for w in grading_frame.winfo_children(): w.destroy()
    if not meta: return
    sync_grading_data_to_disk(str(meta.get('lecture', '')), str(meta.get('category', '')))
    cur_grade = get_current_grade(meta)
    
    # 显示包含班级和学号的信息
    lecture_display = meta.get('lecture', '')
    if lecture_display and lecture_display not in ('考试',) and not lecture_display.startswith('打卡'):
        lecture_display = f"第{lecture_display}讲"

    info_text = f"类型: {meta.get('category', '')}\n班级: {meta['class_prefix']}-{meta['class_full']}\n姓名: {meta['name']}\n讲次: {lecture_display}"
    tk.Label(grading_frame, text=info_text, justify=tk.LEFT).pack(anchor=tk.W, pady=2)
    
    tk.Label(grading_frame, text="快捷评价:").pack(anchor=tk.W, pady=(5,0))
    bf = tk.Frame(grading_frame); bf.pack(fill=tk.X, pady=2)
    for g in ['A+', 'A', 'A-', 'B']: 
        tk.Button(bf, text=g, command=lambda x=g: apply_grading_text(x, meta)).pack(side=tk.LEFT, padx=2, fill=tk.X, expand=True)
    
    # 作业、课前小测、考试和打卡天都显示评分控件
    cat = str(meta.get('category', ''))
    if cat.startswith('考试'):
        # 考试：0-100 手动输入 + 常用快捷分
        tk.Label(grading_frame, text="考试分数 (0-100):").pack(anchor=tk.W, pady=(5,0))
        ipf = tk.Frame(grading_frame); ipf.pack(fill=tk.X, pady=2)
        sv = tk.StringVar(value=cur_grade)
        se = tk.Entry(ipf, textvariable=sv, width=12); se.pack(side=tk.LEFT, fill=tk.X, expand=True)
        def osc(e=None): apply_grading_text(sv.get(), meta)
        se.bind('<Return>', osc); se.bind('<FocusOut>', osc)
        tk.Button(ipf, text="确认", command=osc).pack(side=tk.LEFT, padx=5)
        tk.Label(grading_frame, text="快捷分数:").pack(anchor=tk.W, pady=(5,0))
        sf = tk.Frame(grading_frame); sf.pack(fill=tk.X, pady=2)
        for i in range(5): sf.columnconfigure(i, weight=1)
        quick_scores = ['100', '95', '90', '85', '80', '75', '70', '60', '50', '40']
        for i, sc in enumerate(quick_scores):
            btn = tk.Button(sf, text=sc, command=lambda x=sc: apply_grading_text(x, meta))
            r, c = divmod(i, 5)
            btn.grid(row=r, column=c, sticky="nsew", padx=1, pady=1)
    elif cat in ('作业', '课前小测') or is_exam_or_checkin(cat):
        # 课前小测/打卡：0-10 快捷按钮
        tk.Label(grading_frame, text="快捷分数 (0-10):").pack(anchor=tk.W, pady=(5,0))
        sf = tk.Frame(grading_frame); sf.pack(fill=tk.X, pady=2)
        for i in range(5): sf.columnconfigure(i, weight=1)
        for i in range(21):
            score = i * 0.5
            txt = f"{score:g}"
            r, c = divmod(i, 5)
            btn = tk.Button(sf, text=txt, command=lambda x=txt: apply_grading_text(x, meta))
            btn.grid(row=r, column=c, sticky="nsew", padx=1, pady=1)
    else:
        tk.Label(grading_frame, text="自定义评价:").pack(anchor=tk.W, pady=(5,0))
        ipf = tk.Frame(grading_frame); ipf.pack(fill=tk.X, pady=2)
        sv = tk.StringVar(value=cur_grade); se = tk.Entry(ipf, textvariable=sv); se.pack(side=tk.LEFT, fill=tk.X, expand=True)
        def osc(e=None): apply_grading_text(sv.get(), meta)
        se.bind('<Return>', osc); se.bind('<FocusOut>', osc)
        tk.Button(ipf, text="确认", command=osc).pack(side=tk.LEFT, padx=5)

def _apply_grading_to_meta(meta, text, target):
    """评分公共流程（联排/单图共用）：校验分数 → 写 grading_data → 替换评分文字元素。
    target=None 表示单图模式（作用于全局 elements）；否则为联排组条目（评分打在其序号1图）。"""
    global elements
    key, norm_lec, cat = _grading_ctx(meta)
    text = str(text).strip()
    if text:
        try:
            val = float(text)
            if cat.startswith('考试'):
                if not (0 <= val <= 100): show_danmaku("请输入0-100之间的数字"); return
            elif cat in ('课前小测',) or is_exam_or_checkin(cat):
                if not (0 <= val <= 10): show_danmaku("请输入0-10之间的数字"); return
            text = f"{val:g}"
        except Exception:
            pass
    if norm_lec not in grading_data: grading_data[norm_lec] = {}
    if cat not in grading_data[norm_lec]: grading_data[norm_lec][cat] = {}
    grading_data[norm_lec][cat][key] = text
    save_grading_json(norm_lec)
    save_state()   # 记录操作前状态（可撤销评分）
    img = target['image'] if target is not None else bg_image
    lst = target['elements'] if target is not None else elements
    new_lst = [e for e in lst if not (isinstance(e, TextElement) and getattr(e, 'is_grading_text', False))]
    if text:
        gcfg = get_section('grading')
        try:
            grading_size = max(16, min(200, int(gcfg.get('size', 60))))
        except (TypeError, ValueError):
            grading_size = 60
        ne = TextElement(img.width - 20, 50, text=text,
                         color=gcfg.get('color', 'red'), ff=gcfg.get('font', 'SimHei'),
                         fs=grading_size, fw='bold', anchor='e')
        ne.is_grading_text = True
        new_lst.append(ne)
    if target is not None:
        target['elements'] = new_lst
        if tile_active == 0:
            elements = new_lst
    else:
        elements = new_lst
    redraw_all()

def apply_grading_text(text, meta):
    # ---------------- 联排模式：评分固定打在序号1的图片 ----------------
    if tile_mode:
        if not tile_entries: return
        target = tile_entries[0]
        tmeta = parse_filename(os.path.basename(target['path'])) or meta
        _apply_grading_to_meta(tmeta, text, target)
        return
    # ---------------- 单图模式 ----------------
    if not bg_image: return
    _apply_grading_to_meta(meta, text, None)

# ---------- 辅助函数 ----------
def get_base_size():
    if bg_image: return min(bg_image.width, bg_image.height) / 6.0
    return 20

def smart_filter_files(file_list):
    """用 -改 文件替换其对应原图（缓存列表存"当前有效形态"）。
    配对兼容扩展名不一致的情况（如 xxx.png 与 xxx-改.jpg，与 common.smart_rename_folder 一致）"""
    original_to_modified = {}
    for f in file_list:
        fname = os.path.basename(f)
        name, ext = os.path.splitext(fname)
        if name.endswith("-改"):
            base = name[:-2]
            for check_ext in IMAGE_EXTENSIONS:
                original_path = os.path.join(os.path.dirname(f), base + check_ext)
                if original_path in file_list:
                    original_to_modified[original_path] = f
                    break
    return [f for f in file_list if f not in original_to_modified]

def _finalize_file_list(files):
    """文件列表收尾：排序 + 用 -改 替换原图（当前有效形态语义）。结果有序。
    （sort 与 filter 可交换：filter 为子集操作，最终均为"排序后去掉被替换原图"）"""
    files.sort()
    return smart_filter_files(files)

_scan_cache_local = threading.local()

def _scan_dir_cached_local(d):
    """线程局部缓存的增量扫描（并行扫描时避免公共缓存竞争）"""
    cache = getattr(_scan_cache_local, 'cache', None)
    if cache is None:
        cache = {}
        _scan_cache_local.cache = cache
    return scan_dir_incremental(d, cache=cache)

def _scan_student_tree(folder):
    """递归扫描单个学生文件夹下的图片（供并行调用）"""
    files = []
    stack = [folder]
    while stack:
        d = stack.pop()
        dirs, fs = _scan_dir_cached_local(d)
        for f in fs:
            if _is_image_file(f):
                files.append(os.path.join(d, f))
        for sub in dirs:
            stack.append(os.path.join(d, sub))
    return files

def get_all_images_recursive(directory):
    files = []
    try:
        entries = os.listdir(directory)
    except OSError:
        return files
    students = [os.path.join(directory, e) for e in entries if is_student_folder(e)]
    # 并行扫描各学生目录（按 CPU 自适应，上限 8）
    workers = PARALLEL_WORKERS
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for sub in ex.map(_scan_student_tree, students):
            files.extend(sub)
    return _finalize_file_list(files)

def clear_scan_cache():
    """清空扫描与解析缓存（删除图片等场景调用）"""
    clear_dir_scan_cache()
    clear_filename_cache()

def _scan_scope_images(lec_display=None, cat=None, classes=None):
    """
    按监控器限制范围扫描图片（目录级过滤，避免全量遍历，打开更快）：
    lec_display=讲次显示名（第1讲/考试/打卡第01天/全部）、cat=分类（作业等）、classes=逗号分隔年份。
    条件都为空/全部时回退全量扫描。
    """
    if not lec_display or lec_display == '全部':
        if (not cat or cat == '全部') and (not classes or classes == '全部'):
            return get_all_images_recursive(BASE_DIR)
    lec_norm = normalize_lecture(lec_display) if lec_display and lec_display != '全部' else None
    cls_set = set(x.strip() for x in classes.split(',')) if classes and classes != '全部' else None
    # 目标 lecture 目录名（讲次补零 / 考试 / 打卡第NN天 原样）
    if lec_norm is None:
        lec_dirs = LECTURES
    elif lec_norm.isdigit():
        lec_dirs = [f"第{int(lec_norm):02d}讲"]
    else:
        lec_dirs = [lec_display]
    files = []
    try:
        entries = os.listdir(BASE_DIR)
    except OSError:
        return files
    # 班级过滤
    target_students = []
    for e in entries:
        if not is_student_folder(e):
            continue
        if cls_set and e.split('-')[0] not in cls_set:
            continue
        target_students.append(os.path.join(BASE_DIR, e))
    # 并行扫描匹配的学生目录（目录级过滤）
    def _scan_student(folder):
        out = []
        for ld in lec_dirs:
            d = os.path.join(folder, ld)
            if not os.path.isdir(d):
                continue
            # 分类过滤：统一"进该讲次的 cat 子目录"（缺该分类目录则跳过）。
            # 修复历史 bug：原实现只有"有具体讲次"时才进 cat 子目录，
            # 讲次为"全部"但有分类时 cat 被忽略 → 扫描讲次顶层混入
            # 课前小测/错题再练等其他分类图片，检索范围过宽（与监控器不一致）。
            # 考试分类：考试目录即目标（考试/考试1…为顶层目录，无 cat 子目录），
            # 且 do_search 的分类过滤已限定考试文件，故此处按"全部"处理。
            if cat and cat != '全部' and not cat.startswith('考试'):
                d = os.path.join(d, cat)
                if not os.path.isdir(d):
                    continue   # 该讲次无此分类：无匹配图片
            _, names = _scan_dir_cached_local(d)
            for n in names:
                if _is_image_file(n):
                    out.append(os.path.join(d, n))
        return out
    workers = PARALLEL_WORKERS
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for sub in ex.map(_scan_student, target_students):
            files.extend(sub)
    return _finalize_file_list(files)

def update_image_name_display():
    # 由于不再显示文件信息，这里仅更新评价UI
    if bg_path:
        name = os.path.basename(bg_path)
        meta = parse_filename(name); update_grading_ui(meta)
    else:
        if grading_frame: 
            for w in grading_frame.winfo_children(): w.destroy()

# ---------- 绘图元素类 ----------
class DrawElement:
    def __init__(self, x, y, color='red', width=2): self.x, self.y, self.color, self.width, self.type, self.id = x, y, color, width, 'base', None
    def draw(self, c, s, ox=0, oy=0): pass
    def draw_pil(self, d, s, sz): pass

class CheckElement(DrawElement):
    def __init__(self, x, y, color='red', width=3): super().__init__(x, y, color, width); self.type = 'check'
    def draw(self, c, s, ox=0, oy=0):
        sx, sy = self.x*s+ox, self.y*s+oy; b = get_base_size(); w = b*s
        c.create_line(sx-w/3, sy-w/10, sx-w/10, sy+w/2, sx+w/2, sy-w/2,
                      fill=self.color, width=max(3, self.width*s), smooth=True, tags=('element',))
    def draw_pil(self, d, s, sz):
        sx, sy = self.x*s, self.y*s; b = get_base_size(); w = b*s
        p0, p1, p2 = (sx-w/3, sy-w/10), (sx-w/10, sy+w/2), (sx+w/2, sy-w/2); pts = []
        for i in range(21):
            t = i/20
            px = (1-t)**2*p0[0] + 2*(1-t)*t*p1[0] + t**2*p2[0]
            py = (1-t)**2*p0[1] + 2*(1-t)*t*p1[1] + t**2*p2[1]
            pts.append((px, py))
        d.line(pts, fill=self.color, width=int(max(3, self.width*s)), joint='curve')

class CrossElement(DrawElement):
    def __init__(self, x, y, color='red', width=3): super().__init__(x, y, color, width); self.type = 'cross'
    def draw(self, c, s, ox=0, oy=0):
        sx, sy = self.x*s+ox, self.y*s+oy; w = 20*s
        c.create_line(sx-w/2, sy-w/2, sx+w/2, sy+w/2, fill=self.color, width=max(3, self.width*s), tags=('element',))
        c.create_line(sx-w/2, sy+w/2, sx+w/2, sy-w/2, fill=self.color, width=max(3, self.width*s), tags=('element',))
    def draw_pil(self, d, s, sz):
        sx, sy = self.x*s, self.y*s; w = 20*s
        lw = int(max(3, self.width*s))
        d.line([(sx-w/2, sy-w/2), (sx+w/2, sy+w/2)], fill=self.color, width=lw)
        d.line([(sx-w/2, sy+w/2), (sx+w/2, sy-w/2)], fill=self.color, width=lw)

class LineElement(DrawElement):
    def __init__(self, x1, y1, x2, y2, color='red', width=3): super().__init__(x1, y1, color, width); self.x2, self.y2 = x2, y2; self.type = 'line'
    def draw(self, c, s, ox=0, oy=0): c.create_line(self.x*s+ox, self.y*s+oy, self.x2*s+ox, self.y2*s+oy, fill=self.color, width=max(1, self.width*s), tags=('element',))
    def draw_pil(self, d, s, sz): d.line([(self.x*s, self.y*s), (self.x2*s, self.y2*s)], fill=self.color, width=max(1, int(self.width*s)))

class TextElement(DrawElement):
    """单行/多行普通文本（评分文字使用）。font_size 单位为像素，Tk/PIL 渲染一致"""
    def __init__(self, x, y, text='', color='red', ff='SimHei', fs=16, fw='normal', anchor='center'):
        super().__init__(x, y, color)
        self.text, self.font_family, self.font_size, self.font_weight = text, ff, fs, fw
        self.type = 'text'
        self.is_grading_text = False
        self.anchor = anchor

    def draw(self, c, s, ox=0, oy=0):
        fs = int(self.font_size * s)
        if fs <= 0: fs = 1
        f = get_tk_font(self.font_family, fs, self.font_weight)
        c.create_text(self.x*s+ox, self.y*s+oy, text=self.text, fill=self.color, font=f, anchor=self.anchor, tags=('element',))

    def draw_pil(self, d, s, sz):
        afs = int(self.font_size * s)
        if afs <= 0: afs = 1
        f = get_pil_font(self.font_family, afs)
        # 保存时加粗：按字号描边模拟（20号→1，60号→2）
        bsw = max(1, int(afs / 30))

        pil_anchor_map = {'center': 'mm', 'e': 'rm', 'w': 'lm'}
        pil_anchor = pil_anchor_map.get(self.anchor, 'mm')

        try:
            d.text((self.x*s, self.y*s), self.text, fill=self.color, font=f, anchor=pil_anchor,
                   stroke_width=bsw, stroke_fill=self.color)
        except Exception:
            try:
                bbox = d.textbbox((0, 0), self.text, font=f)
                if self.anchor == 'e':      draw_x = self.x*s - bbox[2]; draw_y = self.y*s - (bbox[1] + bbox[3]) / 2
                elif self.anchor == 'w':    draw_x = self.x*s - bbox[0]; draw_y = self.y*s - (bbox[1] + bbox[3]) / 2
                else:                        draw_x = self.x*s - (bbox[0] + bbox[2]) / 2; draw_y = self.y*s - (bbox[1] + bbox[3]) / 2
                d.text((draw_x, draw_y), self.text, fill=self.color, font=f,
                       stroke_width=bsw, stroke_fill=self.color)
            except Exception:
                d.text((self.x*s, self.y*s), self.text, fill=self.color, font=f,
                       stroke_width=bsw, stroke_fill=self.color)

class BoxTextElement(DrawElement):
    """无边框文本框：可拖动、可调整大小、文字自动换行、所见即所得（默认 20 号红色加粗）"""
    def __init__(self, x, y, w=200, h=60, text='', color='red',
                 font_family='SimHei', font_size=20, font_weight='bold',
                 align='left', valign='top', fill=False, fill_color='#ffffff', padding=6):
        super().__init__(x, y, color, 2)
        self.w, self.h = w, h
        self.text = text
        self.font_family, self.font_size, self.font_weight = font_family, font_size, font_weight
        self.align, self.valign = align, valign
        self.fill, self.fill_color, self.padding = fill, fill_color, padding
        self.type = 'boxtext'
        self.is_grading_text = False

    def _lines(self, s, f, max_w):
        return wrap_text_by_width(self.text, lambda t: f.measure(t), max_w)

    def draw(self, c, s, ox=0, oy=0):
        sx, sy = self.x*s+ox, self.y*s+oy
        sw, sh = max(1, self.w*s), max(1, self.h*s)
        pad = self.padding * s
        # 无边框文本框：不画边框线；仅可选背景填充
        if self.fill:
            c.create_rectangle(sx, sy, sx+sw, sy+sh, fill=self.fill_color, outline='')
        # 文字（自动换行 + 对齐；加粗）
        f = get_tk_font(self.font_family, self.font_size*s, self.font_weight)
        inner_w = max(1, sw - pad*2)
        lines = self._lines(s, f, inner_w)
        lh = text_line_height(f)
        # 垂直对齐
        text_h = lh * len(lines)
        if self.valign == 'middle': ty = sy + (sh - text_h) / 2
        elif self.valign == 'bottom': ty = sy + sh - text_h - pad
        else: ty = sy + pad
        for line in lines:
            line_w = f.measure(line)
            if self.align == 'center': tx = sx + sw/2 - line_w/2
            elif self.align == 'right': tx = sx + sw - pad - line_w
            else: tx = sx + pad
            c.create_text(tx, ty, text=line, fill=self.color, font=f, anchor='nw', tags=('element',))
            ty += lh

    def draw_pil(self, d, s, sz):
        sx, sy = self.x*s, self.y*s
        sw, sh = max(1, self.w*s), max(1, self.h*s)
        pad = self.padding * s
        if self.fill:
            d.rectangle([sx, sy, sx+sw, sy+sh], fill=self.fill_color, outline='')
        afs = max(1, int(self.font_size * s))
        f = get_pil_font(self.font_family, afs)
        # 保存时加粗：按字号描边模拟（20号→1，60号→2）
        bsw = max(1, int(afs / 30))
        inner_w = max(1, sw - pad*2)
        try:
            measurer = lambda t: f.getlength(t)
        except AttributeError:
            measurer = lambda t: f.getbbox(t)[2]
        lines = wrap_text_by_width(self.text, measurer, inner_w)
        lh = text_line_height(f)
        text_h = lh * len(lines)
        if self.valign == 'middle': ty = sy + (sh - text_h) / 2
        elif self.valign == 'bottom': ty = sy + sh - text_h - pad
        else: ty = sy + pad
        for line in lines:
            try: line_w = f.getlength(line)
            except AttributeError: line_w = f.getbbox(line)[2]
            if self.align == 'center': tx = sx + sw/2 - line_w/2
            elif self.align == 'right': tx = sx + sw - pad - line_w
            else: tx = sx + pad
            d.text((tx, ty), line, fill=self.color, font=f,
                   stroke_width=bsw, stroke_fill=self.color)
            ty += lh

    # ---------- 命中与控制点 ----------
    def hit(self, lx, ly, tol=0):
        return self.x <= lx <= self.x + self.w and self.y <= ly <= self.y + self.h

    def get_handles(self):
        x, y, w, h = self.x, self.y, self.w, self.h
        return {'nw': (x, y), 'ne': (x+w, y), 'sw': (x, y+h), 'se': (x+w, y+h),
                'n': (x+w/2, y), 's': (x+w/2, y+h), 'w': (x, y+h/2), 'e': (x+w, y+h/2)}

    def hit_handle(self, lx, ly, tol):
        for name, (hx, hy) in self.get_handles().items():
            if abs(lx-hx) <= tol and abs(ly-hy) <= tol:
                return name
        return None

# ---------- 核心控制流 ----------
MAX_UNDO_STEPS = 200   # 撤销栈上限（防长会话内存膨胀）

def _reset_undo():
    """清空撤销/重做栈（换图/旋转/联排切换/保存等使历史失效的场景）"""
    undo_stack.clear()
    redo_stack.clear()

def _safe_close(img):
    """安全关闭图片句柄（防切图/联排累积句柄泄漏；异常忽略）"""
    try:
        if img is not None:
            img.close()
    except Exception:
        pass

def sync_elements_ref():
    """联排模式下，把全局 elements 引用同步回当前图的 elements 槽位"""
    if tile_mode and tile_entries:
        tile_entries[tile_active]['elements'] = elements

def _snapshot_current():
    """取当前状态快照：(kind, payload, tile_active, selected_index)。
    联排模式 payload = 所有图元素深拷贝列表（撤销/重做跨图安全，不丢其他图状态）；
    单图模式 kind='single'，payload = elements 深拷贝。
    深拷贝失败返回 None（跳过记录，不崩溃不失灵）。"""
    try:
        if tile_mode and tile_entries:
            all_els = [copy.deepcopy(ent['elements']) for ent in tile_entries]
            return ('tile', all_els, tile_active, selected_index)
        return ('single', copy.deepcopy(elements), 0, selected_index)
    except Exception:
        return None   # 深拷贝失败（异常元素）：跳过本次记录，不崩溃不失灵

def save_state():
    if is_undoing: return
    snap = _snapshot_current()
    if snap is None:
        return
    undo_stack.append(snap)
    redo_stack.clear()
    if len(undo_stack) > MAX_UNDO_STEPS:
        undo_stack.pop(0)

def restore_state(state):
    global elements, selected_index, tile_active, bg_path
    kind, payload, idx, sel = state
    if kind == 'tile' and tile_mode and tile_entries:
        # 联排全量快照：逐图恢复；组内图数变化时按索引交集恢复
        n = min(len(payload), len(tile_entries))
        for i in range(n):
            tile_entries[i]['elements'] = payload[i]
        if 0 <= idx < len(tile_entries):
            tile_active = idx
        elements = tile_entries[tile_active]['elements']
        bg_path = tile_entries[tile_active]['path']   # 跨图撤销：同步聚焦图路径（防退出联排加载错图）
    else:
        elements = payload
    selected_index = sel
    if selected_index is not None and not (0 <= selected_index < len(elements)):
        selected_index = None   # 恢复后索引越界防护
    try:
        sync_elements_ref()
    except Exception:
        pass
    try:
        redraw_all()
    except Exception:
        pass

def undo(e=None):
    global is_undoing
    if not undo_stack:
        show_danmaku("没有可撤销的操作")
        return
    snap = _snapshot_current()
    if snap is not None:
        redo_stack.append(snap)
    is_undoing = True
    try:
        restore_state(undo_stack.pop())
    finally:
        is_undoing = False   # 异常也必须复位，否则 save_state 全部失效

def redo(e=None):
    global is_undoing
    if not redo_stack:
        show_danmaku("没有可恢复的操作")
        return
    snap = _snapshot_current()
    if snap is not None:
        undo_stack.append(snap)
    is_undoing = True
    try:
        restore_state(redo_stack.pop())
    finally:
        is_undoing = False


def load_background(path):
    global bg_image, bg_path, selected_index
    if path:
        try:
            if tile_mode:
                # 联排是持久模式：加载图片 = 在联排内定位（切换组并选中），不退出
                tile_focus_image(path)
                return
            # 原样加载图片（不做任何自动转向/摆正；方向调整仅用手动"旋转主图"按钮）
            old_image = bg_image
            bg_image = Image.open(path)
            _safe_close(old_image)   # 显式释放上一张图句柄（防切图累积，None 安全）
            bg_path = path
            _display_photo_cache.clear()  # 新图片，旧缓存全部失效
            _discard_line_start()         # 换图：未完成的直线起点作废
            elements.clear(); selected_index = None
            _reset_undo()
            update_image_name_display(); redraw_all()
            # 打开图片后聚焦画布：后续 ↑保存/PgDn切图 等快捷键稳定生效，
            # 不被左栏检索列表的 ↑↓ 滚动抢占（_shortcut_active 仍保护左栏聚焦场景）
            try:
                canvas.focus_set()
            except Exception:
                pass
        except Exception as e: show_danmaku(f"无法打开图片: {e}")

def tile_focus_image(path):
    """
    联排模式下定位到指定图片：若图片在别的文件夹则切换组，并在组内选中该图。
    同时按所选图片的批改状态（原图 / -改）决定组内显示内容。
    保持联排模式不变（仅手动关闭联排按钮才退出）。
    """
    if not path: return
    folder = os.path.dirname(path)
    # 目标显示状态：由所选图片决定（-改 → 已批改组）
    target_mode = 'modified' if os.path.splitext(os.path.basename(path))[0].endswith('-改') else 'orig'
    # 若所在文件夹不在列表（检索范围变化等），按当前检索范围重建
    if folder not in tile_folder_list:
        tile_folder_list[:] = _search_scope_folders()
    try:
        idx = tile_folder_list.index(folder)
    except ValueError:
        idx = tile_folder_idx
    if idx != tile_folder_idx or target_mode != tile_show_mode:
        # 切组 或 批改状态变化：按目标状态重载组
        if not _load_tile_folder(idx, target_mode):
            return
    # 在当前组内选中该图
    for i, ent in enumerate(tile_entries):
        if ent['path'] == path:
            if i != tile_active:
                set_active_tile(i)
            redraw_all()
            return
    # 组内未找到（可能超出单组上限被截断）——保持当前组

def redraw_all():
    if not canvas: return
    canvas.delete('all')
    if tile_mode:
        draw_tiles()
        return
    if bg_image:
        w, h = int(bg_image.width*scale), int(bg_image.height*scale)
        if w>0 and h>0:
            # 缓存 PhotoImage：同一张图+同一缩放尺寸只 resize 一次
            # 撤销/添加元素/滚动时尺寸不变，直接复用，避免每次全图重采样
            key = (id(bg_image), w, h)
            photo = _display_photo_cache.get(key)
            if photo is None:
                img = bg_image.resize((w,h), Image.Resampling.BILINEAR)
                photo = ImageTk.PhotoImage(img)
                _display_photo_cache[key] = photo
                # 内存保护：只保留最近 3 个尺寸（图变了 id 变，自动失效）
                if len(_display_photo_cache) > 3:
                    _display_photo_cache.pop(next(iter(_display_photo_cache)))
            bg_photo = photo
            canvas.create_image(0,0, anchor=tk.NW, image=bg_photo); canvas.image_ref = bg_photo
            canvas.config(scrollregion=(0,0,w,h))
    else: canvas.config(scrollregion=(0,0,1000,800))
    # 绘制元素（单图模式）
    for e in elements: e.draw(canvas, scale)
    # 绘制选中框
    draw_selection_overlay()

def draw_selection_overlay():
    """在选中元素上绘制边框/控制点（单图模式）"""
    if selected_index is None or not (0 <= selected_index < len(elements)):
        return
    e = elements[selected_index]
    if isinstance(e, BoxTextElement):
        sx, sy, sw, sh = e.x*scale, e.y*scale, e.w*scale, e.h*scale
        canvas.create_rectangle(sx, sy, sx+sw, sy+sh, outline='#0099ff', width=1, dash=(4,2))
        # 控制点方块（随缩放保持可见）
        tol = max(4, 5*scale)
        for hx, hy in e.get_handles().values():
            canvas.create_rectangle(hx*scale-tol, hy*scale-tol, hx*scale+tol, hy*scale+tol,
                                    fill='#0099ff', outline='white')
    else:
        # 点/线元素用近似范围标记
        tol = 8*scale
        x, y = e.x*scale, e.y*scale
        canvas.create_oval(x-tol, y-tol, x+tol, y+tol, outline='#0099ff', width=1, dash=(2,2))

def add_element(elem):
    global selected_index
    save_state()   # 必须先记录"操作前"状态（否则第一步永远无法撤销）
    elements.append(elem)
    selected_index = len(elements) - 1
    redraw_all()

def del_elem(e=None):
    global selected_index
    if selected_index is not None and 0 <= selected_index < len(elements):
        save_state(); del elements[selected_index]; selected_index = None
        sync_elements_ref()
        redraw_all()

# ---------- 鼠标事件 ----------
def hit_test_element(lx, ly):
    """在当前 elements 中做命中测试，返回索引（后画的优先）；未命中返回 None"""
    for i in range(len(elements)-1, -1, -1):
        e = elements[i]
        if isinstance(e, BoxTextElement):
            if e.hit(lx, ly): return i
        elif isinstance(e, LineElement):
            # 点到线段距离近似
            x1, y1, x2, y2 = e.x, e.y, e.x2, e.y2
            dx, dy = x2-x1, y2-y1
            if dx == 0 and dy == 0: dist = math.hypot(lx-x1, ly-y1)
            else:
                t = max(0, min(1, ((lx-x1)*dx + (ly-y1)*dy) / (dx*dx + dy*dy)))
                px, py = x1 + t*dx, y1 + t*dy
                dist = math.hypot(lx-px, ly-py)
            if dist <= 12: return i
        else:
            if abs(lx-e.x) <= 12 and abs(ly-e.y) <= 12: return i
    return None

def _tile_disp_params(ent, idx):
    """联排元素坐标换算参数 (显示缩放, 显示原点x, 显示原点y)：
    元素逻辑坐标 = 原图像素坐标；显示位置 = 逻辑坐标 × scale + 原点偏移。
    缺失（未绘制）时用 tile_scale + 格子坐标兜底。"""
    disp = ent.get('disp')
    if disp:
        ix, iy = disp[0], disp[1]
    else:
        ix, iy = tile_layout[idx][0], tile_layout[idx][1]
    off = ent.get('disp_off')
    if off:
        return ent.get('disp_scale', tile_scale), off[0], off[1]
    return tile_scale, ix, iy


def point_to_logic(event):
    """把画布事件坐标转为逻辑坐标（图内像素，基于实际显示矩形）"""
    x, y = canvas.canvasx(event.x), canvas.canvasy(event.y)
    if tile_mode:
        ent = tile_entries[tile_active]
        ds, dox, doy = _tile_disp_params(ent, tile_active)
        return (x - dox)/ds, (y - doy)/ds, True
    return x/scale, y/scale, False

def _discard_line_start():
    """丢弃未完成的直线起点（切换工具/模式/图片/组时调用）：
    否则下次单击会从很久以前的旧点拉出直线（跨工具/跨图残留，历史 bug）"""
    try:
        if hasattr(canvas, '_line_start'):
            delattr(canvas, '_line_start')
    except Exception:
        pass


def _dispatch_click(lx, ly, mode, handle_tol):
    """画布点击工具分发（单图/联排共用，消除两份 ~50 行重复）：
    lx/ly 为图内逻辑坐标；handle_tol 为文本框控制点命中容差。
    返回 'break'（阻止传播到 root 级鼠标快捷键）。"""
    global selected_index, drag_state
    if mode != 'line':
        _discard_line_start()   # 非直线操作（含右键画叉）后，遗留的起点作废
    cfg = get_tool_config(mode)
    if mode == 'select':
        # 选择：命中元素则选中并准备拖动；点空白取消选择
        idx = hit_test_element(lx, ly)
        if idx is not None:
            selected_index = idx
            e = elements[idx]
            if isinstance(e, BoxTextElement):
                handle = e.hit_handle(lx, ly, handle_tol)
                if handle:
                    drag_state = {'type': 'resize', 'handle': handle, 'start_lx': lx, 'start_ly': ly,
                                  'orig': (e.x, e.y, e.w, e.h), 'moved': False}
                else:
                    drag_state = {'type': 'move', 'start_lx': lx, 'start_ly': ly,
                                  'orig': (e.x, e.y), 'moved': False}
            else:
                drag_state = {'type': 'move', 'start_lx': lx, 'start_ly': ly,
                              'orig': (e.x, e.y), 'moved': False}
        else:
            selected_index = None
        redraw_all()
    elif mode == 'check': add_element(CheckElement(lx, ly, color=cfg['color'], width=cfg['width']))
    elif mode == 'cross': add_element(CrossElement(lx, ly, color=cfg['color'], width=cfg['width']))
    elif mode == 'line':
        if not hasattr(canvas, '_line_start'): canvas._line_start = (lx, ly)
        else:
            x1, y1 = canvas._line_start
            add_element(LineElement(x1, y1, lx, ly, color=cfg['color'], width=cfg['width']))
            delattr(canvas, '_line_start')
    elif mode == 'text':
        # 规则：点击已有文本框 → 切换为编辑该文本框；点击空白 → 创建新文本框（自动进入编辑）
        idx = hit_test_element(lx, ly)
        if idx is not None and isinstance(elements[idx], BoxTextElement):
            selected_index = idx
            start_box_edit(elements[idx])
            redraw_all()
            return 'break'
        tcfg = get_section('textbox')
        box = BoxTextElement(lx, ly, w=200, h=60, text=tcfg.get('text', ''),
                             color=tcfg.get('color', 'red'), font_family=tcfg.get('font', 'KaiTi'),
                             font_size=tcfg.get('size', 20), font_weight=tcfg.get('weight', 'bold'),
                             align=tcfg.get('align', 'left'), valign=tcfg.get('valign', 'top'),
                             fill=tcfg.get('fill', False), fill_color=tcfg.get('fill_color', '#ffffff'),
                             padding=tcfg.get('padding', 6))
        add_element(box)
        start_box_edit(box)   # 创建后立即进入输入状态
    return 'break'   # 阻止传播到 root 级鼠标快捷键（画布交互优先）

def canvas_click(event):
    try:
        canvas.focus_set()   # 点击画布：聚焦主绘图区（方向键等快捷键只在画布区生效）
    except Exception:
        pass
    # 若正在就地编辑文本框，点击画布其他位置先提交（避免点击丢失）
    if editing_text is not None:
        finish_box_edit()
    if tile_mode:
        tile_canvas_click(event)
        return 'break'   # 阻止传播到 root 级鼠标快捷键（画布交互优先）
    lx, ly, _ = point_to_logic(event)
    mode = left_click_mode if event.num == 1 else 'cross'
    return _dispatch_click(lx, ly, mode, 12)

def _canvas_pos_of_box(box):
    """文本框在画布上的像素位置与编辑字号（单图/联排）"""
    if tile_mode:
        idx = tile_active
        if not (0 <= idx < len(tile_entries)):
            return None
        ent = tile_entries[idx]
        if not ent.get('disp'):
            return None
        ds, dox, doy = _tile_disp_params(ent, idx)
        return (dox + box.x * ds, doy + box.y * ds,
                max(60, box.w * ds), max(30, box.h * ds),
                max(8, box.font_size * ds))
    return (box.x * scale, box.y * scale,
            max(60, box.w * scale), max(30, box.h * scale),
            max(8, box.font_size * scale))

def _do_focus_edit():
    """延迟聚焦：始终聚焦"当前"编辑控件（旧控件已销毁时安全跳过）"""
    global _edit_focus_after
    _edit_focus_after = None
    if editing_text is not None:
        try:
            # 不调用 update_idletasks()：回调链中处理事件队列可能级联触发其他回调
            editing_text.focus_set()
            editing_text.focus_force()
        except Exception:
            pass

def start_box_edit(box):
    """
    在画布上就地编辑文本框内容（无对话框）：创建/双击文本框后直接输入，
    Enter=提交，Esc=取消，Ctrl+Enter=换行，点击画布其他位置=提交。
    """
    global editing_box, editing_text, editing_window, _edit_focus_after
    finish_box_edit()
    # 取消旧的延迟聚焦回调，避免指向已销毁控件抢焦点
    if _edit_focus_after is not None:
        try:
            canvas.after_cancel(_edit_focus_after)
        except Exception:
            pass
        _edit_focus_after = None
    pos = _canvas_pos_of_box(box)
    if pos is None:
        return
    x, y, w, h, fs = pos
    tw = tk.Text(canvas, width=1, height=1, wrap=tk.WORD,
                 font=get_tk_font(box.font_family, fs, 'normal'),
                 bg='white', fg='black', relief=tk.FLAT,
                 highlightthickness=0, insertbackground='black')
    try:
        tw.insert('1.0', box.text)
    except Exception:
        pass
    editing_window = canvas.create_window(x, y, anchor=tk.NW, window=tw,
                                          width=int(w), height=int(h))
    editing_box = box
    editing_text = tw
    # 立即聚焦 + 延迟聚焦兜底（延迟回调总是指向当前 editing_text，安全）
    try:
        tw.focus_set()
        tw.focus_force()
    except Exception:
        pass
    _edit_focus_after = canvas.after(10, _do_focus_edit)

    def _commit(e):
        # 仅当仍是当前编辑控件时提交（旧控件的回车不会误伤新控件）
        if editing_text is tw:
            finish_box_edit()
        return 'break'   # 阻止 Enter 插入换行

    def _newline(e):
        # Ctrl+Enter：插入换行（文本框内换行）
        if editing_text is not tw:
            return 'break'
        try:
            tw.insert(tk.INSERT, '\n')
        except Exception:
            tw.insert('end', '\n')
        return 'break'

    def _on_escape(e):
        if editing_text is tw:
            cancel_box_edit()
        return 'break'

    def _on_focus_out(e):
        # 关键：旧文本框的失焦事件可能在下一个文本框创建后才被处理，
        # 只有"当前编辑控件"的失焦才提交（否则会误杀新控件的编辑状态）
        if editing_text is tw:
            finish_box_edit()

    tw.bind('<Return>', _commit)
    tw.bind('<Control-Return>', _newline)   # Ctrl+回车 = 换行
    tw.bind('<Escape>', _on_escape)
    tw.bind('<FocusOut>', _on_focus_out)

def finish_box_edit():
    """提交就地编辑的内容到文本框，并关闭编辑控件"""
    if editing_text is None:
        return
    save_state()   # 记录修改前状态（可撤销文本框内容修改）
    try:
        text = editing_text.get('1.0', 'end-1c')
        if editing_box is not None:
            editing_box.text = text
    except Exception:
        pass
    cancel_box_edit()
    redraw_all()

def cancel_box_edit():
    """取消/关闭就地编辑控件（不保存内容）"""
    global editing_box, editing_text, editing_window, _edit_focus_after
    if editing_window is not None:
        try:
            canvas.delete(editing_window)
        except Exception:
            pass
    editing_box = None
    editing_text = None
    editing_window = None
    _edit_focus_after = None   # 排队中的聚焦回调会在 _do_focus_edit 里安全跳过

def on_canvas_motion(event):
    """选择工具下：悬停文本框控制点/本体时切换光标（拖动/缩放提示）"""
    if left_click_mode != 'select' or editing_text is not None:
        return
    if selected_index is None or not (0 <= selected_index < len(elements)):
        canvas.configure(cursor='arrow')
        return
    el = elements[selected_index]
    if not isinstance(el, BoxTextElement):
        canvas.configure(cursor='arrow')
        return
    try:
        if tile_mode:
            ent = tile_entries[tile_active]
            ds, dox, doy = _tile_disp_params(ent, tile_active)
            lx = (canvas.canvasx(event.x) - dox) / ds
            ly = (canvas.canvasy(event.y) - doy) / ds
        else:
            lx, ly, _ = point_to_logic(event)
        handle = el.hit_handle(lx, ly, 12)
        cursors = {'nw': 'size_nw_se', 'se': 'size_nw_se', 'ne': 'size_ne_sw', 'sw': 'size_ne_sw',
                   'n': 'size_ns', 's': 'size_ns', 'w': 'size_we', 'e': 'size_we'}
        canvas.configure(cursor=cursors.get(handle, 'fleur'))
    except Exception:
        canvas.configure(cursor='arrow')

def on_drag(event):
    """拖动：移动元素或调整文本框大小（B1-Motion）"""
    if drag_state is None or selected_index is None:
        return
    if not (0 <= selected_index < len(elements)):
        return
    # 首次移动时记录"操作前"状态（撤销可回到拖动前位置）
    if not drag_state.get('saved'):
        drag_state['saved'] = True
        save_state()
    lx, ly, _ = point_to_logic(event)
    e = elements[selected_index]
    if drag_state['type'] == 'move':
        e.x = drag_state['orig'][0] + (lx - drag_state['start_lx'])
        e.y = drag_state['orig'][1] + (ly - drag_state['start_ly'])
        drag_state['moved'] = True
    elif drag_state['type'] == 'resize' and isinstance(e, BoxTextElement):
        ox0, oy0, w0, h0 = drag_state['orig']
        handle = drag_state['handle']
        dx, dy = lx - drag_state['start_lx'], ly - drag_state['start_ly']
        if 'w' in handle: e.x = ox0 + dx; e.w = w0 - dx
        if 'e' in handle: e.w = w0 + dx
        if 'n' in handle: e.y = oy0 + dy; e.h = h0 - dy
        if 's' in handle: e.h = h0 + dy
        e.w = max(20, e.w); e.h = max(20, e.h)
        drag_state['moved'] = True
    redraw_all()

def on_release(event):
    """拖动结束（ButtonRelease-1）：状态已在首次移动时记录，无需重复"""
    global drag_state
    drag_state = None

def on_double_click(event):
    """双击文本框进入编辑"""
    global selected_index
    if tile_mode:
        x, y = canvas.canvasx(event.x), canvas.canvasy(event.y)
        idx = hit_tile_index(x, y)
        if idx is None: return 'break'
        if idx != tile_active: set_active_tile(idx)
        ent = tile_entries[tile_active]
        ds, dox, doy = _tile_disp_params(ent, tile_active)
        lx, ly = (x - dox)/ds, (y - doy)/ds
    else:
        lx, ly, _ = point_to_logic(event)
    sel = hit_test_element(lx, ly)
    if sel is not None and isinstance(elements[sel], BoxTextElement):
        # 双击文本框：进入画布就地编辑（无对话框）
        selected_index = sel
        start_box_edit(elements[sel])
    return 'break'   # 阻止传播到 root 级鼠标快捷键

def _wheel_steps(e):
    """滚轮步数归一化（120=1 格）"""
    d = getattr(e, 'delta', 0)
    if abs(d) >= 120:
        return d // 120
    return 1 if d > 0 else -1


def on_zoom_slider(v):
    """缩放滑块：单图模式控制 scale；联排模式控制 tile_zoom"""
    global scale, tile_zoom
    if tile_mode:
        tile_zoom = float(v)
        compute_tile_layout(); redraw_all()
    else:
        scale = float(v)
        redraw_all()


def _ctrl_wheel_zoom(delta):
    """Ctrl+滚轮缩放核心：正=放大 负=缩小（单图 scale / 联排 tile_zoom）"""
    global scale, tile_zoom
    factor = 1.1 if delta > 0 else 0.9
    if tile_mode:
        tile_zoom = min(5.0, max(0.1, tile_zoom * factor))
        compute_tile_layout(); redraw_all()
    else:
        scale = min(5.0, max(0.1, scale * factor))
        scale_slider.set(scale); redraw_all()


def on_mousewheel(e):
    """画布滚轮统一分发（widget 级绑定，处理完必须 return 'break' 阻止 bind_all 二次处理）：
    - Ctrl+滚轮 = 缩放当前图/联排视图
    - Alt+滚轮  = 横向滚动
    - 无修饰    = 垂直滚动
    （修复历史问题：Ctrl/Alt+滚轮时普通 <MouseWheel> 绑定也会触发，
     导致"既滚动又缩放/双倍横滚"，表现为组合滚轮时不时失灵）"""
    mods = e.state & 0x4        # Control
    alt = e.state & 0x20000     # Alt/Mod1
    if mods:
        _ctrl_wheel_zoom(_wheel_steps(e))
    elif alt:
        canvas.xview_scroll(-_wheel_steps(e), 'units')
    else:
        canvas.yview_scroll(-_wheel_steps(e), 'units')
    return 'break'   # 关键：阻止 <MouseWheel> 继续传播到 bind_all


def on_mousewheel_linux(e):
    """Linux Button-4/5 兼容（widget 级绑定，同样按修饰符分发 + break）"""
    mods = e.state & 0x4
    alt = e.state & 0x20000
    step = -1 if e.num == 4 else 1
    if mods:
        _ctrl_wheel_zoom(step)
    elif alt:
        canvas.xview_scroll(step, 'units')
    else:
        canvas.yview_scroll(step, 'units')
    return 'break'


def _global_wheel(e):
    """
    全局滚轮兜底（bind_all）：只在画布区域之外时触发——
    画布上的滚轮已被 on_mousewheel（widget 绑定 + break）处理并阻止传播；
    本函数负责：右栏滚动；其余区域（左栏/下拉框等）不拦截，交给焦点控件。
    """
    # 右栏滚动（复用 _on_right_wheel 的区域判定）
    try:
        x = right_pane.winfo_pointerx(); y = right_pane.winfo_pointery()
        rx = right_pane.winfo_rootx(); ry = right_pane.winfo_rooty()
        rw = right_pane.winfo_width(); rh = right_pane.winfo_height()
        if rx <= x <= rx + rw and ry <= y <= ry + rh:
            steps = _wheel_steps(e)
            right_canvas.yview_scroll(-steps, 'units')
            return 'break'
    except Exception:
        return None
    return None   # 不在右栏：不拦截（左栏列表/输入框等自行滚动）

# ---------- 联排多图模式 ----------
def hit_tile_index(x, y):
    """画布坐标命中哪张平铺图；未命中返回 None"""
    for i, (ox, oy, w, h) in enumerate(tile_layout):
        if ox <= x <= ox+w and oy <= y <= oy+h:
            return i
    return None

def set_active_tile(i):
    """切换当前编辑的图，同步 elements 引用与 bg_path（退出联排时恢复该图）。
    不清撤销栈：联排快照含全部图 elements + tile_active，跨图撤销安全（撤销会切回操作时的图）"""
    global elements, tile_active, selected_index, bg_path
    if not (0 <= i < len(tile_entries)): return
    sync_elements_ref()          # 保存当前图的引用
    tile_active = i
    elements = tile_entries[i]['elements']
    bg_path = tile_entries[i]['path']
    selected_index = None
    redraw_all()

def _search_scope_folders():
    """
    联排切组范围 = 当前检索结果图片（原图与 -改 均可）所在的文件夹集合，按路径排序。
    这样联排上下页被限制在检索要求（讲次/分类/班级/序号/状态）内；
    组内显示原图还是 -改，由进入联排/切换时选中的图片状态决定。
    检索为"全部"时等价于所有含图片的文件夹。
    """
    folders = set()
    for f in search_result_list:
        folders.add(os.path.dirname(f))
    return sorted(folders)

def _folder_display_name(folder):
    """组的显示名：学生/讲次/类型（相对路径）"""
    try:
        rel = os.path.relpath(folder, BASE_DIR)
        return rel
    except Exception:
        return os.path.basename(folder)

def _close_tile_images(entries):
    """显式关闭组内图片文件句柄（切组/退出/保存更新时调用，
    防 Windows 文件句柄累积；Pillow 惰性 Image 依赖 GC 释放太慢）"""
    for ent in entries:
        _safe_close(ent.get('image'))


def _load_tile_folder(idx, mode=None):
    """
    加载第 idx 个文件夹（组）的图片到 tile_entries。
    mode: 'orig'=显示原图  'modified'=显示 -改（批改结果）；None 沿用当前状态。
    自动降级：目标状态无文件时切换到另一种（如全部已批改 → 显示 -改 组）。
    切组时把当前组的未保存标注暂存到 tile_drafts，切回时恢复，不丢失。
    """
    global tile_entries, tile_active, elements, selected_index
    global tile_folder_idx, bg_path, tile_show_mode
    if not (0 <= idx < len(tile_folder_list)):
        return False
    if mode is None:
        mode = tile_show_mode
    folder = tile_folder_list[idx]
    try:
        files = [os.path.join(folder, f) for f in os.listdir(folder)
                 if _is_image_file(f)]
    except OSError:
        return False
    # 按批改状态分组：原图 / -改
    orig_files = [f for f in files
                  if not os.path.splitext(os.path.basename(f))[0].endswith('-改')]
    mod_files = [f for f in files
                 if os.path.splitext(os.path.basename(f))[0].endswith('-改')]
    if mode == 'modified':
        chosen = mod_files
        if not chosen:
            chosen = orig_files      # 无 -改：降级显示原图
            mode = 'orig'
    else:
        # 原图模式：若无原图，或所有原图均已批改（-改 完整），直接显示 -改 组
        mod_stems = {os.path.splitext(os.path.basename(f))[0] for f in mod_files}
        need_grade = [f for f in orig_files
                      if os.path.splitext(os.path.basename(f))[0] + '-改' not in mod_stems]
        if not need_grade:
            chosen = mod_files       # 全部已批改：自动显示 -改 组
            mode = 'modified'
        else:
            chosen = orig_files      # 还有待批改：显示原图组
    if not chosen:
        return False
    chosen.sort(key=tile_seq_key)
    # 单文件夹张数保护（默认上限较大，文件夹一般不超过）
    max_count = int(get_cfg('tile', 'max_count', 50))
    if len(chosen) > max_count:
        show_danmaku(f"该文件夹 {len(chosen)} 张，超过上限只显示前 {max_count} 张")
        chosen = chosen[:max_count]
    # 暂存当前组未保存状态（默认无条件更新，含空列表）：
    # 内容 = {'elements': 标注, 'rot90': 顺时针90°旋转次数}
    # 若只暂存"有元素的图"，用户删除某图全部标注后切组再切回，
    # tile_drafts 里残留的旧标注会让已删除的标注"复活"；
    # rot90 随暂存恢复，避免切组后旋转丢失、元素坐标与重载原图错位。
    # 设置 tile.keep_drafts_on_group_switch=False 时：切组不保留草稿（丢弃并清空，
    # 切回不恢复），仅释放句柄——用户可选"切组即放弃未保存批改"。
    keep_drafts = bool(get_cfg('tile', 'keep_drafts_on_group_switch', True))
    if not keep_drafts:
        tile_drafts.clear()                       # 不保留：丢弃全部未保存草稿
        if tile_entries:
            _close_tile_images(tile_entries)
    elif tile_entries:
        for ent in tile_entries:
            tile_drafts[ent['path']] = {'elements': list(ent['elements']),
                                        'rot90': ent.get('rot90', 0),
                                        'disp': ent.get('disp')}   # 保存时按显示矩形换算坐标
        _close_tile_images(tile_entries)   # 暂存完毕：显式释放旧组句柄
    # 构建新组（原样加载；标注与旋转从暂存恢复；不做任何自动转向）
    tile_entries = []
    for f in chosen:
        try:
            img = Image.open(f)
        except Exception:
            continue
        draft = tile_drafts.get(f)
        els = list(draft['elements']) if draft else []
        rot = draft['rot90'] if draft else 0
        for _ in range(rot):   # 重放旋转（元素坐标已按旋转后暂存，直接匹配）
            img = img.rotate(-90, expand=True)
        tile_entries.append({'path': f, 'image': img,
                             'elements': els, 'rot90': rot,
                             'name': os.path.basename(f), 'photo': None, 'photo_key': None,
                             'disp': None})
    if not tile_entries:
        return False
    tile_folder_idx = idx
    tile_show_mode = mode
    tile_active = 0
    _discard_line_start()   # 切组：未完成的直线起点作废（防跨组从旧点画线）
    elements = tile_entries[0]['elements']
    selected_index = None
    _reset_undo()
    bg_path = tile_entries[0]['path']   # 退出联排时恢复当前组 1 号图
    compute_tile_layout()
    redraw_all()
    m0 = parse_filename(os.path.basename(tile_entries[0]['path']))
    if m0: update_grading_ui(m0)
    return True

def tile_next_group():
    """联排模式：转到下一个文件夹（组）"""
    if not tile_mode: return
    if tile_folder_idx + 1 >= len(tile_folder_list):
        show_danmaku("已是最后一组")
        return
    if _load_tile_folder(tile_folder_idx + 1, tile_show_mode):
        tag = "（已批改）" if tile_show_mode == 'modified' else ""
        show_danmaku(f"组 {tile_folder_idx+1}/{len(tile_folder_list)}：{_folder_display_name(tile_folder_list[tile_folder_idx])}{tag}")

def tile_prev_group():
    """联排模式：转到上一个文件夹（组）"""
    if not tile_mode: return
    if tile_folder_idx <= 0:
        show_danmaku("已是第一组")
        return
    if _load_tile_folder(tile_folder_idx - 1, tile_show_mode):
        tag = "（已批改）" if tile_show_mode == 'modified' else ""
        show_danmaku(f"组 {tile_folder_idx+1}/{len(tile_folder_list)}：{_folder_display_name(tile_folder_list[tile_folder_idx])}{tag}")

def tile_seq_key(f):
    m = parse_filename(os.path.basename(f))
    if m and m['seq'].isdigit():
        return (0, int(m['seq']))
    return (1, 0)

def toggle_tile_mode():
    """开启/关闭联排模式：一个文件夹 = 一组，按序号无缝拼接平铺到画布"""
    global tile_mode, elements, selected_index, tile_zoom
    global tile_folder_list, tile_folder_idx, tile_drafts, tile_show_mode, bg_image
    if tile_mode:
        # 退出前处理未保存标注：默认"保存后退出"（不弹窗；历史弹窗已取消）
        unsaved = [ent for ent in tile_entries if ent['elements']] or \
                  [p for p, d in tile_drafts.items() if d and d.get('elements')]
        if unsaved:
            # 保存失败时**不退出**：保留 entries/drafts 与未保存标注，
            # 避免原实现"保存失败仍清空全部草稿"导致批改成果丢失
            if not save_tiles():
                show_danmaku("保存失败，已保留未保存标注（暂不退出联排）")
                return
        tile_mode = False
        _close_tile_images(tile_entries)   # 显式释放联排图句柄
        tile_entries.clear(); tile_layout.clear(); tile_drafts.clear()
        elements.clear(); selected_index = None
        _reset_undo()
        if bg_path:
            try:
                bg_image = Image.open(bg_path)   # 原样加载，不做任何摆正
                _display_photo_cache.clear()
                update_image_name_display()
            except Exception: pass
        if tile_btn: tile_btn.config(relief=tk.RAISED, bg='SystemButtonFace')
        if nav_prev_btn: nav_prev_btn.config(text="上一张")
        if nav_next_btn: nav_next_btn.config(text="下一张")
        scale_slider.set(1.0)
        redraw_all()
        show_danmaku("已退出联排模式")
        return
    if not bg_path:
        show_danmaku("请先在左侧列表打开一张图片，再开启联排")
        return
    # 联排范围 = 当前检索结果图片所在文件夹（限制在检索要求内）
    tile_folder_list = _search_scope_folders()
    if not tile_folder_list:
        show_danmaku("当前检索区间内没有图片，请先检索或调整检索条件")
        return
    # 组内显示状态：由进入时选中的图片决定（-改 → 已批改组；原图 → 原图组）
    tile_show_mode = 'modified' if os.path.splitext(os.path.basename(bg_path))[0].endswith('-改') else 'orig'
    folder = os.path.dirname(bg_path)
    try:
        tile_folder_idx = tile_folder_list.index(folder)
    except ValueError:
        tile_folder_idx = 0
    tile_drafts = {}
    pending_elements = list(elements) if elements else []
    pending_bg = bg_path
    tile_mode = True
    if not _load_tile_folder(tile_folder_idx, tile_show_mode):
        tile_mode = False
        show_danmaku("当前文件夹没有图片"); return
    # 把当前打开图的已有标注挂到对应 entry（若在当前组）
    if pending_elements:
        matched = False
        for i, ent in enumerate(tile_entries):
            if ent['path'] == pending_bg:
                ent['elements'] = pending_elements
                if i == tile_active:
                    elements = pending_elements
                matched = True
                break
        if not matched:
            # 打开图不在当前组（如进入联排时组内全是 -改、原图被过滤）：
            # 标注暂存到 tile_drafts，切回该文件夹或保存时不会丢失
            tile_drafts[pending_bg] = {'elements': pending_elements, 'rot90': 0}
    tile_zoom = 1.0
    scale_slider.set(1.0)
    if tile_btn: tile_btn.config(relief=tk.SUNKEN, bg='#d1e7dd')
    if nav_prev_btn: nav_prev_btn.config(text="上一组")
    if nav_next_btn: nav_next_btn.config(text="下一组")
    tag = "（已批改）" if tile_show_mode == 'modified' else ""
    show_danmaku(f"联排模式：组 {tile_folder_idx+1}/{len(tile_folder_list)}，共 {len(tile_entries)} 张{tag}，评分打在 1 号图")

def compute_tile_layout():
    """计算联排布局：所有图片放入统一尺寸的格子（像一张大图）
    格子宽/高取所有图片缩放后的最大值，保证每行每列边缘对齐；
    图片在格子内的实际显示位置由 draw_tiles 按 fill_mode 决定并存入 entry['disp']"""
    global tile_layout, tile_scale
    if not tile_entries:
        tile_layout = []; return
    cfg = get_section('tile')
    cols = max(1, int(cfg.get('columns', 2)))
    spacing = max(0, int(cfg.get('spacing', 0)))
    # 极端防护：图片尺寸异常（0/负）时兜底为 1，防除零/负格子
    max_w = max((max(1, e['image'].width) for e in tile_entries), default=800)
    max_h = max((max(1, e['image'].height) for e in tile_entries), default=600)
    avail_w = max(canvas.winfo_width() - spacing*2, 300)
    fit_scale = min(1.0, (avail_w - (cols+1)*spacing) / (max_w * cols))
    fit_scale = max(0.05, fit_scale)
    tile_scale = max(0.05, fit_scale * tile_zoom)
    cell_w = max_w * tile_scale
    cell_h = max_h * tile_scale
    layout = []
    cur_x, cur_y = spacing, spacing
    for i in range(len(tile_entries)):
        if i > 0 and i % cols == 0:
            cur_y += cell_h + spacing
            cur_x = spacing
        layout.append((cur_x, cur_y, cell_w, cell_h))
        cur_x += cell_w + spacing
    tile_layout = layout

def _fit_image_to_cell(image, cell_w, cell_h, fill_mode):
    """把图片放入 (cell_w, cell_h) 格子。
    返回 (显示图, 显示矩形(ix, iy, dw, dh), 显示缩放scale, 裁剪偏移left, 裁剪偏移top)。
    坐标换算约定（关键防位移）：元素逻辑坐标 = **原图像素坐标**（与单图模式一致）；
    显示位置 = 原图坐标 × scale + 显示原点偏移(ox+ix-left, oy+iy-top)；
    保存时按 1.0 直接画原图，无需任何换算。"""
    iw, ih = max(1, int(image.size[0])), max(1, int(image.size[1]))   # 防 0/负尺寸除零
    cell_w, cell_h = max(1, int(cell_w)), max(1, int(cell_h))
    if fill_mode == 'cover':
        # 等比缩放到覆盖整个格子，居中裁剪（填满，可能裁掉边缘）
        scale = max(cell_w/iw, cell_h/ih)
        nw, nh = max(1, int(round(iw*scale))), max(1, int(round(ih*scale)))
        disp = image.resize((nw, nh), Image.Resampling.BILINEAR)
        left, top = (nw - cell_w)//2, (nh - cell_h)//2
        disp = disp.crop((left, top, left+cell_w, top+cell_h))
        return disp, (0, 0, cell_w, cell_h), scale, left, top
    # contain：等比缩放到格子内，居中留白（不裁内容）
    scale = min(cell_w/iw, cell_h/ih)
    nw, nh = max(1, int(round(iw*scale))), max(1, int(round(ih*scale)))
    disp = image.resize((nw, nh), Image.Resampling.BILINEAR)
    ix, iy = (cell_w - nw)//2, (cell_h - nh)//2
    return disp, (ix, iy, nw, nh), scale, 0, 0

def draw_tiles():
    """绘制联排模式：统一格子无缝拼接（像一张大图）
    每张图按 fill_mode 填充格子（contain 留白 / cover 裁剪）；
    当前编辑的图用蓝色细框高亮，带标注的图右上角显示 ✎"""
    cfg = get_section('tile')
    spacing = max(0, int(cfg.get('spacing', 0)))
    show_labels = cfg.get('show_labels', False)
    fill_mode = cfg.get('fill_mode', 'contain')
    photos = []
    for i, (ox, oy, w, h) in enumerate(tile_layout):
        ent = tile_entries[i]
        # 底图（显示尺寸缓存，避免拖动元素时反复重采样）
        key = (w, h, fill_mode)
        if ent.get('photo_key') != key:
            disp, rect, scale, left, top = _fit_image_to_cell(ent['image'], w, h, fill_mode)
            ent['disp'] = (ox + rect[0], oy + rect[1], rect[2], rect[3])  # 画布坐标下的实际显示矩形
            # 坐标换算（防保存位移）：元素逻辑坐标 = 原图像素坐标；
            # 显示位置 = 原图坐标 × scale + 显示原点偏移(含 cover 裁剪偏移)
            ent['disp_scale'] = scale
            ent['disp_off'] = (ox + rect[0] - left, oy + rect[1] - top)
            ent['photo'] = ImageTk.PhotoImage(disp)
            ent['photo_key'] = key
        photo = ent['photo']
        photos.append(photo)
        # contain 模式：格子内留白区域填白色（贴近纸张）
        if fill_mode != 'cover':
            canvas.create_rectangle(ox, oy, ox+w, oy+h, fill='white', outline='')
        ix, iy = ent['disp'][0], ent['disp'][1]
        canvas.create_image(ix, iy, anchor='nw', image=photo)
        # 元素（原图坐标 × 显示缩放 + 显示原点偏移）
        ds = ent.get('disp_scale', tile_scale)
        dox, doy = ent.get('disp_off', (ix, iy))
        for el in ent['elements']:
            el.draw(canvas, ds, dox, doy)
        # 序号标签（默认关闭，设置中可开启）
        if show_labels:
            seq = tile_seq_label(ent['name'])
            canvas.create_text(ox+4, oy+4, anchor='nw', text=f"#{seq}",
                               fill='#333333', font=('微软雅黑', 10))
        # 无缝拼接：无边框。仅当前编辑的图用蓝色细框高亮
        if i == tile_active:
            canvas.create_rectangle(ox-1, oy-1, ox+w+1, oy+h+1, outline='#3399ff', width=2)
        # 未保存标记
        if ent['elements']:
            canvas.create_text(ox+w-6, oy+6, anchor='ne', text='✎', fill='#0055ff', font=('微软雅黑', 11))
    canvas._tile_photos = photos
    total_w = max((l[0]+l[2] for l in tile_layout), default=800) + spacing
    total_h = max((l[1]+l[3] for l in tile_layout), default=600) + spacing
    canvas.config(scrollregion=(0, 0, total_w, total_h))

def tile_seq_label(name):
    m = parse_filename(name)
    return m['seq'] if m else '?'

def tile_canvas_click(event):
    """联排模式下的点击：切换活动图 + 在当前图绘图/选择"""
    x, y = canvas.canvasx(event.x), canvas.canvasy(event.y)
    idx = hit_tile_index(x, y)
    if idx is None:
        # 点击空白：仅重绘（联排模式不渲染选中框，selected_index 无需清理）
        redraw_all(); return 'break'
    if idx != tile_active:
        set_active_tile(idx)
    # 基于实际显示矩形换算图内逻辑坐标（原图像素坐标）
    ent = tile_entries[tile_active]
    ds, dox, doy = _tile_disp_params(ent, tile_active)
    lx, ly = (x - dox)/ds, (y - doy)/ds
    # 修复历史 bug：contain 模式下点击格子留白（图像未覆盖区域）换算出的
    # lx/ly 在图像外（负值/超宽高），照常落点会创建"画在图像边界外"的元素，
    # 保存时被裁剪、标注凭空消失——越界只切活动图，不落点。
    img = ent.get('image')
    if img is not None:
        iw, ih = img.width, img.height
        if lx < -1 or ly < -1 or lx > iw + 1 or ly > ih + 1:
            redraw_all()
            return 'break'
    mode = left_click_mode if event.num == 1 else 'cross'
    return _dispatch_click(lx, ly, mode, 12/ds)

def save_tiles():
    """联排模式保存：把每张有元素的图合成各自 -改 文件。
    除当前组外，还会保存切组时暂存在 tile_drafts 里的其他组未保存标注
    （避免退出联排选"保存"时丢失之前组的内容）。
    返回 True=全部成功；False=存在失败（失败的标注保留，不清空）。
    修复历史 bug：原实现任一张图写入失败（磁盘满/占用/权限）就中断整批且
    不返回失败标志，调用方（退出联排）据此认为已保存，随后清空全部草稿——
    一次保存失败 = 整批批改成果丢失且无提示。"""
    saved = 0
    attempted = 0
    try:
        # 合并待保存项：当前组 entries + 暂存的其他组（path 不重复）
        pending = list(tile_entries)
        cur_paths = {ent['path'] for ent in tile_entries}
        for p, d in tile_drafts.items():
            if p not in cur_paths and d and d.get('elements'):
                pending.append({'path': p, 'elements': list(d['elements']),
                                'image': None, 'rot90': d.get('rot90', 0),
                                'disp': d.get('disp')})
        for ent in pending:
            if not ent['elements']: continue
            attempted += 1
            try:
                if ent.get('image') is not None:
                    img = ent['image'].copy()   # 当前组：内存图（旋转已应用）
                else:
                    img = Image.open(ent['path'])   # 暂存组：磁盘原图，需重放旋转
                    for _ in range(ent.get('rot90', 0)):
                        img = img.rotate(-90, expand=True)
            except Exception:
                try:
                    img = Image.open(ent['path'])
                except Exception as ex2:
                    show_danmaku(f"保存失败 {os.path.basename(ent['path'])}: {ex2}（标注已保留）")
                    continue   # 该图无法打开：跳过，不中断其他图，标注保留
            # 元素逻辑坐标 = 原图像素坐标（与单图模式统一），保存直接画原图：
            # 显示缩放（fit_scale/tile_zoom）只影响绘制，不影响保存坐标——
            # 这是"标注保存位移"的根本修复（旧实现联排用显示图坐标，视图非 1:1 必错位）
            draw = ImageDraw.Draw(img)
            for el in ent['elements']:
                el.draw_pil(draw, 1.0, (img.width, img.height))
            dn = os.path.dirname(ent['path']); bn, ext = os.path.splitext(os.path.basename(ent['path']))
            sp = os.path.join(dn, bn + '-改' + ext) if "-改" not in bn else ent['path']
            ext_l = os.path.splitext(sp)[1].lower()
            save_kwargs = {}
            if ext_l in ('.jpg', '.jpeg'):
                save_kwargs['quality'] = 95; save_kwargs['subsampling'] = 0
            elif ext_l == '.png':
                save_kwargs['optimize'] = True
            img.save(sp, **save_kwargs)
            # 检索列表同步（红标转化）：原图条目移除、-改 条目加入——
            # 否则 do_search 基于旧列表仍把该图标红（对齐单图 save_image 的列表更新）
            if sp != ent['path']:   # bn 已含 -改 时 sp==path（二次保存），不增删
                if ent['path'] in cached_nav_list:
                    cached_nav_list.remove(ent['path'])
                if sp not in cached_nav_list:
                    cached_nav_list.append(sp)
            ent['elements'].clear()   # 与单图模式一致：保存后清空标注
            tile_drafts.pop(ent['path'], None)  # 已写入 -改，清理暂存避免切回重复
            # 关键：把该图底图更新为"含标注的合成图"并失效显示缓存——
            # 否则用户再次标注并保存时，底图仍是原图，旧标注会丢失
            # （与单图模式 save_image 里 bg_image = img + 清缓存 行为对齐）
            _close_tile_images([ent])   # 旧底图句柄已 copy 完成，显式释放
            ent['image'] = img
            ent['photo'] = None
            ent['photo_key'] = None
            ent['rot90'] = 0   # 旋转已固化到 -改，重置（重载时从原图起点开始）
            if ent not in tile_entries:
                # 暂存组条目：保存完毕即释放磁盘句柄（该 dict 保存后即被丢弃）
                _safe_close(img)
            saved += 1
        if saved:
            cached_nav_list.sort()
            clear_scan_cache()
            update_filters_options(); do_search()
            # 联排保存后撤销栈失效（标注已固化到 -改，Ctrl+Z 会"复活"已保存标注
            # 导致重复叠加）——与单图 save_image 的清栈行为对齐
            _reset_undo()
        redraw_all()
        if attempted and saved < attempted:
            show_danmaku(f"已保存 {saved}/{attempted} 张，失败张的标注已保留")
            return False
        if saved:
            write_modifier_changed()   # 通知监视器：文件已变动，请刷新检索同步
        show_danmaku(f"已保存 {saved} 张")
        return True
    except Exception as ex:
        show_danmaku(f"保存失败: {ex}（标注已保留）")
        return False

# ---------- 图片导航与删除 ----------
def load_adjacent_image(direction):
    if tile_mode:
        # 联排模式：上下页 = 整组切换（直接转到下一组/上一组）
        if direction == 'prev': tile_prev_group()
        else: tile_next_group()
        return
    if not bg_path: show_danmaku("请先在左侧列表单击打开主图"); return
    if not search_result_list: show_danmaku("当前检索区间无图片"); return
    try: idx = search_result_list.index(bg_path)
    except ValueError: show_danmaku("当前图片不在检索区间内，请重新检索"); return
    new_idx = (idx - 1) % len(search_result_list) if direction == 'prev' else (idx + 1) % len(search_result_list)
    new_path = search_result_list[new_idx]
    if new_path != bg_path: load_background(new_path)

def delete_current_image():
    global bg_path, bg_image
    if tile_mode:
        show_danmaku("请先退出联排模式再删除图片"); return
    if not bg_path: return
    if messagebox.askyesno("确认删除", f"彻底删除主图源文件？\n{os.path.basename(bg_path)}"):
        path_to_delete = bg_path; next_path = None
        if bg_path in search_result_list:
            idx = search_result_list.index(bg_path); search_result_list.remove(bg_path)
            if search_result_list: next_path = search_result_list[idx % len(search_result_list)]
        try:
            bg_image = None; bg_path = None; elements.clear(); redraw_all()
            if os.path.exists(path_to_delete): os.remove(path_to_delete)
            clear_scan_cache()  # 删除文件后目录 mtime 已变，缓存需重置
            write_modifier_changed()   # 通知监视器：文件已变动，请刷新检索同步
            update_image_name_display(); refresh_nav_list(False)
            if next_path: load_background(next_path)
            else: show_danmaku("已无图片")
        except Exception as e: show_danmaku(f"删除失败: {e}")

def _rotate_elements_clockwise(elements, w, h):
    """把元素坐标随图片顺时针旋转 90° 变换（原图 w×h → 旋转后 h×w）。
    点/线：坐标映射 (x,y) -> (h-y, x)；文本框：坐标映射 + 宽高互换。"""
    for e in elements:
        if isinstance(e, LineElement):
            e.x, e.y = h - e.y, e.x
            e.x2, e.y2 = h - e.y2, e.x2
        elif isinstance(e, BoxTextElement):
            e.x, e.y = h - e.y, e.x
            e.w, e.h = e.h, e.w   # 旋转 90° 后宽高互换
        else:
            # Check / Cross / Text（含评分文字）
            e.x, e.y = h - e.y, e.x

def rotate_main_image():
    global bg_image
    if tile_mode:
        # 联排模式：分别旋转当前激活的图（含其标注元素，坐标同步变换）
        if not tile_entries or not (0 <= tile_active < len(tile_entries)):
            show_danmaku("当前没有图片")
            return
        idx = tile_active
        ent = tile_entries[idx]
        img = ent['image']
        w, h = img.size
        rotated = img.rotate(-90, expand=True)   # 顺时针 90°
        _safe_close(img)   # 显式释放旧图句柄（旋转已生成新对象，防 Windows 句柄累积）
        ent['image'] = rotated
        ent['rot90'] = (ent.get('rot90', 0) + 1) % 4   # 记录旋转次数（4次复原），切组时随暂存恢复
        _rotate_elements_clockwise(ent['elements'], w, h)
        # 底图变了：失效显示缓存并重排（旋转后尺寸交换，格子宽高需重算）
        ent['photo'] = None
        ent['photo_key'] = None
        # 关键：旋转改变了图片坐标系，撤销栈里存的是旋转前的元素坐标，
        # 不清空会导致旋转后按撤销 → 标注错位（单图模式同样处理，见下）
        _reset_undo()
        compute_tile_layout()
        redraw_all()
        show_danmaku(f"已顺时针旋转第 {idx+1} 张（保存后生效）")
        return
    if not bg_image: show_danmaku("请先在左侧列表单击打开主图"); return
    w, h = bg_image.size
    rotated = bg_image.rotate(-90, expand=True)
    _safe_close(bg_image)   # 显式释放旧图句柄（与联排模式一致，防 Windows 句柄累积）
    bg_image = rotated
    _rotate_elements_clockwise(elements, w, h)   # 标注随图旋转（与联排模式一致，防错位）
    _display_photo_cache.clear()  # 图片对象已替换
    _reset_undo()   # 坐标系已变，历史撤销状态失效（防撤销错位）
    redraw_all()

# ---------- 保存 ----------
def save_image(e=None):
    global bg_path, bg_image, selected_index
    if tile_mode:
        save_tiles(); return
    if not bg_image and not elements: return
    w, h = (bg_image.width, bg_image.height) if bg_image else (800, 600)
    img = bg_image.copy() if bg_image else Image.new('RGB', (w, h), 'white')
    draw = ImageDraw.Draw(img)
    for el in elements: el.draw_pil(draw, 1.0, (w, h))

    if bg_path:
        dn = os.path.dirname(bg_path); bn, ext = os.path.splitext(os.path.basename(bg_path))
        sp = os.path.join(dn, bn + '-改' + ext) if "-改" not in bn else bg_path
        try:
            # 按格式使用高质量参数保存，减小体积加快磁盘写入
            ext_l = os.path.splitext(sp)[1].lower()
            save_kwargs = {}
            if ext_l in ('.jpg', '.jpeg'):
                save_kwargs['quality'] = 95
                save_kwargs['subsampling'] = 0
            elif ext_l == '.png':
                save_kwargs['optimize'] = True
            img.save(sp, **save_kwargs)
            if sp != bg_path:
                if bg_path in cached_nav_list: cached_nav_list.remove(bg_path)
                if sp not in cached_nav_list:
                    cached_nav_list.append(sp)
                    cached_nav_list.sort()
            bg_path = sp; bg_image = img
            elements.clear(); selected_index = None
            _reset_undo()
            _display_photo_cache.clear()  # 图片对象已替换，防止 id 复用误命中缓存
            update_image_name_display()
            update_filters_options(); do_search()
            redraw_all()
            show_danmaku("图片已保存")
            write_modifier_changed()   # 通知监视器：文件已变动，请刷新检索同步
            # 保存后聚焦画布：连续批改（↑保存→PgDn下一张→批改）不被打断
            try:
                canvas.focus_set()
            except Exception:
                pass
        except Exception as ex: show_danmaku(f"保存失败: {ex}")

# ---------- 设置中心（统一设置窗口：修改器+监控器） ----------
def _apply_settings_center():
    """设置中心保存后：重读配置并即时应用（工具/快捷键/联排/弹幕时长）"""
    global _config_cache, tool_config
    _config_cache = load_config()
    tool_config = _config_cache.get('tools', DEFAULT_CONFIG['tools'])
    gcfg = _config_cache.get('grading', DEFAULT_CONFIG['grading'])
    try:
        grading_size = max(16, min(200, int(gcfg.get('size', 60))))
    except (TypeError, ValueError):
        grading_size = 60
    lists = [elements] + [entry.get('elements', []) for entry in tile_entries]
    seen = set()
    for lst in lists:
        if id(lst) in seen:
            continue
        seen.add(id(lst))
        for elem in lst:
            if isinstance(elem, TextElement) and getattr(elem, 'is_grading_text', False):
                elem.color = gcfg.get('color', 'red')
                elem.font_family = gcfg.get('font', 'SimHei')
                elem.font_size = grading_size
    bind_shortcuts()
    if tile_mode:
        compute_tile_layout()
    redraw_all()
    show_danmaku("设置已保存并应用")


def open_settings():
    """打开统一设置中心（修改器全部设置 + 监控器设置；与监控器共用同一窗口）。
    监控器页参数下次启动监控器生效；修改器页参数保存后即时生效。
    嵌入模式：路由到主窗口「设置」页（单窗口原则，不另弹 Toplevel）。"""
    import 设置中心
    try:
        if _embedded and _embed_container is not None:
            on_settings = getattr(_embed_container, '_dsh_on_open_settings', None)
            if callable(on_settings):
                on_settings()
                return
        设置中心.open_settings_window(root, 'modifier', apply_modifier=_apply_settings_center)
    except Exception as e:
        show_danmaku(f"打开设置中心失败：{e}")

def _ime_open():
    """Windows 输入法（IME）是否开启（中文输入状态下裸字符键会被输入法消费，
    若同时触发快捷键会弹出候选框/无响应，需在 _shortcut_active 中屏蔽）。"""
    try:
        import ctypes
        imm32 = ctypes.windll.imm32
        hwnd = root.winfo_id()
        ctx = imm32.ImmGetContext(hwnd)
        if not ctx:
            return False
        try:
            return imm32.ImmGetOpenStatus(ctx) != 0
        finally:
            imm32.ImmReleaseContext(hwnd, ctx)
    except Exception:
        return False


def _shortcut_active(e=None):
    """
    全局快捷键是否生效：只在主绘图区（画布区域）内控制，避免与左/右工具栏冲突。
    - 就地编辑文本框时屏蔽
    - **中文输入法开启时，裸字符键（字母/数字/标点）屏蔽**——避免输入法候选框
      与快捷键同时触发（组合键 Ctrl/Shift/Alt 不受输入法消费，照常生效）
    - 焦点在画布区域（canvas_frame 内，如 canvas 本身）或无焦点（刚操作画布）→ 允许
    - 焦点在左栏/右栏或输入类控件（检索列表、下拉框、输入框等）→ 屏蔽，
      让这些区域自己的方向键行为（如检索列表上下选择、下拉框切换）不被全局快捷键抢占
    """
    if editing_text is not None:
        return False
    if e is not None:
        try:
            # 鼠标按钮事件（含 Windows 侧键 Button-4..9）：侧键不改变键盘焦点，
            # 用"指针是否在画布区域"判定，而非键盘焦点（修复侧键绑了没反应——
            # 此前焦点在左栏/右栏控件残留时侧键被焦点判定挡掉）
            num = getattr(e, 'num', 0)
            etype = getattr(e, 'type', None)
            if num in (4, 5, 6, 7, 8, 9) or (etype is not None and etype in ('4', '5')):
                return _pointer_in_canvas()
            ks = getattr(e, 'keysym', '')
            # 裸字符键（无修饰、可打印）：中文输入法开启时屏蔽。
            # 组合键（Ctrl/Shift/Alt 修饰）不被输入法消费，照常生效——
            # 否则 Ctrl+Z 撤销 / Ctrl+Y 重做 / Ctrl+T 联排 在中文输入法下全部失灵
            if len(ks) == 1 and ks.isprintable() and _ime_open():
                if not (e.state & 0x4 or e.state & 0x1 or e.state & 0x20000):
                    # 用户自定义的裸字符快捷键（如 save=<w>）在中文输入法开启时也
                    # 等效生效（大小写兼容：keysym 小写后与配置比对）——
                    # 否则用户按 w 保存却因输入法开启被屏蔽，表现为"保存没反应"
                    if ks.lower() not in _custom_char_shortcuts:
                        return False
        except Exception:
            pass
    # 键盘事件生效范围与鼠标一致：**指针在画布上即生效**（修复嵌入模式键盘快捷键
    # 失效——原实现要求键盘焦点在 canvas_frame 内，而主窗口导航/其他控件常持有焦点，
    # 导致 Ctrl+Z/方向键/Ctrl+T 等全部被挡；鼠标侧键因用指针判定一直正常）。
    # 指针不在画布时回退焦点判定（独立模式点击画布后焦点在画布也能用）。
    if _pointer_in_canvas():
        return True
    w = root.focus_get()
    if w is None:
        return True
    try:
        cur = w
        while cur is not None:
            if cur is canvas_frame:
                return True
            try:
                p = cur.winfo_parent()
            except Exception:
                return False
            if p in ('', '.'):
                break
            cur = cur.nametowidget(p)
    except Exception:
        pass
    return False


def _pointer_in_canvas():
    """指针是否位于画布区域内（鼠标侧键/滚轮快捷键用；修复侧键不改变键盘焦点的问题）"""
    try:
        if canvas is None:
            return False
        x = root.winfo_pointerx(); y = root.winfo_pointery()
        cx = canvas.winfo_rootx(); cy = canvas.winfo_rooty()
        cw = canvas.winfo_width(); ch = canvas.winfo_height()
        if cw <= 0 or ch <= 0:
            return True   # 尚未布局，保守允许
        return cx <= x <= cx + cw and cy <= y <= cy + ch
    except Exception:
        return True   # 异常时保守允许

_last_shortcut_binds = []   # 上一轮绑定过的快捷键序列（重绑前全部解除，防旧键残留/串键）
_custom_char_shortcuts = set()   # 用户配置的自定义裸字符快捷键 keysym 小写集合（如 save=<w>→{'w'}）；
                                 # 由 bind_shortcuts 更新，供 _shortcut_active 在中文输入法开启时放行


def bind_shortcuts():
    """绑定全局快捷键。先解除上一轮绑定的全部序列（含固定键），再绑当前配置：
    修复自定义快捷键后旧键残留（如 prev 从 <Left> 改到 <Up> 后 <Left> 仍会翻页）。
    所有回调把事件传入 _shortcut_active(e) 以支持输入法状态检测。
    绑定目标统一为 toplevel(root)：独立模式是修改器 Tk 根；嵌入模式是主窗口 Tk 根。
    【关键修复】原实现嵌入模式绑 _embed_container（页面 Frame）——Tk 按键事件沿
    focus widget→class→toplevel→all 的 bindtags 链传播，页面 Frame 不在该链中，
    嵌入后快捷键【完全失效】。绑到 toplevel 后，任意子控件（画布）有焦点都会触发，
    再由 _shortcut_active 按焦点位置限制生效范围（只在画布区生效）。"""
    global _last_shortcut_binds, _custom_char_shortcuts
    unbind_shortcuts()
    _last_shortcut_binds = []
    target = root   # toplevel（独立=修改器窗口，嵌入=主窗口）
    c = load_config(); sc = c.get('shortcuts', DEFAULT_CONFIG['shortcuts'])

    # 收集用户配置的自定义裸字符快捷键（如 save=<w>），供 _shortcut_active 判定
    _custom_char_shortcuts = set()
    for _seq in sc.values():
        _inner = (_seq or '').strip('<>')
        if len(_inner) == 1 and _inner.isprintable():
            _custom_char_shortcuts.add(_inner.lower())

    def _bind(seq, fn):
        try:
            target.bind(seq, fn)
            _last_shortcut_binds.append(seq)
        except Exception:
            try:
                show_danmaku(f"快捷键绑定失败：{seq}")
            except Exception:
                pass   # 非法序列（如录制出错）忽略，不影响其他键

    def _bind_letter(seq, fn):
        """绑定快捷键序列；若是单字母（如 <w>）自动补绑大写 <W>，实现大小写兼容"""
        _bind(seq, fn)
        inner = (seq or '').strip('<>')
        if len(inner) == 1 and inner.isalpha():
            up = inner.upper()
            if up != inner:
                _bind(f'<{up}>', fn)

    def _bind_action(default_seq, key, fn):
        """绑定一个动作：默认键盘键常驻 + 用户自定义键并存（键盘/鼠标侧键都能用）。
        修复：用户把 prev/next 配成鼠标侧键后，键盘方向键不再绑定 → 表现为
        "键盘快捷键没反应"；现默认键始终绑定，自定义键（侧键/w 等）并存。"""
        seqs = [default_seq]
        custom = sc.get(key, default_seq)
        if custom and custom != default_seq:
            seqs.append(custom)
        for seq in seqs:
            _bind_letter(seq, fn)

    # 注意：_shortcut_active(e) 为 True 表示焦点在主绘图区（快捷键应生效）。
    # 条件顺序必须写成 "生效区 → 执行动作"，否则方向键在画布区切不了图、
    # 在左栏反而会抢走列表框的上下选择（历史 bug：曾写反）。
    _bind_action('<Left>', 'prev', lambda e: load_adjacent_image('prev') if _shortcut_active(e) else None)
    _bind_action('<Right>', 'next', lambda e: load_adjacent_image('next') if _shortcut_active(e) else None)
    _bind_action('<Up>', 'save', lambda e: save_image() if _shortcut_active(e) else None)
    _bind_action('<Control-t>', 'tile', lambda e: toggle_tile_mode() if _shortcut_active(e) else None)
    # PgUp/PgDn：单图模式切图片，联排模式切整组
    _bind('<Prior>', lambda e: load_adjacent_image('prev') if _shortcut_active(e) else None)
    _bind('<Next>', lambda e: load_adjacent_image('next') if _shortcut_active(e) else None)
    _bind('<Control-z>', lambda e: undo() if _shortcut_active(e) else None)
    _bind('<Control-y>', lambda e: redo() if _shortcut_active(e) else None)
    _bind('<Delete>', lambda e: del_elem() if _shortcut_active(e) else None)  # 绑定Delete键删除选中元素


def unbind_shortcuts():
    """解除当前已绑定的全部快捷键序列（页面切换/关闭时清理，防残留占用共享 root）。
    与 bind_shortcuts 一致：统一从 toplevel(root) 解除。"""
    global _last_shortcut_binds
    target = root
    for seq in _last_shortcut_binds:
        try:
            target.unbind(seq)
        except Exception:
            pass
    _last_shortcut_binds = []


# ---------- 监控器联动：检索范围接收（复用窗口，避免重复打开） ----------
_SCOPE_PORT = 47518   # 本地端口：监控器 → 修改器 检索规则传输
_scope_queue = queue.Queue()   # socket 线程 → 主线程 安全传递
_search_btns = None            # 检索/刷新按钮行（学生面板 pack 时插入其前）

def _apply_scope(scope):
    """应用监控器传来的检索范围（主线程调用）：更新筛选并检索、置顶窗口。
    内容模式：讲次/分类/班级；学生模式：姓名/类别（切换检索方式）。"""
    if _app_closing:
        return
    try:
        if scope.get('search_mode') == 'student':
            # 姓名-类别检索：切换检索方式并应用学生/类别
            search_mode_var.set('student')
            switch_search_mode()
            if scope.get('name'):
                search_student_var.set(scope['name'])
            if scope.get('category'):
                search_cat_var.set(scope['category'])
        else:
            if scope.get('lecture'):
                search_lecture_var.set(scope['lecture'])
            if scope.get('category'):
                search_cat_var.set(scope['category'])
            if scope.get('classes') and scope.get('classes') != '全部':
                search_class_var.set(scope['classes'])
        # 优先直接采用监视器发布的检索结果（修改器不再自行承担检索）；
        # 监视器文件缺失/范围不一致时回退自行 do_search（独立运行兼容）
        global cached_nav_list, _monitor_search_mtime
        snapshot = _monitor_nav_snapshot()
        if snapshot is not None:
            cached_nav_list = snapshot
            # 已直接应用快照，记录当前文件 mtime：轮询不再重复刷新同一版本
            try:
                _monitor_search_mtime = os.path.getmtime(MONITOR_SEARCH_FILE)
            except OSError:
                _monitor_search_mtime = 0.0
        do_search()
        try:
            if not _embedded:
                root.deiconify(); root.lift(); root.focus_force()
            canvas.focus_set()   # 应用规则后聚焦画布，立即可用快捷键批改
        except Exception:
            pass
        show_danmaku("已应用监控器检索范围")
    except Exception as e:
        print(f"应用检索范围失败: {e}")

def _poll_scope_queue():
    """主线程轮询检索规则队列（socket 线程不直接调 Tk，避免跨线程 Tk 调用失败）"""
    global _scope_poll_after
    try:
        while True:
            scope = _scope_queue.get_nowait()
            _apply_scope(scope)
    except Exception:
        pass   # 队列空或其他异常：继续轮询
    if not _app_closing:
        _scope_poll_after = root.after(300, _poll_scope_queue)


# ---------- 监控器检索状态同步（修改器不再自行检索，直接读取监视器发布的检索结果） ----------
# 监视器每次刷新后把 当前检索范围 + 范围内图片文件列表 写入 MONITOR_SEARCH_FILE；
# 修改器据此作为检索底表（cached_nav_list），不再自行全量扫描；
# 修改器保存/删除/重命名后写 MODIFIER_CHANGED_FILE，监视器检测到后立即刷新并重新发布。
_monitor_search_mtime = 0.0   # 已应用的检索状态文件 mtime（避免重复应用同一版本）


def _monitor_scope_matches(scope, current=None):
    """监视器发布的检索范围是否与修改器当前检索条件一致。
    一致才采用其文件列表（避免把监视器的范围强加给修改器内手动改过的条件）。
    current: 主线程快照的当前检索条件 dict（后台线程调用时传入，避免非主线程读 Tk 变量）；
    为 None 时直接读 Tk 变量（仅主线程调用场景）。"""
    try:
        if current is None:
            current = {
                'mode': search_mode_var.get() if search_mode_var else 'content',
                'lecture': search_lecture_var.get() if search_lecture_var else '',
                'category': search_cat_var.get() if search_cat_var else '',
                'classes': search_class_var.get() if search_class_var else '',
                'student': search_student_var.get() if search_student_var else '',
            }
        if scope.get('search_mode') == 'student':
            if current.get('mode') != 'student':
                return False
            if scope.get('name') and scope['name'] != current.get('student'):
                return False
            cat = scope.get('category')
            if cat and cat != '全部' and cat != current.get('category'):
                return False
            return True
        # 内容模式
        if current.get('mode') != 'content':
            return False
        if scope.get('lecture') and \
                normalize_lecture(scope['lecture']) != normalize_lecture(current.get('lecture')):
            return False
        if scope.get('category') and scope['category'] != current.get('category'):
            return False
        if scope.get('classes') and scope['classes'] != current.get('classes'):
            return False
        return True
    except Exception:
        return False


def _monitor_nav_snapshot(current=None, embedded=None):
    """读取监视器发布的检索结果文件列表；范围与当前条件一致时返回
    _finalize_file_list 处理后的列表（与自行检索语义一致），否则返回 None。
    嵌入模式（单窗口整合，监视器与本页同进程）：
    - 监视器每 5 秒发布检索状态，本页直接继承（"修改器不再自行承担检索"）
    - 跳过 120 秒新鲜度（同进程内监视器状态始终权威）
    - 跳过范围匹配（本页筛选直接在监视器发布的文件集内过滤，避免回退全量扫描）
    独立运行（无监视器）：保持原语义——新鲜度保护 + 范围匹配，不符则回退自行检索。
    current: 主线程快照的当前检索条件（后台线程调用时传入，避免跨线程读 Tk）。"""
    if embedded is None:
        embedded = _embedded
    state = read_monitor_search_state()
    if not state:
        return None
    files = state.get('files')
    if not isinstance(files, list):
        return None
    if not embedded:
        try:
            if time.time() - float(state.get('updated', 0)) > 120:
                return None   # 快照过期：监视器未在运行，回退自行检索
        except (TypeError, ValueError):
            return None
        if not _monitor_scope_matches(state.get('scope') or {}, current):
            return None
    # v3.4.2 起 检索状态 files 存相对 BASE_DIR 路径；读回拼成绝对路径（亦兼容旧版绝对路径）
    abs_files = []
    for f in files:
        if isinstance(f, str):
            abs_files.append(f if os.path.isabs(f) else os.path.join(BASE_DIR, f))
    return _finalize_file_list(abs_files)


def _current_search_snapshot():
    """主线程快照当前检索条件（供后台线程调用 _monitor_nav_snapshot 使用）。"""
    return {
        'mode': search_mode_var.get() if search_mode_var else 'content',
        'lecture': search_lecture_var.get() if search_lecture_var else '',
        'category': search_cat_var.get() if search_cat_var else '',
        'classes': search_class_var.get() if search_class_var else '',
        'student': search_student_var.get() if search_student_var else '',
    }


def _poll_monitor_search():
    """主线程周期同步监视器检索状态：监视器刷新后（检索状态文件更新），
    修改器重新读取其文件列表并刷新检索结果（"同步监视器刷新后的信息"）。"""
    global cached_nav_list, _monitor_search_mtime, _monitor_poll_after
    if _app_closing:
        return
    try:
        mt = os.path.getmtime(MONITOR_SEARCH_FILE)
    except OSError:
        mt = 0.0
    if mt and mt > _monitor_search_mtime:
        snapshot = _monitor_nav_snapshot()
        if snapshot is not None:
            _monitor_search_mtime = mt
            if snapshot != cached_nav_list:
                cached_nav_list = snapshot
                try:
                    do_search()
                except Exception:
                    pass
    if not _app_closing:
        _monitor_poll_after = root.after(1500, _poll_monitor_search)

def _start_scope_listener():
    """后台线程监听本地端口：接收监控器的检索规则（修改器已打开时复用窗口）。
    socket 线程只写入队列，由主线程 after 轮询应用（避免跨线程 Tk 调用）。"""
    import socket
    def _listen():
        try:
            srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            srv.bind(('127.0.0.1', _SCOPE_PORT))
            srv.listen(1)
            srv.settimeout(1.0)
        except OSError:
            return   # 端口被占：已有修改器实例在监听，本实例不再监听（保持独立）
        while not _app_closing:
            try:
                conn, _ = srv.accept()
            except socket.timeout:
                continue
            except OSError:
                break
            try:
                # 修复历史 bug：①recv 无超时——监控器连接后不发数据/崩溃时
                # 无限阻塞，accept 循环停摆，此后所有范围同步永久失效；
                # ②单次 recv 可能收到半条 TCP 消息——改为读至连接关闭（EOF）
                # 再整段解析（发送端每次 sendall 后立即关闭连接）。
                conn.settimeout(3.0)
                buf = b''
                while True:
                    try:
                        chunk = conn.recv(4096)
                    except socket.timeout:
                        break
                    if not chunk:
                        break
                    buf += chunk
                if buf:
                    scope = json.loads(buf.decode('utf-8'))
                    _scope_queue.put(scope)
            except Exception as e:
                print(f"接收检索范围失败: {e}")
            finally:
                try:
                    conn.close()
                except Exception:
                    pass
        try:
            srv.close()
        except Exception:
            pass
    threading.Thread(target=_listen, daemon=True).start()
    _poll_scope_queue()   # 主线程启动轮询

# ---------- 检索功能 ----------
def _collect_seqs(files):
    """从文件列表中收集图片序号（自动识别，供序号下拉选项）"""
    seqs = set()
    for f in files:
        m = parse_filename(os.path.basename(f))
        if m:
            seqs.add(m['seq'])
    # 排序键：数字序号按数值排前，非数字（如命名异常）排后——避免 int/str 混合比较崩溃
    return ["全部"] + sorted(list(seqs), key=seq_sort_key)


def update_student_options(e=None):
    """姓名-类别检索：班级下拉→序号下拉 逐级过滤，刷新 序号与姓名 选项。
    班级+序号唯一对应学生时，姓名下拉自动锁定（"得到一个学生的姓名"）。"""
    if student_seq_combo_box is None:
        return
    cls = student_class_var.get() if student_class_var else '全部'
    seqs, names = collect_student_options(cls)
    student_seq_combo_box.config(values=seqs)
    # 序号过滤姓名
    sel_seq = student_seq_var.get() if student_seq_var else '全部'
    if sel_seq != '全部':
        pad = f"{int(sel_seq):02d}"
        names = ['全部'] + [n for n in names[1:] if n.split('-')[1] == pad]
    student_combo_box.config(values=names)
    cur = search_student_var.get() if search_student_var else '全部'
    if cur != '全部' and cur not in names:
        search_student_var.set('全部')   # 选中学生不在新范围：自动重置


def _student_seq_selected(e=None):
    """序号选择：刷新姓名选项；班级+序号唯一 → 自动选中姓名并检索"""
    update_student_options()
    if student_seq_var.get() != '全部':
        cands = [n for n in student_combo_box.cget('values') if n != '全部']
        if len(cands) == 1:
            if search_student_var.get() != cands[0]:
                search_student_var.set(cands[0])
    do_search()


def switch_search_mode():
    """切换 内容检索（讲次-学生）↔ 姓名-类别检索（学生-讲次）。
    两种模式筛选条件各自独立，共用同一检索列表/修改器。"""
    global search_mode
    mode = search_mode_var.get() if search_mode_var else 'content'
    if mode == search_mode:
        return
    search_mode = mode
    for f in _content_mode_frames:
        if mode == 'content':
            f.pack(fill=tk.X, pady=2)
        else:
            f.pack_forget()
    for f in _student_mode_frames:
        if mode == 'student':
            # 学生面板插入到检索按钮之前（条件区位置），避免追加到按钮下方
            try:
                f.pack(fill=tk.X, pady=2, before=_search_btns)
            except Exception:
                f.pack(fill=tk.X, pady=2)
        else:
            f.pack_forget()
    if mode == 'student':
        update_student_options()
    do_search()

def update_filters_options():
    seq_combo_box.config(values=_collect_seqs(cached_nav_list))

def _parse_cli_args():
    """
    解析监控器传入的检索范围参数：--lecture 讲次 --category 分类 --classes 班级(逗号分隔)。
    无参数时返回全 None（作为独立程序默认全部）。
    """
    out = {'lecture': None, 'category': None, 'classes': None,
           'search_mode': None, 'name': None}
    argv = sys.argv[1:]
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == '--lecture' and i + 1 < len(argv):
            out['lecture'] = argv[i + 1]; i += 2
        elif a == '--category' and i + 1 < len(argv):
            out['category'] = argv[i + 1]; i += 2
        elif a == '--classes' and i + 1 < len(argv):
            out['classes'] = argv[i + 1]; i += 2
        elif a == '--search-mode' and i + 1 < len(argv):
            out['search_mode'] = argv[i + 1]; i += 2
        elif a == '--name' and i + 1 < len(argv):
            out['name'] = argv[i + 1]; i += 2
        else:
            i += 1
    return out

def _collect_student_dir(files, directory):
    """把目录内的图片文件加入列表（增量扫描缓存，学生检索用）"""
    try:
        _, names = scan_dir_incremental(directory)
    except Exception:
        return
    for n in names:
        if _is_image_file(n):
            files.append(os.path.join(directory, n))


def _do_search_student():
    """姓名-类别检索：选定学生的 各讲次×(类别) + 考试 + 打卡 图片。
    - 类别（作业/课前小测/错题再练/全部）：考试与打卡在任何类别下都包含
    - 班级/序号仅用于快速定位姓名下拉中的学生，不影响结果
    - 与内容检索（讲次-班级-学生）独立，共用同一检索结果列表/修改器"""
    global search_result_list
    search_result_list.clear()
    if search_listbox: search_listbox.delete(0, tk.END)
    student = search_student_var.get()
    status = search_status_var.get()
    cat = search_cat_var.get()
    if cat.startswith('考试'):
        cat = '全部'   # 学生模式类别不含考试（考试/打卡自动包含）
    if not student or student == '全部':
        # 未确定学生：列表留空（不显示任何选项/提示项）
        return
    base = os.path.join(BASE_DIR, student)
    # 优先直接采用监视器发布的检索结果（修改器不再自行承担检索）；
    # 快照缺失/范围不一致时回退自行扫描该学生目录（独立运行兼容）
    global cached_nav_list
    snapshot = _monitor_nav_snapshot()
    if snapshot is not None:
        cached_nav_list = snapshot
    if snapshot is not None:
        files = list(snapshot)
    else:
        if not os.path.isdir(base):
            if search_listbox:
                search_listbox.insert(tk.END, '（未找到该学生文件夹）')
            return
        files = []
        for ld in LECTURES:
            if is_exam_or_checkin(ld):
                # 考试/打卡：任何类别下都包含（直接目录）
                d0 = os.path.join(base, ld)
                if os.path.isdir(d0):
                    _collect_student_dir(files, d0)
            elif cat == '全部':
                # 全部类别：遍历讲次下全部子分类目录（作业/课前小测/错题再练）
                for sub in LECTURE_SUB_TYPES:
                    d0 = os.path.join(base, ld, sub)
                    if os.path.isdir(d0):
                        _collect_student_dir(files, d0)
            else:
                d0 = os.path.join(base, ld, cat)
                if os.path.isdir(d0):
                    _collect_student_dir(files, d0)
    # 排序 + 用 -改 替换原图（与内容检索一致的"当前有效形态"语义）
    files = _finalize_file_list(files)
    # 状态过滤
    if status == '未批改':
        files = [f for f in files
                 if not os.path.splitext(os.path.basename(f))[0].endswith('-改')]
    elif status == '已批改':
        files = [f for f in files
                 if os.path.splitext(os.path.basename(f))[0].endswith('-改')]
    search_result_list = files
    _fill_search_ui()
    # 持久化学生检索条件：读最新盘（修改器/监控器独立进程，避免覆盖另一进程刚保存的设置）
    c = load_config()
    c.update({'last_cat': cat, 'last_status': status,
              'last_search_mode': 'student', 'last_student': student})
    save_config(c)


def _fill_search_ui():
    """检索结果 UI 公共尾部：列表填充/未批改标红/联排联动（内容与学生检索共用）"""
    if not search_listbox:
        return
    display = []
    for f in search_result_list:
        bn = os.path.basename(f); name, ext = os.path.splitext(bn); parts = name.split('-')
        if len(parts) >= 6:
            dn = f"{parts[0]}-{parts[1]}-{parts[2]}-{parts[4]}-{parts[5]}" + ("-改" if len(parts)>6 and parts[6]=='改' else "")
        elif len(parts) == 5:
            # 考试/打卡天格式: 2024-01-张三-考试-01
            dn = f"{parts[0]}-{parts[1]}-{parts[3]}-{parts[4]}"
        else: dn = name
        display.append(dn)
    if display:
        search_listbox.insert(tk.END, *display)
        # 未批改（无 -改）标红：Python tkinter 的 Listbox 未封装 tag 方法
        # （tag_config/tag_configure 均不存在，历史 bug：调用 tag_config 抛
        # AttributeError，导致标红失效 + 保存时被 except 误报"保存失败"），
        # 改用逐项 itemconfig 标色。
        try:
            for i, f in enumerate(search_result_list):
                if '-改' not in os.path.basename(f):
                    search_listbox.itemconfig(i, foreground='red')
        except Exception:
            pass   # 标红失败不阻断检索
    # 联排模式下检索变化：重建切组范围并重定位当前组
    if tile_mode:
        folders = _search_scope_folders()
        if folders and folders != tile_folder_list:
            tile_folder_list[:] = folders
            folder = os.path.dirname(bg_path) if bg_path else ''
            try:
                idx = tile_folder_list.index(folder)
            except ValueError:
                idx = 0
            if not _load_tile_folder(idx) and tile_folder_list:
                _load_tile_folder(0)
        elif not folders:
            # 检索结果无原图：保留当前联排，提示
            show_danmaku("检索范围内没有可批改的原图")


def do_search(e=None):
    if search_mode == 'student':
        _do_search_student()
        return
    search_result_list.clear()
    if search_listbox: search_listbox.delete(0, tk.END)
    lec, cat, cls, seq, status = search_lecture_var.get(), search_cat_var.get(), search_class_var.get(), search_seq_var.get(), search_status_var.get()
    target_lecture = normalize_lecture(lec)
    all_lecture = (target_lecture == '全部')
    # 班级支持多值（监控器传入逗号分隔，如 "1993,1994"）
    cls_set = None
    if cls and cls != '全部':
        cls_set = set(x.strip() for x in cls.split(',') if x.strip())
    # 第一轮：按讲次/分类/班级预过滤（不应用序号/状态筛选）——检索范围的候选集
    scope = []
    cat_match = (lambda c: True) if cat == '全部' else (
        # '考试' 分类选项匹配任意考试名（考试/考试1/考试2…，多考试支持）
        (lambda c: str(c).startswith('考试')) if cat == '考试' else
        (lambda c: c == cat))
    for f in cached_nav_list:
        m = parse_filename(os.path.basename(f))
        if m and (all_lecture or normalize_lecture(m['lecture']) == target_lecture) and \
           cat_match(m['category']) and \
           (cls_set is None or m['class_prefix'] in cls_set):
            scope.append((f, m))
    # 序号下拉：自动识别当前检索范围（讲次+分类+班级）内的实际图片序号
    seq_list = _collect_seqs([f for f, _ in scope])
    seq_combo_box.config(values=seq_list)
    if seq != '全部' and seq not in seq_list:
        seq = '全部'; search_seq_var.set('全部')   # 当前序号不在新范围内：自动重置
    # 第二轮：序号/状态过滤 → 最终结果
    for f, m in scope:
        match = (seq == '全部' or m['seq'] == seq)
        if status == '未批改' and m['is_modified']: match = False
        if status == '已批改' and not m['is_modified']: match = False
        if match: search_result_list.append(f)
    search_result_list.sort()
    _fill_search_ui()
    # 持久化内容检索条件：读最新盘（修改器/监控器独立进程，避免覆盖另一进程刚保存的设置）
    c = load_config()
    c.update({'last_lecture': lec, 'last_cat': cat, 'last_class': cls,
              'last_seq': seq, 'last_status': status, 'last_search_mode': 'content'})
    save_config(c)

def _on_nav_loaded():
    """导航列表后台加载完成：刷新筛选选项并检索（打开不再阻塞）"""
    try:
        update_filters_options()
        do_search()
    except Exception:
        pass
    if search_listbox and not search_result_list:
        show_danmaku("导航列表加载完成，当前范围内没有匹配图片")

def check_search_naming():
    """
    检查当前检索范围内的命名，发现不规范自动重命名（无需确认）。
    删除类操作仍必须确认（本流程不含删除）。
    """
    folders = _search_scope_folders()
    if not folders:
        show_danmaku("当前检索范围内没有图片")
        return
    bad = check_filename_format(BASE_DIR, folders=folders)
    if not bad:
        show_danmaku("当前检索范围内的文件名均符合规范 ✓")
        return
    renamed = 0
    # 按目录去重：bad 中多个文件可能同目录，每个目录只需处理一次（smart_rename_folder 是目录级）
    for folder in {os.path.dirname(p) for p, _ in bad}:
        try:
            renamed += smart_rename_folder(folder, BASE_DIR)
        except Exception:
            pass
    clear_scan_cache()
    write_modifier_changed()   # 通知监视器：文件已变动，请刷新检索同步
    update_filters_options(); do_search()
    show_danmaku(f"已自动修正 {renamed} 个文件名，检索列表已刷新")

def refresh_nav_list(show_msg=True):
    """刷新图片列表：直接继承监视器发布的检索结果（修改器不再自行承担检索）。
    嵌入模式（与监视器同进程）：监视器发布缺失/未就绪时显示提示，绝不回退全量扫描
    （避免与监视器重复检索、占用性能）；独立运行（无监视器）回退后台全量扫描兼容。"""
    search_snap = _current_search_snapshot()   # 主线程快照（后台线程不读 Tk 变量）
    def _job():
        global cached_nav_list
        try:
            snapshot = _monitor_nav_snapshot(search_snap)
            if snapshot is not None:
                cached_nav_list = snapshot   # 直接获取监视器检索信息
            elif _embedded:
                cached_nav_list = []   # 嵌入模式：不自行检索（等监视器发布）
            else:
                cached_nav_list = get_all_images_recursive(BASE_DIR)
        except Exception:
            cached_nav_list = []
        if not _app_closing:   # 窗口已关闭：不再排队回调
            try:
                if show_msg:
                    if _embedded and not cached_nav_list:
                        root.after(0, lambda: show_danmaku(
                            "等待监视器发布检索信息…（可在监视器页刷新后返回）"))
                    else:
                        root.after(0, lambda: (_on_nav_loaded(),
                                               show_danmaku("目录已刷新")))
                else:
                    root.after(0, _on_nav_loaded)
            except Exception:
                pass   # 窗口已销毁，忽略
    threading.Thread(target=_job, daemon=True).start()

def on_listbox_select(event):
    sel = search_listbox.curselection()
    if sel:
        idx = sel[0]
        if idx < len(search_result_list): load_background(search_result_list[idx])

# ---------- 布局保存与折叠逻辑 ----------
def save_layout(e=None):
    try:
        c = load_config()
        if 'layout' not in c: c['layout'] = {}
        if is_left_expanded and left_pane:
            w = left_pane.winfo_width()
            if w > 20: c['layout']['left_pane_width'] = w
        if right_pane:
            w = right_pane.winfo_width()
            if w > 20: c['layout']['right_pane_width'] = w
        save_config(c)
    except Exception:
        pass

def init_layout():
    root.update_idletasks()
    c = load_config().get('layout', {})
    try:
        if left_pane: paned_window.paneconfig(left_pane, width=c.get('left_pane_width', 240), minsize=20)
        if right_pane: paned_window.paneconfig(right_pane, width=c.get('right_pane_width', 160), minsize=100)
    except Exception:
        pass

def toggle_left_pane():
    global is_left_expanded
    if is_left_expanded:
        try:
            w = left_pane.winfo_width()
            if w > 20:
                c = load_config()
                if 'layout' not in c: c['layout'] = {}
                c['layout']['left_pane_width'] = w; save_config(c)
            paned_window.forget(left_pane); toggle_btn.config(text="▶"); is_left_expanded = False
        except Exception as e: print("折叠错误:", e)
    else:
        try:
            paned_window.add(left_pane, before=canvas_frame, minsize=20, stretch="never")
            c = load_config(); paned_window.paneconfig(left_pane, width=c.get('layout', {}).get('left_pane_width', 240), minsize=20)
            do_search(); toggle_btn.config(text="◀"); is_left_expanded = True
        except Exception as e: print("展开错误:", e)

_toggle_btn_after = None   # 折叠按钮去抖回调 id

def update_toggle_btn_size(e=None):
    """窗口 <Configure> 时调整折叠按钮尺寸；去抖合并（拖动窗口时高频触发）"""
    global _toggle_btn_after
    if not toggle_btn:
        return
    if _toggle_btn_after is not None:
        try:
            root.after_cancel(_toggle_btn_after)
        except Exception:
            pass
    _toggle_btn_after = root.after(80, _apply_toggle_btn_size)

def _apply_toggle_btn_size():
    global _toggle_btn_after
    _toggle_btn_after = None
    if not toggle_btn:
        return
    try:
        anchor = _embed_container if _embedded else root
        h = max(10, int(anchor.winfo_height() / 25))
        toggle_btn.place(x=0, y=0, width=h, height=h); toggle_btn.lift()
        if top_spacer and is_left_expanded:
            try: top_spacer.config(height=h)
            except Exception: pass
    except Exception:
        pass

_app_closing = False   # 窗口关闭中：后台线程不再排队主线程回调（防销毁后 TclError）
_embedded = False        # 嵌入主窗口模式（单窗口整合）
_embed_container = None  # 嵌入时的页面容器 Frame（顶层控件挂这里，root 仅作 Tk）
_scope_poll_after = None
_monitor_poll_after = None


def _unmount_page():
    """嵌入模式页面卸载（主窗口切走本页时调用）：停止后台线程排队、取消定时器、
    解除快捷键/滚轮绑定、销毁页面控件树；不销毁 root（由主窗口管理）。"""
    global _app_closing, _embedded, _embed_container, _scope_poll_after, _monitor_poll_after
    _app_closing = True
    # 解除本页绑定（bind_shortcuts 的记录 + 滚轮兜底）
    unbind_shortcuts()
    try:
        if _embedded and _embed_container is not None:
            _embed_container.unbind('<MouseWheel>')
    except Exception:
        pass
    try:
        root.unbind_all('<MouseWheel>')
    except Exception:
        pass
    # 取消已排队的定时器（作用在主窗口 root 上，避免残留回调触发 TclError）
    for attr in ('_toggle_btn_after', '_scope_poll_after', '_monitor_poll_after',
                 '_edit_focus_after'):
        t = globals().get(attr)
        if t is not None:
            try:
                root.after_cancel(t)
            except Exception:
                pass
            globals()[attr] = None
    # 销毁页面控件树（paned_window 及其全部子控件）
    if _embed_container is not None:
        try:
            for w in _embed_container.winfo_children():
                w.destroy()
        except Exception:
            pass
    _embedded = False
    _embed_container = None


def on_close():
    global _app_closing
    _app_closing = True
    save_layout()
    # 延迟 120ms 再销毁：让已排队的后台回调（如 _on_nav_loaded）先执行完，
    # 避免销毁后触发 "invalid command name"
    try:
        root.after(120, root.destroy)
    except Exception:
        try:
            root.destroy()
        except Exception:
            pass

# ---------- 主窗口 ----------
def main(container=None, initial_scope=None):
    """单窗口整合：container=None 独立运行；container 提供时嵌入主窗口内容区
    （root 取 container.winfo_toplevel() 作 Tk，顶层控件挂 container）。
    initial_scope：嵌入时由主窗口传入监视器当前检索范围（直接继承监视器检索），
    构建完成后自动应用（修改器不再自行承担检索）。"""
    global root, canvas, scale_slider, tool_config, cached_nav_list
    global tool_buttons, preset_frame_inner, grading_frame
    global search_lecture_var, search_cat_var, search_class_var, search_seq_var, search_status_var, search_listbox
    global search_mode_var, search_student_var, student_seq_var, student_class_var
    global paned_window, left_pane, left_content, canvas_frame, top_spacer, toggle_btn, right_pane, right_canvas
    global seq_combo_box, _embedded, _embed_container, _app_closing

    _embedded = container is not None
    _embed_container = container
    _app_closing = False

    config = load_config()
    tool_config = config.get('tools', DEFAULT_CONFIG['tools'])
    cached_nav_list = []   # 后台扫描填充（打开提速，不再阻塞启动）

    cli = _parse_cli_args()   # 监控器传入的检索范围（--lecture/--category/--classes）

    parent = container if container is not None else None
    if container is None:
        root = tk.Tk(); root.title(f"作业批改工具 - 定制版 v{PROJECT_VERSION}"); root.geometry(window_geometry(root, 1300, 850))
    else:
        root = container.winfo_toplevel()
    paned_window = tk.PanedWindow(parent or root, orient=tk.HORIZONTAL, sashwidth=5, sashrelief=tk.RAISED)
    paned_window.pack(fill=tk.BOTH, expand=True); paned_window.bind('<ButtonRelease-1>', save_layout)

    # 左侧：检索栏
    left_pane = tk.Frame(paned_window, bg='#f0f0f0', width=240); paned_window.add(left_pane, minsize=20, stretch="never")
    top_spacer = tk.Frame(left_pane, bg='#f0f0f0'); top_spacer.pack(fill=tk.X)
    left_content = tk.Frame(left_pane, bg='#f0f0f0'); left_content.pack(fill=tk.BOTH, expand=True)

    # ---- 检索方式切换：内容检索（讲次-学生）/ 姓名-类别检索（学生-讲次）----
    # 布局要求：检索格式为检索区第一项；"筛选自动换行"开关紧随其后
    # ---- 检索栏精简（用户需求：删除检索栏，保留序号分类）----
    # 修改器检索信息直接继承监视器实时发布的结果（监视器已按 讲次/分类/班级/学生
    # 范围发布文件，修改器不再自行筛选），故不再渲染 检索方式/讲次/分类/状态/班级/
    # 姓名-类别 等筛选控件；仅保留「序号」下拉（图片序号分类，便于在结果内定位）。
    # 变量仍保留默认值"全部"，保证 do_search/_monitor_scope_matches/_apply_scope 等
    # 下游逻辑安全（默认全选=直接采用监视器发布范围）。
    search_mode_var = tk.StringVar(value='content')
    search_lecture_var = tk.StringVar(value='全部')
    search_cat_var = tk.StringVar(value='全部')
    search_status_var = tk.StringVar(value='全部')
    search_class_var = tk.StringVar(value='全部')
    search_seq_var = tk.StringVar(value='全部')
    search_student_var = tk.StringVar(value='全部')
    student_class_var = tk.StringVar(value='全部')
    student_seq_var = tk.StringVar(value='全部')

    # 序号下拉（保留：图片序号分类）。不加入 _content_mode_frames —— 检索方式切换已
    # 删除（固定继承监视器发布结果），序号下拉始终显示，不被模式切换隐藏。
    r5 = tk.Frame(left_content, bg='#f0f0f0'); r5.pack(fill=tk.X, pady=2)
    tk.Label(r5, text="序号:", bg='#f0f0f0', width=5).pack(side=tk.LEFT)
    seq_combo_box = ttk.Combobox(r5, textvariable=search_seq_var, values=["全部"], state="readonly")
    seq_combo_box.pack(side=tk.LEFT, padx=5, fill=tk.X, expand=True); seq_combo_box.bind('<<ComboboxSelected>>', do_search)

    # 应用监控器传入的检索范围（讲次/分类/班级），实现"检索范围=监控器限制范围"
    # （cli 在 main 开头已解析一次，此处复用；班级勾选应用在下方左栏构建处）
    if cli.get('lecture'):
        try:
            norm = normalize_lecture(cli['lecture'])
            if norm.isdigit():
                search_lecture_var.set(f"第{int(norm)}讲")     # 第01讲 -> 第1讲（修改器格式）
            else:
                search_lecture_var.set(cli['lecture'])          # 考试 / 打卡第NN天 原样
        except Exception:
            pass
    if cli.get('category'):
        search_cat_var.set(cli['category'])
    # 姓名-类别检索：监控器学生模式下传入（--search-mode student --name 学生）
    if cli.get('search_mode') == 'student':
        search_mode_var.set('student')
        if cli.get('name'):
            search_student_var.set(cli['name'])
        if cli.get('category'):
            search_cat_var.set(cli['category'])
        if not _embedded:
            root.title(f"作业批改工具 - 定制版 v{PROJECT_VERSION}（学生检索:监控器）")
    elif cli.get('lecture') or cli.get('category') or cli.get('classes'):
        if not _embedded:
            root.title(f"作业批改工具 - 定制版 v{PROJECT_VERSION}（检索范围:监控器）")
    # 检索栏已精简：学生模式面板已删除，强制内容模式（避免 config 遗留 student 模式
    # 导致空列表；嵌入模式监视器学生检索仍由 initial_scope 经 _apply_scope 生效）
    search_mode_var.set('content')
    update_student_options()   # 学生控件已删除，内部立即返回（兼容保留）

    bf = tk.Frame(left_content, bg='#f0f0f0'); bf.pack(fill=tk.X, pady=5)
    global _search_btns
    _search_btns = bf
    tk.Button(bf, text="检索", command=do_search).pack(side=tk.LEFT, fill=tk.X, expand=True)
    tk.Button(bf, text="刷新目录", command=refresh_nav_list).pack(side=tk.LEFT, fill=tk.X, expand=True)

    lf = tk.Frame(left_content); lf.pack(fill=tk.BOTH, expand=True)
    ls = tk.Scrollbar(lf); ls.pack(side=tk.RIGHT, fill=tk.Y)
    search_listbox = tk.Listbox(lf, yscrollcommand=ls.set, bg='#f0f0f0')
    search_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True); ls.config(command=search_listbox.yview)
    search_listbox.bind('<<ListboxSelect>>', on_listbox_select)

    # 后台加载导航列表与评分数据（打开提速）：直接继承监视器发布的检索结果
    # （修改器不再自行承担检索）；监视器文件缺失时独立运行回退自行扫描，
    # 嵌入模式（与监视器同进程）不自行扫描（等监视器发布，避免重复检索）。
    nav_snap = _current_search_snapshot()   # 主线程快照（后台线程不读 Tk 变量）
    def _load_nav():
        global cached_nav_list
        load_all_grading_data()   # 评分数据后台读取（不阻塞打开）
        try:
            snapshot = _monitor_nav_snapshot(nav_snap)
            if snapshot is not None:
                cached_nav_list = snapshot   # 直接获取监视器检索信息
            elif _embedded:
                cached_nav_list = []
            elif cli.get('lecture') or cli.get('category') or (cli.get('classes') and cli['classes'] != '全部'):
                cached_nav_list = _scan_scope_images(cli.get('lecture'), cli.get('category'), cli.get('classes'))
            else:
                cached_nav_list = get_all_images_recursive(BASE_DIR)
        except Exception:
            try:
                if _embedded:
                    cached_nav_list = []
                else:
                    cached_nav_list = get_all_images_recursive(BASE_DIR)
            except Exception:
                cached_nav_list = []
        if not _app_closing:   # 窗口已关闭：不再排队回调
            try:
                root.after(0, _on_nav_loaded)
            except Exception:
                pass   # 窗口已销毁，忽略

    threading.Thread(target=_load_nav, daemon=True).start()
    root.after(300, lambda: show_danmaku("正在加载图片列表…"))

    # 中间：画布
    canvas_frame = tk.Frame(paned_window, bg='#cccccc'); paned_window.add(canvas_frame, minsize=200, stretch="always")
    canvas = tk.Canvas(canvas_frame, bg='#f0f0f0')
    h_scroll = tk.Scrollbar(canvas_frame, orient=tk.HORIZONTAL, command=canvas.xview)
    v_scroll = tk.Scrollbar(canvas_frame, orient=tk.VERTICAL, command=canvas.yview)
    canvas.configure(xscrollcommand=h_scroll.set, yscrollcommand=v_scroll.set)
    v_scroll.pack(side=tk.RIGHT, fill=tk.Y); h_scroll.pack(side=tk.BOTTOM, fill=tk.X); canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
    canvas.bind('<Button-1>', canvas_click); canvas.bind('<Button-3>', canvas_click)
    canvas.bind('<B1-Motion>', on_drag)
    canvas.bind('<ButtonRelease-1>', on_release)
    canvas.bind('<Double-Button-1>', on_double_click)
    canvas.bind('<Motion>', on_canvas_motion)
    canvas.bind('<MouseWheel>', on_mousewheel)
    # 全局滚轮兜底：画布上的滚轮由 on_mousewheel 处理并 return 'break' 阻止传播；
    # 画布外的滚轮由 _global_wheel 按区域分发（右栏滚动 / 其他不拦截）。
    # 修复历史问题：原 Ctrl/Alt+滚轮用 bind_all 单独绑定，与 canvas 的 <MouseWheel>
    # 同时触发（Ctrl+滚轮既滚动又缩放、Alt+滚轮双倍横滚），表现为组合滚轮失灵。
    # 嵌入模式绑 container 级（不污染主窗口其他页面）；独立模式 bind_all 保持原样
    if _embedded and container is not None:
        container.bind('<MouseWheel>', _global_wheel)
    else:
        root.bind_all('<MouseWheel>', _global_wheel)
    # 仅 Linux 绑 Button-4/5 为滚轮：Windows 上 Button-4/5 是鼠标侧键
    # （XButton1/2，可录制为快捷键），不能当滚轮处理（历史 bug：侧键失灵）
    if platform.system() != 'Windows':
        canvas.bind('<Button-4>', on_mousewheel_linux)
        canvas.bind('<Button-5>', on_mousewheel_linux)

    # 右侧：工具栏（可滚动容器，避免窗口较小时工具显示不全）
    right_pane = tk.Frame(paned_window, width=160); paned_window.add(right_pane, minsize=100, stretch="never")
    right_canvas = tk.Canvas(right_pane, highlightthickness=0, width=160, bg='SystemButtonFace')
    right_sb = tk.Scrollbar(right_pane, orient=tk.VERTICAL, command=right_canvas.yview)
    right_canvas.configure(yscrollcommand=right_sb.set)
    right_sb.pack(side=tk.RIGHT, fill=tk.Y)
    right_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
    right_inner = tk.Frame(right_canvas)
    right_inner_id = right_canvas.create_window((0, 0), window=right_inner, anchor='nw')

    def _on_right_inner_cfg(e=None):
        # 内容滚动区 = 全部内容；内容宽度跟随画布（避免横向被裁）
        try:
            br = right_canvas.bbox('all')
            if br:
                right_canvas.configure(scrollregion=br)
        except Exception:
            pass
        cw = right_canvas.winfo_width()
        if cw > 20:
            right_canvas.itemconfigure(right_inner_id, width=cw)

    right_inner.bind('<Configure>', _on_right_inner_cfg)
    # 右栏滚轮：统一由全局 _global_wheel 处理（区域判断在右栏→滚动），
    # 不再单独 bind/bind_all（原 right_canvas.bind_all 会覆盖 root.bind_all 的 _global_wheel）

    top_menu = tk.Frame(right_inner); top_menu.pack(fill=tk.X, pady=2)
    # 顶部主窗口已有「⚙设置」导航入口：嵌入模式不再重复提供设置/返回按钮
    # （独立运行无顶部工具栏，保留设置入口供使用）
    if not _embedded:
        tk.Button(top_menu, text="⚙ 设置", command=open_settings).pack(fill=tk.X, padx=2)
    tk.Button(top_menu, text="检查命名", command=check_search_naming).pack(fill=tk.X, padx=2)

    tool_frame = tk.LabelFrame(right_inner, text="绘图工具", font=("Arial", 10)); tool_frame.pack(fill=tk.X, pady=5)
    btn_container = tk.Frame(tool_frame); btn_container.pack(fill=tk.BOTH, expand=True, padx=2, pady=2)
    btn_container.columnconfigure(0, weight=1); btn_container.columnconfigure(1, weight=1)
    def set_tool(mode):
        global left_click_mode, active_preset_name
        left_click_mode = mode
        active_preset_name = None   # 切换工具后旧的激活预设失效（删除预设按当前工具+激活预设）
        _discard_line_start()       # 切换工具：未完成的直线起点作废
        for m, btn in tool_buttons.items():
            btn.config(relief=tk.SUNKEN if m == mode else tk.RAISED, bg='#d1e7dd' if m == mode else 'SystemButtonFace')
        refresh_preset_buttons()
    # 工具按钮布局：第一行 勾|直线；第二行 选择|文本框（选择与文本框同行，便于切换）
    btn_select = tk.Button(btn_container, text="选择", command=lambda: set_tool('select'), font=('微软雅黑', 10))
    btn_check = tk.Button(btn_container, text="勾", command=lambda: set_tool('check'), font=('微软雅黑', 10))
    btn_line = tk.Button(btn_container, text="直线", command=lambda: set_tool('line'), font=('微软雅黑', 10))
    btn_text = tk.Button(btn_container, text="文本框", command=lambda: set_tool('text'), font=('微软雅黑', 10))
    btn_check.grid(row=0, column=0, sticky='nsew', padx=1, pady=1)
    btn_line.grid(row=0, column=1, sticky='nsew', padx=1, pady=1)
    btn_select.grid(row=1, column=0, sticky='nsew', padx=1, pady=1)
    btn_text.grid(row=1, column=1, sticky='nsew', padx=1, pady=1)
    tool_buttons = {'select': btn_select, 'check': btn_check,
                    'line': btn_line, 'text': btn_text}

    preset_frame = tk.LabelFrame(right_inner, text="预设风格", font=("Arial", 10)); preset_frame.pack(fill=tk.X, pady=5)
    preset_frame_inner = tk.Frame(preset_frame); preset_frame_inner.pack(fill=tk.X, padx=2, pady=2)
    pbtn = tk.Frame(preset_frame); pbtn.pack(fill=tk.X, padx=2, pady=2)
    tk.Button(pbtn, text="新增预设", command=open_preset_editor).pack(side=tk.LEFT, fill=tk.X, expand=True)
    tk.Button(pbtn, text="删除预设", command=delete_selected_preset).pack(side=tk.RIGHT, fill=tk.X, expand=True)
    set_tool('select')

    grading_frame = tk.LabelFrame(right_inner, text="评价/评分", font=("Arial", 10)); grading_frame.pack(fill=tk.X, pady=5)
    file_frame = tk.LabelFrame(right_inner, text="文件操作", font=("Arial", 10)); file_frame.pack(fill=tk.X, pady=5)
    # 不再显示文件信息 lbl_img_name 和 lbl_file_info
    tile_row = tk.Frame(file_frame); tile_row.pack(fill=tk.X, padx=2, pady=2)
    global tile_btn
    tile_btn = tk.Button(tile_row, text="联排模式 (Ctrl+T)", command=toggle_tile_mode, bg='#d1e7dd')
    tile_btn.pack(fill=tk.X)
    tk.Button(file_frame, text="旋转图片 (顺时针)", command=rotate_main_image).pack(fill=tk.X, padx=2, pady=2)
    nav_frame = tk.Frame(file_frame); nav_frame.pack(fill=tk.X, padx=2, pady=2)
    global nav_prev_btn, nav_next_btn
    nav_prev_btn = tk.Button(nav_frame, text="上一张", command=lambda: load_adjacent_image('prev'))
    nav_prev_btn.pack(side=tk.LEFT, fill=tk.X, expand=True)
    nav_next_btn = tk.Button(nav_frame, text="下一张", command=lambda: load_adjacent_image('next'))
    nav_next_btn.pack(side=tk.RIGHT, fill=tk.X, expand=True)
    tk.Button(file_frame, text="保存图片", command=save_image, bg='lightgreen').pack(fill=tk.X, padx=2, pady=2)
    tk.Button(file_frame, text="删除源文件", command=delete_current_image, bg='#ffcccc').pack(fill=tk.X, padx=2, pady=2)
    tk.Button(file_frame, text="打开评分文件夹", command=open_grading_dir, bg='#ffff99').pack(fill=tk.X, padx=2, pady=2)

    zoom_frame = tk.LabelFrame(right_inner, text="缩放"); zoom_frame.pack(fill=tk.X, pady=5)
    scale_slider = tk.Scale(zoom_frame, from_=0.1, to=5.0, resolution=0.01, orient=tk.HORIZONTAL, # 步长精修为0.01
                            command=on_zoom_slider)
    scale_slider.set(1.0); scale_slider.pack(fill=tk.X)

    # 取消了元素属性框 prop_frame

    toggle_btn = tk.Button(parent or root, text="◀", command=toggle_left_pane, bg='#d1e7dd', relief=tk.GROOVE)

    bind_shortcuts()
    (parent or root).bind('<Configure>', update_toggle_btn_size)
    root.after(200, init_layout); root.after(250, update_toggle_btn_size)
    if container is None:
        root.protocol("WM_DELETE_WINDOW", on_close)
    else:
        # 嵌入模式：顶部主窗口已有「← 返回监视器 (Esc)」导航，不再注入右栏返回按钮。
        # 进入本页后延迟聚焦画布：确保快捷键（翻页/撤销/保存）立即可用
        # （主窗口 show_page 末尾 container.focus_set() 会抢走焦点，故延迟到其后执行）。
        try:
            def _focus_canvas():
                try:
                    canvas.focus_set()
                except Exception:
                    pass
            root.after(120, _focus_canvas)
        except Exception:
            pass
    _start_scope_listener()   # 监听监控器检索规则（修改器已打开时复用窗口，不重复打开）
    # 嵌入模式：主窗口传入的监视器当前检索范围 → 构建完成后直接应用（继承监视器检索，
    # 修改器不再自行承担检索）。延迟执行：等后台导航列表加载（_load_nav）先填充，
    # _apply_scope 再覆盖为监视器发布的文件列表，避免闪烁/空列表。
    if initial_scope:
        root.after(300, lambda: (_apply_scope(initial_scope) if not _app_closing else None))
    root.after(1500, _poll_monitor_search)   # 同步监视器刷新后的检索信息（修改器不再自行承担检索）
    if container is None:
        root.mainloop()

if __name__ == "__main__":
    main()
