import os
import sys
import json
import re
import subprocess
import threading
import shutil
import tkinter as tk
from tkinter import ttk, StringVar, IntVar
import datetime
import time
from concurrent.futures import ThreadPoolExecutor

from PIL import Image   # 存储优化：按年龄压缩/降质/缩略

# 导入公共模块（目录结构配置与工具函数）
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (BASE_DIR, PROGRAM_DIR, LECTURES,
                    LECTURE_SUB_TYPES, IMAGE_EXTENSIONS, STUDENTS,
                    is_exam_or_checkin, get_current_sub_types, is_student_folder,
                    open_in_file_manager, check_student_folders, check_sub_folders,
                    move_to_recycle_bin, is_empty_dir, check_filename_format,
                    smart_rename_folder, scan_dir_incremental, clear_dir_scan_cache,
                    PROJECT_VERSION, atomic_write_json, SKIP_SCAN_DIRS,
                    load_storage_opt_state, save_storage_opt_state, PROCESS_LOCK,
                    PARALLEL_WORKERS, add_students_from_folders,
                    remove_students_by_folder, GRADING_DIR, collect_student_options,
                    MONITOR_SEARCH_FILE, MODIFIER_CHANGED_FILE, window_geometry,
                    student_lecture_names, STUDENT_FOLDER_RE, config_file_path)
# 图片处理（HEIC→JPG、缩放1080、规范命名）——单文件夹粒度，供自动/手动调用
import 作业命名器 as _namer

# 拖放支持（外部图片拖入卡片存储）：tkinterdnd2 可选依赖
# 未安装时程序照常运行，仅拖放功能不可用（会提示）
try:
    from tkinterdnd2 import TkinterDnD, DND_FILES
    DND_AVAILABLE = True
except ImportError:
    TkinterDnD = None
    DND_FILES = None
    DND_AVAILABLE = False

SETTINGS_FILE = config_file_path(".file_monitor_settings.json")


# ============================================================
#  视频胶囊匹配（视频胶囊.txt → 情况说明文本中的胶囊部分）
#  文件格式（用户维护）：每个胶囊 2 行（【知识胶囊】分享文本 + 链接），
#  每讲次一组（作业/课前小测/错题再练），讲次之间空行。
#  胶囊标题命名不统一，需智能解析讲次与分类，例如：
#    《新高一第一讲作业》 → 第1讲 作业
#    《新高一第二次课前测》 → 第2讲 课前小测
#    《第五讲错题再练》 → 第5讲 错题再练
#    《作业9》 / 《课前测9》 → 第9讲 作业 / 课前小测
#    《第十三讲作业》 → 第13讲 作业
#  打卡暂无胶囊（后续补充后自动生效）。
# ============================================================
_CAPSULE_CACHE = {'path': None, 'mtime_ns': None, 'data': None}

# 中文数字 → 阿拉伯（讲次编号）
_CN_NUM = {'一': 1, '二': 2, '三': 3, '四': 4, '五': 5, '六': 6, '七': 7,
           '八': 8, '九': 9, '十': 10, '十一': 11, '十二': 12, '十三': 13,
           '十四': 14, '十五': 15}

# 分类关键词（标题中的叫法 → 标准分类名）
_CAPSULE_CAT_KEYWORDS = (('作业', '作业'), ('课前小测', '课前小测'),
                         ('课前测', '课前小测'), ('错题再练', '错题再练'),
                         ('错题', '错题再练'))


def _parse_capsule_title(title):
    """从胶囊标题解析 (讲次数字, 标准分类)；无法解析返回 None。"""
    t = title.strip()
    cat = None
    for kw, c in _CAPSULE_CAT_KEYWORDS:
        if kw in t:
            cat = c
            break
    if cat is None:
        return None
    # 讲次：'第X讲' / '第X次'（X 可为阿拉伯或中文数字）
    m = re.search(r'第([0-9一二三四五六七八九十]+)(讲|次)', t)
    if m:
        num_s = m.group(1)
        num = int(num_s) if num_s.isdigit() else _CN_NUM.get(num_s)
        if num:
            return num, cat
    # 标题末尾数字：作业9 / 课前测9 / 错题再练9
    m = re.search(r'(\d+)\s*$', t)
    if m:
        return int(m.group(1)), cat
    return None


def _load_capsules():
    """读取 视频胶囊.txt → {(讲次, 分类): {'title': 胶囊名, 'url': 链接}}。
    (路径+mtime) 缓存：文件未变化不重读。文件缺失/损坏返回 {}。"""
    path = os.path.join(BASE_DIR, '视频胶囊.txt')
    try:
        mtime = os.stat(path).st_mtime_ns
    except OSError:
        return {}
    c = _CAPSULE_CACHE
    if c['path'] == path and c['mtime_ns'] == mtime and c['data'] is not None:
        return c['data']
    data = {}
    try:
        with open(path, encoding='utf-8') as f:
            lines = [l.strip() for l in f]
    except Exception:
        return {}
    i = 0
    while i < len(lines):
        line = lines[i]
        i += 1
        if not line:
            continue
        # 胶囊块：标题行（可能含《标题》与链接），链接也可能在下一行
        title = ''
        url = ''
        m_t = re.search(r'《([^》]+)》', line)
        if m_t:
            title = m_t.group(1)
        m_u = re.search(r'(https?://\S+)', line)
        if m_u:
            url = m_u.group(1)
        if title:
            if not url and i < len(lines):
                m_u2 = re.search(r'(https?://\S+)', lines[i])
                if m_u2:
                    url = m_u2.group(1)
                    i += 1   # 消费链接行
            parsed = _parse_capsule_title(title)
            if parsed:
                data[parsed] = {'title': title, 'url': url}
    c['path'] = path
    c['mtime_ns'] = mtime
    c['data'] = data
    return data


def _get_capsule_text(lecture, sub_type):
    """匹配当前讲次+分类的视频胶囊，返回《胶囊名》链接 文本；无匹配返回 ''。
    打卡天暂不匹配（视频胶囊.txt 暂无打卡内容，补充后自动生效）。"""
    if lecture.startswith('打卡'):
        return ''
    m = re.search(r'第(\d+)讲', str(lecture))
    if not m:
        return ''
    num = int(m.group(1))
    cap = _load_capsules().get((num, sub_type))
    if not cap:
        return ''
    parts = []
    if cap.get('title'):
        parts.append(f'《{cap["title"]}》')
    if cap.get('url'):
        parts.append(cap['url'])
    return ' '.join(parts)


# ============================================================
#  复制批改内容配置（设置中心可调，讲次/考试/打卡 分开记忆，互不影响）
#  每项控制复制批改时携带的内容：
#    lecture = 讲次信息（第02讲 / 考试 / 第02天）
#    sub     = 类型信息（作业/课前小测/错题再练；考试/打卡无此概念，勾选无影响）
#    capsule = 胶囊视频（《胶囊名》链接（视频胶囊），无匹配自动省略）
#    image   = 图片（-改 批改图进剪贴板，微信/QQ 粘贴发图）
#  默认全选。
# ============================================================
def _as_bool(value, default=False):
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return bool(value)
    if isinstance(value, str):
        text = value.strip().lower()
        if text in ('true', '1', 'yes', 'on', '是'):
            return True
        if text in ('false', '0', 'no', 'off', '否', ''):
            return False
    return default


DEFAULT_COPY_TEMPLATE = '{class}班 {seq}号 {name}的{lecture}的{sub}{capsule}'


DEFAULT_COPY_CONTENT = {
    'lecture': {'lecture': True, 'sub': True, 'capsule': True, 'image': True},
    'exam':    {'lecture': True, 'sub': True, 'capsule': True, 'image': True},
    'checkin': {'lecture': True, 'sub': True, 'capsule': True, 'image': True},
}


def _merge_copy_content(raw):
    """把设置文件里的 copy_content（可能缺键/旧格式）合并进默认值，返回完整结构。"""
    merged = {}
    raw = raw if isinstance(raw, dict) else {}
    for scene, dflt in DEFAULT_COPY_CONTENT.items():
        item = raw.get(scene, {})
        item = item if isinstance(item, dict) else {}
        merged[scene] = {
            'lecture': _as_bool(item.get('lecture', dflt['lecture']), dflt['lecture']),
            'sub': _as_bool(item.get('sub', dflt['sub']), dflt['sub']),
            'capsule': _as_bool(item.get('capsule', dflt['capsule']), dflt['capsule']),
            'image': _as_bool(item.get('image', dflt['image']), dflt['image']),
        }
    if isinstance(raw, dict):
        merged['text_template'] = str(raw.get('text_template', raw.get(
            'identity_template', DEFAULT_COPY_TEMPLATE)))
        merged['save_report_text'] = _as_bool(raw.get('save_report_text', False))
    else:
        merged['text_template'] = DEFAULT_COPY_TEMPLATE
        merged['save_report_text'] = False
    return merged


def _copy_scene(lecture):
    """复制场景：讲次 / 考试 / 打卡（用于各自独立的复制内容配置）。"""
    if str(lecture).startswith('考试'):
        return 'exam'
    if str(lecture).startswith('打卡'):
        return 'checkin'
    return 'lecture'



# ============================================================
#  剪贴板文件列表（Windows CF_HDROP）
#  复制批改时把 -改 图片文件路径放入剪贴板：微信/QQ 等应用粘贴时
#  直接读取路径发送图片（保留原图质量，支持多张），与文本说明共存。
#  非 Windows 返回 False（仅文本进剪贴板）。
# ============================================================
def _build_hdrop_payload(paths):
    """构造 CF_HDROP 数据：DROPFILES 头（20 字节）+ UTF-16LE 路径列表"""
    import struct
    payload = struct.pack('<IiiII', 20, 0, 0, 0, 1)   # pFiles=20, pt, fNC=0, fWide=1
    for p in paths:
        payload += p.encode('utf-16-le') + b'\x00\x00'
    payload += b'\x00\x00'
    return payload


def _build_cf_html(text, image_paths):
    r"""构造 CF_HTML（HTML Format）数据：文字段落 + <img> 引用本地图片。
    对齐 QQ 原生写法（逆向自真实 QQ 图文复制样本）：
    - 头部含 SourceURL 字段；行尾 \r\n
    - 文本 + <br> + <img src="file:///D:\...\图片.jpg">（file:/// 后跟**原样反斜杠路径**，
      不做 URL 编码/正斜杠转换）
    偏移按 UTF-8 **字节**计算（10 位补零）。"""
    parts = [text] if text else []
    for p in image_paths:
        parts.append(f'<img src="file:///{p}">')
    fragment = '<!--StartFragment-->' + '<br>'.join(parts) + '<!--EndFragment-->'
    html = '<html>\r\n<body>\r\n' + fragment + '\r\n</body>\r\n</html>'
    html_b = html.encode('utf-8')

    def build(start, end, sf, ef):
        header = (f'Version:0.9\r\nStartHTML:{start:010d}\r\nEndHTML:{end:010d}\r\n'
                  f'StartFragment:{sf:010d}\r\nEndFragment:{ef:010d}\r\nSourceURL:\r\n')
        return (header + html).encode('utf-8')

    # 纯 header 长度（占位 10 位与真实同宽；不含 html）
    header_len = len(('Version:0.9\r\nStartHTML:0000000000\r\nEndHTML:0000000000\r\n'
                      'StartFragment:0000000000\r\nEndFragment:0000000000\r\n'
                      'SourceURL:\r\n').encode('utf-8'))
    start = header_len
    frag_s = '<!--StartFragment-->'.encode('utf-8')
    frag_e = '<!--EndFragment-->'.encode('utf-8')
    sf = header_len + html_b.index(frag_s)
    ef = header_len + html_b.index(frag_e) + len(frag_e)
    end = header_len + len(html_b)
    return build(start, end, sf, ef)


def _build_qq_richedit(text, image_paths):
    """构造 QQ_Unicode_RichEdit_Format（QQ 图文复制的**核心私有格式**，逆向自真实样本）：
    <QQRichEditFormat><Info version="1001"></Info>
      <EditElement type="0"><![CDATA[文本]]></EditElement>           文本元素
      <EditElement type="1" filepath="D:\\...\\图.jpg" shortcut=""></EditElement>  图片元素（本地路径）
    </QQRichEditFormat>
    QQ 粘贴时优先读此格式 → 图文同现。UTF-8 编码。"""
    parts = []
    if text:
        parts.append(f'<EditElement type="0"><![CDATA[{text}]]></EditElement>')
    for p in image_paths:
        parts.append(f'<EditElement type="1" filepath="{p}" shortcut=""></EditElement>')
    return ('<QQRichEditFormat><Info version="1001"></Info>'
            + ''.join(parts) + '</QQRichEditFormat>').encode('utf-8')


def _copy_qq_style_clipboard(text, image_paths):
    """QQ 图文风格剪贴板（Windows）：一次写入 QQ 完整格式组合——
    QQ_Unicode_RichEdit_Format（QQ 图文同贴核心）
    + HTML Format（标准图文，含 SourceURL）
    + CF_UNICODETEXT / CF_TEXT（纯文本多编码）
    + CF_HDROP（图片文件列表，微信发图兜底）。"""
    if os.name != 'nt':
        return False
    import ctypes
    from ctypes import wintypes
    user32 = ctypes.windll.user32
    user32.RegisterClipboardFormatW.argtypes = [wintypes.LPCWSTR]
    user32.RegisterClipboardFormatW.restype = wintypes.UINT
    image_paths = [os.path.abspath(p) for p in image_paths if os.path.isfile(p)]
    payloads = []
    if text:
        payloads.append((13, text.encode('utf-16-le') + b'\x00\x00'))
        try:
            payloads.append((1, text.encode('gbk') + b'\x00\x00'))   # CF_TEXT（ANSI）
        except Exception:
            pass
    if image_paths:
        payloads.append((15, _build_hdrop_payload(image_paths)))
    cf_html = user32.RegisterClipboardFormatW('HTML Format')
    if cf_html:
        payloads.append((cf_html, _build_cf_html(text, image_paths)))
    cf_qq = user32.RegisterClipboardFormatW('QQ_Unicode_RichEdit_Format')
    if cf_qq:
        payloads.append((cf_qq, _build_qq_richedit(text, image_paths)))
    return _set_clipboard_formats(payloads)


def _set_clipboard_formats(payloads):
    """清空剪贴板并写入多格式数据（Windows）。
    payloads: [(格式编号, bytes), ...]。成功返回 True。"""
    if os.name != 'nt' or not payloads:
        return False
    import ctypes
    from ctypes import wintypes
    user32 = ctypes.windll.user32
    kernel32 = ctypes.windll.kernel32
    user32.OpenClipboard.argtypes = [wintypes.HWND]
    user32.OpenClipboard.restype = wintypes.BOOL
    user32.EmptyClipboard.argtypes = []
    user32.EmptyClipboard.restype = wintypes.BOOL
    user32.SetClipboardData.argtypes = [wintypes.UINT, wintypes.HANDLE]
    user32.SetClipboardData.restype = wintypes.HANDLE
    kernel32.GlobalAlloc.argtypes = [wintypes.UINT, ctypes.c_size_t]
    kernel32.GlobalAlloc.restype = wintypes.HGLOBAL
    kernel32.GlobalLock.argtypes = [wintypes.HGLOBAL]
    kernel32.GlobalLock.restype = ctypes.c_void_p
    kernel32.GlobalUnlock.argtypes = [wintypes.HGLOBAL]
    kernel32.GlobalFree.argtypes = [wintypes.HGLOBAL]
    GMEM_MOVEABLE = 0x0002
    GMEM_ZEROINIT = 0x0040
    try:
        opened = False
        for _ in range(3):
            if user32.OpenClipboard(None):
                opened = True
                break
            time.sleep(0.1)
        if not opened:
            return False
        try:
            user32.EmptyClipboard()
            for fmt, data in payloads:
                if not data:
                    continue
                h = kernel32.GlobalAlloc(GMEM_MOVEABLE | GMEM_ZEROINIT, len(data))
                if not h:
                    continue
                ptr = kernel32.GlobalLock(h)
                if not ptr:
                    kernel32.GlobalFree(h)
                    continue
                try:
                    ctypes.memmove(ptr, data, len(data))
                finally:
                    kernel32.GlobalUnlock(h)
                if not user32.SetClipboardData(fmt, h):
                    kernel32.GlobalFree(h)
            return True
        finally:
            user32.CloseClipboard()
    except Exception:
        return False


# 相邻讲次状态标记颜色（与卡片原背景色有差异，便于区分）：
# 灰 = 上一讲/下一讲同类型无文件；绿 = 全部已批改（比卡片浅绿 #ccffcc 更深）；
# 红 = 存在未批改（比卡片浅红 #ffcccc 更深）
ADJ_MARKER_GRAY = '#9e9e9e'
ADJ_MARKER_GREEN = '#2E8B57'
ADJ_MARKER_RED = '#D32F2F'

# 顶部反馈标记行「常驻」状态色（无反馈标记时按文件状态显示，始终可见、
# 区别于卡片浅色背景）：灰 = 无文件/目录不存在；红 = 存在未批改；绿 = 全部已批改。
# 有反馈标记时该块显示标记对应颜色（作业黄/课前小测蓝/错题再练黑/考试紫/打卡绿）。
MARKER_STATUS_GRAY = '#bdbdbd'
MARKER_STATUS_RED = '#ff9b9b'
MARKER_STATUS_GREEN = '#9fe0a0'

# 主窗口标题前缀（多处拼接，统一常量）
_TITLE_PREFIX = f"文件监控器 v{PROJECT_VERSION} - "


class WrapFrame(tk.Frame):
    """可自动换行的工具栏容器：子控件超宽时自动换到下一行，
    窗口缩放（<Configure>）时自动重排——监控器上方按钮随窗口宽度合理布局。"""

    def __init__(self, master, **kw):
        super().__init__(master, **kw)
        self._items = []
        self.bind('<Configure>', self._relayout)

    def add(self, w):
        try:
            w.pack_forget()   # 创建处可能已 pack：先解除，统一由本容器 grid 管理
        except Exception:
            pass
        self._items.append(w)
        self._relayout()

    def set_visible(self, w, visible):
        """显示/隐藏某个子控件（隐藏后不参与换行重排）"""
        if visible:
            if w not in self._items:
                self._items.append(w)
        else:
            while w in self._items:
                self._items.remove(w)
            try:
                w.grid_forget()   # 解除当前 grid 位置（否则仍显示）
            except Exception:
                pass
        self._relayout()

    def _relayout(self, e=None):
        if not self._items:
            return
        for w in self._items:
            w.grid_forget()
        width = self.winfo_width()
        if width < 30:
            return
        row = col = 0
        used = 0
        for w in self._items:
            try:
                # 不能在此调用 update_idletasks()（Configure 事件链级联触发递归）；
                # winfo_reqwidth() 同步返回请求宽度
                ww = w.winfo_reqwidth() + 4
            except Exception:
                ww = 30
            if col > 0 and used + ww > width:
                row += 1
                col = 0
                used = 0
            w.grid(row=row, column=col, sticky='w', pady=1)
            col += 1
            used += ww


class FileMonitorApp:
    def __init__(self, root, container=None):
        """单窗口整合：container=None 时独立运行（UI 构建进 root）；
        container 提供时嵌入主窗口内容区（UI 顶层控件构建进 container，root 仅作 Tk）。"""
        self.root = root
        self.container = container or root   # 顶层控件统一挂这里（独立时=root）
        self._embedded = container is not None
        if not self._embedded:
            self.root.title(f"文件数量监控器 - 手动列数 v{PROJECT_VERSION}")
            self.root.geometry(window_geometry(root, 900, 700))   # 相对屏幕尺寸
            self.root.resizable(True, True)

        # ---- 加载保存的设置 ----
        saved = self.load_settings()

        # 验证并应用：配置文件可被用户手工编辑，任何类型错误都回退到安全值。
        lecture = saved.get("lecture", LECTURES[0] if LECTURES else '')
        if lecture not in LECTURES:
            lecture = LECTURES[0] if LECTURES else ''
        available_subs = list(get_current_sub_types(lecture))
        sub = saved.get("sub", available_subs[0] if available_subs else '')
        if not isinstance(sub, str) or sub not in available_subs:
            sub = available_subs[0] if available_subs else ''
        try:
            font_size = max(8, min(24, int(saved.get("font_size", 12))))
        except (TypeError, ValueError):
            font_size = 12
        try:
            columns = max(1, min(10, int(saved.get("columns", 3))))
        except (TypeError, ValueError):
            columns = 3

        # 控制变量
        self.current_lecture = StringVar(value=lecture)
        self.current_sub = StringVar(value=sub)
        self.font_size = IntVar(value=font_size)
        self.columns = IntVar(value=columns)

        # 已隐藏的班级（年份组），如 {'2001', '2011'}
        hidden = saved.get("hidden_classes", [])
        self.hidden_classes = set(hidden) if isinstance(hidden, (list, tuple, set)) else set()

        # 统计结果缓存: {(讲次, 分类): (时间戳, [student_data])}
        # 切换分类时 5 秒内命中缓存直接复用，实现秒级切换
        self._stats_cache = {}
        self._pending_refresh = False  # 刷新进行中收到新请求时标记，完成后补刷

        # 不规范命名的图片文件列表（自动检查，只读文件名，毫秒级）
        self._bad_names = []
        # 自动图片处理缓存：目录 -> 处理后 mtime（仅处理"变化的目录"，限频）
        self._img_process_cache = {}

        # 已反馈集合: 键 = "学生文件夹|讲次|子类型"
        feedback = saved.get("feedback", [])
        self.feedback_set = set(feedback) if isinstance(feedback, (list, tuple, set)) else set()

        # 弹幕列表（顶部浮动提示，替代弹窗；见 show_danmaku）
        self._danmakus = []
        # 弹幕显示时长（毫秒；设置中心可调）
        try:
            self._danmaku_ms = max(1000, min(10000, int(saved.get('danmaku_ms', 3000))))
        except (TypeError, ValueError):
            self._danmaku_ms = 3000
        # 自动处理/刷新间隔（毫秒；设置中心可调，默认 5 秒）
        try:
            self._auto_interval_ms = max(1000, min(60000, int(saved.get('auto_interval_sec', 5)) * 1000))
        except (TypeError, ValueError):
            self._auto_interval_ms = 5000
        # 复制批改剪贴板模式记忆：连续点击同一卡片 = 图片→文字 交替
        # （微信/QQ 一次粘贴只消费一种格式：图片模式=发图，文字模式=发文字）
        self._last_clip = None
        # 复制批改内容配置（设置中心可选：讲次信息/类型信息/胶囊视频/图片；
        # 讲次/考试/打卡 分开记忆、互不影响，默认全选）
        self.copy_content = _merge_copy_content(saved.get('copy_content'))

        # ---- 检索方式（与修改器一致）：内容检索（讲次-学生）/ 姓名-类别检索（学生-讲次）----
        self.search_mode = saved.get('search_mode', 'content')
        if self.search_mode not in ('content', 'student'):
            self.search_mode = 'content'
        self.student_name = saved.get('student', '全部') if isinstance(saved.get('student', '全部'), str) else '全部'
        self.student_cat = saved.get('student_cat', sub)
        if self.student_cat not in LECTURE_SUB_TYPES:
            self.student_cat = sub

        # ---- 刷新/命名范围 + 复制批改/删除模式开关（持久化：关闭后重启用保持原样）----
        self._saved_refresh_scope = saved.get('refresh_scope', '当前范围')
        if self._saved_refresh_scope not in ('当前范围', '全局'):
            self._saved_refresh_scope = '当前范围'
        self._saved_naming_scope = saved.get('naming_scope', '当前范围')
        if self._saved_naming_scope not in ('当前范围', '全局'):
            self._saved_naming_scope = '当前范围'
        self._saved_copy_mode = _as_bool(saved.get('copy_mode', False))
        self._saved_delete_mode = _as_bool(saved.get('delete_mode', False))
        if self._saved_copy_mode and self._saved_delete_mode:
            self._saved_copy_mode = False
        # 修改器变更标记的已处理 mtime（双向同步：避免重复触发）
        self._last_modifier_change_seen = 0.0

        self.student_data = []
        self.card_widgets = []
        self.card_data = {}       # card -> (folder_name, folder_path, target_dir)
        self.card_labels = {}     # card -> label_widget (为了快速更新文本)
        self.card_markers = {}    # card -> {动态分类/考试/打卡: widget}
        self.card_markers_colors = {'考试': 'purple', '打卡': 'green'}
        for i, cat in enumerate(LECTURE_SUB_TYPES):
            self.card_markers_colors[cat] = ('yellow', 'blue', 'black', '#d97706', '#2a9d8f')[i % 5]
        self.card_top_rows = {}       # card -> 顶部反馈标记行 frame
        self.card_bottom_rows = {}      # card -> 底部行 frame（含上一讲/下一讲标记）
        self.card_bottom_visible = {}   # card -> 底部行当前可见状态（防重复 pack 抖动）
        self.separators = []      # 保存班级分割线控件

        # 线程控制
        self.is_refreshing = False
        self.after_id = None
        self._need_arrange = True  # 标记是否需要重新排列布局
        self._closing = False      # 窗口关闭中：后台线程不再排队主线程回调

        # 命名器节流：避免每次自动刷新都全量运行 作业命名器.py（低配机器优化）
        self._last_namer_run = 0.0
        self._namer_throttle_sec = 30

        # 上一次窗口尺寸
        self._last_width = self.root.winfo_width()
        self._last_height = self.root.winfo_height()

        # ---- 存储优化（按图片年龄分级压缩/降质/缩略） ----
        self.storage_cfg = self.load_storage_cfg()   # 用户可自定义天数
        self._storage_running = False    # 优化线程运行中
        self._storage_done = False       # 优化线程完成（主线程周期检查取结果）
        self._storage_result = None
        self._storage_progress = 0       # 已处理张数（标题栏实时进度）
        self._storage_cancel = threading.Event()  # 页面离开后停止尚未开始的图片任务
        self._last_storage_check = 0.0   # 自动检查节流（默认 30 分钟）
        # 图片处理跨进程互斥锁（自动处理/存储优化/手动规范化/显式命名器共用）：
        # 同一把锁同时保护 同实例多线程、多监控器实例、命令行命名器 之间的互斥，
        # 防止多个写流程同时改同一图片导致损坏/重复处理
        self._processing_lock = PROCESS_LOCK

        self.create_widgets()
        self.load_data()
        self.build_cards()
        self.update_title()
        # 打开应用即发布一次检索状态并保留结果（后续修改器直接读取，不必等待首次定时刷新）：
        # 「在打开应用、学生信息变更时对学生信息进行检索并保留检索结果」——
        # load_data 已填充 student_data（target_dir），直接复用发布，零额外扫描。
        # student_data 为空（如学生模式未选学生）时跳过，避免用空列表覆盖上次结果。
        try:
            if self.student_data:
                self._publish_search_state()
        except Exception as e:
            print(f"启动发布检索状态失败: {e}")
        # 初始检索模式（持久化配置）：学生模式 → 切换面板并加载
        if self.search_mode == 'student':
            self.search_mode = 'content'   # 强制触发切换
            self.search_mode_var.set('student')
            self._switch_search_mode()

        # 鼠标滚轮
        self._bind_mouse_wheel()

        # 启动5秒定时刷新
        self.schedule_periodic_refresh()
        # 修改器变更检测：独立短轮询（不受自动处理间隔影响——用户把间隔调大时
        # 修改器保存/删除后仍能快速同步检索，满足"变动文件后传递给监视器刷新"）
        self._modifier_watch_id = self.root.after(1000, self._modifier_watch_tick)
        # 启动后延迟检查：不符合命名格式的文件夹（用户确认后移入回收站）
        self._startup_folder_check_id = self.root.after(800, self._startup_folder_check)
        if not self._embedded:
            self.root.protocol("WM_DELETE_WINDOW", self.on_closing)

        # 每次启动监视器即判定一次存储优化：延迟 2 秒执行（后台线程不阻塞界面；
        # 延迟避免与启动扫描抢 IO，也便于测试窗口短开时不触发）。
        # 幂等防重复：已按级别处理过的文件状态记录在 _storage_opt.json，跳过。
        self._storage_start_id = self.root.after(
            2000, lambda: None if self._closing else self._run_storage_optimize(force=True))

    def _modifier_watch_tick(self):
        """修改器变更独立短轮询：检测到变更立即刷新（与定时刷新解耦）。
        每 1 秒轮询一次修改器变更标记文件（getmtime 开销可忽略）。"""
        if self._closing:
            return
        self._watch_modifier_changes()
        if not self._closing:
            self._modifier_watch_id = self.root.after(1000, self._modifier_watch_tick)

    def _startup_folder_check(self):
        """运行时检查根目录与学生文件夹内部的文件夹是否合规、是否多余。
        安全约束：文件夹若含有文件，不得删除/重命名——
        仅"空"的不合规/多余文件夹移入回收站（可恢复，无确认弹窗）；
        含文件的一律只弹幕提示，请用户手动处理。
        名单内的缺失/名单外存在仅提示，不自动处理（序号固定，改动仅限用户）。
        """
        if self._closing:
            return
        try:
            bad, missing, extra = check_student_folders(BASE_DIR)
            sub_extra, _ = check_sub_folders(BASE_DIR)

            # ---- 可删除项（空文件夹）：根级不合规 + 子级多余，直接移入回收站 ----
            deletable = []   # [(完整路径, 相对显示名)]
            for d in bad:
                p = os.path.join(BASE_DIR, d)
                if is_empty_dir(p):
                    deletable.append((p, d))
            for p, empty in sub_extra:
                if empty:
                    deletable.append((p, os.path.relpath(p, BASE_DIR)))
            if deletable:
                results = {'recycled': [], 'moved': [], 'failed': []}
                for p, name in deletable:
                    r = move_to_recycle_bin(p)
                    results[r].append(name)
                msg = f"已将 {len(results['recycled']) + len(results['moved'])} 个空的、不合规/多余的文件夹移入回收站（可恢复）"
                if results['moved']:
                    msg += f"；其中 {len(results['moved'])} 个降级移至「_待清理」（回收站不可用）"
                if results['failed']:
                    msg += f"；{len(results['failed'])} 个处理失败（请手动删除）"
                self.show_danmaku(msg)
                self.refresh()

            # ---- 提示项（含文件，绝不删除/重命名）----
            nonempty = []
            for d in bad:
                p = os.path.join(BASE_DIR, d)
                if not is_empty_dir(p):
                    nonempty.append(d)
            nonempty += [os.path.relpath(p, BASE_DIR) for p, empty in sub_extra if not empty]
            if nonempty:
                self.show_danmaku(
                    f"有 {len(nonempty)} 个不合规/多余的文件夹含文件，未处理（安全起见请手动确认）")

            # ---- 名单与磁盘不符：提供 添加文件/删除名单/暂时不管 三选项 ----
            if missing or extra:
                self._prompt_student_diff(missing, extra)
        except Exception as e:
            print(f"启动文件夹检查出错: {e}")

            # ---- 名单与磁盘不符：提供 添加文件/删除名单/暂时不管 三选项 ----
            if missing or extra:
                self._prompt_student_diff(missing, extra)
        except Exception as e:
            print(f"启动文件夹检查出错: {e}")

    def _prompt_student_diff(self, missing, extra):
        """名单与磁盘不一致时弹窗，用户三选一：
        - 添加文件：磁盘上有但名单没有（extra）→ 加入名单（名单.json 持久化）
        - 删除名单：名单中有但磁盘没有（missing）→ 从名单移除
        - 暂时不管：本次不处理（下次启动会再次提示）
        """
        if not missing and not extra:
            return
        win = tk.Toplevel(self.root)
        win.title("名单与文件夹不符")
        win.geometry("520x420")
        win.transient(self.root)
        win.grab_set()
        lines = ["检测到学生名单与实际文件夹不一致：", ""]
        if missing:
            shown = '、'.join(missing[:20])
            lines.append(f"【名单有·磁盘无】{len(missing)} 个：{shown}" +
                         (' …' if len(missing) > 20 else ''))
            lines.append("")
        if extra:
            shown = '、'.join(extra[:20])
            lines.append(f"【磁盘有·名单无】{len(extra)} 个：{shown}" +
                         (' …' if len(extra) > 20 else ''))
            lines.append("")
        tk.Label(win, text='\n'.join(lines), justify=tk.LEFT, wraplength=480,
                 font=('微软雅黑', 9)).pack(padx=14, pady=(12, 4))
        tk.Label(win, text="处理方式（名单保存在「名单.json」，选择后立即生效并落盘）：",
                 justify=tk.LEFT, fg='#555555').pack(anchor=tk.W, padx=14, pady=(6, 2))

        result = {}

        def _on_add():
            n = add_students_from_folders(extra)
            result['msg'] = f"已将磁盘上 {n} 个学生文件夹加入名单（名单.json）。"
            win.destroy()

        def _on_remove():
            n = remove_students_by_folder(missing)
            result['msg'] = f"已从名单删除 {n} 个磁盘上不存在的学生（名单.json）。"
            win.destroy()

        def _on_skip():
            result['msg'] = "本次暂不处理（下次启动将再次提示）。"
            win.destroy()

        def _on_framework():
            # 打开框架搭建器 GUI：可在其中逐项自由选择
            # （左栏 创建文件夹/删除名单条目；右栏 加入名单/删除文件夹）
            script = os.path.join(PROGRAM_DIR, '框架搭建器.py')
            try:
                subprocess.Popen([sys.executable, script])
            except Exception as e:
                self.show_danmaku(f"启动框架搭建器失败：{e}")
                win.destroy()
                return
            result['msg'] = "已打开框架搭建器，可逐项全面处理（本弹窗已关闭）。"
            win.destroy()

        # 第一行：逐项全面处理入口（推荐）
        top_row = tk.Frame(win)
        top_row.pack(pady=(10, 2))
        tk.Button(top_row, text="打开框架搭建器（逐项全面处理）", command=_on_framework,
                  font=('微软雅黑', 10), bg='#fff3cd').pack()

        # 第二行：原有快速批量选项
        btns = tk.Frame(win)
        btns.pack(pady=(4, 10))
        if extra:
            tk.Button(btns, text="全部加入名单", command=_on_add,
                      bg='#d1e7dd').pack(side=tk.LEFT, padx=5)
        if missing:
            tk.Button(btns, text="全部删除名单", command=_on_remove,
                      bg='#ffcccc').pack(side=tk.LEFT, padx=5)
        tk.Button(btns, text="暂时不管", command=_on_skip).pack(side=tk.LEFT, padx=5)

        win.wait_window()   # 阻塞到用户选择
        if result.get('msg'):
            self.show_danmaku(result['msg'])
            try:
                self.refresh()   # 名单变化：刷新卡片（显示新名单学生）
            except Exception:
                pass

    # ================================================================
    #  设置持久化
    # ================================================================

    def load_settings(self):
        try:
            with open(SETTINGS_FILE, 'r', encoding='utf-8') as f:
                data = json.load(f)
            # 防御：设置文件是合法 JSON 但不是 dict（如被手改成 []/"x"）时
            # 按空设置处理，避免启动即 AttributeError 崩溃
            return data if isinstance(data, dict) else {}
        except (FileNotFoundError, json.JSONDecodeError):
            return {}

    def save_settings(self):
        settings = self.load_settings()
        if not isinstance(settings, dict):
            settings = {}
        settings.update({
            "lecture": self.current_lecture.get(),
            "sub": self.current_sub.get(),
            "font_size": self.font_size.get(),
            "columns": self.columns.get(),
            "feedback": list(self.feedback_set),
            "hidden_classes": sorted(self.hidden_classes),
            "storage": dict(self.storage_cfg),
            "search_mode": self.search_mode,
            "student": self.student_name,
            "student_cat": self.student_cat,
            "copy_content": self.copy_content,
            # 补齐持久化：弹幕时长/自动刷新间隔（设置中心可调）、
            # 刷新/命名范围（当前范围|全局）、复制批改/删除模式开关——
            # 全部保持"关闭后在启用仍为原样"
            "danmaku_ms": int(getattr(self, '_danmaku_ms', 3000)),
            "auto_interval_sec": int(getattr(self, '_auto_interval_ms', 5000) // 1000),
            "refresh_scope": getattr(self, 'refresh_scope', None).get() if getattr(self, 'refresh_scope', None) else '当前范围',
            "naming_scope": getattr(self, 'naming_scope', None).get() if getattr(self, 'naming_scope', None) else '当前范围',
            "copy_mode": bool(getattr(self, 'copy_mode', False)),
            "delete_mode": _as_bool(getattr(self, 'delete_mode', False)),
        })
        try:
            atomic_write_json(SETTINGS_FILE, settings, ensure_ascii=False, indent=2)
        except Exception as e:
            print(f"保存设置失败: {e}")

    def load_storage_cfg(self):
        """读取存储优化配置（天数可自定义；0 = 关闭该级）"""
        s = self.load_settings().get('storage', {})
        if not isinstance(s, dict):
            s = {}
        try:
            return {
                'enabled': _as_bool(s.get('enabled', True), True),
                'compress_days': max(0, int(s.get('compress_days', 4))),
                'degrade_days': max(0, int(s.get('degrade_days', 7))),
                'thumb_days': max(0, int(s.get('thumb_days', 10))),
                'thumb_max_edge': max(200, int(s.get('thumb_max_edge', 640))),
            }
        except (ValueError, TypeError):
            return {'enabled': True, 'compress_days': 4, 'degrade_days': 7,
                    'thumb_days': 10, 'thumb_max_edge': 640}

    # ================================================================
    #  鼠标滚轮
    # ================================================================

    def _bind_mouse_wheel(self):
        self.canvas.bind_all('<MouseWheel>', self._on_mousewheel)
        self.canvas.bind_all('<Button-4>', self._on_mousewheel_linux)
        self.canvas.bind_all('<Button-5>', self._on_mousewheel_linux)

    def _pointer_in_canvas(self):
        """指针是否位于卡片画布区域内（限定滚轮只滚动画布，避免影响下拉框/输入框）"""
        try:
            x = self.root.winfo_pointerx(); y = self.root.winfo_pointery()
            cx = self.canvas.winfo_rootx(); cy = self.canvas.winfo_rooty()
            cw = self.canvas.winfo_width(); ch = self.canvas.winfo_height()
            if cw <= 0 or ch <= 0:
                return True   # 尚未布局，保守允许
            return cx <= x <= cx + cw and cy <= y <= cy + ch
        except Exception:
            return True   # 异常时保守允许

    def _on_mousewheel(self, event):
        if not self._pointer_in_canvas():
            return   # 不拦截，交给焦点控件（下拉框/输入框）自己的滚轮行为
        if abs(event.delta) >= 120:
            scroll_amount = int(-event.delta / 120) * 3
        else:
            # 触控板平滑滚动：delta 是小值（非 120 倍数），按方向滚 1 行。
            # 修复历史 bug：原实现 int(-delta)*3 把 delta=30 当作 30 行×3=90 行，
            # 一次手势直接滚到底部。
            scroll_amount = 1 if event.delta < 0 else -1
        self.canvas.yview_scroll(scroll_amount, 'units')

    def _on_mousewheel_linux(self, event):
        if not self._pointer_in_canvas():
            return
        if event.num == 4:
            self.canvas.yview_scroll(-3, 'units')
        elif event.num == 5:
            self.canvas.yview_scroll(3, 'units')

    # ================================================================
    #  控件创建
    # ================================================================

    def create_widgets(self):
        # ============ 工具栏（自动换行容器：窗口缩放时按钮自动重排） ============
        wrap_row1 = WrapFrame(self.container)
        wrap_row1.pack(pady=(8, 2), fill=tk.X, padx=10, side=tk.TOP)

        tk.Label(wrap_row1, text="刷新:").pack(side=tk.LEFT, padx=(5, 0)); wrap_row1.add(wrap_row1.winfo_children()[-1])
        self.refresh_scope = ttk.Combobox(wrap_row1, values=["当前范围", "全局"], state="readonly", width=8)
        self.refresh_scope.set(self._saved_refresh_scope); self.refresh_scope.pack(side=tk.LEFT, padx=2); wrap_row1.add(self.refresh_scope)
        b = tk.Button(wrap_row1, text="刷新", command=self.refresh_by_scope); b.pack(side=tk.LEFT, padx=2); wrap_row1.add(b)

        tk.Label(wrap_row1, text="命名:").pack(side=tk.LEFT, padx=(15, 0)); wrap_row1.add(wrap_row1.winfo_children()[-1])
        self.naming_scope = ttk.Combobox(wrap_row1, values=["当前范围", "全局"], state="readonly", width=8)
        self.naming_scope.set(self._saved_naming_scope); self.naming_scope.pack(side=tk.LEFT, padx=2); wrap_row1.add(self.naming_scope)
        b = tk.Button(wrap_row1, text="命名", command=self.rename_by_scope); b.pack(side=tk.LEFT, padx=2); wrap_row1.add(b)

        tk.Label(wrap_row1, text="字体:").pack(side=tk.LEFT, padx=(15, 2)); wrap_row1.add(wrap_row1.winfo_children()[-1])
        size_scale = tk.Scale(wrap_row1, from_=8, to=24, orient=tk.HORIZONTAL,
                              variable=self.font_size, length=70, command=self.on_font_changed)
        size_scale.pack(side=tk.LEFT, padx=2); wrap_row1.add(size_scale)

        tk.Label(wrap_row1, text="列数:").pack(side=tk.LEFT, padx=5); wrap_row1.add(wrap_row1.winfo_children()[-1])
        col_spinbox = tk.Spinbox(wrap_row1, from_=1, to=10, width=3,
                                 textvariable=self.columns, command=self.on_columns_changed)
        col_spinbox.pack(side=tk.LEFT, padx=2); wrap_row1.add(col_spinbox)

        # 顶部主窗口导航已有「⚙设置」「✏修改器」入口：嵌入模式不再重复提供设置/
        # 存储优化/打开修改器按钮（存储优化功能已并入设置中心「监控器」页，「立即优化」
        # 可触发）；独立运行无顶部工具栏，保留 设置/打开修改器 入口。
        if not self._embedded:
            b = tk.Button(wrap_row1, text="⚙ 设置", command=self.open_settings_center)
            b.pack(side=tk.LEFT, padx=(15, 2)); wrap_row1.add(b)
            b = tk.Button(wrap_row1, text="✏ 打开修改器", command=self.open_modifier, bg='#d1e7dd')
            b.pack(side=tk.LEFT, padx=15); wrap_row1.add(b)
        # 复制批改模式开关：启用后左键点击学生卡片 = 复制该学生对应文件夹的 -改 图片
        # （+ 生成"这是第X讲的X情况"说明文本），用于向家长汇报批改情况
        self.copy_mode = self._saved_copy_mode
        self.copy_btn = tk.Button(wrap_row1, text="📋 复制批改：关", command=self.toggle_copy_mode)
        self.copy_btn.pack(side=tk.LEFT, padx=(15, 2)); wrap_row1.add(self.copy_btn)
        # 删除模式开关：启用后左键点击学生卡片 = 列出该学生当前讲次/分类文件夹的图片，
        # 多选移入回收站（可恢复）——方便删除放错的图片（与复制批改互斥）
        self.delete_mode = self._saved_delete_mode
        self.delete_btn = tk.Button(wrap_row1, text="🗑 删除：关", command=self.toggle_delete_mode)
        self.delete_btn.pack(side=tk.LEFT, padx=2); wrap_row1.add(self.delete_btn)
        # 恢复按钮文字/背景，与持久化的开关状态一致
        self.copy_btn.config(text="📋 复制批改：开" if self.copy_mode else "📋 复制批改：关",
                             bg='#d1e7dd' if self.copy_mode else 'SystemButtonFace')
        self.delete_btn.config(text="🗑 删除：开" if self.delete_mode else "🗑 删除：关",
                               bg='#f8d7da' if self.delete_mode else 'SystemButtonFace')

        # ============ 第二行：筛选条件（检索方式/讲次/分类/班级） ============
        self.wrap_row2 = WrapFrame(self.container)
        self.wrap_row2.pack(pady=2, fill=tk.X, padx=10, side=tk.TOP)

        # 检索方式：内容检索（讲次-学生）/ 姓名-类别检索（学生-讲次），两者独立
        tk.Label(self.wrap_row2, text="检索:").pack(side=tk.LEFT, padx=(0, 2))
        self.wrap_row2.add(self.wrap_row2.winfo_children()[-1])
        self.search_mode_var = tk.StringVar(value=self.search_mode)
        rb = tk.Radiobutton(self.wrap_row2, text="讲次-学生", variable=self.search_mode_var,
                            value='content', command=self._switch_search_mode)
        rb.pack(side=tk.LEFT); self.wrap_row2.add(rb)
        rb = tk.Radiobutton(self.wrap_row2, text="姓名-类别", variable=self.search_mode_var,
                            value='student', command=self._switch_search_mode)
        rb.pack(side=tk.LEFT); self.wrap_row2.add(rb)

        self._lecture_label = tk.Label(self.wrap_row2, text="讲次：")
        self._lecture_label.pack(side=tk.LEFT, padx=5); self.wrap_row2.add(self._lecture_label)
        self.lecture_combo = ttk.Combobox(self.wrap_row2, textvariable=self.current_lecture,
                                          values=LECTURES, state="readonly", width=12)
        self.lecture_combo.pack(side=tk.LEFT, padx=5); self.wrap_row2.add(self.lecture_combo)
        self.lecture_combo.bind('<<ComboboxSelected>>', self.on_lecture_changed)

        # 分类：单选按钮组（考试/打卡时隐藏）
        self.cat_group = tk.Frame(self.wrap_row2)
        self.cat_label = tk.Label(self.cat_group, text="分类：")
        self.cat_label.pack(side=tk.LEFT, padx=(12, 2))
        self.cat_buttons = []
        for cat in LECTURE_SUB_TYPES:
            rb = tk.Radiobutton(self.cat_group, text=cat, variable=self.current_sub,
                                value=cat, command=self.on_control_changed)
            rb.pack(side=tk.LEFT, padx=1)
            self.cat_buttons.append(rb)
        self.cat_group.pack(side=tk.LEFT)
        self.wrap_row2.add(self.cat_group)

        # 班级组（内容模式：勾选显示班级）
        self.class_label = tk.Label(self.wrap_row2, text="班级:")
        self.class_label.pack(side=tk.LEFT, padx=(12, 2)); self.wrap_row2.add(self.class_label)
        self.class_buttons = []
        for year in self._collect_classes():
            var = tk.BooleanVar(value=(year not in self.hidden_classes))
            cb = tk.Checkbutton(self.wrap_row2, text=year, variable=var,
                                command=lambda y=year, v=var: self.on_class_toggled(y, v))
            cb.pack(side=tk.LEFT, padx=1)
            self.wrap_row2.add(cb)
            self.class_buttons.append((year, var, cb))

        # 初始状态：如果当前选的是考试/打卡，隐藏分类组
        if is_exam_or_checkin(self.current_lecture.get()):
            self.wrap_row2.set_visible(self.cat_group, False)

        # ---- 姓名-类别检索面板（班级→序号→姓名 逐级过滤，独立换行行） ----
        self.row_student = WrapFrame(self.container)   # 默认不显示（切换时 pack）
        tk.Label(self.row_student, text="班级:").pack(side=tk.LEFT, padx=(5, 2))
        self.row_student.add(self.row_student.winfo_children()[-1])
        self.student_class_var = tk.StringVar(value='全部')
        self.student_class_combo = ttk.Combobox(self.row_student, textvariable=self.student_class_var,
                                                values=['全部'] + self._collect_classes(),
                                                state='readonly', width=6)
        self.student_class_combo.pack(side=tk.LEFT, padx=2); self.row_student.add(self.student_class_combo)
        self.student_class_combo.bind('<<ComboboxSelected>>', self._on_student_filter_changed)
        tk.Label(self.row_student, text="序号:").pack(side=tk.LEFT, padx=(12, 2))
        self.row_student.add(self.row_student.winfo_children()[-1])
        self.student_seq_var = tk.StringVar(value='全部')
        self.student_seq_combo = ttk.Combobox(self.row_student, textvariable=self.student_seq_var,
                                              values=['全部'], state='readonly', width=5)
        self.student_seq_combo.pack(side=tk.LEFT, padx=2); self.row_student.add(self.student_seq_combo)
        self.student_seq_combo.bind('<<ComboboxSelected>>', self._on_student_filter_changed)
        tk.Label(self.row_student, text="姓名:").pack(side=tk.LEFT, padx=(12, 2))
        self.row_student.add(self.row_student.winfo_children()[-1])
        self.student_name_var = tk.StringVar(value=self.student_name)
        self.student_combo = ttk.Combobox(self.row_student, textvariable=self.student_name_var,
                                          values=['全部'], state='readonly', width=14)
        self.student_combo.pack(side=tk.LEFT, padx=2); self.row_student.add(self.student_combo)
        self.student_combo.bind('<<ComboboxSelected>>', self._on_student_changed)

        canvas_frame = tk.Frame(self.container)
        self.canvas_frame = canvas_frame   # 学生面板切换时 pack 到其前（检索栏之后）
        canvas_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        self.canvas = tk.Canvas(canvas_frame, highlightthickness=0)
        scrollbar = ttk.Scrollbar(canvas_frame, orient=tk.VERTICAL, command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=scrollbar.set)

        self.inner_frame = tk.Frame(self.canvas)
        self.inner_window = self.canvas.create_window((0, 0), window=self.inner_frame, anchor='nw')

        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        self.inner_frame.bind('<Configure>', self.on_inner_frame_configure)
        self.canvas.bind('<Configure>', self.on_canvas_configure)
        # 嵌入时 <Configure> 挂 container（页面缩放重排），独立时 container==root 语义不变
        self.container.bind('<Configure>', self.on_window_resize)

    def _collect_classes(self):
        """收集所有班级（年份）：磁盘上学生文件夹的年份 ∪ 名单中的年份，排序"""
        years = set(STUDENTS.keys())
        try:
            with os.scandir(BASE_DIR) as it:
                for e in it:
                    if e.is_dir() and is_student_folder(e.name):
                        years.add(e.name.split('-')[0])
        except OSError:
            pass
        return sorted(years)

    def on_class_toggled(self, year, var):
        """班级显示勾选变化：更新隐藏集合、清统计缓存并刷新（内容模式用；
        学生模式班级由独立下拉控制，不随勾选变化）"""
        if var.get():
            self.hidden_classes.discard(year)
        else:
            self.hidden_classes.add(year)
        self._stats_cache.clear()   # 班级过滤影响统计结果，缓存失效
        self.save_settings()
        self.refresh()

    # ================================================================
    #  姓名-类别检索模式（与内容检索独立；卡片 = 选定学生的各讲次×类别+考试+打卡）
    # ================================================================
    def _switch_search_mode(self):
        """切换 内容检索（讲次-学生）↔ 姓名-类别检索（学生-讲次），各自条件独立"""
        mode = self.search_mode_var.get()
        if mode == self.search_mode:
            return
        self.search_mode = mode
        if mode == 'student':
            self.wrap_row2.set_visible(self._lecture_label, False)
            self.wrap_row2.set_visible(self.lecture_combo, False)
            # 学生面板插到检索选项栏之后、卡片区之前（原实现 pack 追加到末尾，
            # 会显示在卡片区下方）
            try:
                self.row_student.pack(pady=2, fill=tk.X, padx=10, side=tk.TOP,
                                      before=self.canvas_frame)
            except Exception:
                self.row_student.pack(pady=2, fill=tk.X, padx=10, side=tk.TOP)
            self.wrap_row2.set_visible(self.cat_group, True)
            self._update_student_options()
            self._load_student_cards()
        else:
            self.row_student.pack_forget()
            self.wrap_row2.set_visible(self._lecture_label, True)
            self.wrap_row2.set_visible(self.lecture_combo, True)
            if is_exam_or_checkin(self.current_lecture.get()):
                self.wrap_row2.set_visible(self.cat_group, False)
            self.refresh()
        self.save_settings()

    def _update_student_options(self):
        """姓名-类别检索：按 班级下拉→序号下拉 逐级过滤，刷新 序号/姓名 选项。
        班级+序号通常唯一对应一个学生，姓名下拉会自动锁定（"得到一个学生的姓名"）。"""
        if not hasattr(self, 'student_seq_combo') or self.student_seq_combo is None:
            return
        cls = self.student_class_var.get()
        seqs, names = collect_student_options(cls)
        self.student_seq_combo.config(values=seqs)
        sel = self.student_seq_var.get()
        if sel != '全部':
            pad = f"{int(sel):02d}"
            names = ['全部'] + [n for n in names[1:] if n.split('-')[1] == pad]
        self.student_combo.config(values=names)
        # 当前姓名不在新范围 → 重置
        if self.student_name != '全部' and self.student_name not in names:
            self.student_name_var.set('全部')
            self.student_name = '全部'

    def _on_student_filter_changed(self, event=None):
        """班级/序号过滤变化：刷新下级选项；班级+序号唯一对应学生时自动选中姓名并加载"""
        self._update_student_options()
        # 序号已选且非"全部"：该班该序号通常唯一 → 自动定位姓名（"得到一个学生的姓名"）
        if self.student_seq_var.get() != '全部':
            cands = [n for n in self.student_combo.cget('values') if n != '全部']
            if len(cands) == 1:
                if self.student_name_var.get() != cands[0]:
                    self.student_name_var.set(cands[0])
                    self.student_name = cands[0]
                    self._load_student_cards()
                    self.save_settings()
                return
        # 多候选或未选序号：若当前姓名已不在范围则加载（否则保持）
        if self.student_name_var.get() != self.student_name:
            self.student_name = self.student_name_var.get()
            self._load_student_cards()
            self.save_settings()

    def _on_student_changed(self, event=None):
        """选择学生：加载该学生卡片（各讲次×类别 + 考试 + 打卡）"""
        self.student_name = self.student_name_var.get()
        self.student_cat = self.current_sub.get()
        self._load_student_cards()
        self.save_settings()

    def _load_student_cards(self):
        """学生模式统计：选定学生的 各讲次×(类别) + 考试 + 打卡 卡片。
        未确定学生时**不显示任何组件**（卡片区空白），确认学生后才显示其各讲次文件夹。
        学生可在名单中自定义「学习讲次」（默认全部）：只显示该学生学习的讲次卡片。"""
        student = self.student_name
        cat = self.current_sub.get()
        self.student_cat = cat
        self.student_data.clear()
        student_path = os.path.join(BASE_DIR, student) if student and student != '全部' else ''
        if not student_path or not os.path.isdir(student_path):
            self.build_cards()   # 未确定学生：卡片区留白（重建=清空组件）
            return
        # 解析学生 班级/序号，查询其「学习讲次」（默认全部 = LECTURES）
        m = STUDENT_FOLDER_RE.match(student)
        if m:
            year, seq = m.group(1), int(m.group(2))
            learn_set = set(student_lecture_names(year, seq)) if student_lecture_names(year, seq) else None
        else:
            learn_set = None   # 无法解析：视为学习全部
        for ld in LECTURES:
            if learn_set is not None and ld not in learn_set:
                continue   # 该学生未学习此讲次：不显示卡片
            if is_exam_or_checkin(ld):
                # 考试/打卡：任何类别下都显示
                target = os.path.join(student_path, ld)
                self._stat_student_card(student, student_path, ld, '', target)
            elif cat == '全部':
                for sub in LECTURE_SUB_TYPES:
                    target = os.path.join(student_path, ld, sub)
                    self._stat_student_card(student, student_path, f"{ld}·{sub}", sub, target)
            else:
                target = os.path.join(student_path, ld, cat)
                self._stat_student_card(student, student_path, f"{ld}·{cat}", cat, target)
        # 重建卡片组件（原实现只更新数据，选姓名后界面不变化）
        self.build_cards()

    def _dir_count_state(self, target_dir):
        """统计目录文件数与批改状态：返回 (file_count, has_images, has_modified)。
        目录不存在 → (0, False, False)。"""
        file_count = 0
        has_images = has_modified = False
        if os.path.isdir(target_dir):
            try:
                files = self._scan_dir_files(target_dir)
                file_count = len(files)
                for fname in files:
                    ext = os.path.splitext(fname)[1].lower()
                    if ext in IMAGE_EXTENSIONS:
                        has_images = True
                        if os.path.splitext(fname)[0].endswith('-改'):
                            has_modified = True
            except Exception:
                pass
        return file_count, has_images, has_modified

    def _status_style(self, title, file_count, has_images, has_modified):
        """按文件情况选卡片样式：(背景色, 显示文案)。
        灰=无图、浅绿=已批改、浅红=有图未批改。"""
        if not has_images:
            return '#f0f0f0', f"{title}\n文件数: {file_count}"
        if has_modified:
            return '#ccffcc', f"{title}\n文件数: {file_count}"
        return '#ffcccc', f"{title}\n文件数: {file_count}"

    def _stat_student_card(self, student, student_path, display, sub, target_dir):
        """统计单个讲次/分类目录（学生模式卡片）"""
        file_count, has_images, has_modified = self._dir_count_state(target_dir)
        bg, line = self._status_style(display, file_count, has_images, has_modified)
        self.student_data.append((student, file_count, bg, line, student_path, target_dir))

    def _card_lecture_sub(self, card):
        """解析卡片对应的 讲次/分类（学生模式下从 target_dir 相对学生目录推导；
        内容模式与当前筛选一致）。返回 (lecture, sub_type)；无法解析返回 (None, None)。"""
        try:
            folder_name, folder_path, target_dir = self.card_data.get(card, ('', '', ''))
            if not folder_path or not target_dir:
                return None, None
            rel = os.path.relpath(target_dir, folder_path)
            parts = rel.split(os.sep)
        except Exception:
            return None, None
        if len(parts) >= 2:
            return parts[0], parts[1]
        return rel, None

    def _update_scrollregion(self):
        """统一维护卡片区滚动范围：
        - scrollregion 高度至少等于可视高度：内容不满一屏时不可滚动
          （原实现直接用 bbox('all')，内容不满屏时滚轮仍可滚动，顶部/底部留白）
        - 内容变矮后视口超出范围时复位到顶部（防组件显示不全/留白）"""
        try:
            br = self.canvas.bbox('all')
            if not br:
                return
            ch = self.canvas.winfo_height()
            if ch > 0:
                content_h = br[3] - br[1]
                if content_h < ch:
                    br = (br[0], br[1], br[2], br[1] + ch)
                self.canvas.configure(scrollregion=br)
                # 内容不满屏（scrollregion=视口高）时视口必须贴顶，否则留白
                if content_h <= ch:
                    self.canvas.yview_moveto(0)
            else:
                self.canvas.configure(scrollregion=br)
        except Exception:
            pass

    def on_inner_frame_configure(self, event):
        self._update_scrollregion()

    def on_canvas_configure(self, event):
        self.canvas.itemconfig(self.inner_window, width=event.width)

    def on_window_resize(self, event):
        if event.widget == self.container:
            new_width = event.width
            new_height = event.height
            if new_width != self._last_width or new_height != self._last_height:
                self._last_width = new_width
                self._last_height = new_height
                # 去抖：拖动窗口时 Configure 高频触发，合并为 120ms 内只重排一次
                if getattr(self, '_resize_after', None) is not None:
                    try:
                        self.root.after_cancel(self._resize_after)
                    except Exception:
                        pass
                self._resize_after = self.root.after(120, self._debounced_arrange)

    def _debounced_arrange(self):
        self._resize_after = None
        try:
            self.arrange_cards()
        except Exception:
            pass

    # ================================================================
    #  事件处理
    # ================================================================

    def on_control_changed(self, event=None):
        # event 兼容两种调用：Radiobutton command（无参）与事件绑定（带 event）
        self.save_settings()
        if self.search_mode == 'student':
            # 学生模式：分类切换 → 重新加载该学生卡片
            self._on_student_changed()
            return
        self.refresh()

    def on_lecture_changed(self, event):
        """讲次变化时，动态显示/隐藏分类单选组（换行容器内重排）"""
        lecture = self.current_lecture.get()
        if is_exam_or_checkin(lecture):
            # 考试/打卡天：隐藏分类组
            self.wrap_row2.set_visible(self.cat_group, False)
        else:
            # 讲次：显示分类组
            self.wrap_row2.set_visible(self.cat_group, True)
            if self.current_sub.get() not in LECTURE_SUB_TYPES:
                self.current_sub.set(LECTURE_SUB_TYPES[0])
        self.save_settings()
        self.refresh()

    def on_font_changed(self, value):
        # 拖动字体滑块时高频触发：去抖合并为 150ms 内只重建一次卡片
        if getattr(self, '_font_after', None) is not None:
            try:
                self.root.after_cancel(self._font_after)
            except Exception:
                pass
        self._font_after = self.root.after(150, self._apply_font_change)

    def _apply_font_change(self):
        self._font_after = None
        self.save_settings()
        self._need_arrange = True  # 字体改变可能引起尺寸变化
        try:
            self.build_cards()
        except Exception:
            pass

    def on_columns_changed(self):
        try:
            val = int(self.columns.get())
        except (ValueError, TypeError, tk.TclError):
            # 用户手动输入非数字：回退到默认 3 列，避免 TclError 崩溃
            self.columns.set(3)
            val = 3
        if val < 1:
            self.columns.set(1)
        elif val > 10:
            self.columns.set(10)
        self.save_settings()
        self.arrange_cards()

    # ================================================================
    #  数据加载
    # ================================================================

    def _scan_dir_files(self, directory):
        """增量扫描目录文件列表（复用 common.scan_dir_incremental，mtime 缓存）"""
        return scan_dir_incremental(directory)[1]

    def _stat_one_student(self, folder_name, folder_path, lecture, sub_type, is_exam_checkin):
        """统计单个学生目标目录的文件情况（供多线程并行调用，无 UI 操作）"""
        if is_exam_checkin:
            # 考试或打卡天：直接统计该目录下的所有文件
            target_dir = os.path.join(folder_path, lecture)
        else:
            target_dir = os.path.join(folder_path, lecture, sub_type)

        file_count, has_images, has_modified = self._dir_count_state(target_dir)
        bg, display = self._status_style(folder_name, file_count, has_images, has_modified)
        return (folder_name, file_count, bg, display, folder_path, target_dir)

    def _scan_student_folders(self, hidden):
        """扫描根目录学生文件夹列表（按班级过滤、排序）。
        每个刷新周期只调用一次，结果供 图片处理/命名检查/统计 三处复用，
        避免每 5 秒对 BASE_DIR 顶层重复 scandir 3 次。"""
        student_folders = []
        try:
            with os.scandir(BASE_DIR) as it:
                for entry in it:
                    try:
                        if not entry.is_dir():
                            continue
                    except OSError:
                        # 单个条目访问失败（权限/占用）：跳过该条，不中断整轮
                        # （修复历史 bug：原实现 entry.is_dir() 抛错会中止整个
                        # 循环，学生列表缺失、自动处理空跑一轮）
                        continue
                    if is_student_folder(entry.name):
                        # 隐藏的班级（年份组）不显示
                        if entry.name.split('-')[0] in hidden:
                            continue
                        student_folders.append((entry.name, entry.path))
        except OSError as e:
            print(f"扫描根目录出错: {e}")
        student_folders.sort(key=lambda x: x[0])
        return student_folders

    def load_data(self, lecture=None, sub_type=None, hidden=None, student_folders=None):
        # lecture/sub_type/hidden 由主线程快照传入（后台线程读 Tk 变量非线程安全）；
        # None 时回退直接读取（主线程调用场景）；student_folders 由调用方预扫描传入
        if lecture is None:
            lecture = self.current_lecture.get()
        if sub_type is None:
            sub_type = self.current_sub.get()
        if hidden is None:
            hidden = self.hidden_classes
        key = (lecture, sub_type)

        # 缓存命中（5 秒内）：直接复用统计结果，切换分类秒级响应。
        # 注意返回**副本**：命中路径的 student_data 不得与缓存条目共享同一 list，
        # 否则后续缓存未命中时 self.student_data.clear() 会把缓存数据一起清空
        # （历史 bug：快速切换分类后卡片空白）。
        cached = self._stats_cache.get(key)
        if cached is not None and time.time() - cached[0] < 5:
            self.student_data = list(cached[1])
            return

        # 重新绑定而非 clear()：避免误清共享的缓存列表（见上）
        self.student_data = []
        is_exam_checkin = is_exam_or_checkin(lecture)

        if student_folders is None:
            student_folders = self._scan_student_folders(hidden)

        if not student_folders:
            self.student_data.append(("⚠️ 未找到学生文件夹", 0, '#f0f0f0',
                                      "⚠️ 未找到学生文件夹", "", ""))
            return

        # 并行统计每个学生（IO 密集，线程并行提速；目录扫描缓存线程安全）
        workers = PARALLEL_WORKERS
        with ThreadPoolExecutor(max_workers=workers) as ex:
            results = list(ex.map(
                lambda s: self._stat_one_student(s[0], s[1], lecture, sub_type, is_exam_checkin),
                student_folders))
        self.student_data = results
        # 写入缓存（快照），供快速切换分类复用；限制条数防止极端情况膨胀
        self._stats_cache[key] = (time.time(), list(self.student_data))
        if len(self._stats_cache) > 30:
            # 清理最旧的条目（按写入时间排序，保留最近 30 个组合）
            oldest = sorted(self._stats_cache, key=lambda k: self._stats_cache[k][0])[:-30]
            for k in oldest:
                del self._stats_cache[k]

    # ================================================================
    #  卡片构建与复用优化 (彻底防闪烁)
    # ================================================================

    def build_cards(self):
        if not self.student_data:
            for card in self.card_widgets:
                card.grid_forget()
            return

        font = ("Arial", self.font_size.get())
        needed_cards = len(self.student_data)

        # 如果卡片数量不够，需要创建并重排
        if len(self.card_widgets) < needed_cards:
            self._need_arrange = True
            for i in range(len(self.card_widgets), needed_cards):
                card = tk.Frame(self.inner_frame, relief=tk.RAISED, borderwidth=2, padx=10, pady=10, cursor='hand2')
                label = tk.Label(card, font=font, justify=tk.CENTER, cursor='hand2')
                # 顶部反馈标记行按当前配置动态生成，新增/改名分类无需改代码。
                top_row = tk.Frame(card)
                marker_colors = {'考试': 'purple', '打卡': 'green'}
                marker_frames = {}
                for col, cat in enumerate(LECTURE_SUB_TYPES):
                    frame = tk.Frame(top_row, bg=self.card_markers_colors.get(cat, 'gray'),
                                      relief=tk.SOLID, borderwidth=1, height=8)
                    frame.grid(row=0, column=col, sticky='nsew')
                    top_row.columnconfigure(col, weight=1, uniform='topmark')
                    marker_frames[cat] = frame
                for cat, color in marker_colors.items():
                    frame = tk.Frame(top_row, bg=color, relief=tk.SOLID,
                                     borderwidth=1, height=8, width=100)
                    frame.grid(row=0, column=0, columnspan=max(1, len(LECTURE_SUB_TYPES)), sticky='nsew')
                    frame.grid_remove()
                    marker_frames[cat] = frame
                # 位置提前留存：顶部行始终占位（固定高度），标记切换不改变卡片布局
                top_row.pack(side=tk.TOP, fill=tk.X)
                # 名字区在反馈块之后 pack → 显示在反馈块下方（反馈块位于卡片顶部）
                label.pack(fill=tk.BOTH, expand=True)

                # 底部行：上一讲 / 下一讲 同类型状态标记
                # （灰=无文件 绿=全部已批改 红=存在未批改；考试/打卡天无讲次概念，整行隐藏）
                bottom = tk.Frame(card)
                prev_m = tk.Frame(bottom, bg=ADJ_MARKER_GRAY, relief=tk.SOLID, borderwidth=1, height=8)
                next_m = tk.Frame(bottom, bg=ADJ_MARKER_GRAY, relief=tk.SOLID, borderwidth=1, height=8)
                prev_m.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
                next_m.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
                bottom.pack(side=tk.BOTTOM, fill=tk.X)

                self.card_widgets.append(card)
                self.card_labels[card] = label
                self.card_markers[card] = marker_frames
                self.card_top_rows[card] = top_row
                self.card_bottom_rows[card] = (prev_m, next_m, bottom)
                self.card_bottom_visible[card] = False
                # 占位数据（下方更新循环立即覆盖）；事件回调按事件时读取最新值
                self.card_data[card] = ("", "", "")
                # 事件/拖放只在此绑定一次（不随 5 秒刷新重复绑定）
                self._bind_card_events(card, label, "", "", "")

        # 数量没变时不重排，只更新属性
        # 更新所有卡片属性
        for i in range(needed_cards):
            folder_name, _, bg, display_text, folder_path, target_dir = self.student_data[i]
            card = self.card_widgets[i]
            label = self.card_labels[card]

            card.config(bg=bg)
            label.config(text=display_text, bg=bg, font=font)
            # 顶部/底部标记行背景跟随卡片（否则独立 Frame 露出系统灰条）
            top_row = self.card_top_rows[card]
            _, _, bottom = self.card_bottom_rows[card]
            top_row.config(bg=bg)
            bottom.config(bg=bg)
            self.card_data[card] = (folder_name, folder_path, target_dir)
            self._update_markers(card, folder_name)
            self._update_adj_markers(card, folder_name)

        # 隐藏多余的卡片 (如果学生数量变少了)
        if len(self.card_widgets) > needed_cards:
            self._need_arrange = True
            for i in range(needed_cards, len(self.card_widgets)):
                self.card_widgets[i].grid_forget()

        # 分割线复用机制
        prefixes = []
        for data in self.student_data:
            name = data[0]
            if "⚠️" in name: continue
            prefix = name.split('-')[0] if '-' in name else name
            if not prefixes or prefixes[-1] != prefix:
                prefixes.append(prefix)

        needed_seps = max(0, len(prefixes) - 1)
        if len(self.separators) < needed_seps:
            for _ in range(len(self.separators), needed_seps):
                sep = ttk.Separator(self.inner_frame, orient='horizontal')
                self.separators.append(sep)

        if self._need_arrange:
            self.arrange_cards()
            self._need_arrange = False
        else:
            # 内容变化但未触发重排：仍同步滚动范围。
            # 修复历史 bug：切讲次/切检索模式后若未走 arrange_cards，
            # scrollregion 停留在旧值，新布局中超出旧滚动范围的卡片
            # （及卡片顶部反馈标签）在 canvas 中不渲染，表现为"标签/卡片
            # 偶尔不显示"；切走再切回（触发重排刷新 scrollregion）后恢复。
            self._update_scrollregion()

    def _feedback_key(self, folder_name, lecture, sub_type):
        """反馈标记键（单点构造，防多处拼接漂移）：
        考试/打卡天 → '{学生}|{讲次}'；讲次 → '{学生}|{讲次}|{子类型}'"""
        if is_exam_or_checkin(lecture):
            return f"{folder_name}|{lecture}"
        return f"{folder_name}|{lecture}|{sub_type}"

    def _marker_status_color(self, directory):
        """目录状态色（标记常驻：无反馈标记时按文件状态显示）。
        灰=无文件/目录不存在；红=存在未批改；绿=全部已批改。"""
        st = self._dir_graded_status(directory)
        if st is None:
            return MARKER_STATUS_GRAY
        if st is True:
            return MARKER_STATUS_GREEN
        return MARKER_STATUS_RED

    def _update_markers(self, card, folder_name):
        """顶部反馈标记（常驻显色行，固定占位，标记出现/消失不改变卡片大小）：
        讲次模式三分类固定 1/3 等分——**始终可见**：无反馈按该分类目录状态显示
        （灰=无文件/红=有未批改/绿=已批改），有反馈显示标记对应颜色；
        考试/打卡天全宽单块（columnspan=3）。只更新颜色，不改变布局。
        讲次/分类优先从卡片目录解析（学生检索模式下每张卡片是不同讲次）。"""
        lecture, _ = self._card_lecture_sub(card)
        if lecture is None:
            lecture = self.current_lecture.get()
        current_lecture = lecture
        markers = self.card_markers.get(card)
        if not markers or card not in self.card_top_rows:
            return
        folder_path = self.card_data.get(card, ('', '', ''))[1]

        if is_exam_or_checkin(current_lecture):
            # 考试/打卡天：全宽单块，讲次分类块隐藏避免重叠。
            wide_key = '考试' if str(current_lecture).startswith('考试') else '打卡'
            key = self._feedback_key(folder_name, current_lecture, '')
            wide = markers[wide_key]
            wide_color = 'purple' if wide_key == '考试' else 'green'
            for cat in LECTURE_SUB_TYPES:
                markers[cat].grid_remove()
            if wide.winfo_manager() != 'grid':
                wide.grid(row=0, column=0, columnspan=max(1, len(LECTURE_SUB_TYPES)), sticky='nsew')
            active = key in self.feedback_set
            if active:
                wide.config(bg=wide_color, relief=tk.SOLID, borderwidth=1)
            else:
                # 常驻：无标记也显示目录状态色（灰/红/绿）
                directory = os.path.join(folder_path, current_lecture) if folder_path else ''
                wide.config(bg=self._marker_status_color(directory),
                            relief=tk.FLAT, borderwidth=0)
            return

        # ---------------- 讲次模式：全部配置分类等分并常驻显色 ----------------
        for key in ('考试', '打卡'):
            markers[key].grid_remove()
        colors = self.card_markers_colors
        fallback_colors = ('#f0c419', '#4f86c6', '#555555', '#8e6cbe', '#2a9d8f', '#d97706')
        for col, cat in enumerate(LECTURE_SUB_TYPES):
            w = markers[cat]
            if w.winfo_manager() != 'grid':
                w.grid(row=0, column=col, sticky='nsew')
            active = self._feedback_key(folder_name, current_lecture, cat) in self.feedback_set
            if active:
                w.config(bg=colors.get(cat, fallback_colors[col % len(fallback_colors)]),
                         relief=tk.SOLID, borderwidth=1)
            else:
                directory = os.path.join(folder_path, current_lecture, cat) if folder_path else ''
                w.config(bg=self._marker_status_color(directory),
                         relief=tk.FLAT, borderwidth=0)

    # ================================================================
    #  上一讲/下一讲 同类型状态标记（卡片底部）
    # ================================================================
    def _dir_graded_status(self, directory):
        """目录内图片批改状态（复用 mtime 缓存扫描，主线程调用安全）：
        None = 无图片/目录不存在；True = 全部已批改（含仅剩 -改 文件）；
        False = 存在未批改的原图（无对应 -改）。"""
        try:
            files = self._scan_dir_files(directory)
        except Exception:
            return None
        imgs = [f for f in files if os.path.splitext(f)[1].lower() in IMAGE_EXTENSIONS]
        if not imgs:
            return None
        mod_stems = set()
        for f in imgs:
            stem = os.path.splitext(f)[0]
            if stem.endswith('-改'):
                mod_stems.add(stem[:-2])
        for f in imgs:
            stem = os.path.splitext(f)[0]
            if not stem.endswith('-改') and stem not in mod_stems:
                return False
        return True

    def _adjacent_entry_status(self, folder_name, lecture, sub_type):
        """上一项/下一项（沿完整目录顺序 LECTURES：讲次/考试/打卡）目录的批改状态。
        返回 (prev_status, next_status)，status 同 _dir_graded_status；越界为 None。
        边界联动（随目录顺序配置自动一致）：
        - 最后一讲：右侧=考试信息（下一项即考试）、左侧=倒数第二讲；
        - 考试页：左侧=最后一讲（同子类型）、右侧=打卡第一天；
        - 打卡第一天页：左侧=考试信息。
        讲次项按 学生/讲次/子类型 检查；考试/打卡项按 学生/考试 或 学生/打卡第NN天。"""
        try:
            idx = LECTURES.index(lecture)
        except ValueError:
            return (None, None)
        use_sub = sub_type if sub_type in LECTURE_SUB_TYPES else LECTURE_SUB_TYPES[0]
        results = []
        for delta in (-1, 1):
            j = idx + delta
            if not (0 <= j < len(LECTURES)):
                results.append(None)   # 越界（第1项无上一项/末项无下一项）
                continue
            adj = LECTURES[j]
            if re.match(r'^第\d+讲$', adj):
                d = os.path.join(BASE_DIR, folder_name, adj, use_sub)
            else:
                d = os.path.join(BASE_DIR, folder_name, adj)   # 考试/打卡：无子类型
            results.append(self._dir_graded_status(d))
        return tuple(results)

    def _adjacent_feedback_color(self, folder_name, lecture, sub_type, delta):
        """相邻项（上一/下一讲）反馈标记颜色：相邻项有反馈标记时返回标记对应颜色，
        无反馈标记返回 None。讲次用 子类型 颜色（作业黄/课前小测蓝/错题再练黑），
        考试=紫、打卡=绿（与卡片顶部反馈标记配色一致）。"""
        try:
            idx = LECTURES.index(lecture)
        except ValueError:
            return None
        j = idx + delta
        if not (0 <= j < len(LECTURES)):
            return None
        adj = LECTURES[j]
        if re.match(r'^第\d+讲$', adj):
            use_sub = sub_type if sub_type in LECTURE_SUB_TYPES else LECTURE_SUB_TYPES[0]
            key = self._feedback_key(folder_name, adj, use_sub)
            return self.card_markers_colors.get(use_sub) if key in self.feedback_set else None
        # 考试/打卡：无子类型（反馈键 学生|讲次）
        key = self._feedback_key(folder_name, adj, '')
        if key not in self.feedback_set:
            return None
        return self.card_markers_colors.get('考试') if str(adj).startswith('考试') else \
               self.card_markers_colors.get('打卡')

    def _update_adj_markers(self, card, folder_name):
        """更新卡片底部上一项/下一项状态标记（沿完整目录顺序联动）：
        灰=无文件 绿=全部已批改 红=存在未批改；若相邻项有**反馈标记**则优先显示
        标记对应颜色（反馈优先，与卡片顶部一致）；讲次/考试/打卡页都常态化显示。
        讲次/分类优先从卡片目录解析（学生检索模式下每张卡片是不同讲次）。"""
        row = self.card_bottom_rows.get(card)
        if not row:
            return
        prev_m, next_m, bottom = row
        lecture, sub_type = self._card_lecture_sub(card)
        if lecture is None:
            lecture = self.current_lecture.get()
        if sub_type is None:
            sub_type = self.current_sub.get()
        show = lecture in LECTURES
        if show != self.card_bottom_visible.get(card, False):
            # 可见状态变化：pack/pack_forget 一次（防每次刷新重复抖动）
            self.card_bottom_visible[card] = show
            if show:
                bottom.pack(side=tk.BOTTOM, fill=tk.X)
            else:
                bottom.pack_forget()
            self._need_arrange = True
        if not show:
            return
        ps, ns = self._adjacent_entry_status(folder_name, lecture, sub_type)
        # 反馈标记优先：相邻项有反馈 → 显示标记颜色；否则按目录批改状态色
        pc = self._adjacent_feedback_color(folder_name, lecture, sub_type, -1)
        nc = self._adjacent_feedback_color(folder_name, lecture, sub_type, +1)
        prev_m.config(bg=pc if pc else (ADJ_MARKER_GRAY if ps is None else
                                        ADJ_MARKER_GREEN if ps else ADJ_MARKER_RED))
        next_m.config(bg=nc if nc else (ADJ_MARKER_GRAY if ns is None else
                                        ADJ_MARKER_GREEN if ns else ADJ_MARKER_RED))

    def _bind_card_events(self, card, label, folder_name, folder_path, target_dir):
        """绑定卡片交互事件（卡片创建时调用一次，不随每 5 秒刷新重复绑定）：
        点击/拖放时从 self.card_data 读取该卡片的**最新**目录数据，
        避免每轮 build_cards 对全部卡片 unbind/rebind + 重复注册拖放目标
        （tkinterdnd2 重复 register 属于无谓开销，且有重复处理器风险）。"""
        def _current():
            # card_data 在每轮 build_cards 中先更新；兜底用创建时的值
            return self.card_data.get(card, (folder_name, folder_path, target_dir))

        for widget in (card, label):
            widget.unbind('<Button-1>')
            widget.unbind('<Button-3>')
            if DND_AVAILABLE:
                try:
                    widget.drop_target_register(DND_FILES)
                    widget.dnd_bind('<<Drop>>', self._make_drop_handler(card))
                    widget.dnd_bind('<<DropEnter>>', lambda e, w=widget: w.config(relief=tk.SUNKEN))
                    widget.dnd_bind('<<DropLeave>>', lambda e, w=widget: w.config(relief=tk.RAISED))
                except Exception:
                    pass

        def on_click(e):
            fn, fp, td = _current()
            if self.delete_mode:
                # 删除模式：列出该文件夹图片，多选移入回收站
                self._delete_folder_images(fn, fp, td)
            elif self.copy_mode:
                # 复制批改模式：左键 = 汇总复制该学生 -改 图 + 情况说明
                self._copy_grading_summary(fn, fp, td)
            else:
                self._open_folder(fp, td)

        def on_right_click(e):
            self._toggle_feedback(card, _current()[0])

        for widget in (card, label):
            widget.bind('<Button-1>', on_click)
            widget.bind('<Button-3>', on_right_click)

    def _make_drop_handler(self, card):
        """返回拖放回调：把外部拖入的图片文件复制到该学生对应文件夹。
        卡片目录数据在事件发生时从 self.card_data 读取（最新值）。"""
        def on_drop(e):
            try:
                files = self.root.tk.splitlist(e.data)
            except Exception:
                files = e.data.split()
            # 仅保留图片：常规扩展名 + HEIC/HEIF（复制后由自动处理转 JPG）；
            # 无扩展名/未知扩展名（微信/QQ 拖出的临时文件）用 Pillow 探测内容
            imgs = [f for f in files if self._is_dnd_image(f)]
            if not imgs:
                self.show_danmaku("拖入的文件中没有可识别的图片（支持 jpg/png/bmp/gif/webp/tiff/heic）")
                return
            # 目标卡片：取当前卡片数据（卡片可能已被复用/重排）
            cur = self.card_data.get(card)
            if not cur:
                return
            folder_path, target_dir = cur[1], cur[2]
            dest = self._resolve_target_dir(folder_path, target_dir)
            if not os.path.isdir(dest):
                try:
                    os.makedirs(dest)
                except OSError:
                    self.show_danmaku(f"无法创建目标文件夹：{dest}")
                    return
            copied = 0
            for f in imgs:
                try:
                    # 重名时自动加 (1)/(2)…避免覆盖同名文件
                    stem, ext = os.path.splitext(os.path.basename(f))
                    if ext.lower() not in IMAGE_EXTENSIONS and ext.lower() not in ('.heic', '.heif'):
                        # 无扩展名/未知扩展名（微信/QQ 拖出的临时文件）：
                        # 按内容探测补扩展名，复制后自动处理（缩放/命名）才能识别它
                        try:
                            with Image.open(f) as im:
                                fmt = (im.format or '').lower()
                            # 映射表键带点（'.png'），im.format 返回不带点（'png'）
                            ext = {'.jpeg': '.jpg', '.jpg': '.jpg', '.png': '.png',
                                   '.webp': '.webp', '.gif': '.gif', '.bmp': '.bmp',
                                   '.tiff': '.tiff', '.heic': '.heic', '.heif': '.heif'}.get(
                                '.' + fmt, ext)
                        except Exception:
                            pass
                    target = os.path.join(dest, stem + ext)
                    n = 1
                    while os.path.exists(target):
                        target = os.path.join(dest, f"{stem} ({n}){ext}")
                        n += 1
                    shutil.copy2(f, target)
                    copied += 1
                except OSError as err:
                    print(f"复制失败 {f}: {err}")
            if copied:
                # 提示去向：复制后会立即自动规范化命名（原文件名可能变化），
                # 弹幕直接告知目标目录，用户不会"找不到"
                self.show_danmaku(
                    f"已复制 {copied} 张图片到 {os.path.relpath(dest, BASE_DIR)}"
                    "（将自动缩放 1080 + 规范命名）")
                # 立即触发该目录处理（与自动处理路径一致，幂等）
                self._process_folder_now(dest)
            else:
                self.show_danmaku("图片复制失败（权限/占用？）")
        return on_drop

    @staticmethod
    def _is_dnd_image(f):
        """拖放文件是否可识别为图片：常规扩展名 / HEIC/HEIF / Pillow 内容探测
        （微信/QQ 拖出的临时文件常无扩展名或带随机扩展名）。"""
        ext = os.path.splitext(f)[1].lower()
        if ext in IMAGE_EXTENSIONS:
            return True
        if ext in ('.heic', '.heif'):
            return True
        if os.path.isfile(f):
            try:
                with Image.open(f) as im:
                    im.load()   # 验证可完整解码
                return True
            except Exception:
                return False
        return False

    def _resolve_target_dir(self, folder_path, target_dir):
        """返回当前范围的精确目标目录；拖放端负责创建缺失目录。

        新增分类尚未补齐目录时也不能退回讲次根目录，否则图片会落错层级。
        """
        lecture = self.current_lecture.get()
        if is_exam_or_checkin(lecture):
            return os.path.join(folder_path, lecture)
        return os.path.join(folder_path, lecture, self.current_sub.get())

    def _process_folder_now(self, folder):
        """立即处理单目录（拖放后）：缩放/命名，与自动处理一致。
        在后台线程执行（大量图片时不冻结界面）；拿不到锁则交给 5 秒循环。"""
        def _job():
            try:
                if self._processing_lock.acquire(blocking=False):
                    try:
                        skip_optimized = set(self._load_storage_state().keys())
                        _namer.normalize_folder(folder, BASE_DIR, skip_optimized)
                    finally:
                        self._processing_lock.release()
                # 拿不到锁：跳过，5 秒自动处理循环会接管
            except Exception as e:
                print(f"拖放目录处理失败 {folder}: {e}")
        threading.Thread(target=_job, daemon=True).start()

    def toggle_copy_mode(self):
        """切换 复制批改 模式（按钮状态同步；与删除模式互斥）"""
        self.copy_mode = not self.copy_mode
        if self.copy_mode and self.delete_mode:
            self.delete_mode = False
            self.delete_btn.config(text="🗑 删除：关", bg='SystemButtonFace')
        self.copy_btn.config(text="📋 复制批改：开" if self.copy_mode else "📋 复制批改：关",
                             bg='#d1e7dd' if self.copy_mode else 'SystemButtonFace')

    def toggle_delete_mode(self):
        """切换 删除 模式（按钮状态同步；与复制批改互斥）。
        启用后左键点击学生卡片 = 列出该学生当前讲次/分类文件夹的图片，
        多选移入回收站（可恢复）——方便删除放错的图片（历史错图/刚拖放放入的错图）。"""
        self.delete_mode = not self.delete_mode
        if self.delete_mode and self.copy_mode:
            self.copy_mode = False
            self.copy_btn.config(text="📋 复制批改：关", bg='SystemButtonFace')
        self.delete_btn.config(text="🗑 删除：开" if self.delete_mode else "🗑 删除：关",
                               bg='#f8d7da' if self.delete_mode else 'SystemButtonFace')

    # ================================================================
    #  删除放错的图片：列出该学生当前讲次/分类文件夹的图片，
    #  多选移入回收站（move_to_recycle_bin 双保险，可恢复）
    # ================================================================
    def _delete_folder_images(self, folder_name, folder_path, target_dir):
        """删除模式：打开 删除图片 对话框（列表按修改时间倒序=最新在前，
        便于删除"刚拖放放入/之前放错"的图）。删除走回收站（可恢复）。"""
        src = self._resolve_target_dir(folder_path, target_dir)
        if not os.path.isdir(src):
            self.show_danmaku("文件夹不存在")
            return
        try:
            names = [n for n in os.listdir(src)
                     if os.path.isfile(os.path.join(src, n))]
        except OSError:
            self.show_danmaku("无法读取文件夹")
            return
        # 图片扩展名 + 无扩展名文件（微信/QQ 拖出的临时文件可能无扩展名）
        def _is_image(n):
            return os.path.splitext(n)[1].lower() in IMAGE_EXTENSIONS \
                or '.' not in os.path.basename(n)
        imgs = [n for n in names if _is_image(n)]
        if not imgs:
            self.show_danmaku(f"该文件夹没有图片：{os.path.relpath(src, BASE_DIR)}")
            return
        # 按修改时间倒序（新放入的排前面，方便删"刚放错"的）
        imgs.sort(key=lambda n: os.path.getmtime(os.path.join(src, n)), reverse=True)

        win = tk.Toplevel(self.root)
        win.title(f"删除图片 - {folder_name} {os.path.relpath(src, BASE_DIR)}")
        win.geometry("460x400")
        win.transient(self.root)
        try:
            win.grab_set()
        except Exception:
            pass

        head = tk.Frame(win); head.pack(fill=tk.X, padx=10, pady=6)
        tk.Label(head, text="勾选要删除的图片（最新在前；删除走回收站，可恢复）",
                 fg='#555555').pack(side=tk.LEFT)
        tk.Button(head, text="全选", width=5, command=lambda: lb.select_set(0, tk.END)).pack(side=tk.RIGHT, padx=2)
        tk.Button(head, text="全不选", width=5, command=lambda: lb.selection_clear(0, tk.END)).pack(side=tk.RIGHT)

        body = tk.Frame(win); body.pack(fill=tk.BOTH, expand=True, padx=10)
        lb = tk.Listbox(body, selectmode=tk.EXTENDED, exportselection=False)
        sb = tk.Scrollbar(body, orient=tk.VERTICAL, command=lb.yview)
        lb.config(yscrollcommand=sb.set)
        lb.pack(side=tk.LEFT, fill=tk.BOTH, expand=True); sb.pack(side=tk.RIGHT, fill=tk.Y)
        for n in imgs:
            lb.insert(tk.END, n)

        status = tk.StringVar(value=f"共 {len(imgs)} 张图片")
        tk.Label(win, textvariable=status, fg='#888888').pack(fill=tk.X, padx=10)

        def _do_delete():
            sel = [lb.get(i) for i in lb.curselection()]
            if not sel:
                status.set("未选择任何图片")
                return
            if not tk.messagebox.askyesno("确认删除",
                                          f"将把 {len(sel)} 张图片移入回收站（可恢复），确认？",
                                          parent=win):
                return
            recycled = moved = failed = 0
            for n in sel:
                r = move_to_recycle_bin(os.path.join(src, n))
                if r == 'recycled':
                    recycled += 1
                elif r == 'moved':
                    moved += 1
                else:
                    failed += 1
            win.destroy()
            self.show_danmaku(f"已删除 {recycled + moved} 张（回收站可恢复）"
                              + (f"，失败 {failed}" if failed else ""))
            self.refresh()   # 图片变化 → 卡片统计刷新

        foot = tk.Frame(win); foot.pack(fill=tk.X, padx=10, pady=8)
        tk.Button(foot, text="删除选中（回收站）", command=_do_delete, bg='#f8d7da',
                  width=18).pack(side=tk.RIGHT)
        tk.Button(foot, text="取消", command=win.destroy, width=8).pack(side=tk.RIGHT, padx=6)

    # ================================================================
    #  复制批改汇总：把该学生当前讲次/分类的 -改 图片复制到「登记/汇报/」，
    #  同时生成"这是第X讲的X情况"说明文本（txt + 剪贴板），便于向家长汇报
    # ================================================================

    @staticmethod
    def summary_text(lecture, sub_type, cfg=None, identity=''):
        """生成情况说明文本（按复制内容配置决定包含哪些片段）：
        cfg = {'lecture':bool, 'sub':bool, 'capsule':bool}（image 不影响文本）；
        None 或缺失键按全选处理。
        考试 → "这是考试情况"；讲次 → "这是第02讲的作业，《胶囊》链接（视频胶囊）"
        （胶囊来自 视频胶囊.txt，无则省略）；打卡 → "这是第02天的打卡"。"""
        if cfg is None:
            cfg = {}
        on = lambda k: _as_bool(cfg.get(k, True), True)
        if str(lecture).startswith('考试'):
            name = '考试' if on('lecture') else ''
            base = f'这是{name}情况' if name else '这是情况'
            return f'{identity}\n{base}' if identity else base
        capsule = _get_capsule_text(lecture, sub_type)
        if str(lecture).startswith('打卡'):
            day = lecture[2:]   # '打卡第02天' → '第02天'
            base = f'这是{day}的打卡' if on('lecture') else '这是打卡'
        else:
            parts = []
            if on('lecture'):
                parts.append(lecture)
            if on('sub'):
                parts.append(sub_type or '')
            if len(parts) > 1:
                base = '这是' + '的'.join(parts)
            elif parts:
                base = '这是' + parts[0]
            else:
                base = '这是'
        if on('capsule') and capsule:
            base += f'，{capsule}（视频胶囊）'
        return f'{identity}\n{base}' if identity else base

    @staticmethod
    def collect_modified_files(folder):
        """收集文件夹内所有 `-改` 图片的完整路径（含 无-改 的原图？不：仅 -改，批改结果）
        按文件名排序返回。"""
        try:
            files = [os.path.join(folder, f) for f in os.listdir(folder)
                     if os.path.splitext(f)[1].lower() in IMAGE_EXTENSIONS
                     and os.path.splitext(f)[0].endswith('-改')]
        except OSError:
            return []
        return sorted(files)

    def _set_clipboard_text(self, text):
        """剪贴板写纯文本（失败静默，不影响主流程）"""
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append(text)
        except Exception:
            pass

    def _copy_grading_summary(self, folder_name, folder_path, target_dir):
        """复制批改汇总：-改 图 → 登记/汇报/{学生}/{讲次-分类}/，生成 情况说明.txt。
        剪贴板两种模式（**连续点击同一卡片交替**，微信/QQ 一次粘贴只消费一种格式）：
        - 图片模式（默认）：图片文件列表 + 说明文本 —— 微信/QQ 粘贴发图
        - 文字模式：仅说明文本 —— 微信/QQ 粘贴即文字消息
        流程：先点卡片发图，再点同一卡片切文字，正好"先图片在文本"。"""
        try:
            src = self._resolve_target_dir(folder_path, target_dir)
            mods = self.collect_modified_files(src)
            if not mods:
                self.show_danmaku(f"该文件夹没有「-改」批改图片：{os.path.relpath(src, BASE_DIR)}")
                return
            # 讲次/分类从卡片目录解析（内容与学生检索模式统一；考试/打卡无分类）
            rel = os.path.relpath(src, folder_path)
            parts = rel.split(os.sep)
            if len(parts) >= 2:
                lecture, sub = parts[0], parts[1]
            else:
                lecture, sub = rel, None
            # 复制内容配置：讲次/考试/打卡 分开记忆（互不影响），默认全选
            scene = _copy_scene(lecture)
            cfg = self.copy_content.get(scene, DEFAULT_COPY_CONTENT[scene])
            text_template = self.copy_content.get('text_template', DEFAULT_COPY_TEMPLATE)
            save_report_text = _as_bool(self.copy_content.get('save_report_text', False))
            # 学生文件夹格式：班级-两位学号-姓名。模板字段可在设置中心修改。
            bits = folder_name.split('-', 2)
            class_name, seq, name = (bits + ['', '', ''])[:3]
            capsule = _get_capsule_text(lecture, sub or '') if _as_bool(cfg.get('capsule', True), True) else ''
            capsule_value = f'，{capsule}（视频胶囊）' if capsule else ''
            values = {
                'class': class_name, 'class_name': class_name, 'seq': seq, 'name': name,
                'lecture': lecture if _as_bool(cfg.get('lecture', True), True) else '',
                'sub': sub or '' if _as_bool(cfg.get('sub', True), True) else '',
                'capsule': capsule_value,
            }
            try:
                text = text_template.format(**values).strip()
            except (KeyError, ValueError):
                text = DEFAULT_COPY_TEMPLATE.format(**values).strip()
            label = lecture if sub is None else f"{lecture}-{sub}"
            copied = len(mods)
            # 不复制图片到登记/汇报：剪贴板直接引用原始 -改 图片路径，零中间图片副本。
            copied_targets = list(mods)
            if save_report_text:
                report_root = os.path.join(GRADING_DIR, '汇报')
                dest = os.path.join(report_root, folder_name, label)
                os.makedirs(dest, exist_ok=True)
                txt_path = os.path.join(dest, '情况说明.txt')
                n = 1
                while os.path.exists(txt_path):
                    if n >= 100:
                        break
                    txt_path = os.path.join(dest, f'情况说明 ({n}).txt')
                    n += 1
                with open(txt_path, 'w', encoding='utf-8') as f:
                    f.write(text + '\n')
            # ---- 剪贴板：按配置（图片勾选则保留 图片/文字 交替模式）----
            want_image = bool(cfg.get('image', True))
            clip_key = (folder_name, label)
            # 交替仅在"设置勾选图片"时生效；未勾选则始终纯文字
            text_only = (self._last_clip == clip_key) and want_image
            self._last_clip = None if text_only else (clip_key if want_image else None)
            if text_only:
                # 文字模式：仅纯文本——微信/QQ 粘贴即文字消息
                self._set_clipboard_text(text)
                self.show_danmaku(
                    "剪贴板已切换为纯文字，微信/QQ 粘贴即文字消息（再次点击本卡片切回图片）")
            elif want_image:
                # 图片模式：QQ 图文风格剪贴板——
                # QQ_Unicode_RichEdit_Format（QQ 图文同贴核心）+ HTML Format
                # + 纯文本 + 图片文件列表（微信发图兜底）
                if copied_targets:
                    ok = _copy_qq_style_clipboard(text, copied_targets)
                    if not ok:
                        # 剪贴板被占用/系统不支持：不要谎报"复制成功"
                        # （修复历史 bug：原实现忽略返回值，占用时仍弹成功提示）
                        self.show_danmaku("复制失败：剪贴板被占用，请稍后重试")
                        return
                else:
                    self._set_clipboard_text(text)
                self.show_danmaku(
                    f"已复制 {copied} 张批改图（QQ 图文同现、微信发图）；"
                    "再次点击本卡片切换纯文字")
            else:
                # 设置未勾选「图片」：始终纯文字，不创建任何汇报图片副本。
                self._set_clipboard_text(text)
                self.show_danmaku("已复制文字（设置未勾选「图片」，不携带图片）")
        except Exception as e:
            self.show_danmaku(f"复制批改失败：{e}")

    def _open_folder(self, folder_path, target_dir):
        # 目标目录回退逻辑与 _resolve_target_dir 一致（考试/打卡/讲次逐级回退）
        path_to_open = self._resolve_target_dir(folder_path, target_dir)
        if os.path.isdir(path_to_open):
            if not open_in_file_manager(path_to_open):
                self.show_danmaku(f"无法打开文件夹：{path_to_open}")
        else:
            self.show_danmaku("文件夹不存在")

    def _toggle_feedback(self, card, folder_name):
        """直接切换反馈状态，不再弹窗，直接重绘色块。
        讲次/分类优先从卡片目录解析（学生检索模式下每张卡片是不同讲次）。"""
        lecture, sub = self._card_lecture_sub(card)
        if lecture is None:
            lecture = self.current_lecture.get()
        if sub is None:
            sub = self.current_sub.get()
        fb_key = self._feedback_key(folder_name, lecture, sub)

        if fb_key in self.feedback_set:
            self.feedback_set.remove(fb_key)
        else:
            self.feedback_set.add(fb_key)

        self._update_markers(card, folder_name)
        self.save_settings()

    def arrange_cards(self):
        if not self.card_widgets:
            return

        # 防御：列数 Spinbox 允许手输，若残留非数字（如打字未回车触发 resize
        # 重排），IntVar.get() 抛 TclError → 回退默认 3 列（否则重排路径持续失败）
        try:
            cols = self.columns.get()
        except (ValueError, TypeError, tk.TclError):
            cols = 3
            try:
                self.columns.set(3)
            except Exception:
                pass
        if cols < 1:
            cols = 1
            self.columns.set(1)
        elif cols > 10:
            cols = 10
            self.columns.set(10)

        self.inner_frame.update_idletasks()

        for card in self.card_widgets:
            card.grid_forget()
        for sep in self.separators:
            sep.grid_forget()

        current_row = 0
        current_col = 0
        prev_prefix = None
        sep_idx = 0

        for idx, card in enumerate(self.card_widgets):
            if idx >= len(self.student_data):
                break

            folder_name = self.card_data[card][0]
            prefix = folder_name.split('-')[0] if '-' in folder_name else folder_name

            if prev_prefix is not None and prefix != prev_prefix:
                if current_col > 0:
                    current_row += 1
                    current_col = 0

                if sep_idx < len(self.separators):
                    sep = self.separators[sep_idx]
                    sep.grid(row=current_row, column=0, columnspan=cols, sticky='ew', padx=8, pady=8)
                    sep_idx += 1

                current_row += 1
                current_col = 0

            elif current_col >= cols:
                current_row += 1
                current_col = 0

            card.grid(row=current_row, column=current_col, padx=8, pady=8, sticky='nsew')
            current_col += 1
            prev_prefix = prefix

        for c in range(int(self.inner_frame.grid_size()[0])):
            self.inner_frame.grid_columnconfigure(c, weight=0)

        for c in range(cols):
            self.inner_frame.grid_columnconfigure(c, weight=1)

        self._update_scrollregion()

    # ================================================================
    #  刷新与外部脚本调用
    # ================================================================

    def run_homework_namer(self, force=False):
        """
        运行 作业命名器.py（图片规范化：缩放 1080、标准命名）。
        force=False 时受节流限制（避免高频自动调用）；
        force=True（显式按钮）时总是运行。
        """
        now = time.time()
        if not force and now - self._last_namer_run < self._namer_throttle_sec:
            return
        self._last_namer_run = now
        script_path = os.path.join(PROGRAM_DIR, "作业命名器.py")
        if os.path.exists(script_path):
            try:
                subprocess.run([sys.executable, script_path], cwd=BASE_DIR, check=False, timeout=120)
            except subprocess.TimeoutExpired:
                print("运行 作业命名器.py 超时（超过120秒）")
            except Exception as e:
                print(f"运行 作业命名器.py 时出错: {e}")
        else:
            print("未找到 作业命名器.py，跳过运行。")

    def refresh(self):
        if self.is_refreshing:
            # 正在刷新：不忽略，标记等待完成后立即补刷（连续切换分类不丢）
            self._pending_refresh = True
            return

        if self.after_id:
            self.root.after_cancel(self.after_id)
            self.after_id = None

        self.is_refreshing = True
        # 主线程快照 Tk 变量，后台线程只读参数（Tkinter 非线程安全）
        snapshot = (self.current_lecture.get(), self.current_sub.get(),
                    frozenset(self.hidden_classes))
        threading.Thread(target=self._async_refresh, args=(snapshot,), daemon=True).start()

    def _async_refresh(self, snapshot):
        # 后台线程：先处理新图片（当前讲次，仅变化的目录）→ 再统计 → 再检查命名
        lecture, sub_type, hidden = snapshot
        try:
            # 每个刷新周期只扫一次学生列表，三处复用（消除每 5 秒 3 次根目录 scandir）
            students = self._scan_student_folders(hidden)
            # 写文件操作与存储优化互斥（防双线程同时写同一图片导致损坏）；
            # 拿不到锁说明存储优化/其他处理正在运行：跳过本轮处理，统计照常
            if self._processing_lock.acquire(blocking=False):
                try:
                    self._auto_process_images(lecture, hidden, students)
                    self._auto_check_naming(lecture, hidden, students)
                finally:
                    self._processing_lock.release()
            # 学生模式：不覆盖学生卡片数据（内容统计与自动处理无关；
            # 定时刷新保持学生卡片，否则每 5 秒内容数据会把学生卡片冲掉）
            if self.search_mode != 'student':
                self.load_data(lecture, sub_type, hidden, students)
        except Exception as e:
            print(f"后台刷新出错: {e}")
        finally:
            if not self._closing:   # 窗口已关闭：不再排队回调
                try:
                    self.root.after(0, self._on_refresh_done)
                except Exception:
                    pass   # 窗口已销毁，忽略

    def _auto_process_images(self, lecture=None, hidden=None, students=None):
        """
        每 5 秒自动处理当前讲次（所有分类）的新图片：
        HEIC→JPG、窄边缩放到 1080、规范命名。
        限频条件：仅处理"目录内容有变化"的文件夹（mtime 增量缓存），
        无新图片时零开销；处理本身幂等（已缩放的不再缩放、已规范的不改名）。
        """
        if lecture is None:
            lecture = self.current_lecture.get()
        if hidden is None:
            hidden = self.hidden_classes
        folders = self._current_lecture_folders(lecture, hidden, students)
        # 已被存储优化处理（缩略/降质）的文件：自动缩放跳过，
        # 避免把缩略图放大回 1080（upscale 模糊 + 体积膨胀，破坏优化效果）
        try:
            skip_optimized = set(self._load_storage_state().keys())
        except Exception:
            skip_optimized = set()
        for folder in folders:
            try:
                mtime = os.stat(folder).st_mtime_ns
            except OSError:
                continue
            rec = self._img_process_cache.get(folder)
            # 目录 mtime 相同但记录已超过 15 秒：仍重扫一次（仅该 mtime 首次超时）。
            # Windows/NTFS 下目录 mtime 对"连续快速写入"可能不更新或延迟更新
            # （实测可永久漏检），纯 mtime 判断会漏掉同一批快速放入的文件；
            # 处理本身幂等（已缩放/已规范的不再处理），重扫代价极小。
            # 修复历史 bug：原实现每次重扫后刷新时间戳 → mtime 不变时每≥15秒
            # **永久**全量重处理一遍（PIL 逐张打开+命名全检），与"零开销"相悖。
            if rec is not None and rec[0] == mtime:
                forced = rec[2] if len(rec) >= 3 else None
                if time.time() - rec[1] < 15 or forced == mtime:
                    continue   # 15 秒内 或 该 mtime 已强制重扫过：跳过
                try:
                    _namer.normalize_folder(folder, BASE_DIR, skip_optimized)
                except Exception as e:
                    print(f"自动处理图片失败 {folder}: {e}")
                # 记录已强制重扫的 mtime（同一 mtime 只强制一次）
                self._img_process_cache[folder] = (mtime, time.time(), mtime)
                continue
            try:
                _namer.normalize_folder(folder, BASE_DIR, skip_optimized)
            except Exception as e:
                print(f"自动处理图片失败 {folder}: {e}")
            # 记录处理后的 mtime + 时间戳（防重复处理 + 防 NTFS 漏检）
            try:
                self._img_process_cache[folder] = (os.stat(folder).st_mtime_ns, time.time(), None)
            except OSError:
                pass

    def _current_lecture_folders(self, lecture=None, hidden=None, students=None):
        """当前讲次（所有分类）的目标目录：学生/第X讲/{作业,课前小测,错题再练}；考试/打卡直接目录。
        students: 预扫描的学生列表 [(名称, 路径), ...]，由调用方一次算好复用（防每 5 秒重复 scandir）"""
        if lecture is None:
            lecture = self.current_lecture.get()
        if hidden is None:
            hidden = self.hidden_classes
        if students is None:
            students = self._scan_student_folders(hidden)
        folders = []
        for _, path in students:
            if is_exam_or_checkin(lecture):
                folders.append(os.path.join(path, lecture))
            else:
                for sub in LECTURE_SUB_TYPES:
                    folders.append(os.path.join(path, lecture, sub))
        return folders

    def _auto_check_naming(self, lecture=None, hidden=None, students=None):
        """
        每5秒自动检查当前讲次（所有分类）的命名，发现不规范自动重命名。
        减少人工确认：重命名直接执行；删除类操作仍必须确认（本流程不含删除）。
        """
        if lecture is None:
            lecture = self.current_lecture.get()
        if hidden is None:
            hidden = self.hidden_classes
        folders = self._current_lecture_folders(lecture, hidden, students)
        if not folders:
            self._bad_names = []
            return
        bad = check_filename_format(BASE_DIR, folders=folders)
        if bad:
            try:
                # 按目录去重：同一目录多个坏文件只处理一次（smart_rename_folder 是目录级）
                for folder in {os.path.dirname(p) for p, _ in bad}:
                    smart_rename_folder(folder, BASE_DIR)
            except Exception as e:
                print(f"自动重命名出错: {e}")
            # 修改后复查
            self._bad_names = check_filename_format(BASE_DIR, folders=folders)
        else:
            self._bad_names = []

    def run_namer_now(self):
        """显式运行命名器（规范化图片命名/缩放），完成后刷新统计"""
        if self.is_refreshing:
            return
        self.is_refreshing = True
        # 主线程快照 Tk 变量（后台线程只读参数）
        snapshot = (self.current_lecture.get(), self.current_sub.get(),
                    frozenset(self.hidden_classes))
        threading.Thread(target=self._async_namer, args=(snapshot,), daemon=True).start()

    def _async_namer(self, snapshot):
        """显式运行命名器（子进程全量规范化）。
        注意：父进程**不得**先持 PROCESS_LOCK 再启动子进程——同一把文件锁
        父子进程会自锁（子进程必然拿不到锁退出，按钮失效）。
        互斥改由子进程自己拿锁保证：子进程运行期间，本进程的自动处理/
        存储优化会因拿不到锁自动跳过；本进程持锁期间，子进程拿不到锁
        会提示退出（与手动运行命令行一致，安全）。"""
        try:
            if self._closing:
                return
            self.run_homework_namer(force=True)
            if self._closing:
                return
            self.load_data(*snapshot)
        except Exception as e:
            print(f"命名器运行出错: {e}")
        finally:
            if not self._closing:   # 窗口已关闭：不再排队回调
                try:
                    self.root.after(0, self._on_refresh_done)
                except Exception:
                    pass   # 窗口已销毁，忽略

    def _on_refresh_done(self):
        try:
            if self.search_mode == 'student':
                # 学生模式：定时刷新后重载学生卡片（数据保持新鲜）
                self._load_student_cards()
            else:
                self.build_cards()
            self.update_title()
        finally:
            self.is_refreshing = False
            self.schedule_periodic_refresh()
            if self._pending_refresh:
                # 刷新期间有新的切换请求：立即补刷
                self._pending_refresh = False
                self.refresh()
        self._publish_search_state()   # 每次刷新后发布检索状态（修改器读取）

    # ================================================================
    #  监视器 ↔ 修改器 检索状态发布（双向同步）
    #  每次刷新后把 当前检索范围 + 范围内图片文件列表 写入共享 JSON，
    #  修改器读取该文件替代自行检索（"修改器不再承担检索"）。
    # ================================================================
    def _current_scope(self):
        """当前检索条件（与 open_modifier 一致；修改器据此判断是否采用共享列表）"""
        if self.search_mode == 'student':
            return {'search_mode': 'student', 'name': self.student_name,
                    'category': self.current_sub.get()}
        lec = self.current_lecture.get()
        cat = self.current_sub.get() if not is_exam_or_checkin(lec) else '全部'
        classes = ','.join(y for y, v, cb in self.class_buttons if v.get()) or '全部'
        return {'search_mode': 'content', 'lecture': lec, 'category': cat,
                'classes': classes}

    def _publish_search_state(self):
        """把当前检索范围 + 范围内图片文件列表写入 MONITOR_SEARCH_FILE。
        files 直接来自本次统计的 target_dir（内容模式=各学生该讲次/分类目录；
        学生模式=选定学生各讲次×类别），与卡片显示一致，无需重复扫描。"""
        try:
            scope = self._current_scope()
            files = []
            for data in self.student_data:
                target = data[5] if len(data) > 5 else ''
                if target and os.path.isdir(target):
                    try:
                        for f in self._scan_dir_files(target):
                            if os.path.splitext(f)[1].lower() in IMAGE_EXTENSIONS:
                                # v3.4.2 起存相对 BASE_DIR 路径（转移/换目录后可恢复，
                                # 读取端拼回绝对路径），不再写死盘符绝对路径
                                files.append(os.path.relpath(os.path.join(target, f), BASE_DIR))
                    except Exception:
                        continue
            state = {'updated': time.time(), 'scope': scope, 'files': files}
            atomic_write_json(MONITOR_SEARCH_FILE, state, ensure_ascii=False, indent=1)
        except Exception as e:
            print(f"发布检索状态失败: {e}")

    def _modifier_changed_mtime(self):
        """修改器变更标记文件的 mtime（不存在返回 0）"""
        try:
            return os.path.getmtime(MODIFIER_CHANGED_FILE)
        except OSError:
            return 0.0

    def _watch_modifier_changes(self):
        """周期检查修改器变更标记：比上次记录新 → 立即刷新（同步修改器改动的文件）。
        返回是否触发了刷新（供 periodic_refresh 跳过当轮重复刷新）。"""
        if self._closing:
            return False
        t = self._modifier_changed_mtime()
        if t and t > getattr(self, '_last_modifier_change_seen', 0.0):
            self._last_modifier_change_seen = t
            if not self.is_refreshing:
                self.show_danmaku("检测到修改器已变动文件，正在刷新")
                self.refresh()
                return True
        return False

    def schedule_periodic_refresh(self):
        if self._closing:
            return   # 关闭中不再排定时器
        self.after_id = self.root.after(self._auto_interval_ms, self.periodic_refresh)

    def periodic_refresh(self):
        # 修改器变动文件 → 立即刷新（优先于定时轮询，避免等待下一个周期）
        if not self._watch_modifier_changes():
            self.refresh()
        # 存储优化进行中：标题栏实时进度
        if self._storage_running and not self._embedded:
            try:
                self.root.title(_TITLE_PREFIX + f"存储优化中…(已处理 {self._storage_progress} 张)")
            except Exception:
                pass
        # 存储优化：低频自动检查（默认 30 分钟一次），完成后弹幕提示并刷新统计
        if self._storage_done:
            self._storage_done = False
            result = self._storage_result
            self._storage_result = None
            if result and result[0] != 'err':
                processed, freed = result
                mb = freed / 1048576
                self.show_status_danmaku(f"存储优化完成：处理 {processed} 张，释放 {mb:.1f} MB")
                self.refresh()   # 卡片统计随文件变化刷新
            elif result and result[0] == 'err':
                self.show_status_danmaku(f"存储优化失败: {result[1]}")
        if self.storage_cfg.get('enabled') and not self._storage_running:
            # 30 分钟节流在 _run_storage_optimize 内部判断（勿在此预置 _last_storage_check，
            # 否则节流检查会立刻拦截，自动优化永不触发——历史 bug）
            self._run_storage_optimize()

    def show_status_danmaku(self, text):
        """状态弹幕：仅在标题/状态区显示（存储优化等低频状态提示）"""
        try:
            if not self._embedded:   # 嵌入模式不覆盖主窗口标题栏
                self.root.title(_TITLE_PREFIX + text)
            self.root.after(5000, self.update_title)
        except Exception:
            pass

    # ================================================================
    #  弹幕提示（与修改器一致：非阻塞、3 秒自动消失，替代全部弹窗）
    # ================================================================
    def show_danmaku(self, text):
        """顶部弹幕提示：3 秒自动消失，最多同时 3 条。
        替代 messagebox 弹窗（用户操作反馈不打断批改流程）。"""
        try:
            text = str(text)
            if len(text) > 80:
                text = text[:77] + '…'
            # 清理已销毁的弹幕（窗口关闭等场景）
            alive = []
            for d in getattr(self, '_danmakus', []):
                try:
                    if d.winfo_exists():
                        alive.append(d)
                except Exception:
                    pass
            self._danmakus = alive
            while len(self._danmakus) >= 3:
                old = self._danmakus.pop()
                try:
                    if old.winfo_exists():
                        old.destroy()
                except Exception:
                    pass
            # 已有弹幕下移一行，新弹幕置顶
            for i in range(len(self._danmakus) - 1, -1, -1):
                lbl = self._danmakus[i]
                try:
                    if lbl.winfo_exists():
                        lbl.place_configure(y=10 + (i + 1) * 40)
                except Exception:
                    pass
            lbl = tk.Label(self.container, text=text, bg='#333333', fg='white',
                           font=('微软雅黑', 10), bd=0, highlightthickness=0)
            lbl.place(relx=0.5, y=10, anchor='n')
            self._danmakus.insert(0, lbl)

            def _remove(l=lbl):
                try:
                    if l.winfo_exists():
                        l.destroy()
                except Exception:
                    pass
                if l in self._danmakus:
                    self._danmakus.remove(l)

            self.root.after(self._danmaku_ms, _remove)
        except Exception:
            pass   # 弹幕失败不影响功能

    # ================================================================
    #  存储优化：按图片年龄分级压缩 / 降质 / 缩略（微信式）
    # ================================================================

    def _load_storage_state(self):
        """处理状态记录：path -> 已处理级别(1=压缩 2=降质 3=缩略)，防重复处理。
        统一走 common.load_storage_opt_state：自动迁移旧机器绝对路径
        （转移电脑后旧盘符路径失效，已优化图片仍可正确跳过）。"""
        return load_storage_opt_state()

    def _save_storage_state(self, state):
        """保存处理状态：统一存相对 BASE_DIR 路径，换机器/换盘符后可迁移。"""
        try:
            save_storage_opt_state(state)
        except Exception as e:
            print(f"存储优化状态保存失败: {e}")

    def open_settings_center(self):
        """打开统一设置中心（修改器+监控器全部设置；与修改器共用同一窗口）。
        嵌入模式：路由到主窗口「设置」页（单窗口原则，不另弹 Toplevel）。"""
        import 设置中心
        try:
            if self._embedded:
                on_settings = getattr(self.container, '_dsh_on_open_settings', None)
                if callable(on_settings):
                    on_settings()
                    return
            设置中心.open_settings_window(
                self.root, 'monitor',
                apply_monitor=self._apply_settings_from_file,
                on_optimize=lambda cfg=None: self._optimize_from_settings(cfg))
        except Exception as e:
            self.show_danmaku(f"打开设置中心失败：{e}")

    def _optimize_from_settings(self, storage_cfg=None):
        if storage_cfg is not None:
            self.storage_cfg = dict(storage_cfg)
        self._run_storage_optimize(force=True)

    def _apply_settings_from_file(self):
        """设置中心保存后：重读设置并即时应用（字体/列数/存储优化/弹幕时长/自动间隔/复制内容）"""
        if self._closing:
            return
        saved = self.load_settings()
        try:
            self.font_size.set(max(8, min(24, int(saved.get('font_size', 12)))))
        except (TypeError, ValueError):
            self.font_size.set(12)
        try:
            self.columns.set(max(1, min(10, int(saved.get('columns', 3)))))
        except (TypeError, ValueError):
            self.columns.set(3)
        self.storage_cfg = self.load_storage_cfg()
        try:
            self._danmaku_ms = max(1000, min(10000, int(saved.get('danmaku_ms', 3000))))
        except (TypeError, ValueError):
            self._danmaku_ms = 3000
        try:
            self._auto_interval_ms = max(1000, min(60000, int(saved.get('auto_interval_sec', 5)) * 1000))
        except (TypeError, ValueError):
            self._auto_interval_ms = 5000
        # 复制批改内容配置：设置中心可改，保存后立即重载生效（否则显示"已保存"但实际不生效）
        self.copy_content = _merge_copy_content(saved.get('copy_content'))
        # 目录结构也可能刚在设置中心变更：独立窗口模式下原页面仍存活，需重建筛选控件。
        try:
            self.lecture_combo.configure(values=LECTURES)
            if self.current_lecture.get() not in LECTURES:
                self.current_lecture.set(LECTURES[0])
            for button in self.cat_buttons:
                button.destroy()
            self.cat_buttons.clear()
            for cat in LECTURE_SUB_TYPES:
                rb = tk.Radiobutton(self.cat_group, text=cat, variable=self.current_sub,
                                    value=cat, command=self.on_control_changed)
                rb.pack(side=tk.LEFT, padx=1)
                self.cat_buttons.append(rb)
            if self.current_sub.get() not in LECTURE_SUB_TYPES:
                self.current_sub.set(LECTURE_SUB_TYPES[0])
            self.card_markers_colors = {'考试': 'purple', '打卡': 'green'}
            for i, cat in enumerate(LECTURE_SUB_TYPES):
                self.card_markers_colors[cat] = ('yellow', 'blue', 'black', '#d97706', '#2a9d8f')[i % 5]
            # 卡片顶部标记块数量随分类配置变化，旧卡片不能复用。
            for card in list(self.card_widgets):
                card.destroy()
            self.card_widgets.clear(); self.card_labels.clear(); self.card_markers.clear()
            self.card_top_rows.clear(); self.card_bottom_rows.clear(); self.card_bottom_visible.clear()
        except Exception:
            pass
        self._last_storage_check = 0   # 存储优化参数变更：允许下次自动检查
        self._need_arrange = True
        try:
            self.build_cards()
        except Exception:
            pass
        self.refresh()
        self.show_danmaku("设置已保存并应用")

    def open_storage_settings(self):
        """存储优化设置弹窗：自定义天数（0=关闭该级）、缩略图尺寸、立即优化"""
        win = tk.Toplevel(self.root)
        win.title(f"存储优化设置 v{PROJECT_VERSION}")
        win.geometry("460x340")
        win.transient(self.root); win.grab_set()
        cfg = self.storage_cfg

        tk.Label(win, text="按图片存放天数自动分级优化，释放磁盘空间（微信式缩略）。",
                 justify=tk.LEFT, fg='#555555').pack(anchor=tk.W, padx=12, pady=(12, 2))
        tk.Label(win, text="⚠ 处理不可逆：降质/缩略后原画质无法恢复；-改 批改文件同样参与压缩。",
                 justify=tk.LEFT, fg='#cc4444').pack(anchor=tk.W, padx=12, pady=(0, 6))

        en = tk.BooleanVar(value=cfg['enabled'])
        tk.Checkbutton(win, text="启用自动存储优化（后台每 30 分钟检查）", variable=en).pack(anchor=tk.W, padx=12)

        frm = tk.Frame(win); frm.pack(fill=tk.X, padx=12, pady=8)
        vars_days = {}
        for label, key, default in (("≥ 4 天压缩(quality 88)", 'compress_days', 4),
                                    ("≥ 7 天降质(quality 60)", 'degrade_days', 7),
                                    ("≥ 10 天缩略(长边 640)", 'thumb_days', 10)):
            tk.Label(frm, text=label).grid(row=len(vars_days), column=0, sticky=tk.W, pady=2)
            v = tk.IntVar(value=cfg[key])
            vars_days[key] = v
            tk.Spinbox(frm, from_=0, to=365, width=6, textvariable=v).grid(
                row=len(vars_days) - 1, column=1, sticky=tk.E, pady=2)
            tk.Label(frm, text="天（0=关闭该级）").grid(row=len(vars_days) - 1, column=2, sticky=tk.W, padx=4)

        tk.Label(frm, text="缩略图长边(px):").grid(row=3, column=0, sticky=tk.W, pady=2)
        v_edge = tk.IntVar(value=cfg['thumb_max_edge'])
        tk.Spinbox(frm, from_=200, to=2000, increment=80, width=6, textvariable=v_edge).grid(
            row=3, column=1, sticky=tk.E, pady=2)

        def save_and_close():
            try:
                self.storage_cfg = {
                    'enabled': bool(en.get()),
                    'compress_days': max(0, int(vars_days['compress_days'].get())),
                    'degrade_days': max(0, int(vars_days['degrade_days'].get())),
                    'thumb_days': max(0, int(vars_days['thumb_days'].get())),
                    'thumb_max_edge': max(200, int(v_edge.get())),
                }
                self.save_settings()
                win.destroy()
            except (tk.TclError, ValueError):
                self.show_danmaku("请输入有效数字")

        btns = tk.Frame(win); btns.pack(fill=tk.X, padx=12, pady=8)
        tk.Button(btns, text="立即优化", bg='#d1e7dd',
                  command=lambda: (self._run_storage_optimize(force=True), win.destroy())).pack(side=tk.LEFT)
        tk.Button(btns, text="保存", command=save_and_close).pack(side=tk.LEFT, padx=8)
        tk.Button(btns, text="取消", command=win.destroy).pack(side=tk.LEFT)

    def _run_storage_optimize(self, force=False):
        """启动后台存储优化（不卡 UI）；force 忽略 30 分钟节流（启动判定/立即优化用）。
        自动路径（periodic_refresh）每 5 秒调用本函数，由内部完成节流判断；
        环境变量 WB_SKIP_STORAGE_OPT=1 时跳过（自动化测试用，避免触碰真实数据）。"""
        if os.environ.get('WB_SKIP_STORAGE_OPT') == '1':
            return
        if self._closing:
            return
        self._storage_cancel.clear()
        if self._storage_running:
            self.show_status_danmaku("存储优化正在进行…")
            return
        now = time.time()
        if not force and now - self._last_storage_check < 1800:
            return   # 30 分钟节流内：跳过（下次 5 秒后再判）
        self._last_storage_check = now   # force 也记录：启动判定后 30 分钟内不重复自动跑
        self._storage_running = True
        threading.Thread(target=self._storage_job, daemon=True).start()

    def _storage_job(self):
        if self._storage_cancel.is_set() or self._closing:
            self._storage_running = False
            return
        # 与自动图片处理/手动规范化互斥：拿不到锁说明有写操作进行中，
        # 静默跳过本轮（不报"完成 0 张"误导用户），30 分钟节流后或下次启动再判定；
        # 避免双线程同时写同一图片损坏文件
        if not self._processing_lock.acquire(blocking=False):
            self._storage_running = False
            return
        self._storage_progress = 0
        try:
            processed, freed = self._optimize_all()
            self._storage_result = (processed, freed)
        except Exception as e:
            self._storage_result = ('err', str(e))
        finally:
            self._processing_lock.release()
            self._storage_running = False
            self._storage_done = True   # 主线程 periodic_refresh 取结果

    def _optimize_all(self):
        """扫描 BASE_DIR 下全部图片，按 mtime 年龄分级处理；返回 (处理数, 释放字节)。
        两阶段：先只读扫描收集任务（快），再 8 线程并行处理（Pillow 释放 GIL，
        多张独立图片真实并行；基准测试 6C12T 下约 4.5x 加速）。
        互斥：调用方已持 PROCESS_LOCK（跨进程），本函数不再加锁。"""
        cfg = self.storage_cfg
        if not cfg.get('enabled'):
            return 0, 0
        state = self._load_storage_state()
        now = time.time()
        # ---- 阶段 1：只读收集任务（不处理文件） ----
        tasks = []   # (path, level, mtime, size_before)
        for root, dirs, files in os.walk(BASE_DIR):
            if self._storage_cancel.is_set() or self._closing:
                return 0, 0
            # 剪枝：不进入 登记/__pycache__/测试 及隐藏目录。
            # （仅 continue 跳过当前目录时，os.walk 仍会递归枚举整棵子树；
            #   剪枝后完全不遍历，每 30 分钟全量检查显著提速）
            dirs[:] = [d for d in dirs if not d.startswith('.') and d not in SKIP_SCAN_DIRS]
            rel = os.path.relpath(root, BASE_DIR)
            if rel == '.' or rel.startswith('.') or rel.split(os.sep)[0] in SKIP_SCAN_DIRS:
                continue
            for f in files:
                ext = os.path.splitext(f)[1].lower()
                if ext not in IMAGE_EXTENSIONS:
                    continue   # 只处理图片；-改 批改文件同样参与分级压缩（用户要求）
                p = os.path.join(root, f)
                try:
                    st = os.stat(p)
                    mtime = st.st_mtime
                except OSError:
                    continue
                age = (now - mtime) / 86400.0
                if cfg['thumb_days'] and age >= cfg['thumb_days']:
                    lv = 3
                elif cfg['degrade_days'] and age >= cfg['degrade_days']:
                    lv = 2
                elif cfg['compress_days'] and age >= cfg['compress_days']:
                    lv = 1
                else:
                    continue
                if state.get(p, 0) >= lv:
                    continue   # 已处理到该级别
                tasks.append((p, lv, mtime, st.st_size))
        if not tasks:
            return 0, 0   # 无任务：状态未变化，无需落盘（也避免无谓失效 mtime 缓存）
        # ---- 阶段 2：并行处理（不同文件互不影响；state/落盘加锁） ----
        processed = freed = 0
        state_lock = threading.Lock()

        def _work(task):
            nonlocal processed, freed
            if self._storage_cancel.is_set() or self._closing:
                return
            p, lv, mtime, size_before = task
            try:
                r = self._apply_storage_level(p, lv, cfg, mtime)
            except Exception:
                # 单文件处理失败（被删/占用/损坏）：跳过该文件，不中断整轮
                # （修复历史 bug：原实现 ex.map 收集到异常会中止整个存储优化）
                r = None
            with state_lock:
                if r == 'skip':
                    state[p] = lv   # 已是目标形态（如长边已≤阈值）：仅记录状态，不重复重存
                elif r:
                    state[p] = lv
                    processed += 1
                    try:
                        freed += max(0, size_before - os.path.getsize(p))
                    except OSError:
                        pass   # 文件已被删除：仅记录状态，无法统计释放量
                    # 进度 + 周期落盘（窗口中断最多丢部分记录；已缩略的图下次判定
                    # 走 skip 分支不重存，幂等性由尺寸启发式兜底）
                    if processed % 50 == 0:
                        self._storage_progress = processed
                        try:
                            self._save_storage_state(state)
                        except Exception:
                            pass
        with ThreadPoolExecutor(max_workers=PARALLEL_WORKERS) as ex:
            list(ex.map(_work, tasks))
        # 清理已不存在文件的记录（防状态文件无限膨胀）
        stale = [k for k in state if not os.path.exists(k)]
        for k in stale:
            del state[k]
        self._save_storage_state(state)
        return processed, freed

    def _apply_storage_level(self, path, level, cfg, mtime=None):
        """对单张图片执行对应级别处理。
        返回 True=已处理 / 'skip'=已是目标形态（仅需记录状态）/ False=失败。
        处理后恢复原 mtime（保持放入时间语义）。
        - 动画图（GIF/多帧）直接跳过，避免保存时只存首帧破坏动画
        - quality 仅对 JPEG/WebP 有效；PNG 无损 optimize；BMP/GIF/TIFF 按默认保存
          （缩略级已缩尺寸，体积仍会下降）"""
        try:
            with Image.open(path) as im:
                if getattr(im, 'is_animated', False):
                    return False   # 动画图跳过（保存会丢帧）
                ext = os.path.splitext(path)[1].lower()
                edge = cfg['thumb_max_edge']
                if level >= 3 and (im.width > edge or im.height > edge):
                    resample = (Image.Resampling.LANCZOS
                                if hasattr(Image, 'Resampling') else Image.LANCZOS)
                    im.thumbnail((edge, edge), resample)
                elif level >= 3:
                    # 尺寸已 ≤ 缩略阈值：状态丢失等场景下不重复重存（省 IO）
                    return 'skip'
                if ext == '.png':
                    kwargs = {'optimize': True}   # PNG 无损优化体积（缩略级已缩尺寸）
                elif ext in ('.jpg', '.jpeg', '.webp'):
                    if level >= 3:
                        kwargs = {'quality': 70}
                    elif level == 2:
                        kwargs = {'quality': 60}
                    else:
                        kwargs = {'quality': 88}
                    kwargs['optimize'] = True
                    if ext in ('.jpg', '.jpeg'):
                        kwargs['subsampling'] = 0   # 减少色彩锯齿，压缩观感更好
                else:
                    # bmp/gif/tiff：quality 参数无效，按默认参数保存（无损）；
                    # 缩略级已缩尺寸，体积仍会下降
                    kwargs = {}
                if mtime is None:
                    mtime = os.stat(path).st_mtime
                # 原子写：先写同目录临时文件再 os.replace，中途崩溃/断电不会留下
                # 半写的损坏图片（直接覆盖原文件时中断会截断文件）
                tmp = path + '.opt_tmp'
                try:
                    im.save(tmp, **kwargs)
                    os.replace(tmp, path)
                finally:
                    try:
                        if os.path.exists(tmp):
                            os.remove(tmp)
                    except OSError:
                        pass
                os.utime(path, (mtime, mtime))
            return True
        except Exception:
            return False   # 损坏/占用等：跳过，不中断

    def normalize_current_lecture(self):
        """
        手动规范化当前讲次的全部图片（含老图片）：HEIC→JPG、
        窄边缩放到 1080、规范命名。后台执行，完成后自动刷新。
        （无确认弹窗：直接后台执行，处理幂等，弹幕反馈结果）
        """
        folders = self._current_lecture_folders()
        if not folders:
            self.show_danmaku("当前没有目标文件夹")
            return
        self.show_danmaku(f"正在规范化当前讲次 {len(folders)} 个文件夹…")

        def _job():
            total = 0
            try:
                if self._processing_lock.acquire(blocking=False):
                    try:
                        # 跳过已被存储优化处理（缩略/降质）的文件，
                        # 避免把缩略图放大回 1080（与自动处理路径行为一致）
                        try:
                            skip_optimized = set(load_storage_opt_state().keys())
                        except Exception:
                            skip_optimized = set()
                        for folder in folders:
                            total += _namer.normalize_folder(folder, BASE_DIR, skip_optimized)
                    finally:
                        self._processing_lock.release()
                else:
                    # 后台线程不得直接操作 Tk（非线程安全），排队回主线程弹幕
                    if not self._closing:
                        try:
                            self.root.after(0, self.show_danmaku, "有其他图片处理进行中，请稍后再试")
                        except Exception:
                            pass
                    return
            except Exception as e:
                print(f"规范化失败: {e}")
            if not self._closing:   # 窗口已关闭：不再排队回调
                try:
                    self.root.after(0, lambda: self._on_normalize_done(total))
                except Exception:
                    pass   # 窗口已销毁，忽略

        threading.Thread(target=_job, daemon=True).start()

    def _on_normalize_done(self, total):
        self._img_process_cache.clear()
        self.refresh()
        self.show_danmaku(f"当前讲次处理完成（{total} 次操作），统计已刷新。")

    def refresh_by_scope(self):
        """刷新：全局=清增量缓存强制全量重扫；当前范围=常规刷新"""
        if self.refresh_scope.get() == '全局':
            clear_dir_scan_cache()
            self._img_process_cache.clear()
        self.refresh()

    def rename_by_scope(self):
        """
        命名：全局=全量检查+自动重命名；当前范围=当前讲次（所有分类）检查+自动重命名。
        删除类操作仍必须确认（本流程不含删除）。
        """
        if self.naming_scope.get() == '全局':
            self.global_check_naming()
            return
        folders = self._current_lecture_folders()
        if not folders:
            self.show_danmaku("当前没有目标文件夹")
            return
        bad = check_filename_format(BASE_DIR, folders=folders)
        if not bad:
            self.show_danmaku("当前范围的图片命名均符合规范 ✓")
            return
        renamed = 0
        for folder in {os.path.dirname(b) for b, _ in bad}:
            try:
                renamed += smart_rename_folder(folder, BASE_DIR)
            except Exception:
                pass
        remain = check_filename_format(BASE_DIR, folders=folders)
        self._bad_names = remain
        self._img_process_cache.clear()
        self.refresh()
        self.show_danmaku(f"已自动修正 {renamed} 个文件的命名；仍不规范 {len(remain)} 个（请手动处理）")

    def _send_scope_to_modifier(self, scope):
        """尝试把检索规则发送给已打开的修改器实例（本地端口）；成功返回 True（复用窗口）"""
        import socket
        try:
            with socket.create_connection(('127.0.0.1', 47518), timeout=0.5) as s:
                s.sendall(json.dumps(scope).encode('utf-8'))
            return True
        except OSError:
            return False

    def open_modifier(self):
        """
        带当前限制范围打开修改器（**始终同步当前检索方式**）：
        内容模式传 讲次+分类+班级；学生模式传 姓名+类别（未选学生也切学生模式，
        修改器内自行选择学生）——保证修改器检索设置与监控器一致。
        若修改器已打开：不重复新开窗口，直接把新检索规则应用到已打开窗口并置顶。
        嵌入模式：直接切主窗口「修改器」页（检索范围由监视器发布的检索状态文件驱动）。
        """
        if self._embedded:
            on_open = getattr(self.container, '_dsh_on_open_modifier', None)
            if callable(on_open):
                on_open()
            return
        if self.search_mode == 'student':
            cat = self.current_sub.get()
            scope = {'search_mode': 'student', 'name': self.student_name,
                     'category': cat}
            args = ['--search-mode', 'student', '--name', self.student_name,
                    '--category', cat]
        else:
            lec = self.current_lecture.get()
            cat = self.current_sub.get() if not is_exam_or_checkin(lec) else '全部'
            classes = ','.join(y for y, v, cb in self.class_buttons if v.get()) or '全部'
            scope = {'lecture': lec, 'category': cat, 'classes': classes}
            args = ['--lecture', lec, '--category', cat, '--classes', classes]
        if self._send_scope_to_modifier(scope):
            return   # 已有修改器实例：检索规则已应用，避免窗口重复打开
        script = os.path.join(PROGRAM_DIR, '作业修改器.py')
        try:
            subprocess.Popen([sys.executable, script] + args)
        except Exception as e:
            self.show_danmaku(f"启动修改器失败：{e}")

    def update_title(self):
        if self._embedded:
            return   # 嵌入模式不覆盖主窗口标题栏
        current_time = datetime.datetime.now().strftime('%H:%M:%S')
        if self._bad_names:
            self.root.title(_TITLE_PREFIX + f"最后更新: {current_time} | ⚠ {len(self._bad_names)} 个不规范命名（点『全局检查命名』处理）")
        else:
            self.root.title(_TITLE_PREFIX + f"最后更新: {current_time}")

    def global_check_naming(self):
        """
        全局检查并修改命名（手动触发）：全量扫描所有文件夹，
        发现不规范自动重命名（无需确认）；删除类操作仍必须确认（本流程不含删除）。
        """
        try:
            bad = check_filename_format(BASE_DIR)
        except Exception as e:
            self.show_danmaku(f"全局检查命名失败：{e}")
            return
        if not bad:
            self.show_danmaku("所有图片文件名均符合规范 ✓")
            return
        renamed = 0
        # 与自动处理/存储优化共用跨进程锁：手动重命名不得与后台并发改名
        # 竞争（修复历史 bug：原实现不取锁，可能和自动处理同时 rename 同一文件）
        if not self._processing_lock.acquire(blocking=False):
            self.show_danmaku("有其他图片处理正在进行，请稍后再试")
            return
        try:
            # 按目录去重：每个目录只处理一次（smart_rename_folder 是目录级操作）
            for folder in {os.path.dirname(p) for p, _ in bad}:
                try:
                    renamed += smart_rename_folder(folder, BASE_DIR)
                except Exception:
                    pass
        finally:
            self._processing_lock.release()
        remain = check_filename_format(BASE_DIR)
        self._bad_names = remain
        self.show_danmaku(
            f"已自动修正 {renamed} 个文件的命名；仍不规范 {len(remain)} 个（请手动处理）")
        self.refresh()

    def stop_page(self):
        """停止本页的全部定时器/全局绑定（页面切换时调用；不销毁 root）。
        独立关闭（on_closing）复用本方法后再销毁 root。"""
        self._closing = True   # 后台线程不再排队回调（防销毁后 TclError）
        self._storage_cancel.set()
        if self.after_id:
            try:
                self.root.after_cancel(self.after_id)
            except Exception:
                pass
            self.after_id = None
        for attr in ('_resize_after', '_font_after', '_startup_folder_check_id',
                     '_storage_start_id'):
            t = getattr(self, attr, None)
            if t is not None:
                try:
                    self.root.after_cancel(t)
                except Exception:
                    pass
                setattr(self, attr, None)
        # 修改器变更短轮询：同样取消（防销毁后回调 TclError）
        if getattr(self, '_modifier_watch_id', None) is not None:
            try:
                self.root.after_cancel(self._modifier_watch_id)
            except Exception:
                pass
            self._modifier_watch_id = None
        # 解除页面级全局滚轮绑定（bind_all 挂 'all' tag，容器销毁后仍残留，
        # 必须显式解绑，避免影响宿主整窗其他页面的滚轮行为）
        for seq in ('<MouseWheel>', '<Button-4>', '<Button-5>'):
            try:
                self.canvas.unbind_all(seq)
            except Exception:
                pass
        # 解除本页 <Configure> 绑定（挂 container 上，容器销毁自动消失，稳妥起见再解）
        try:
            self.container.unbind('<Configure>')
        except Exception:
            pass

    def on_closing(self):
        self.save_settings()
        self.stop_page()
        # 延迟 120ms 再销毁：让已排队的后台回调（如 _on_refresh_done）先执行完，
        # 避免销毁后触发 "invalid command name"
        try:
            self.root.after(120, self._final_destroy)
        except Exception:
            self._final_destroy()

    def _final_destroy(self):
        try:
            self.root.destroy()
        except Exception:
            pass


def run():
    """启动监控器主界面（支持拖放的 Tk 根窗口）。
    供「启动.py」统一入口与直接运行本文件共用。"""
    if DND_AVAILABLE:
        root = TkinterDnD.Tk()
    else:
        root = tk.Tk()
    app = FileMonitorApp(root)
    # 保留引用防回收（界面对象由回调闭包自持，root.mainloop 驱动事件循环）
    del app
    if not DND_AVAILABLE:
        # 拖放不可用：给个一次性提示（不打扰，可在状态栏看到）
        print("提示：未安装 tkinterdnd2，外部图片拖放功能不可用。"
              "可执行: python -m pip install -i https://pypi.tuna.tsinghua.edu.cn/simple tkinterdnd2")
    root.mainloop()


if __name__ == "__main__":
    run()
