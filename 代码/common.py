# -*- coding: utf-8 -*-
"""
作业批改工具集 - 公共模块
========================================
集中管理目录结构配置与跨脚本复用的工具函数，
消除 框架搭建器 / 情况监视器 / 作业命名器 / 作业修改器 之间的重复定义。

使用约定：
    全部脚本（含 common.py）集中放在 程序根/代码/ 子文件夹内（v3.4.0 起）。
    程序根 APP_ROOT = 代码/ 的上一级；配置目录 CONFIG_DIR = 程序根/配置/；
    说明目录 DOC_DIR = 程序根/说明/。
    各脚本开头统一：
        import sys, os
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        from common import ...
"""
import os
import sys
import platform
import subprocess
import re
import shutil
import time
import json
import tempfile

# 项目版本号（修改器/监控器窗口标题显示；功能迭代时手动递增）
# 历史：v1.x = 项目迁移与基础修复；v2.0 = 弹窗改造；v2.1 = 联排分别旋转；
#       v2.2 = 相邻讲状态标记；v2.3 = 撤销/重做跨图安全；
#       v2.4 = Python 3.14 适配、存储优化状态跨机器迁移、跳过测试副本目录、
#              只缩不放（小图/缩略图不再放大回 1080）；
#       v2.5 = 名单外置名单.json + 启动弹窗（添加文件/删除名单/暂时不管）；
#       v2.6 = 监视器拖放导入（外部图片拖入卡片存入对应文件夹）、
#              复制批改模式（点卡片汇总 -改 图 + 情况说明文本）
#       v2.6.1 = 维护轮：统计缓存别名/目录缓存抖动/NTFS mtime 漏检/
#               快捷键残留/联排标注丢失/句柄泄漏/原子写等修复 + 性能与杂糅清理
#       v2.7.0 = 姓名-类别检索（监控器+修改器，与内容检索独立、共用修改器）；
#               统一设置中心（两边同一窗口）；联排保存位移/输入法冲突/鼠标侧键修复
#       v2.8.0 = 复制批改内容可选（讲次/考试/打卡 分开记忆）；监控器卡片反馈块位置修复
#       v2.9.0 = 功能整合：独立「批改工具」程序目录 + 统一启动入口（启动.py/启动.bat，
#               启动即监控器）；程序与数据分离（data_dir.txt 指定数据目录）；
#               监控器新增「🗑 删除」模式（一键列图删放错的图，走回收站可恢复）
#       v2.9.1 = 监控器顶部反馈标记改为「常驻显色」：无标记按文件状态显示（灰=无文件/
#               红=有未批改/绿=已批改），有标记显示标记对应颜色（优先，无视文件状态）
#       v2.9.2 = 修复「设置修改后没应用」：设置中心保存后复制内容配置（copy_content）
#               未重载进内存，界面弹幕显示已保存但实际不生效——保存后即时重载
#       v2.9.3 = 修复「撤回（撤销）无法使用」：中文输入法开启时 _shortcut_active 的
#               裸字符键屏蔽误伤组合键，导致 Ctrl+Z 撤销 / Ctrl+Y 重做 / Ctrl+T 联排
#               全部失灵——现仅屏蔽无修饰的裸字符键，组合键照常生效
#       v2.9.4 = 修复「设置没法保存」：设置中心数字输入框（字体/列数/弹幕时长/存储优化
#               天数/工具线宽等）手输非法值（字母/清空/空格）时 int() 抛异常导致保存
#               失败弹窗、设置存不进去——现对全部数字字段容错，非法输入保留原配置值，
#               保存总能成功
#       v2.9.5 = 修复「设置中心没有保存选项」：保存/取消栏打包顺序在 Notebook 之后，
#               被 expand 的 Notebook 挤到 1px 高不可见——改为固定底部先打包 + 窗口
#               高度自适应小屏幕，保存按钮始终可见
#       v2.9.6 = 设置中心两页（监控器/修改器）内容超高时出现垂直滚动条，可滚动查看/
#               修改下方设置；鼠标滚轮悬停本区域时接管、移出自动释放
#       v2.9.7 = 代码结构优化（纯内部精简重构，功能行为不变）：删除冗余别名/包装函数；
#               合并 联排/单图评分、统计与配色、学生选项收集、剪贴板、句柄释放、
#               配置惰性加载、文件列表收尾 等重复代码为公共函数（common 提供
#               seq_sort_key / collect_student_options 供 监控器/修改器 共用）
#       v2.9.8 = 修复「监控器侧改的修改器设置被下一次检索静默还原」：修改器/监控器
#               独立进程，修改器检索持久化前改用读最新配置（原内存缓存可能整体覆盖
#               另一进程刚保存的设置）；删除不可达的「无权限」死分支（扫描已吞 OSError）
#       v2.9.9 = 修复「联排跨图撤销失效」：联排模式切换聚焦图（set_active_tile）时
#               原实现清空撤销栈，导致切到另一张图后无法撤销原图的操作——联排快照本
#               含全部图 elements + tile_active（跨图安全），现保留撤销历史；并修复
#               restore_state 跨图撤销未同步 bg_path（退出联排会加载错图）
#       v3.4.3 = 设置应用完整性修复：评分字号/参数范围/颜色/快捷键校验；讲次分类支持
#                 单项添加、修改、删除、排序，自动补目录并迁移文件名/评分，非空改删确认归档
#       v3.0.0 = 大版本：结构与名单全面配置化 + 监视器↔修改器双向检索同步
#               · 目录结构配置化：讲次/考试/打卡 次数与顺序可在设置中心自定义，
#                 考试可插入讲次中（考试/考试1/考试2…），多考试支持
#               · 学生名单外置化：班级/学生全部存 名单.json（缺失回退默认名单.json），
#                 设置中心可增删改班级与学生（班级/序号/姓名）；兼容旧版名单
#               · 双向检索同步：修改器不再自行承担检索，直接读取监视器每次刷新后
#                 发布的检索结果（.workbuddy/检索状态.json）；修改器保存/删除/重命名
#                 文件后写变更标记，监视器检测到立即刷新并重新发布（联排切组是否保留
#                 批改草稿也可在设置中心开关）
#               · 标记栏边界联动常态化：沿完整目录顺序（讲次/考试/打卡）上下联动，
#                 最后一讲→考试、考试→打卡第一天 信息自动衔接
#               · 设置持久化补齐（关闭后重启用保持原样）：弹幕时长/自动处理间隔/
#                 刷新范围/命名范围/复制批改/删除模式 等全部记住
#               · 相对尺寸：各主窗口按屏幕分辨率等比缩放，不再固定像素
PROJECT_VERSION = "3.4.3"

# ============================================================
#  目录结构配置（讲次/考试/打卡 的顺序与次数、讲次下子类型）
#  由 BASE_DIR 解析后从「结构配置.json」加载（见下方 _load_structure）；
#  缺失时使用默认结构（第01~15讲 + 考试 + 打卡第01~10天，与历史硬编码一致）。
#  用户可在设置中心调整，或直接编辑 结构配置.json：
#    { "order": [完整目录顺序,如 第01讲…考试…打卡第01天…],
#      "sub_types": [讲次下子类型,如 作业/课前小测/错题再练] }
# ============================================================

# 常见图片扩展名（frozenset 不可变，判断更快）
IMAGE_EXTENSIONS = frozenset({'.jpg', '.jpeg', '.png', '.bmp', '.gif', '.webp', '.tiff'})

# 工作代码目录（本文件所在目录 = 批改工具/代码/，全部 .py 集中于此）
PROGRAM_DIR = os.path.dirname(os.path.abspath(__file__))
# 程序根目录（批改工具/）：工作代码的上一级，配置/说明 子文件夹所在
APP_ROOT = os.path.dirname(PROGRAM_DIR)
# 配置目录（data_dir.txt / requirements.txt / 名单.json / 结构配置.json 等程序配置）
# v3.4.2 起 名单完全由配置（配置/名单.json）决定：py 代码不再内置/兜底任何学生信息，
# 转移时可抛弃配置，新环境名单缺失 = 空名单，由监控器「添加文件」/框架搭建器重建。
CONFIG_DIR = os.path.join(APP_ROOT, '配置')
# 说明文档目录（使用说明.md / 交接文档.md）
DOC_DIR = os.path.join(APP_ROOT, '说明')


def _resolve_path(base, p):
    """把配置路径解析为绝对路径：绝对路径原样；相对路径相对 base 解析。
    支持 ~ 与 %VAR% 展开。"""
    p = os.path.expandvars(os.path.expanduser(p.strip()))
    return p if os.path.isabs(p) else os.path.abspath(os.path.join(base, p))


def _resolve_data_dir():
    """确定数据目录（学生文件夹/名单/登记汇报/配置文件/视频胶囊所在）：
    1) 环境变量 DSH_DATA_DIR（启动时指定，优先级最高）
    2) 配置目录 配置/data_dir.txt（记录数据目录；支持绝对路径或**相对程序根的路径**，
       便于程序与数据一起整体迁移，如上一级数据目录写 `..`）
    3) 默认 = 程序根目录（程序与数据同目录，向后兼容）
    返回绝对路径。"""
    env = os.environ.get('DSH_DATA_DIR')
    if env and os.path.isdir(_resolve_path(APP_ROOT, env)):
        return _resolve_path(APP_ROOT, env)
    # 优先 配置/ 下的 data_dir.txt；兼容旧布局（程序根下的 data_dir.txt）
    for marker in (os.path.join(CONFIG_DIR, 'data_dir.txt'),
                   os.path.join(APP_ROOT, 'data_dir.txt'),
                   os.path.join(PROGRAM_DIR, 'data_dir.txt')):
        try:
            with open(marker, encoding='utf-8') as f:
                p = f.read().strip()
            if p and os.path.isdir(_resolve_path(APP_ROOT, p)):
                return _resolve_path(APP_ROOT, p)
        except Exception:
            continue
    return APP_ROOT


# 数据根目录（学生文件夹/名单/登记汇报/配置/视频胶囊 统一从这里出发）
# 程序与数据分离时指向 data_dir.txt 记录的目录；同目录时即程序根目录。
BASE_DIR = _resolve_data_dir()


def config_file_path(name):
    """程序配置文件统一放 配置/ 目录（v3.4.1 起数据根下的 json 配置收进配置目录）。
    兼容旧布局：配置目录无该文件而数据根有旧文件时自动回退读取（不迁移、无副作用），
    保证未移动的旧部署仍能读到自己配置。返回绝对路径。"""
    p = os.path.join(CONFIG_DIR, name)
    if os.path.isfile(p):
        return p
    q = os.path.join(BASE_DIR, name)
    return q if os.path.isfile(q) else p


def window_geometry(root, base_w, base_h, max_ratio=0.85, min_w=640, min_h=400):
    """按屏幕分辨率等比缩放窗口尺寸（相对尺寸：不同分辨率下窗口比例合适）。
    base_w/base_h：1920x1080 基准下的设计尺寸；返回 f"{w}x{h}" 供 geometry() 使用。
    缩放后不小于 min_w/min_h，且不超过屏幕的 max_ratio 比例。"""
    try:
        sw = root.winfo_screenwidth()
        sh = root.winfo_screenheight()
        if not sw or not sh:
            return f"{base_w}x{base_h}"
        scale = min(sw / 1920.0, sh / 1080.0, 1.0)
        w = max(min_w, min(int(base_w * scale), int(sw * max_ratio)))
        h = max(min_h, min(int(base_h * scale), int(sh * max_ratio)))
        return f"{w}x{h}"
    except Exception:
        return f"{base_w}x{base_h}"

# ============================================================
#  目录结构配置（从 结构配置.json 加载；缺失时使用默认结构）
#  order：完整目录顺序（讲次/考试/打卡，可自由排列与调整数量，考试可插在讲次中）
#  sub_types：讲次下子类型列表
# ============================================================
STRUCTURE_FILE = config_file_path('结构配置.json')


def _default_structure():
    """默认目录结构（与历史硬编码一致）：第01~15讲 + 考试 + 打卡第01~10天"""
    return {
        'order': [f"第{i:02d}讲" for i in range(1, 16)] + ['考试'] +
                 [f"打卡第{i:02d}天" for i in range(1, 11)],
        'sub_types': ['作业', '课前小测', '错题再练'],
    }


def _load_structure():
    """读取目录结构配置；缺失/损坏/格式非法时回退默认结构。
    order 为空、重复或含非字符串时视为非法（逐项校验，任一非法回退默认）。"""
    try:
        with open(STRUCTURE_FILE, encoding='utf-8') as f:
            data = json.load(f)
        if not isinstance(data, dict):
            return _default_structure()
        order = data.get('order')
        subs = data.get('sub_types')
        if (isinstance(order, list) and order and
                isinstance(subs, list) and subs and
                all(isinstance(x, str) and x.strip() for x in order) and
                all(isinstance(x, str) and x.strip() for x in subs)):
            # 去重并保序（重复目录名会导致解析/统计歧义）
            seen = set()
            clean = []
            for x in order:
                if x not in seen:
                    seen.add(x)
                    clean.append(x)
            clean_subs = []
            seen_subs = set()
            for x in subs:
                value = x.strip()
                if value not in seen_subs:
                    seen_subs.add(value)
                    clean_subs.append(value)
            return {'order': clean, 'sub_types': clean_subs}
    except Exception:
        pass
    return _default_structure()


_STRUCTURE = _load_structure()

# 完整目录顺序（讲次/考试/打卡，含用户自定义的考试位置）
LECTURES = _STRUCTURE['order']

# 讲次子类型（作业/课前小测/错题再练 或用户自定义）
LECTURE_SUB_TYPES = _STRUCTURE['sub_types']

# 讲次列表：目录名形如「第NN讲」（考试/打卡不在此列）
LECTURE_LECTURES = [x for x in LECTURES if re.match(r'^第\d+讲$', x)]

# 考试列表：目录名以「考试」开头的（考试/考试1/考试2…均可，支持自定义数量与位置）
EXAM_LECTURES = [x for x in LECTURES if x.startswith('考试')]
# 兼容旧单值用法：取第一个考试目录名；无考试时用「考试」占位
EXAM_LECTURE = EXAM_LECTURES[0] if EXAM_LECTURES else '考试'

# 打卡天列表：目录名以「打卡」开头的
CHECKIN_DAYS = [x for x in LECTURES if x.startswith('打卡')]


def reload_structure():
    """重新读取目录结构，并就地刷新公开列表。

    各工具通过 ``from common import LECTURES`` 持有列表引用，因此必须就地更新，
    不能简单重新赋值；这样设置中心保存后，重新构建页面即可使用新结构。
    """
    global _STRUCTURE, EXAM_LECTURE
    data = _load_structure()
    _STRUCTURE = data
    LECTURES[:] = data['order']
    LECTURE_SUB_TYPES[:] = data['sub_types']
    LECTURE_LECTURES[:] = [x for x in LECTURES if re.match(r'^第\d+讲$', x)]
    EXAM_LECTURES[:] = [x for x in LECTURES if x.startswith('考试')]
    CHECKIN_DAYS[:] = [x for x in LECTURES if x.startswith('打卡')]
    EXAM_LECTURE = EXAM_LECTURES[0] if EXAM_LECTURES else '考试'
    return data


_STRUCTURE_INVALID_CHARS = frozenset('<>:"/\\|?*,-')
_STRUCTURE_RESERVED_NAMES = frozenset(
    {'CON', 'PRN', 'AUX', 'NUL'} |
    {f'{prefix}{i}' for prefix in ('COM', 'LPT') for i in range(1, 10)})


def _validate_structure_names(names, label):
    values = [str(x).strip() for x in names]
    if not values or any(not x or x in ('.', '..') for x in values):
        raise ValueError(f'{label}不能为空')
    if len(values) != len(set(values)):
        raise ValueError(f'{label}不能重复')
    for value in values:
        if value.endswith('.') or any(ord(ch) < 32 or ch in _STRUCTURE_INVALID_CHARS for ch in value):
            raise ValueError(f'{label}含非法名称：{value}')
        if value.split('.')[0].upper() in _STRUCTURE_RESERVED_NAMES:
            raise ValueError(f'{label}含 Windows 保留名称：{value}')
    return values


def save_structure(order, sub_types):
    """校验并写入目录结构配置，并立即刷新运行时公共列表。"""
    order = _validate_structure_names(order, '目录名称')
    sub_types = _validate_structure_names(sub_types, '讲次分类')
    if set(order) & set(sub_types):
        raise ValueError('讲次分类不能与目录名称同名')
    atomic_write_json(STRUCTURE_FILE,
                      {'order': order, 'sub_types': sub_types},
                      ensure_ascii=False, indent=2)
    reload_structure()


# ============================================================
#  监视器 ↔ 修改器 检索信息共享（双向同步）
#  监视器每次刷新后把当前检索范围 + 结果文件列表写入 检索状态.json；
#  修改器读取该文件替代自行全量扫描（"修改器不再承担检索"）。
#  修改器保存/删除/重命名文件后写 修改器变更.json（时间戳），
#  监视器刷新时检测到新变更即立即刷新（"变动文件后同步监视器"）。
#  修改器独立运行（无监视器）时回退自行检索，保持兼容。
# ============================================================
WORKBUDDY_DIR = os.path.join(BASE_DIR, '.workbuddy')
MONITOR_SEARCH_FILE = os.path.join(WORKBUDDY_DIR, '检索状态.json')
MODIFIER_CHANGED_FILE = os.path.join(WORKBUDDY_DIR, '修改器变更.json')


def read_monitor_search_state():
    """读取监视器发布的检索状态；返回 dict（含 scope/files/updated）或 None。
    files 为 检索范围内图片文件的相对 BASE_DIR 路径列表（v3.4.2 起；
    旧版绝对路径亦兼容，读取端用 os.path.isabs 区分后拼回）。"""
    try:
        with open(MONITOR_SEARCH_FILE, encoding='utf-8') as f:
            data = json.load(f)
        if not isinstance(data, dict) or not isinstance(data.get('files'), list):
            return None
        return data
    except Exception:
        return None


def write_modifier_changed():
    """修改器变动文件后写入变更标记（原子写盘；监视器刷新时检测）"""
    try:
        atomic_write_json(MODIFIER_CHANGED_FILE,
                          {'updated': time.time()}, ensure_ascii=False, indent=1)
    except Exception:
        pass

# ============================================================
#  学生名单（完全由配置决定 = 配置/名单.json）
#  v3.4.2 起：名单只读 配置/名单.json，py 代码不内置/不兜底任何学生信息；
#  名单缺失/为空 = 空名单（新环境从零开始），由监控器「添加文件」或框架搭建器重建。
#  格式：{"年份": [[序号, "姓名"], ...]}
#  监控器启动检测名单与磁盘不符时，可弹窗「添加文件/删除名单/暂时不管」更新名单。
# ============================================================
STUDENTS_FILE = config_file_path('名单.json')


# 学生自定义「学习讲次」记录：{(年份, 序号): [目录项名...], ...}
# 仅记录"明确指定了部分讲次"的学生；无记录 = 学习全部（默认）。
# 目录项名来自 结构配置.json 的完整顺序（含 考试/打卡），只存合法项。
# 存储格式（名单.json 条目第三元素，可选）：
#   "1993": [ [1, "张三", ["第01讲","第02讲"]], [2, "李四"] ]
# 旧格式 [序号, 姓名]（无第三元素）等价于学习全部，向后兼容。
STUDENT_LECTURES = {}


def _read_students_file(path):
    """读取一份名单 json；返回 (data, lectures)。
    data = {年份: [(序号, 姓名), ...]}（二元组，与历史结构一致）；
    lectures = {(年份, 序号): [学习讲次目录项...]}（仅含自定义学生）。
    失败返回 (None, {})。"""
    try:
        with open(path, encoding='utf-8') as f:
            raw = json.load(f)
    except FileNotFoundError:
        return None, {}
    except Exception:
        print(f"[common] {os.path.basename(path)} 解析失败（可能损坏），已忽略。",
              file=sys.stderr)
        return None, {}
    if not isinstance(raw, dict) or not raw:
        return None, {}
    out = {}
    lectures = {}
    for year, entries in raw.items():
        norm = []
        for e in entries:
            try:
                seq, name = int(e[0]), str(e[1]).strip()
            except (ValueError, TypeError, IndexError):
                continue
            if name:
                norm.append((seq, name))
                # 第三元素可选：学生自定义学习讲次列表（仅保留合法目录项）
                if len(e) >= 3 and isinstance(e[2], list):
                    items = [str(x).strip() for x in e[2]
                             if isinstance(x, str) and x.strip() and x.strip() in LECTURES]
                    seen, clean = set(), []
                    for x in items:
                        if x not in seen:
                            seen.add(x)
                            clean.append(x)
                    if clean:
                        lectures[(str(year), seq)] = clean
        if norm:
            out[str(year)] = norm
    return (out or None), lectures


def _load_students():
    """名单完全由配置（配置/名单.json）决定：缺失/损坏 = 空名单（新环境从零开始，
    由监控器「添加文件」/框架搭建器重建）。同时填充 STUDENT_LECTURES。"""
    data, lec = _read_students_file(STUDENTS_FILE)
    if data:
        STUDENT_LECTURES.clear()
        STUDENT_LECTURES.update(lec)
        return data
    return {}


# 学生名单（模块加载时确定；各脚本 `from common import STUDENTS` 持有同一 dict 引用，
# 增删条目会全局生效——监控器弹窗修改名单即基于此）
STUDENTS = _load_students()


def get_student_lectures(year, seq):
    """返回学生自定义学习讲次目录项列表；None = 学习全部（默认）。"""
    return STUDENT_LECTURES.get((str(year), int(seq)))


def student_lecture_names(year, seq):
    """返回该学生实际应学习的目录项列表（含 讲次/考试/打卡；未自定义 = 全部）。"""
    lec = get_student_lectures(year, seq)
    return list(lec) if lec else list(LECTURES)


def student_learns(year, seq, lecture):
    """该学生是否学习某目录项（讲次/考试/打卡）。未自定义 = 全部（恒 True）。"""
    lec = get_student_lectures(year, seq)
    if not lec:
        return True
    return str(lecture) in lec


def set_student_lectures(year, seq, lectures):
    """设置学生自定义学习讲次（list 或 None/空列表 = 全部），保存到 名单.json。
    只保留合法目录项并去重保序。"""
    if lectures:
        valid = [x for x in lectures if isinstance(x, str) and x in LECTURES]
        seen, clean = set(), []
        for x in valid:
            if x not in seen:
                seen.add(x)
                clean.append(x)
        if clean:
            STUDENT_LECTURES[(str(year), int(seq))] = clean
        else:
            STUDENT_LECTURES.pop((str(year), int(seq)), None)
    else:
        STUDENT_LECTURES.pop((str(year), int(seq)), None)
    save_students_file()


def seq_sort_key(x):
    """序号排序键：数字按数值排前，非数字（异常名）排后——避免 int/str 混合比较崩溃"""
    return (0, int(x)) if str(x).isdigit() else (1, str(x))


def collect_student_options(cls='全部'):
    """按班级收集 序号列表 与 姓名列表（均含 '全部' 前缀；序号按数值排序）。
    监控器/修改器 姓名-类别检索的选项来源共用，消除重复。返回 (seqs, names)。"""
    seqs, names = ['全部'], ['全部']
    for year, entries in STUDENTS.items():
        if cls != '全部' and year != cls:
            continue
        for seq, name in entries:
            s = str(seq)
            if s not in seqs:
                seqs.append(s)
            names.append(f"{year}-{int(seq):02d}-{name}")
    seqs.sort(key=seq_sort_key)
    return seqs, names


def save_students_file(students=None):
    """把名单写入外部 名单.json（相对项目根，随项目迁移）。students=None 用当前 STUDENTS。
    条目格式：[序号, 姓名] 或 [序号, 姓名, [学习讲次目录项...]]（第三元素仅当有自定义时写）。"""
    data = students if students is not None else STUDENTS
    rows_by_year = {}
    for y, entries in data.items():
        rows = []
        for s, n in entries:
            lec = STUDENT_LECTURES.get((str(y), int(s)))
            if lec:
                rows.append([s, n, list(lec)])
            else:
                rows.append([s, n])
        rows_by_year[str(y)] = rows
    atomic_write_json(STUDENTS_FILE, rows_by_year, ensure_ascii=False, indent=2)


def add_students_from_folders(folder_names):
    """把磁盘上名单外的学生文件夹加入名单（原地修改 STUDENTS 并落盘）。
    folder_names: ['年份-序号-姓名', ...]。返回成功添加数。"""
    added = 0
    for name in folder_names:
        m = STUDENT_FOLDER_RE.match(name)
        if not m:
            continue
        year, seq, sname = m.group(1), int(m.group(2)), m.group(3)
        entries = STUDENTS.setdefault(year, [])
        if (seq, sname) not in entries:
            entries.append((seq, sname))
            entries.sort(key=lambda x: x[0])
            added += 1
    if added:
        save_students_file()
    return added


def remove_students_by_folder(folder_names):
    """把名单中磁盘上缺失的学生条目删除（原地修改 STUDENTS 并落盘）。
    folder_names: ['年份-序号-姓名', ...]。返回删除数。年份组删空后移除。"""
    removed = 0
    for name in folder_names:
        m = STUDENT_FOLDER_RE.match(name)
        if not m:
            continue
        year, seq, sname = m.group(1), int(m.group(2)), m.group(3)
        entries = STUDENTS.get(year)
        if not entries:
            continue
        before = len(entries)
        entries[:] = [e for e in entries if not (e[0] == seq and e[1] == sname)]
        removed += before - len(entries)
        STUDENT_LECTURES.pop((str(year), seq), None)   # 同步清理自定义学习讲次
        if not entries:
            del STUDENTS[year]
    if removed:
        save_students_file()
    return removed

# 学生文件夹名格式：4位年份-2位序号-姓名（姓名不含连字符）
STUDENT_FOLDER_RE = re.compile(r'^(\d{4})-(\d{2})-([^-]+)$')

# 根目录下应保留、不可删除的目录/文件
# （"2222227文件暂存"是用户预留的暂存目录，虽非学生格式，但不得被格式检查删除；
#   "测试"是迁移时遗留的整套项目副本目录，保留但不得被格式检查误删/误报；
#   "_待清理"是回收站降级目录（move_to_recycle_bin 兜底），不得被格式检查误删/误扫；
#   "批改工具"是程序目录（工作代码/配置/说明所在），属合规文件夹，不得被当作
#   不合规文件夹检查/清理）
RESERVED_NAMES = frozenset({'.workbuddy', '登记', '__pycache__', 'common.py',
                            '2222227文件暂存', '测试', '名单.json', '_待清理',
                            '批改工具'})

# 全量扫描（os.walk）时跳过的顶层目录：
# 登记=成绩数据、__pycache__=字节码缓存、测试=迁移遗留的项目副本（避免重复处理/重复检索）、
# _待清理=回收站降级目录（旧文件，不应参与处理/检索）、批改工具=程序目录（代码/配置/说明）
SKIP_SCAN_DIRS = frozenset({'登记', '__pycache__', '测试', '_待清理', '批改工具'})

def student_folder_name(year, seq, name):
    """按固定序号生成学生文件夹名（仅用户手动改名单，工具不自动编号）"""
    return f"{year}-{int(seq):02d}-{name}"

def all_student_folder_names():
    """按名单生成全部应存在的学生文件夹名集合"""
    names = set()
    for year, entries in STUDENTS.items():
        for seq, name in entries:
            names.add(student_folder_name(year, seq, name))
    return names


# ============================================================
#  跨进程互斥锁（图片处理专用）
#  防止多个进程/线程同时写同一图片导致损坏或重复处理：
#  - 同一监控器实例内（自动处理/存储优化/手动规范化/显式命名器）
#  - 多个监控器实例之间（双开场景）
#  - 命令行全量命名器 与 监控器 之间
#  Windows 用 msvcrt 文件锁，Linux/macOS 用 fcntl；进程退出时 OS 自动释放。
# ============================================================
class InterProcessLock:
    """跨进程互斥锁：acquire(blocking=False) 非阻塞尝试，成功返回 True；
    失败返回 False（有其他处理在持有）；release() 释放。
    锁文件常驻 .workbuddy/（不参与业务扫描），无需手动清理。"""

    def __init__(self, path):
        self._path = path
        self._fd = None
        self._acquired = False

    def _ensure_open(self):
        if self._fd is not None:
            return
        try:
            os.makedirs(os.path.dirname(self._path), exist_ok=True)
            # O_BINARY：Windows 以二进制模式打开（文本模式会做 CRLF 转换，
            # 且 msvcrt.locking 语义上应作用于二进制 fd）
            self._fd = os.open(self._path, os.O_RDWR | os.O_CREAT |
                               (getattr(os, 'O_BINARY', 0)))
        except OSError:
            self._fd = None

    def acquire(self, blocking=False):
        self._ensure_open()
        if self._fd is None:
            return False
        try:
            # 关键：msvcrt.locking / fcntl.lockf 都从**当前文件位置**开始锁 nbytes 字节，
            # 且成功后把文件位置前移 nbytes。若每次操作前不归零，锁区间会逐次漂移：
            # 第 1 次锁字节 0、第 2 次锁字节 2……导致①该进程后续 acquire 永远成功
            # （互斥失效）；②首个持锁进程 release 解的是漂移后的字节，字节 0 的锁
            # 残留到进程退出，其他进程从此永远 acquire 失败（历史 bug：双开饿死）。
            os.lseek(self._fd, 0, os.SEEK_SET)
            if platform.system() == 'Windows':
                import msvcrt
                if blocking:
                    msvcrt.locking(self._fd, msvcrt.LK_LOCK, 1)
                else:
                    msvcrt.locking(self._fd, msvcrt.LK_NBLCK, 1)
            else:
                import fcntl
                mode = fcntl.LOCK_EX if blocking else (fcntl.LOCK_EX | fcntl.LOCK_NB)
                fcntl.lockf(self._fd, mode, 1)
            self._acquired = True
            return True
        except (OSError, IOError, BlockingIOError):
            return False

    def release(self):
        if not self._acquired or self._fd is None:
            return
        try:
            os.lseek(self._fd, 0, os.SEEK_SET)   # 与 acquire 一致：归零后再解锁字节 0
            if platform.system() == 'Windows':
                import msvcrt
                msvcrt.locking(self._fd, msvcrt.LK_UNLCK, 1)
            else:
                import fcntl
                fcntl.lockf(self._fd, fcntl.LOCK_UN, 1)
        except Exception:
            pass   # 释放失败（如已崩溃）：OS 会在进程退出时自动释放
        self._acquired = False

    def __enter__(self):
        # 获取失败必须显式失败：静默进入临界区会让互斥名存实亡（历史 bug：
        # 双开场景第二个进程 acquire 失败却被当作已持锁继续处理图片）
        if not self.acquire(blocking=True):
            raise RuntimeError(f"无法获取进程锁: {self._path}")
        return self

    def __exit__(self, *exc):
        self.release()


# 全局图片处理锁（监控器/命名器共用同一把，跨进程互斥）
PROCESS_LOCK = InterProcessLock(os.path.join(BASE_DIR, '.workbuddy', 'image_proc.lock'))


# ============================================================
#  并行线程数（按 CPU 自适应，上限 8）
#  基准测试（R5 5600 6C12T）：图片缩放/压缩 8 线程接近饱和，
#  12 线程无增益；低配机自动降到物理核数。
#  Pillow 的 C 扩展释放 GIL，多线程处理多张独立图片可真实并行。
# ============================================================
PARALLEL_WORKERS = max(2, min(8, os.cpu_count() or 4))

# 评分（登记）数据目录
GRADING_DIR = os.path.join(BASE_DIR, '登记')


# ============================================================
#  类型判断
# ============================================================
def is_exam_or_checkin(lecture):
    """
    判断是否为考试或打卡天（无子类型的目录）。
    兼容多种格式：目录格式('考试'/'考试1'/'打卡第01天')、
    parse_filename 规范化格式('考试1'/'打卡01天')。
    历史 bug：只认 CHECKIN_DAYS('打卡第01天')，规范化后的 '打卡01天' 判定失败，
    导致打卡天评分不显示 0-10 快捷分、也不做数值校验。
    支持自定义考试（EXAM_LECTURES：考试/考试1/考试2…）。
    """
    s = str(lecture)
    if s in EXAM_LECTURES:
        return True
    if s.startswith('考试'):
        return True   # 规范化/自定义考试：考试/考试1/考试2…
    if s in CHECKIN_DAYS:
        return True
    # 规范化格式：'打卡第01天' -> '打卡01天'（去掉了"第"）
    if s.startswith('打卡') and s.endswith('天') and s[2:].rstrip('天').isdigit():
        return True
    return False


def get_current_sub_types(lecture):
    """根据讲次返回子类型列表；考试/打卡天无子类型返回空列表"""
    if lecture in LECTURE_LECTURES:
        return LECTURE_SUB_TYPES
    return []


def is_student_folder(name):
    """判断是否为 年份-序号-姓名 格式的学生文件夹名"""
    parts = name.split('-')
    return len(parts) == 3 and parts[0].isdigit() and parts[1].isdigit()


# ============================================================
#  文件名解析（标准命名：年份-序号-姓名-讲次[-子类型]-序号[-改]）
# ============================================================
def normalize_lecture(s):
    """规范化讲次名：'第01讲'->'1'，'考试'->'考试'，'打卡第01天'->'打卡01天'"""
    s = str(s).replace("第", "").replace("讲", "").strip()
    try:
        return str(int(s))
    except (ValueError, TypeError):
        return s


_filename_meta_cache = {}

# 哨兵：区分"该文件名未缓存"与"缓存了解析结果为 None"（None 结果同样缓存，
# 坏名每次扫描反复检查时不再重复 split+解析）
_FILENAME_MISS = object()

# 文件名解析缓存上限（超过则清最旧一批，防长期运行内存膨胀）。
# 实测项目全树约 6300+ 目录 / 2300 图片；上限须大于工作集，
# 否则每次全量扫描都会触发"插入→淘汰最旧"抖动，缓存命中率趋近于 0
# （2026-08-16 实测：4000 上限对 6336 目录，二次扫描 miss 3000 个）。
# 20000 条目 × 约 250B ≈ 5MB，内存占用可忽略。
_FILENAME_CACHE_MAX = 20000


def parse_filename(filename):
    """解析标准命名的图片文件名，带缓存；无法解析返回 None。
    缓存包含 None 结果（用哨兵区分"未缓存"与"缓存了 None"）：
    未解析成功的坏名每次扫描都会反复检查，不缓存会重复 split+解析。"""
    cached = _filename_meta_cache.get(filename, _FILENAME_MISS)
    if cached is not _FILENAME_MISS:
        return cached if cached is not None else None
    meta = _parse_filename_uncached(filename)
    if len(_filename_meta_cache) >= _FILENAME_CACHE_MAX:
        # 缓存过大：清空最旧的 1/4（字典按插入序，从头删除）
        drop = _FILENAME_CACHE_MAX // 4
        for k in list(_filename_meta_cache)[:drop]:
            _filename_meta_cache.pop(k, None)   # pop 防并发淘汰 KeyError
    _filename_meta_cache[filename] = meta
    return meta


def _parse_filename_uncached(filename):
    try:
        basename = os.path.splitext(filename)[0]
        parts = basename.split('-')
        is_modified = parts[-1] == '改'

        if is_modified:
            if len(parts) >= 7:
                # 标准讲次格式: 2024-01-张三-第01讲-作业-01-改
                seq, category, lecture = parts[-2], parts[-3], parts[-4]
                name, class_full, class_prefix = parts[-5], parts[1], parts[0]
            elif len(parts) == 6:
                # 考试/打卡格式: 2024-01-张三-考试-01-改
                seq, lecture = parts[-2], parts[-3]
                name, class_full, class_prefix = parts[-4], parts[1], parts[0]
                category = None
            else:
                return None
        else:
            if len(parts) >= 6:
                # 标准讲次格式: 2024-01-张三-第01讲-作业-01
                seq, category, lecture = parts[-1], parts[-2], parts[-3]
                name, class_full, class_prefix = parts[-4], parts[1], parts[0]
            elif len(parts) == 5:
                # 考试/打卡格式: 2024-01-张三-考试-01
                seq, lecture = parts[-1], parts[-2]
                name, class_full, class_prefix = parts[-3], parts[1], parts[0]
                category = None
            else:
                return None

        result = {'class_prefix': class_prefix, 'class_full': class_full, 'name': name,
                  'lecture': normalize_lecture(lecture), 'category': category,
                  'seq': seq, 'is_modified': is_modified}
        # 考试/打卡天无子类型：category 与 lecture 一致（便于评分等逻辑）
        if category is None:
            result['category'] = result['lecture']
        # 讲次必须带合法子类型（作业/课前小测/错题再练）：
        # '2024-01-张三-第01讲-01'（漏子类型）会被 6 段分支误当考试格式解析出
        # category='1' 的"看似合法"结果——校验不合法直接视为解析失败（返回 None），
        # 避免调用方把文件归到错误讲次/子类型（历史 bug）。
        lec = result['lecture']
        if lec and lec.isdigit() and result['category'] not in LECTURE_SUB_TYPES:
            return None
        return result
    except Exception:
        pass
    return None


def clear_filename_cache():
    """清空文件名解析缓存（删除/重命名文件后调用）"""
    _filename_meta_cache.clear()


# ============================================================
#  增量目录扫描（mtime 缓存：目录内容变化才重扫，毫秒级）
#  监控器/修改器共用同一实现，消除重复
# ============================================================
_dir_scan_cache = {}   # 目录 -> (mtime_ns, [子目录名], [文件名])
# 目录扫描缓存上限（超过则清最旧一批，防长期运行内存膨胀；线程局部缓存很小不受影响）。
# 必须大于项目目录总数（实测约 6300+），否则缓存持续抖动、命中率趋近于 0。
_DIR_SCAN_CACHE_MAX = 20000


def scan_dir_incremental(directory, cache=None):
    """
    增量扫描目录：记录目录 mtime，只有目录内容变化时才重新扫描。
    返回 (子目录名列表, 文件名列表)。
    cache=None 时使用公共缓存（clear_dir_scan_cache 可整体清空）。
    """
    if cache is None:
        cache = _dir_scan_cache
    try:
        mtime = os.stat(directory).st_mtime_ns
    except OSError:
        return [], []
    cached = cache.get(directory)
    if cached is not None and cached[0] == mtime:
        return cached[1], cached[2]
    dirs, files = [], []
    try:
        with os.scandir(directory) as it:
            for entry in it:
                try:
                    if entry.is_dir(follow_symlinks=False):
                        dirs.append(entry.name)
                    elif entry.is_file(follow_symlinks=False):
                        files.append(entry.name)
                except OSError:
                    pass
    except OSError:
        # 扫描失败（杀毒瞬时占用/网络盘抖动）：**不写缓存**。
        # 否则空列表+合法 mtime 被缓存后，目录内容在 mtime 再次变化前
        # 永久不可见（漏报不规范命名/漏检新图片）——历史 bug。
        return [], []
    if len(cache) >= _DIR_SCAN_CACHE_MAX:
        drop = _DIR_SCAN_CACHE_MAX // 4
        for k in list(cache)[:drop]:
            cache.pop(k, None)   # pop 防并发淘汰 KeyError（多线程扫描共享缓存）
    cache[directory] = (mtime, dirs, files)
    return dirs, files


def clear_dir_scan_cache(cache=None):
    """清空目录扫描缓存（目录结构变化后调用）"""
    if cache is None:
        _dir_scan_cache.clear()
    else:
        cache.clear()


# ============================================================
#  系统工具
# ============================================================
def atomic_write_json(file_path, data, **kwargs):
    """
    原子写 JSON：先写同目录临时文件，再 os.replace 覆盖目标。
    避免中途崩溃/断电把配置文件写坏（评分 JSON、工具配置、监控器设置等）。
    kwargs 透传 json.dump（indent/ensure_ascii 等）。失败时清理临时文件并抛异常。
    临时名用 mkstemp 唯一生成：固定 'x.tmp' 会让多进程/多线程并发写同一目标
    互相截断、产出混合 JSON（历史 bug：双开时名单/存储状态损坏）。
    """
    tmp = None
    try:
        fd, tmp = tempfile.mkstemp(dir=os.path.dirname(file_path) or '.',
                                   prefix=os.path.basename(file_path) + '.',
                                   suffix='.tmp')
        with os.fdopen(fd, 'w', encoding='utf-8') as f:
            json.dump(data, f, **kwargs)
        # Windows 上 os.replace 覆盖已存在目标偶发 PermissionError/WinError 5
        # （目标正被杀软/索引服务瞬时占用，尤其高并发写同一文件时）：
        # 短重试 3 次，仍失败才抛（tmp 内容已完整落盘，重试只是等锁释放）
        for _attempt in range(3):
            try:
                os.replace(tmp, file_path)
                tmp = None   # 已替换，无需清理
                break
            except OSError:
                if _attempt == 2:
                    raise
                time.sleep(0.05)
    except Exception:
        if tmp is not None:
            try:
                if os.path.exists(tmp):
                    os.remove(tmp)
            except OSError:
                pass
        raise


# ============================================================
#  存储优化状态（图片压缩/降质/缩略的"已处理级别"记录）
#  供 情况监视器（写入+读取）与 作业命名器（读取以跳过已优化文件）共用
# ============================================================
STORAGE_OPT_FILE = config_file_path('_storage_opt.json')


def _storage_rel_part(path):
    """从（旧机器）绝对路径中提取相对部分：从第一个学生文件夹段起，到路径结尾。
    例：<旧盘符>\\<旧目录>\\2024-01-张三\\打卡第01天\\x.jpg
      -> 2024-01-张三\\打卡第01天\\x.jpg
    找不到学生文件夹段时返回 None（如非学生目录，不迁移）。"""
    parts = path.split(os.sep)
    for i, p in enumerate(parts):
        if STUDENT_FOLDER_RE.match(p) or p in ('登记', '2222227文件暂存'):
            return os.path.join(*parts[i:])
    return None


# 存储优化状态读取缓存（自动处理每 5 秒调用一次；文件 mtime 不变则不重读，
# 避免反复读盘 + 迁移遍历。save 后失效缓存。返回副本防并发修改共享数据）
_storage_state_cache = {'mtime_ns': None, 'data': {}}


def load_storage_opt_state():
    """
    读取存储优化状态：{图片绝对路径: 已处理级别(1压缩/2降质/3缩略)}。
    自动迁移旧机器绝对路径（转移电脑后旧盘符路径失效）：
    取旧路径的相对部分拼到当前 BASE_DIR，仅当新位置文件存在时迁移。
    保存格式为相对路径（见 save_storage_opt_state），跨机器可迁移。
    带 mtime 缓存：文件未变化时直接返回副本（毫秒级）。
    """
    try:
        mtime_ns = os.stat(STORAGE_OPT_FILE).st_mtime_ns
    except OSError:
        return {}
    c = _storage_state_cache
    if c['mtime_ns'] == mtime_ns:
        return dict(c['data'])
    try:
        with open(STORAGE_OPT_FILE, encoding='utf-8') as f:
            raw = json.load(f)
    except Exception:
        return {}
    if not isinstance(raw, dict):
        return {}
    state = {}
    for k, v in raw.items():
        if k.startswith(BASE_DIR + os.sep) or k == BASE_DIR:
            state[k] = v                      # 已是当前根下的绝对路径
        elif os.path.isabs(k):
            rel = _storage_rel_part(k)        # 旧机器绝对路径：按相对部分迁移
            if rel:
                np = os.path.join(BASE_DIR, rel)
                if os.path.exists(np):
                    state[np] = v
        else:
            np = os.path.join(BASE_DIR, k)    # 相对路径（当前版本保存格式）
            if os.path.exists(np):
                state[np] = v
    c['mtime_ns'] = mtime_ns
    c['data'] = state
    return dict(state)


def save_storage_opt_state(state):
    """保存存储优化状态：统一存相对 BASE_DIR 的路径（换机器/换盘符后自动可迁移）。
    写入后失效读取缓存（下次 load 强制重读）。"""
    rel = {}
    for k, v in state.items():
        try:
            rel[os.path.relpath(k, BASE_DIR)] = v
        except ValueError:                    # 跨盘符等极端情况：保留原键
            rel[k] = v
    atomic_write_json(STORAGE_OPT_FILE, rel, ensure_ascii=False)
    _storage_state_cache['mtime_ns'] = None   # 失效缓存

def get_file_added_time(filepath):
    """
    获取文件"放入文件夹"的时间。
    Windows 上 st_ctime 是创建时间，最贴近"放入时间"；
    Linux/macOS 上回退使用 st_mtime（修改时间）作为近似。
    """
    stat = os.stat(filepath)
    if platform.system() == 'Windows':
        return stat.st_ctime
    return stat.st_mtime


def open_in_file_manager(path):
    """跨平台打开文件夹；成功返回 True"""
    if not os.path.isdir(path):
        return False
    try:
        if platform.system() == 'Windows':
            os.startfile(path)
        elif platform.system() == 'Darwin':
            subprocess.Popen(['open', path])
        else:
            subprocess.Popen(['xdg-open', path])
    except Exception:
        return False
    return True


# ============================================================
#  剪贴板格式检查（Windows）
#  用于逆向"应用复制图文时用了哪些剪贴板格式"：
#  在 QQ/微信 中复制一条图文消息后调用本函数，可列出全部格式
#  （标准格式编号 + 注册格式名 + 内容大小），据此复刻同样的格式组合。
# ============================================================
_STANDARD_CLIPBOARD_FORMATS = {
    1: 'CF_TEXT', 2: 'CF_BITMAP', 3: 'CF_METAFILEPICT', 4: 'CF_SYLK',
    5: 'CF_DIF', 6: 'CF_TIFF', 7: 'CF_OEMTEXT', 8: 'CF_DIB',
    9: 'CF_PALETTE', 10: 'CF_PENDATA', 11: 'CF_RIFF', 12: 'CF_WAVE',
    13: 'CF_UNICODETEXT', 14: 'CF_ENHMETAFILE', 15: 'CF_HDROP',
    16: 'CF_LOCALE', 17: 'CF_DIBV5',
}


def inspect_clipboard(max_bytes=4096, full=False):
    """读取当前剪贴板的全部格式（Windows）。
    返回 [(格式编号, 格式名, 数据大小, 内容摘要), ...]；非 Windows 或失败返回 []。
    内容摘要：文本/HTML/XML 等可解码格式取开头字符；二进制取 hex 开头。
    full=True 时取完整内容（诊断 QQ/微信 图文复制格式用）。"""
    if platform.system() != 'Windows':
        return []
    import ctypes
    from ctypes import wintypes
    user32 = ctypes.windll.user32
    kernel32 = ctypes.windll.kernel32
    user32.OpenClipboard.argtypes = [wintypes.HWND]
    user32.OpenClipboard.restype = wintypes.BOOL
    user32.EnumClipboardFormats.argtypes = [wintypes.UINT]
    user32.EnumClipboardFormats.restype = wintypes.UINT
    user32.GetClipboardData.argtypes = [wintypes.UINT]
    user32.GetClipboardData.restype = wintypes.HANDLE
    user32.GetClipboardFormatNameW.argtypes = [wintypes.UINT, wintypes.LPWSTR, ctypes.c_int]
    user32.GetClipboardFormatNameW.restype = ctypes.c_int
    kernel32.GlobalLock.argtypes = [wintypes.HGLOBAL]
    kernel32.GlobalLock.restype = ctypes.c_void_p
    kernel32.GlobalUnlock.argtypes = [wintypes.HGLOBAL]
    kernel32.GlobalSize.argtypes = [wintypes.HGLOBAL]
    kernel32.GlobalSize.restype = ctypes.c_size_t
    if not user32.OpenClipboard(None):
        return []
    out = []
    try:
        fmt = user32.EnumClipboardFormats(0)
        while fmt:
            name = _STANDARD_CLIPBOARD_FORMATS.get(fmt)
            if name is None:
                buf = ctypes.create_unicode_buffer(128)
                if user32.GetClipboardFormatNameW(fmt, buf, 128):
                    name = buf.value
                else:
                    name = f'格式#{fmt}'
            size = 0
            summary = ''
            h = user32.GetClipboardData(fmt)
            if h:
                ptr = kernel32.GlobalLock(h)
                if ptr:
                    size = kernel32.GlobalSize(h)
                    limit = 65536 if full else max_bytes
                    data = ctypes.string_at(ptr, min(size, limit))
                    kernel32.GlobalUnlock(h)
                    summary = _clipboard_summary(fmt, data, full=full)
            out.append((fmt, name, size, summary))
            fmt = user32.EnumClipboardFormats(fmt)
    finally:
        user32.CloseClipboard()
    return out


def _clipboard_summary(fmt, data, full=False):
    """按格式类型生成内容摘要（full=True 时输出完整内容，用于逆向图文复制格式）"""
    limit = 6000 if full else 120
    try:
        if fmt == 13:   # CF_UNICODETEXT
            return data.decode('utf-16-le', errors='replace').split('\x00')[0][:limit]
        if fmt == 1:    # CF_TEXT
            return data.split(b'\x00')[0].decode('gbk', errors='replace')[:limit]
        if fmt == 15:   # CF_HDROP：文件路径列表
            paths = []
            offset = 20
            while offset + 1 < len(data):
                i = offset
                end = -1
                while i + 1 < len(data):
                    if data[i] == 0 and data[i + 1] == 0:
                        end = i
                        break
                    i += 2
                if end < 0 or end == offset:
                    break
                try:
                    p = data[offset:end].decode('utf-16-le')
                    if p:
                        paths.append(p)
                except Exception:
                    pass
                offset = end + 2
            return '; '.join(paths)[:limit * 2]
        if fmt in (8, 17):   # DIB/DIBV5 位图
            w, h = None, None
            try:
                import struct
                w, h = struct.unpack_from('<ii', data, 4)
            except Exception:
                pass
            return f'位图 {w}x{h}'
        # 注册格式（HTML/QQ RichEdit 等）：优先完整文本
        for enc in ('utf-8', 'utf-16-le', 'gbk'):
            try:
                txt = data.decode(enc)
                if txt and all(c.isprintable() or c in '\r\n\t' for c in txt[:300]):
                    return txt[:limit].replace('\r', ' ').replace('\n', ' ')
            except Exception:
                continue
        return data[:48].hex(' ')
    except Exception:
        return ''


def get_grading_filename(lecture):
    """评分数据 JSON 文件名：讲次->'第NN讲.json'（统一两位补零），考试/打卡->'{lecture}.json'。
    修复历史 bug：int('1') 拼出 '第1讲.json'、int('第01讲') 失败返回 '第01讲.json'——
    同一讲次不同传入格式产生两个评分文件、互相看不到。统一补零到两位后，
    两种传入格式都得到 '第01讲.json'。"""
    try:
        return f"第{int(lecture):02d}讲.json"
    except (ValueError, TypeError):
        return f"{lecture}.json"


# ============================================================
#  命名格式检查（纯文件名判断，不读图片内容，极快）
#  配合增量目录缓存：每次只重扫内容变化的目录
# ============================================================
_check_scan_cache = {}   # 目录 -> (mtime_ns, [文件名列表])
# 命名检查缓存上限（超过则清最旧一批；须大于项目目录总数，防抖动，见 _DIR_SCAN_CACHE_MAX）
_CHECK_CACHE_MAX = 20000
# parse_filename 会把讲次规范化为数字('1'..'15')、考试='考试'、打卡='打卡NN天'
_VALID_NORM_LECTURES = frozenset(normalize_lecture(x) for x in LECTURES)

def is_standard_filename(fname):
    """
    文件名是否符合规范：年份-序号-姓名-讲次-类型-序号[-改]（或 考试/打卡格式）。
    非图片文件视为规范（不评判）。只做文件名判断，不读文件内容。
    """
    name, ext = os.path.splitext(fname)
    if ext.lower() not in IMAGE_EXTENSIONS:
        return True
    m = parse_filename(fname)
    if not m:
        return False
    lec_norm = m['lecture']   # 简化形式：数字 / '考试' / '打卡NN天'
    if lec_norm not in _VALID_NORM_LECTURES:
        return False
    cat = m['category']
    if lec_norm.isdigit():
        # 讲次：分类必须是合法子类型（作业/课前小测/错题再练）
        if cat not in LECTURE_SUB_TYPES:
            return False
    else:
        # 考试/打卡：无子分类，分类应等于讲次本身
        if cat != lec_norm:
            return False
    if not m['seq'].isdigit():
        return False
    return True

def check_filename_format(base_dir=None, folders=None):
    """
    扫描不规范命名的图片文件，返回 [(完整路径, 文件名), ...]。
    folders=None：全量 os.walk（手动全局检查用）；
    folders=[...]：只定向检查这些文件夹（增量缓存，毫秒级，适合每5秒自动检查）。
    只检查不修改；修改请调用 smart_rename_folder（自动重命名，无需确认）。
    """
    if base_dir is None:
        base_dir = BASE_DIR
    bad = []

    def _scan_one(folder):
        try:
            mtime = os.stat(folder).st_mtime_ns
        except OSError:
            return
        cached = _check_scan_cache.get(folder)
        if cached is not None and cached[0] == mtime:
            names = cached[1]
        else:
            try:
                names = [f for f in os.listdir(folder)
                         if os.path.isfile(os.path.join(folder, f))]
            except OSError:
                return
            if len(_check_scan_cache) >= _CHECK_CACHE_MAX:
                drop = _CHECK_CACHE_MAX // 4
                for k in list(_check_scan_cache)[:drop]:
                    _check_scan_cache.pop(k, None)   # pop 防并发淘汰 KeyError
            _check_scan_cache[folder] = (mtime, names)
        for f in names:
            if not is_standard_filename(f):
                bad.append((os.path.join(folder, f), f))

    if folders is not None:
        for folder in folders:
            _scan_one(folder)
        return bad
    for root, dirs, files in os.walk(base_dir):
        # 剪枝：不进入隐藏目录与保留目录（.workbuddy、登记、__pycache__、测试副本等）。
        # 仅 continue 跳过当前目录时 os.walk 仍会递归整棵子树，剪枝后完全不遍历
        dirs[:] = [d for d in dirs if not d.startswith('.') and d not in SKIP_SCAN_DIRS]
        rel = os.path.relpath(root, base_dir)
        # 跳过隐藏目录与保留目录（.workbuddy、登记、__pycache__、测试副本等）
        if rel == '.' or rel.startswith('.') or rel.split(os.sep)[0] in SKIP_SCAN_DIRS:
            continue
        _scan_one(root)
    return bad


def smart_rename_folder(folder, base_dir=None):
    """
    对一个文件夹内的图片执行智能重命名（规范命名；不做缩放/方向摆正）。
    - 配对原图与 -改（容错扩展名）
    - 已标准编号的保留；未编号的按放入时间升序分配新序号（从已用最大+1 起）
    - 两阶段重命名（临时名）防冲突；目标名冲突时加 _1/_2 后缀兜底
    返回重命名文件数。纯重命名操作，不删除任何文件。
    """
    import uuid
    if base_dir is None:
        base_dir = BASE_DIR
    try:
        image_files = [f for f in os.listdir(folder)
                       if os.path.splitext(f)[1].lower() in IMAGE_EXTENSIONS]
    except OSError:
        return 0
    if not image_files:
        return 0

    file_times = {f: get_file_added_time(os.path.join(folder, f)) for f in image_files}
    rel_root = os.path.relpath(folder, base_dir)
    if rel_root in ('', '.'):
        return 0
    prefix = '-'.join(rel_root.split(os.sep)) + '-'

    # 配对：原图 与 -改（-改 找不到原图则作为孤儿独立配对）
    pairs = {}
    for f in image_files:
        name, ext = os.path.splitext(f)
        is_mod = name.endswith('-改')
        if is_mod:
            base_name = name[:-2]
            orig_f = None
            for check_ext in IMAGE_EXTENSIONS:
                if base_name + check_ext in image_files:
                    orig_f = base_name + check_ext
                    break
            orig_id = orig_f if orig_f else f"__orphan_{f}"
        else:
            orig_id = f
        if orig_id not in pairs:
            pairs[orig_id] = {'orig': None, 'mod': None, 'time': float('inf'), 'num': None}
        if is_mod:
            pairs[orig_id]['mod'] = f
            if pairs[orig_id]['orig'] is None:
                pairs[orig_id]['time'] = file_times[f]
        else:
            pairs[orig_id]['orig'] = f
            pairs[orig_id]['time'] = file_times[f]

    used_nums = set()
    needs_action = []
    for p_id, p in pairs.items():
        orig_f, mod_f = p['orig'], p['mod']
        if orig_f:
            nm, _ = os.path.splitext(orig_f)
            if nm.startswith(prefix) and nm[len(prefix):].isdigit():
                p['num'] = int(nm[len(prefix):])
        if mod_f and p['num'] is None:
            nm, _ = os.path.splitext(mod_f)
            if nm.startswith(prefix):
                core = nm[len(prefix):]
                if core.endswith('-改') and core[:-2].isdigit():
                    p['num'] = int(core[:-2])
        if p['num'] is not None:
            used_nums.add(p['num'])
        else:
            needs_action.append(p)

    needs_action.sort(key=lambda x: x['time'])
    next_num = max(used_nums) + 1 if used_nums else 1
    for p in needs_action:
        while next_num in used_nums:
            next_num += 1
        p['num'] = next_num
        used_nums.add(next_num)
        next_num += 1

    # 重命名计划（两阶段防冲突）：按**文件**独立判断是否需要重命名。
    # 规则：已编号文件（文件名本身解析出标准编号）**保持原名**（不补零/不改号，
    # 历史约定）；只有未编号文件才重命名到分配到的编号。
    # 修复历史 bug：原实现"整对跳过"导致未编号的 -改 图（如 xxx-改.jpg）配对后
    # 因同对原图已编号而不进 needs_action，永不被重命名（监控器每 5 秒持续上报
    # 不规范命名且反复修复无效）。改为按文件独立判断后仍保持"已编号不动"语义。
    rename_steps = []
    for p_id, p in pairs.items():
        num = p['num']
        if num is None:
            continue
        if p['orig']:
            nm, ext = os.path.splitext(p['orig'])
            if nm.startswith(prefix) and nm[len(prefix):].isdigit():
                pass   # 原图已编号（含补零 01.jpg）：保持原名，不补零/不改号
            else:
                target = f"{prefix}{num}{ext}"     # 编号 1,2,3 顺延（不补零）
                if os.path.normpath(p['orig']) != os.path.normpath(target):
                    tmp = f"__tmp_{uuid.uuid4().hex}{ext}"
                    rename_steps.append((p['orig'], tmp))
                    rename_steps.append((tmp, target))
        if p['mod']:
            nm, ext = os.path.splitext(p['mod'])
            core = nm[len(prefix):] if nm.startswith(prefix) else ''
            if core.endswith('-改') and core[:-2].isdigit():
                pass   # -改 图已编号：保持原名
            else:
                target = f"{prefix}{num}-改{ext}"
                if os.path.normpath(p['mod']) != os.path.normpath(target):
                    tmp = f"__tmp_{uuid.uuid4().hex}{ext}"
                    rename_steps.append((p['mod'], tmp))
                    rename_steps.append((tmp, target))

    renamed = 0
    for old_name, new_name in rename_steps:
        old_path = os.path.join(folder, old_name)
        if not new_name.startswith("__tmp_"):
            new_path = os.path.join(folder, new_name)
            if os.path.exists(new_path) and os.path.normpath(old_path) != os.path.normpath(new_path):
                base_n, ext_n = os.path.splitext(new_name)
                counter = 1
                while os.path.exists(os.path.join(folder, f"{base_n}_{counter}{ext_n}")):
                    counter += 1
                new_name = f"{base_n}_{counter}{ext_n}"
                new_path = os.path.join(folder, new_name)
        else:
            new_path = os.path.join(folder, new_name)
        if os.path.normpath(old_path) != os.path.normpath(new_path):
            os.rename(old_path, new_path)
            renamed += 1
    if renamed:
        _check_scan_cache.pop(folder, None)   # 目录内容已变，失效该目录缓存
    return renamed


# ============================================================
#  学生文件夹检查（序号固定，工具不自动编号）
# ============================================================
def check_student_folders(base_dir=None):
    """
    扫描根目录顶层文件夹，返回 (格式不符列表, 名单内缺失列表, 名单外存在列表)。
    - 格式不符：不是 年份-序号-姓名 三段式（且非保留目录）——可删除候选
    - 名单内缺失：名单里有但磁盘上不存在——需用户自行创建/补文件夹
    - 名单外存在：磁盘上有但名单里没有（格式符合）——仅报告，不自动处理
    """
    if base_dir is None:
        base_dir = BASE_DIR
    bad, missing, extra = [], [], []
    if not os.path.isdir(base_dir):
        return bad, missing, extra
    disk_dirs = [d for d in os.listdir(base_dir) if os.path.isdir(os.path.join(base_dir, d))]
    disk_student = set()
    for d in disk_dirs:
        if d in RESERVED_NAMES or d.startswith('.'):
            continue
        if STUDENT_FOLDER_RE.match(d):
            disk_student.add(d)
        else:
            bad.append(d)   # 格式不符（可删除候选）
    expected = all_student_folder_names()
    missing = sorted(expected - disk_student)
    extra = sorted(disk_student - expected)
    return bad, missing, extra


def check_sub_folders(base_dir=None):
    """
    检查学生文件夹内部子结构是否合规、是否多余。
    预期结构：
       学生文件夹/第01~15讲/作业|课前小测|错题再练
       学生文件夹/考试            （不应有子目录）
       学生文件夹/打卡第01~10天   （不应有子目录）
    返回 (多余目录列表, 缺失目录列表)：
       extra = [(完整路径, 是否为空目录), ...]
       missing = [完整路径, ...]（缺失的预期目录，框架搭建器会补齐，仅报告）
    """
    if base_dir is None:
        base_dir = BASE_DIR
    extra, missing = [], []
    expected_top = set(LECTURES)
    expected_sub = set(LECTURE_SUB_TYPES)
    try:
        top_entries = os.listdir(base_dir)
    except OSError:
        return extra, missing
    for name in top_entries:
        p = os.path.join(base_dir, name)
        if not os.path.isdir(p) or not STUDENT_FOLDER_RE.match(name):
            continue
        try:
            have_top = {d for d in os.listdir(p) if os.path.isdir(os.path.join(p, d))}
        except OSError:
            continue
        # 一级：多余的目录（不在 讲次/考试/打卡 集合中）
        for d in sorted(have_top - expected_top):
            dp = os.path.join(p, d)
            extra.append((dp, is_empty_dir(dp)))
        # 缺失的预期目录（框架搭建器补齐，仅报告）
        for d in sorted(expected_top - have_top):
            missing.append(os.path.join(p, d))
        # 二级：讲次下的子类型；考试/打卡下不应有任何子目录
        for top in have_top & expected_top:
            top_p = os.path.join(p, top)
            if not os.path.isdir(top_p):
                continue
            try:
                have_sub = [d for d in os.listdir(top_p)
                            if os.path.isdir(os.path.join(top_p, d))]
            except OSError:
                continue
            if top in LECTURE_LECTURES:
                # 讲次下：只允许 作业/课前小测/错题再练
                for d in sorted(set(have_sub) - expected_sub):
                    dp = os.path.join(top_p, d)
                    extra.append((dp, is_empty_dir(dp)))
            else:
                # 考试/打卡天：不应有子文件夹
                for d in sorted(have_sub):
                    dp = os.path.join(top_p, d)
                    extra.append((dp, is_empty_dir(dp)))
    return extra, missing


def is_empty_dir(path):
    """目录是否为空（无任何文件/子目录）"""
    try:
        with os.scandir(path) as it:
            return next(it, None) is None
    except OSError:
        return False


def move_to_recycle_bin(path, fallback_dir=None):
    """
    把文件/文件夹移出根目录（用户已确认的删除操作，双保险不永久丢数据）：
    - Windows：优先移入系统回收站（ctypes SHFileOperationW，FOF_ALLOWUNDO，可恢复）
    - 回收站不可用时降级：移动到「_待清理」目录（从根目录消失，仍可恢复，由用户确认后手动删除）
    返回 'recycled'（回收站/非win删除）| 'moved'（降级移动）| 'failed'。
    """
    if not os.path.exists(path):
        return 'failed'
    try:
        if platform.system() == 'Windows':
            if _win_recycle(path):
                return 'recycled'
            # 回收站调用后源路径已消失 → 视为已处理（可到回收站确认）
            if not os.path.exists(path):
                return 'recycled'
            # 降级：移到待清理目录（绝不永久删除）
            fb = fallback_dir or os.path.join(BASE_DIR, '_待清理')
            os.makedirs(fb, exist_ok=True)
            dst = os.path.join(fb, os.path.basename(path))
            if os.path.exists(dst):
                # 同名冲突：追加毫秒级时间戳 + 递增序号，保证同秒并发降级也不重名
                # （历史 bug：秒级时间戳在同目录两个同名文件同一秒降级时，
                # 第二个 os.path.exists 检查仍为假 → shutil.move 抛 FileExistsError
                # → 整体返回 'failed'，第二个文件既没进回收站也没降级）
                stem, ext = os.path.splitext(dst)
                ts = str(int(time.time() * 1000))
                dst = f"{stem}_{ts}{ext}"
                i = 1
                while os.path.exists(dst):
                    dst = f"{stem}_{ts}_{i}{ext}"
                    i += 1
            shutil.move(path, dst)
            return 'moved'
        else:
            # 非 Windows：无回收站机制，永久删除（调用方必须已经过用户确认）
            if os.path.isdir(path):
                shutil.rmtree(path, ignore_errors=True)
            else:
                os.remove(path)
            return 'recycled'
    except Exception:
        return 'failed'


def _win_recycle(path):
    """Windows 回收站删除（FOF_ALLOWUNDO），纯 ctypes，无第三方依赖"""
    import ctypes
    from ctypes import wintypes

    class SHFILEOPSTRUCTW(ctypes.Structure):
        _fields_ = [
            ('hwnd', wintypes.HWND),
            ('wFunc', wintypes.UINT),
            ('pFrom', wintypes.LPCWSTR),
            ('pTo', wintypes.LPCWSTR),
            ('fFlags', ctypes.c_ushort),
            ('fAnyOperationsAborted', wintypes.BOOL),
            ('hNameMappings', wintypes.LPVOID),
            ('lpszProgressTitle', wintypes.LPCWSTR),
        ]

    FO_DELETE = 3
    FOF_ALLOWUNDO = 0x40      # 允许撤销 = 移入回收站而非永久删除
    FOF_NOCONFIRMATION = 0x10  # 不弹确认框（调用方已在 GUI 层确认）
    FOF_SILENT = 0x4

    op = SHFILEOPSTRUCTW()
    op.hwnd = None
    op.wFunc = FO_DELETE
    op.pFrom = path + '\x00\x00'   # 双 null 结尾（API 要求）
    op.fFlags = FOF_ALLOWUNDO | FOF_NOCONFIRMATION | FOF_SILENT
    result = ctypes.windll.shell32.SHFileOperationW(ctypes.byref(op))
    return result == 0
