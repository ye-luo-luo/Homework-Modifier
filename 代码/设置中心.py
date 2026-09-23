# -*- coding: utf-8 -*-
"""
设置中心 —— 作业修改器与情况监视器共用的统一设置窗口。

两边程序都可以打开同一个窗口，包含双方的设置：
- 监控器页：卡片字体/列数、弹幕时长、自动处理间隔、存储优化参数
- 修改器页：弹幕时长、绘图工具、文本框、评分、联排、快捷键（任意键录制+冲突检测）

保存时各自写入对应配置文件：
- 监控器设置 → .file_monitor_settings.json
- 修改器配置 → image_tool_config.json

打开方式：
    open_settings_window(master, source, apply_monitor=None, apply_modifier=None)
    source: 'monitor' / 'modifier'（当前程序；用于提示生效时机）
    apply_*: 保存后应用回调（当前程序即时生效；另一个程序下次启动生效）
"""
import copy
import os
import json
import re
import platform
import shutil
import sys
import time
import tkinter as tk
from tkinter import messagebox, ttk

# 与其余脚本共用同一数据目录（学生文件夹/名单/配置所在；程序与数据可分离，
# 数据目录由 common 统一解析：DSH_DATA_DIR 环境变量 > 配置目录 配置/data_dir.txt > 程序根目录）
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (BASE_DIR, GRADING_DIR, LECTURES, LECTURE_LECTURES,
                    LECTURE_SUB_TYPES, PROCESS_LOCK, STUDENTS, STUDENT_LECTURES,
                    atomic_write_json, clear_dir_scan_cache,
                    clear_filename_cache, is_student_folder, save_structure,
                    save_students_file, window_geometry, config_file_path)

MONITOR_SETTINGS_FILE = config_file_path('.file_monitor_settings.json')
MODIFIER_CONFIG_FILE = config_file_path('image_tool_config.json')

# 修改器固定功能占用的快捷键（冲突检测）
FIXED_SHORTCUT_SEQS = frozenset({'<Prior>', '<Next>', '<Control-z>', '<Control-y>',
                                 '<Delete>', '<Control-Z>', '<Control-Y>'})
DEFAULT_ACTION_SEQS = {
    'prev': '<Left>', 'next': '<Right>', 'save': '<Up>', 'tile': '<Control-t>'}


def _shortcut_identity(sequence):
    """快捷键冲突标识：单字母不区分大小写，修饰键顺序不影响结果。"""
    value = str(sequence or '').strip()
    if not (value.startswith('<') and value.endswith('>')):
        return value.lower()
    parts = value[1:-1].split('-')
    mods = []
    key = parts[-1].lower()
    for part in parts[:-1]:
        p = part.lower()
        if p in ('control', 'ctrl'):
            p = 'control'
        if p in ('alt', 'option'):
            p = 'alt'
        if p not in mods:
            mods.append(p)
    return '<' + '-'.join(sorted(mods) + [key]) + '>'


_FIXED_SHORTCUT_IDS = frozenset(_shortcut_identity(x) for x in FIXED_SHORTCUT_SEQS)
_DEFAULT_ACTION_IDS = {k: _shortcut_identity(v) for k, v in DEFAULT_ACTION_SEQS.items()}


def _load_json(path):
    try:
        with open(path, encoding='utf-8') as f:
            d = json.load(f)
        return d if isinstance(d, dict) else {}
    except Exception:
        return {}


def _save_json(path, data):
    tmp = path + '.tmp'
    try:
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        os.replace(tmp, path)
    except Exception:
        try:
            if os.path.exists(tmp):
                os.remove(tmp)
        except OSError:
            pass
        raise


def _dict_value(value):
    return value if isinstance(value, dict) else {}


def _safe_int_value(value, default):
    try:
        return int(value)
    except (TypeError, ValueError, tk.TclError):
        return default


def _safe_bool_value(value, default=False):
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


def _get_int(var, default):
    """安全读取整数设置：输入非法/空/TclError 时用 default 兜底。"""
    try:
        return int(var.get())
    except (ValueError, TypeError, tk.TclError):
        return default


def _clamp_int(var, default, minimum, maximum):
    return max(minimum, min(maximum, _get_int(var, default)))


_INVALID_NAME_CHARS = frozenset('<>:"/\\|?*,-')
_RESERVED_NAMES = frozenset(
    {'CON', 'PRN', 'AUX', 'NUL'} |
    {f'{prefix}{i}' for prefix in ('COM', 'LPT') for i in range(1, 10)})


def _validate_category_name(name, existing=()):
    """返回分类名校验错误；合法时返回空字符串。"""
    value = str(name).strip()
    if not value:
        return "分类名不能为空"
    if value != name or value.endswith('.'):
        return "分类名不能以空格或句点开头/结尾"
    if any(ord(ch) < 32 or ch in _INVALID_NAME_CHARS for ch in value):
        return "分类名不能包含 -、逗号、路径分隔符或 Windows 非法字符"
    if value.split('.')[0].upper() in _RESERVED_NAMES:
        return "该名称是 Windows 保留名称"
    if value in existing:
        return f"分类「{value}」已存在"
    if value in LECTURES:
        return "分类名不能与讲次、考试或打卡目录同名"
    return ''


def _category_dirs(name):
    """列出数据根中全部合法学生/讲次下的指定分类目录。"""
    result = []
    try:
        students = list(os.scandir(BASE_DIR))
    except OSError as e:
        raise RuntimeError(f"数据根目录无法扫描：{BASE_DIR}（{e}）") from e
    lectures = tuple(LECTURE_LECTURES)
    for student in students:
        try:
            if not student.is_dir() or not is_student_folder(student.name):
                continue
        except OSError as e:
            raise RuntimeError(f"学生目录状态无法读取：{student.path}（{e}）") from e
        for lecture in lectures:
            path = os.path.join(student.path, lecture, name)
            if os.path.isdir(path):
                result.append(path)
    return result


def _category_usage(name):
    dirs = _category_dirs(name)
    nonempty = files = 0
    for folder in dirs:
        folder_files = 0
        walk_errors = []
        for _root, _dirs, names in os.walk(folder, onerror=walk_errors.append):
            folder_files += len(names)
        if walk_errors:
            raise RuntimeError(f"分类目录无法完整扫描：{folder}（{walk_errors[0]}）")
        if folder_files:
            nonempty += 1
            files += folder_files
    return {'directories': len(dirs), 'nonempty': nonempty, 'files': files}


def _migrate_monitor_category_refs(config, renames, deleted):
    """同步迁移监视器当前分类、学生分类和反馈标记引用。"""
    for old, new in renames:
        if config.get('sub') == old:
            config['sub'] = new
        if config.get('student_cat') == old:
            config['student_cat'] = new
        feedback = config.get('feedback')
        if isinstance(feedback, list):
            updated = []
            for item in feedback:
                parts = str(item).split('|')
                if len(parts) == 3 and parts[2] == old:
                    parts[2] = new
                updated.append('|'.join(parts))
            config['feedback'] = updated
    if config.get('sub') in deleted:
        config['sub'] = ''
    if config.get('student_cat') in deleted:
        config['student_cat'] = ''
    if isinstance(config.get('feedback'), list):
        config['feedback'] = [item for item in config['feedback']
                              if not (len(str(item).split('|')) == 3 and
                                      str(item).split('|')[2] in deleted)]


def _category_change_plan(entries):
    """根据分类列表条目的 origin/name 生成改名、删除、新增计划。"""
    current_origins = {item['origin'] for item in entries if item['origin'] is not None}
    renames = [(item['origin'], item['name']) for item in entries
               if item['origin'] is not None and item['origin'] != item['name']]
    deleted = [name for name in LECTURE_SUB_TYPES if name not in current_origins]
    added = [item['name'] for item in entries if item['origin'] is None]
    return renames, deleted, added


def _renamed_category_filename(filename, old, new):
    """只替换文件名中最靠后的分类字段，避免同名学生姓名被改动。"""
    marker = f'-{old}-'
    if marker not in filename:
        return filename
    head, tail = filename.rsplit(marker, 1)
    return f'{head}-{new}-{tail}'


def _preflight_category_changes(renames):
    """改名前检查目标目录、目标文件名和评分键冲突。"""
    errors = []
    for old, new in renames:
        for src in _category_dirs(old):
            dst = os.path.join(os.path.dirname(src), new)
            if os.path.exists(dst):
                errors.append(f"目标目录已存在：{dst}")
                continue
            walk_errors = []
            for root, _dirs, names in os.walk(src, onerror=walk_errors.append):
                for filename in names:
                    if f'-{old}-' not in filename:
                        continue
                    target = _renamed_category_filename(filename, old, new)
                    if target != filename and os.path.exists(os.path.join(root, target)):
                        errors.append(f"目标文件已存在：{os.path.join(root, target)}")
            if walk_errors:
                errors.append(f"分类目录无法完整扫描：{src}（{walk_errors[0]}）")
        if os.path.isdir(GRADING_DIR):
            for filename in os.listdir(GRADING_DIR):
                if not filename.lower().endswith('.json'):
                    continue
                path = os.path.join(GRADING_DIR, filename)
                try:
                    with open(path, encoding='utf-8') as f:
                        data = json.load(f)
                    if not isinstance(data, dict):
                        raise ValueError("评分文件根节点不是对象")
                except Exception as e:
                    errors.append(f"评分文件无法读取：{path}（{e}）")
                    continue
                if old in data and new in data:
                    errors.append(f"评分文件已有目标分类：{path}")
    return errors


def _rename_category_on_disk(old, new):
    """迁移分类目录、标准图片文件名和评分 JSON；失败时回滚本次迁移。"""
    moved_dirs = []
    renamed_files = []
    grading_before = {}
    try:
        for src in _category_dirs(old):
            dst = os.path.join(os.path.dirname(src), new)
            os.rename(src, dst)
            moved_dirs.append((src, dst))
            for root, _dirs, names in os.walk(dst):
                for filename in names:
                    if f'-{old}-' not in filename:
                        continue
                    target = _renamed_category_filename(filename, old, new)
                    if target != filename:
                        old_path = os.path.join(root, filename)
                        new_path = os.path.join(root, target)
                        os.rename(old_path, new_path)
                        renamed_files.append((old_path, new_path))
        if os.path.isdir(GRADING_DIR):
            for filename in os.listdir(GRADING_DIR):
                if not filename.lower().endswith('.json'):
                    continue
                path = os.path.join(GRADING_DIR, filename)
                try:
                    with open(path, encoding='utf-8') as f:
                        data = json.load(f)
                    if not isinstance(data, dict):
                        raise ValueError("评分文件根节点不是对象")
                except Exception as e:
                    raise RuntimeError(f"评分文件无法读取：{path}（{e}）") from e
                if old in data:
                    grading_before[path] = dict(data)
                    data[new] = data.pop(old)
                    atomic_write_json(path, data, ensure_ascii=False, indent=2)
    except Exception:
        for path, data in grading_before.items():
            try:
                atomic_write_json(path, data, ensure_ascii=False, indent=2)
            except Exception:
                pass
        for old_path, new_path in reversed(renamed_files):
            try:
                if os.path.exists(new_path):
                    os.rename(new_path, old_path)
            except OSError:
                pass
        for src, dst in reversed(moved_dirs):
            try:
                if os.path.exists(dst) and not os.path.exists(src):
                    os.rename(dst, src)
            except OSError:
                pass
        raise


def _archive_category_on_disk(name):
    """删除分类时按原相对路径归档；评分归档先落盘，再改正式文件。"""
    dirs = _category_dirs(name)
    batch = os.path.join(BASE_DIR, '_待清理',
                         f"分类删除_{name}_{time.strftime('%Y%m%d_%H%M%S')}_{time.time_ns() % 1000000:06d}")
    moved = []
    grading_before = {}
    grading_after = {}
    grading_archive = {}
    try:
        if os.path.isdir(GRADING_DIR):
            for filename in os.listdir(GRADING_DIR):
                if not filename.lower().endswith('.json'):
                    continue
                path = os.path.join(GRADING_DIR, filename)
                try:
                    with open(path, encoding='utf-8') as f:
                        data = json.load(f)
                    if not isinstance(data, dict):
                        raise ValueError("评分文件根节点不是对象")
                except Exception as e:
                    raise RuntimeError(f"评分文件无法读取：{path}（{e}）") from e
                if name in data:
                    grading_before[path] = dict(data)
                    grading_archive[filename] = data[name]
                    changed = dict(data)
                    changed.pop(name)
                    grading_after[path] = changed
        if grading_archive:
            os.makedirs(batch, exist_ok=True)
            atomic_write_json(os.path.join(batch, '评分数据.json'), grading_archive,
                              ensure_ascii=False, indent=2)
        for src in dirs:
            rel = os.path.relpath(src, BASE_DIR)
            dst = os.path.join(batch, rel)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.move(src, dst)
            moved.append((src, dst))
        for path, data in grading_after.items():
            atomic_write_json(path, data, ensure_ascii=False, indent=2)
        return batch
    except Exception as original_error:
        rollback_errors = []
        for path, data in grading_before.items():
            try:
                atomic_write_json(path, data, ensure_ascii=False, indent=2)
            except Exception as e:
                rollback_errors.append(f"评分恢复失败：{path}（{e}）")
        for src, dst in reversed(moved):
            try:
                if os.path.exists(dst) and not os.path.exists(src):
                    os.makedirs(os.path.dirname(src), exist_ok=True)
                    shutil.move(dst, src)
            except OSError as e:
                rollback_errors.append(f"目录恢复失败：{src}（{e}）")
        if not rollback_errors:
            shutil.rmtree(batch, ignore_errors=True)
        if rollback_errors:
            raise RuntimeError(f"分类删除失败：{original_error}\n回滚不完整，请从 {batch} 恢复：\n" +
                               '\n'.join(rollback_errors)) from original_error
        raise


def _restore_category_archive(batch, name):
    """恢复一次尚未提交配置的分类删除归档，正式评分读取失败时拒绝覆盖。"""
    grading_path = os.path.join(batch, '评分数据.json')
    if os.path.isfile(grading_path):
        with open(grading_path, encoding='utf-8') as f:
            archived = json.load(f)
        if not isinstance(archived, dict):
            raise ValueError(f"评分归档格式无效：{grading_path}")
        for filename, value in archived.items():
            path = os.path.join(GRADING_DIR, filename)
            try:
                with open(path, encoding='utf-8') as f:
                    data = json.load(f)
                if not isinstance(data, dict):
                    raise ValueError("评分文件根节点不是对象")
            except Exception as e:
                raise RuntimeError(f"无法安全恢复评分文件：{path}（{e}）") from e
            if name not in data:
                data[name] = value
                atomic_write_json(path, data, ensure_ascii=False, indent=2)
    for student in os.listdir(batch) if os.path.isdir(batch) else ():
        student_dir = os.path.join(batch, student)
        if not os.path.isdir(student_dir):
            continue
        for lecture in os.listdir(student_dir):
            src = os.path.join(student_dir, lecture, name)
            if not os.path.isdir(src):
                continue
            dst = os.path.join(BASE_DIR, student, lecture, name)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.move(src, dst)
    shutil.rmtree(batch, ignore_errors=True)


def _ensure_structure_dirs(order, category_names, created=None):
    """为现有学生补齐本次配置中的讲次和讲次分类目录。"""
    created = created if created is not None else []
    try:
        students = list(os.scandir(BASE_DIR))
    except OSError:
        return created
    lecture_names = [x for x in order if re.match(r'^第\d+讲$', x)]
    for student in students:
        if not student.is_dir() or not is_student_folder(student.name):
            continue
        for lecture in order:
            lecture_dir = os.path.join(student.path, lecture)
            if not os.path.isdir(lecture_dir):
                os.makedirs(lecture_dir, exist_ok=True)
                created.append(lecture_dir)
            if lecture in lecture_names:
                for name in category_names:
                    target = os.path.join(lecture_dir, name)
                    if not os.path.isdir(target):
                        os.makedirs(target, exist_ok=True)
                        created.append(target)
    return created


def _ensure_category_dirs(names):
    """兼容旧调用：为已有学生的已有讲次目录补齐新增分类目录。"""
    created = []
    try:
        students = list(os.scandir(BASE_DIR))
    except OSError:
        return []
    for student in students:
        try:
            if not student.is_dir() or not is_student_folder(student.name):
                continue
        except OSError:
            continue
        for lecture in LECTURE_LECTURES:
            lecture_dir = os.path.join(student.path, lecture)
            if not os.path.isdir(lecture_dir):
                continue
            for name in names:
                target = os.path.join(lecture_dir, name)
                if not os.path.isdir(target):
                    os.makedirs(target, exist_ok=True)
                    created.append(target)
    return created


def _scrollable_tab(tab_frame):
    """把 Notebook tab 内容可滚动化：内容超高时出现垂直滚动条，可滚动查看/修改下方设置。
    返回内部 body frame（内容 grid/pack 在 body 上）。调用方把原 tab 变量重指返回值，
    既有代码无需改动即可获得滚动能力。鼠标滚轮仅在悬停本区域时接管，移出自动释放。"""
    canvas = tk.Canvas(tab_frame, highlightthickness=0)
    vsb = tk.Scrollbar(tab_frame, orient=tk.VERTICAL, command=canvas.yview)
    canvas.configure(yscrollcommand=vsb.set)
    vsb.pack(side=tk.RIGHT, fill=tk.Y)
    canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
    body = tk.Frame(canvas)
    body_id = canvas.create_window((0, 0), window=body, anchor='nw')
    body.bind('<Configure>', lambda _e: canvas.configure(scrollregion=canvas.bbox('all')))
    canvas.bind('<Configure>', lambda e: canvas.itemconfigure(body_id, width=e.width))

    def _wheel(e):
        canvas.yview_scroll(int(-e.delta / 120), 'units')

    def _bind_wheel(_e):
        canvas.bind_all('<MouseWheel>', _wheel)

    def _unbind_wheel(_e):
        canvas.unbind_all('<MouseWheel>')

    for w in (canvas, body):
        w.bind('<Enter>', _bind_wheel)
        w.bind('<Leave>', _unbind_wheel)
    return body


# ============================================================
#  快捷键录制（独立实现，不依赖修改器模块；供两侧设置窗口使用）
# ============================================================
_recording = False   # 录制监听中：主窗口全局 ESC 返回短路（防切页破坏 'all' 层录制监听残留）
_active_recordings = []   # 正在监听的 (win, listened) 列表：页面切走时统一清理

def cancel_recordings():
    """解除所有正在进行的快捷键录制监听（主窗口离开设置页时调用，防 'all' 层残留）。"""
    global _recording
    for win, listened in _active_recordings[:]:
        for seq in listened:
            try:
                win.unbind_all(seq)
            except Exception:
                pass
    _active_recordings.clear()
    _recording = False

def _build_shortcut_row(win, parent, row, label, action_key, var, key_vars, msg_label):
    """一行快捷键设置：只读显示 + 录制按钮（支持任意键/鼠标键/组合，冲突拒绝）"""
    tk.Label(parent, text=label).grid(row=row, column=0, padx=8, pady=5, sticky=tk.W)
    entry = tk.Entry(parent, textvariable=var, state='readonly', width=16)
    entry.grid(row=row, column=1, padx=5)
    btn = tk.Button(parent, text="设置", width=5)
    btn.grid(row=row, column=2, padx=5)

    def start_listening():
        global _recording
        btn.config(text="按下...")
        btn.focus_set()
        _recording = True
        listened = []
        _active_recordings.append([win, listened])

        def stop_listen():
            global _recording
            for seq in listened:
                try:
                    win.unbind_all(seq)
                except Exception:
                    pass
            listened.clear()
            try:
                if [win, listened] in _active_recordings:
                    _active_recordings.remove([win, listened])
            except Exception:
                pass
            btn.config(text="设置")
            _recording = False

        def finish(val):
            identity = _shortcut_identity(val)
            if identity in _FIXED_SHORTCUT_IDS or any(
                    action != action_key and identity == default_id
                    for action, default_id in _DEFAULT_ACTION_IDS.items()):
                msg_label.config(text=f"「{label}」：该键已被常驻默认功能占用，请换一个",
                                 fg='#cc4444')
                return   # 冲突：继续监听
            for k, v in key_vars.items():
                if k != action_key and _shortcut_identity(v.get()) == identity:
                    msg_label.config(text=f"「{label}」：该键已被「{k}」占用，请换一个", fg='#cc4444')
                    return
            stop_listen()
            var.set(val)
            msg_label.config(text='')

        def mod_prefix(state):
            p = ''
            if state & 0x4:
                p += 'Control-'
            if state & 0x1:
                p += 'Shift-'
            if state & 0x20000:
                p += 'Alt-'
            return p

        def on_key(ev):
            if ev.keysym in ('Shift_L', 'Shift_R', 'Control_L', 'Control_R',
                             'Alt_L', 'Alt_R', 'Meta_L', 'Meta_R', 'Caps_Lock'):
                return
            mods = ev.state & (0x4 | 0x1 | 0x20000)
            if ev.keysym == 'Escape' and not mods:
                stop_listen()
                return 'break'   # 阻断后续绑定（主窗口 ESC 返回），避免录制取消后误切页
            finish(f"<{mod_prefix(ev.state)}{ev.keysym}>")

        def mk_mouse(seq):
            def h(ev):
                try:
                    # 嵌入模式：win 是共享 root，录制期间指针可能落在主窗口任意控件上；
                    # 放宽 toplevel 判定（录制监听已用 grab 或页面级隔离），
                    # 但仍跳过明显输入控件（避免误录）。
                    top = ev.widget.winfo_toplevel()
                    if top is not win:
                        return
                    if ev.widget.winfo_class() in ('Entry', 'TEntry', 'Spinbox',
                                                   'TCombobox', 'Combobox',
                                                   'Listbox', 'TListbox'):
                        msg_label.config(text="指针请移到空白处再按（当前在输入控件上）", fg='#cc4444')
                        return
                except Exception:
                    return
                finish(f"<{mod_prefix(ev.state)}{seq}>")
            return h

        win.bind_all('<KeyPress>', on_key)   # bind_all 统一管理：stop_listen/cancel_recordings 用 unbind_all 可清除
        listened.append('<KeyPress>')
        seqs = ['Button-1', 'Button-2', 'Button-3',
                'Double-Button-1', 'Double-Button-2', 'Double-Button-3']
        if platform.system() == 'Windows':
            seqs += ['Button-4', 'Button-5', 'Button-6', 'Button-7',
                     'Button-8', 'Button-9', 'Double-Button-4', 'Double-Button-5']
        for seq in seqs:
            win.bind_all(f'<{seq}>', mk_mouse(seq))
            listened.append(f'<{seq}>')

    btn.config(command=start_listening)


def open_settings_window(master, source='modifier', apply_monitor=None, apply_modifier=None,
                         container=None, on_close=None, on_optimize=None):
    """打开统一设置窗口。source: 'monitor'/'modifier'。
    apply_monitor / apply_modifier：保存后的应用回调（当前程序即时生效）。
    container 提供时嵌入主窗口内容区（UI 挂 container，root 仅作 Tk，跳过 Toplevel/
    transient/grab）；on_close：嵌入模式关闭（保存/取消）回调（主窗口切回首页）。
    on_optimize：监控器页「立即优化」回调，接收刚校验的 storage 配置 dict。"""
    mon_cfg = _load_json(MONITOR_SETTINGS_FILE)
    mod_cfg = _load_json(MODIFIER_CONFIG_FILE)
    mon_existed = os.path.exists(MONITOR_SETTINGS_FILE)
    mod_existed = os.path.exists(MODIFIER_CONFIG_FILE)

    if container is None:
        win = tk.Toplevel(master)
        win.title("设置中心")
        # 窗口尺寸相对屏幕：宽度按屏幕比例缩放（最小 560），高度自适应用
        # （小屏幕下缩小，保证底部「保存/取消」栏不被挤出屏幕）
        try:
            max_h = win.winfo_screenheight() - 120
        except Exception:
            max_h = 640
        geo = window_geometry(win, 620, 640, max_ratio=0.9, min_w=560, min_h=400)
        w = int(geo.split('x')[0])
        win.geometry(f"{w}x{min(640, max_h)}")
        win.minsize(560, 420)
        win.transient(master)
        try:
            win.grab_set()
        except Exception:
            pass
        # 修复历史 bug：原实现 parent=master，全部设置内容被打包进 master 而非
        # 新弹窗 win——弹窗空白（"出现名为设置中心的弹窗但没有内容"）、内容却
        # 被塞进主窗口底部划分一块且无法关闭。独立模式 parent 必须指向 win。
        parent = win
    else:
        win = container.winfo_toplevel()
        parent = container
    # 保存/取消栏必须先打包（side=BOTTOM 固定底部），否则被后打包的
    # Notebook(expand 占满) 挤到 1px 高不可见（历史 bug：看不到保存按钮）
    bf = tk.Frame(parent)
    bf.pack(side=tk.BOTTOM, fill=tk.X, padx=12, pady=8)
    nb = ttk.Notebook(parent)
    nb.pack(fill=tk.BOTH, expand=True, padx=8, pady=8)

    # ================= 监控器页 =================
    tab_mon = tk.Frame(nb)
    nb.add(tab_mon, text=" 监控器 ")
    tab_mon = _scrollable_tab(tab_mon)   # 内容可滚动（超高时出现滚动条）
    storage = _dict_value(mon_cfg.get('storage'))
    m_font = tk.IntVar(value=_safe_int_value(mon_cfg.get('font_size'), 12))
    m_cols = tk.IntVar(value=_safe_int_value(mon_cfg.get('columns'), 3))
    m_danmaku = tk.IntVar(value=_safe_int_value(mon_cfg.get('danmaku_ms'), 3000))
    m_interval = tk.IntVar(value=_safe_int_value(mon_cfg.get('auto_interval_sec'), 5))
    m_enable = tk.BooleanVar(value=_safe_bool_value(storage.get('enabled'), True))
    m_compress = tk.IntVar(value=_safe_int_value(storage.get('compress_days'), 4))
    m_degrade = tk.IntVar(value=_safe_int_value(storage.get('degrade_days'), 7))
    m_thumb = tk.IntVar(value=_safe_int_value(storage.get('thumb_days'), 10))
    m_edge = tk.IntVar(value=_safe_int_value(storage.get('thumb_max_edge'), 640))

    row = 0
    tk.Label(tab_mon, text="卡片字体大小:").grid(row=row, column=0, sticky=tk.W, padx=8, pady=4)
    tk.Spinbox(tab_mon, from_=8, to=24, textvariable=m_font, width=6).grid(row=row, column=1, sticky=tk.W)
    row += 1
    tk.Label(tab_mon, text="卡片列数:").grid(row=row, column=0, sticky=tk.W, padx=8, pady=4)
    tk.Spinbox(tab_mon, from_=1, to=10, textvariable=m_cols, width=6).grid(row=row, column=1, sticky=tk.W)
    row += 1
    tk.Label(tab_mon, text="弹幕时长(毫秒):").grid(row=row, column=0, sticky=tk.W, padx=8, pady=4)
    tk.Spinbox(tab_mon, from_=1000, to=10000, increment=500, textvariable=m_danmaku, width=6).grid(row=row, column=1, sticky=tk.W)
    row += 1
    tk.Label(tab_mon, text="自动处理间隔(秒):").grid(row=row, column=0, sticky=tk.W, padx=8, pady=4)
    tk.Spinbox(tab_mon, from_=1, to=60, textvariable=m_interval, width=6).grid(row=row, column=1, sticky=tk.W)
    row += 1
    tk.Label(tab_mon, text="自动存储优化:", font=('', 10, 'bold')).grid(row=row, column=0, sticky=tk.W, padx=8, pady=(10, 2))
    tk.Checkbutton(tab_mon, text="启用（按天数分级压缩/降质/缩略）", variable=m_enable).grid(
        row=row, column=1, columnspan=2, sticky=tk.W, pady=(10, 2))
    row += 1
    for label, v, default in (("≥ 天压缩(quality 88)", m_compress, 4),
                              ("≥ 天降质(quality 60)", m_degrade, 7),
                              ("≥ 天缩略(长边 px)", m_thumb, 10)):
        tk.Label(tab_mon, text=label.replace('天', '')).grid(row=row, column=0, sticky=tk.W, padx=8, pady=2)
        tk.Spinbox(tab_mon, from_=0, to=365, textvariable=v, width=6).grid(row=row, column=1, sticky=tk.W)
        tk.Label(tab_mon, text="天（0=关闭）").grid(row=row, column=2, sticky=tk.W)
        row += 1
    tk.Label(tab_mon, text="缩略图长边(px):").grid(row=row, column=0, sticky=tk.W, padx=8, pady=2)
    tk.Spinbox(tab_mon, from_=200, to=2000, increment=80, textvariable=m_edge, width=6).grid(row=row, column=1, sticky=tk.W)
    row += 1
    # 存储优化入口（原监视器工具栏「🗜 存储优化」按钮功能迁移到设置中心）：
    # 监控器页提供「立即优化」，参数与自动优化一致（启用/天数/长边在下方设置）
    opt_btn_row = tk.Frame(tab_mon)
    opt_btn_row.grid(row=row, column=0, columnspan=3, sticky=tk.W, padx=8, pady=(4, 2))
    def _storage_values():
        old = mon_cfg.get('storage', {}) or {}
        old = dict(old) if isinstance(old, dict) else {}
        values = dict(old)
        values.update({
            'enabled': bool(m_enable.get()),
            'compress_days': _clamp_int(m_compress, old.get('compress_days', 4), 0, 365),
            'degrade_days': _clamp_int(m_degrade, old.get('degrade_days', 7), 0, 365),
            'thumb_days': _clamp_int(m_thumb, old.get('thumb_days', 10), 0, 365),
            'thumb_max_edge': _clamp_int(m_edge, old.get('thumb_max_edge', 640), 200, 2000),
        })
        active = [values[k] for k in ('compress_days', 'degrade_days', 'thumb_days') if values[k] > 0]
        if active != sorted(active):
            raise ValueError("存储优化天数应满足：压缩 ≤ 降质 ≤ 缩略（0 表示关闭）")
        return values

    def _optimize_now():
        if on_optimize is None:
            tk.messagebox.showinfo("立即优化", "请从正在运行的监视器中执行立即优化。", parent=win)
            return
        try:
            mon_cfg['storage'] = _storage_values()
            _save_json(MONITOR_SETTINGS_FILE, mon_cfg)
            on_optimize(mon_cfg['storage'])
        except Exception as e:
            tk.messagebox.showwarning("立即优化", str(e), parent=win)

    opt_btn = tk.Button(opt_btn_row, text="立即优化存储", bg='#d1e7dd', command=_optimize_now)
    opt_btn.pack(side=tk.LEFT)
    tk.Label(opt_btn_row, text="（按上方天数设置立即执行分级压缩/降质/缩略）",
             fg='#888888', font=('微软雅黑', 9)).pack(side=tk.LEFT, padx=6)
    row += 1
    tk.Label(tab_mon, text="⚠ 存储优化不可逆（降质/缩略后原画质无法恢复）",
             fg='#cc4444').grid(row=row, column=0, columnspan=3, sticky=tk.W, padx=8, pady=6)
    row += 1

    # ================= 复制内容设置（复制批改携带的内容，讲次/考试/打卡 分开记忆） =================
    cc_raw = mon_cfg.get('copy_content', {})
    cc_raw = cc_raw if isinstance(cc_raw, dict) else {}
    cc_keys = ('lecture', 'sub', 'capsule', 'image')
    cc_headers = ('讲次信息', '类型信息', '胶囊视频', '图片')
    cc_vars = {}
    text_template_var = tk.StringVar(value=str(cc_raw.get('text_template',
        cc_raw.get('identity_template', '{class}班 {seq}号 {name}的{lecture}的{sub}{capsule}'))))
    save_report_text_var = tk.BooleanVar(value=_safe_bool_value(cc_raw.get('save_report_text'), False))
    for scene in ('lecture', 'exam', 'checkin'):
        item = cc_raw.get(scene, {})
        item = item if isinstance(item, dict) else {}
        cc_vars[scene] = {k: tk.BooleanVar(value=_safe_bool_value(item.get(k), True))
                          for k in cc_keys}
    tk.Label(tab_mon, text="复制批改内容（默认全选；讲次/考试/打卡 分开设置，互不影响）:",
             font=('', 10, 'bold')).grid(row=row, column=0, columnspan=4, sticky=tk.W, padx=8, pady=(10, 2))
    row += 1
    tk.Label(tab_mon, text='场景').grid(row=row, column=0, sticky=tk.W, padx=(16, 8))
    for j, h in enumerate(cc_headers):
        tk.Label(tab_mon, text=h).grid(row=row, column=1 + j, sticky=tk.W, padx=4)
    row += 1
    for scene, label in (('lecture', '讲次'), ('exam', '考试'), ('checkin', '打卡')):
        tk.Label(tab_mon, text=label).grid(row=row, column=0, sticky=tk.W, padx=(16, 8))
        for j, k in enumerate(cc_keys):
            tk.Checkbutton(tab_mon, variable=cc_vars[scene][k]).grid(row=row, column=1 + j, padx=4)
        row += 1
    tk.Label(tab_mon, text="未勾选「图片」时仅复制文字；图片直接引用原批改文件，不建立汇报图片副本。",
             fg='#888888').grid(row=row, column=0, columnspan=4, sticky=tk.W, padx=8, pady=4)
    row += 1
    tk.Label(tab_mon, text="复制文字模板（字段：{class} {seq} {name} {lecture} {sub} {capsule}）:").grid(row=row, column=0, columnspan=2, sticky=tk.W, padx=8, pady=2)
    tk.Entry(tab_mon, textvariable=text_template_var, width=34).grid(row=row, column=2, columnspan=2, sticky=tk.W)
    row += 1
    tk.Checkbutton(tab_mon, text="额外保存情况说明.txt（会写入汇报目录）",
                   variable=save_report_text_var).grid(row=row, column=0, columnspan=4, sticky=tk.W, padx=8)

    # ================= 修改器页 =================
    tab_mod = tk.Frame(nb)
    nb.add(tab_mod, text=" 修改器 ")
    tab_mod = _scrollable_tab(tab_mod)   # 内容可滚动（超高时出现滚动条）
    tools = _dict_value(mod_cfg.get('tools'))
    t_vars = {}
    for mode, label in (('check', '勾'), ('cross', '叉'), ('line', '直线')):
        tool = _dict_value(tools.get(mode))
        mc = str(tool.get('color', 'red'))
        mw = _safe_int_value(tool.get('width'), 3)
        t_vars[mode] = (tk.StringVar(value=mc), tk.IntVar(value=mw))
    t_text = _dict_value(mod_cfg.get('textbox'))
    tb_text = tk.StringVar(value=str(t_text.get('text', '')))
    tb_font = tk.StringVar(value=str(t_text.get('font', 'KaiTi')))
    tb_size = tk.IntVar(value=_safe_int_value(t_text.get('size'), 20))
    tb_color = tk.StringVar(value=str(t_text.get('color', 'red')))
    g_cfg = _dict_value(mod_cfg.get('grading'))
    g_font = tk.StringVar(value=str(g_cfg.get('font', 'SimHei')))
    g_size = tk.IntVar(value=_safe_int_value(g_cfg.get('size'), 60))
    g_color = tk.StringVar(value=str(g_cfg.get('color', 'red')))
    tile = _dict_value(mod_cfg.get('tile'))
    tl_cols = tk.IntVar(value=_safe_int_value(tile.get('columns'), 2))
    tl_spacing = tk.IntVar(value=_safe_int_value(tile.get('spacing'), 0))
    tl_labels = tk.BooleanVar(value=_safe_bool_value(tile.get('show_labels')))
    tl_max = tk.IntVar(value=_safe_int_value(tile.get('max_count'), 50))
    tl_fill = tk.StringVar(value=str(tile.get('fill_mode', 'contain')))
    tl_keep = tk.BooleanVar(value=_safe_bool_value(tile.get('keep_drafts_on_group_switch'), True))
    m2_danmaku = tk.IntVar(value=_safe_int_value(mod_cfg.get('danmaku_ms'), 3000))
    sc = _dict_value(mod_cfg.get('shortcuts'))
    key_vars = {
        'prev': tk.StringVar(value=sc.get('prev', '<Left>')),
        'next': tk.StringVar(value=sc.get('next', '<Right>')),
        'save': tk.StringVar(value=sc.get('save', '<Up>')),
        'tile': tk.StringVar(value=sc.get('tile', '<Control-t>')),
    }
    msg_label = tk.Label(tab_mod, text='', fg='#cc4444')
    msg_label.grid(row=0, column=0, columnspan=3, sticky=tk.W, padx=8)

    row = 1
    tk.Label(tab_mod, text="弹幕时长(毫秒):").grid(row=row, column=0, sticky=tk.W, padx=8, pady=4)
    tk.Spinbox(tab_mod, from_=1000, to=10000, increment=500, textvariable=m2_danmaku, width=6).grid(row=row, column=1, sticky=tk.W)
    row += 1
    tk.Label(tab_mod, text="绘图工具（勾/叉/直线）:", font=('', 10, 'bold')).grid(
        row=row, column=0, sticky=tk.W, padx=8, pady=(8, 2))
    row += 1
    for mode, label in (('check', '勾'), ('cross', '叉'), ('line', '直线')):
        vc, vw = t_vars[mode]
        tk.Label(tab_mod, text=f"{label} 颜色:").grid(row=row, column=0, sticky=tk.W, padx=8)
        tk.Entry(tab_mod, textvariable=vc, width=10).grid(row=row, column=1, sticky=tk.W)
        tk.Label(tab_mod, text="线宽:").grid(row=row, column=2, sticky=tk.W)
        tk.Spinbox(tab_mod, from_=1, to=20, textvariable=vw, width=5).grid(row=row, column=3, sticky=tk.W)
        row += 1
    tk.Label(tab_mod, text="文本框:", font=('', 10, 'bold')).grid(row=row, column=0, sticky=tk.W, padx=8, pady=(8, 2))
    row += 1
    tk.Label(tab_mod, text="默认内容:").grid(row=row, column=0, sticky=tk.W, padx=8)
    tk.Entry(tab_mod, textvariable=tb_text, width=20).grid(row=row, column=1, columnspan=3, sticky=tk.W)
    row += 1
    tk.Label(tab_mod, text="字体:").grid(row=row, column=0, sticky=tk.W, padx=8)
    ttk.Combobox(tab_mod, textvariable=tb_font, width=14,
                 values=['KaiTi', '楷体', 'SimHei', 'Microsoft YaHei', 'SimSun', 'Arial']).grid(row=row, column=1, sticky=tk.W)
    tk.Label(tab_mod, text="字号:").grid(row=row, column=2, sticky=tk.W)
    tk.Spinbox(tab_mod, from_=8, to=200, textvariable=tb_size, width=5).grid(row=row, column=3, sticky=tk.W)
    row += 1
    tk.Label(tab_mod, text="颜色:").grid(row=row, column=0, sticky=tk.W, padx=8)
    tk.Entry(tab_mod, textvariable=tb_color, width=10).grid(row=row, column=1, sticky=tk.W)
    row += 1
    tk.Label(tab_mod, text="评分:", font=('', 10, 'bold')).grid(row=row, column=0, sticky=tk.W, padx=8, pady=(8, 2))
    row += 1
    tk.Label(tab_mod, text="字体:").grid(row=row, column=0, sticky=tk.W, padx=8)
    ttk.Combobox(tab_mod, textvariable=g_font, width=14,
                 values=['SimHei', 'Microsoft YaHei', 'SimSun', 'KaiTi', 'Arial']).grid(row=row, column=1, sticky=tk.W)
    tk.Label(tab_mod, text="字号:").grid(row=row, column=2, sticky=tk.W)
    tk.Spinbox(tab_mod, from_=16, to=200, textvariable=g_size, width=5).grid(row=row, column=3, sticky=tk.W)
    row += 1
    tk.Label(tab_mod, text="颜色:").grid(row=row, column=0, sticky=tk.W, padx=8)
    tk.Entry(tab_mod, textvariable=g_color, width=10).grid(row=row, column=1, sticky=tk.W)
    row += 1
    tk.Label(tab_mod, text="联排:", font=('', 10, 'bold')).grid(row=row, column=0, sticky=tk.W, padx=8, pady=(8, 2))
    row += 1
    tk.Label(tab_mod, text="列数:").grid(row=row, column=0, sticky=tk.W, padx=8)
    tk.Spinbox(tab_mod, from_=1, to=6, textvariable=tl_cols, width=5).grid(row=row, column=1, sticky=tk.W)
    tk.Label(tab_mod, text="间距:").grid(row=row, column=2, sticky=tk.W)
    tk.Spinbox(tab_mod, from_=0, to=100, textvariable=tl_spacing, width=5).grid(row=row, column=3, sticky=tk.W)
    row += 1
    tk.Label(tab_mod, text="最大张数:").grid(row=row, column=0, sticky=tk.W, padx=8)
    tk.Spinbox(tab_mod, from_=5, to=200, textvariable=tl_max, width=5).grid(row=row, column=1, sticky=tk.W)
    tk.Label(tab_mod, text="填充:").grid(row=row, column=2, sticky=tk.W)
    ttk.Combobox(tab_mod, textvariable=tl_fill, width=8,
                 values=['contain', 'cover']).grid(row=row, column=3, sticky=tk.W)
    row += 1
    tk.Checkbutton(tab_mod, text="显示序号标签", variable=tl_labels).grid(row=row, column=0, columnspan=2, sticky=tk.W, padx=8)
    row += 1
    tk.Checkbutton(tab_mod, text="联排切换组时保留未保存的批改（取消后切组不保留草稿）",
                   variable=tl_keep).grid(row=row, column=0, columnspan=2, sticky=tk.W, padx=8)
    row += 1
    tk.Label(tab_mod, text="附加快捷键（常驻默认键仍保留；点击\"设置\"后按键，Esc 取消）:",
             font=('', 10, 'bold')).grid(row=row, column=0, columnspan=4, sticky=tk.W, padx=8, pady=(8, 2))
    row += 1
    for k, label in (('prev', '上一张'), ('next', '下一张'), ('save', '保存图片'), ('tile', '联排开关')):
        _build_shortcut_row(win, tab_mod, row, label, k, key_vars[k], key_vars, msg_label)
        row += 1
    tk.Label(tab_mod, text="文本框输入时快捷键自动屏蔽；与固定功能冲突的键不可用。",
             fg='#666666').grid(row=row, column=0, columnspan=4, sticky=tk.W, padx=8, pady=4)

    # ================= 目录结构页（讲次/考试/打卡 数量与顺序自定义） =================
    tab_struct = tk.Frame(nb)
    nb.add(tab_struct, text=" 目录结构 ")
    tab_struct = _scrollable_tab(tab_struct)

    # 数量初始值从当前 LECTURES 派生（用户可改后"生成默认顺序"重排）
    s_lec = tk.IntVar(value=len([x for x in LECTURES if re.match(r'^第\d+讲$', x)]))
    s_exam = tk.IntVar(value=len([x for x in LECTURES if x.startswith('考试')]))
    s_ck = tk.IntVar(value=len([x for x in LECTURES if x.startswith('打卡')]))
    category_entries = [{'name': name, 'origin': name} for name in LECTURE_SUB_TYPES]

    r = 0
    tk.Label(tab_struct, text="讲次/考试/打卡 的数量与顺序自定义（保存后重启程序生效）:",
             font=('', 10, 'bold')).grid(row=r, column=0, columnspan=4, sticky=tk.W, padx=8, pady=(4, 2))
    r += 1
    tk.Label(tab_struct, text="讲次数:").grid(row=r, column=0, sticky=tk.W, padx=8)
    tk.Spinbox(tab_struct, from_=0, to=99, textvariable=s_lec, width=5).grid(row=r, column=1, sticky=tk.W)
    tk.Label(tab_struct, text="考试数:").grid(row=r, column=2, sticky=tk.W, padx=(12, 0))
    tk.Spinbox(tab_struct, from_=0, to=99, textvariable=s_exam, width=5).grid(row=r, column=3, sticky=tk.W)
    r += 1
    tk.Label(tab_struct, text="打卡天数:").grid(row=r, column=0, sticky=tk.W, padx=8)
    tk.Spinbox(tab_struct, from_=0, to=99, textvariable=s_ck, width=5).grid(row=r, column=1, sticky=tk.W)
    r += 1
    tk.Label(tab_struct, text="目录顺序（选中项可上移/下移/删除；「插入考试」在选中项后插入；"
                              "「按数量生成」用上方数量重排默认顺序）:",
             fg='#666666').grid(row=r, column=0, columnspan=4, sticky=tk.W, padx=8, pady=(6, 2))
    r += 1
    ol = tk.Listbox(tab_struct, height=9, exportselection=False)
    ol.grid(row=r, column=0, columnspan=2, sticky='nsew', padx=(8, 0))
    vsb2 = tk.Scrollbar(tab_struct, orient=tk.VERTICAL, command=ol.yview)
    vsb2.grid(row=r, column=2, sticky='ns')
    ol.configure(yscrollcommand=vsb2.set)
    for x in LECTURES:
        ol.insert(tk.END, x)

    def _move_item(delta):
        sel = ol.curselection()
        if not sel:
            return
        i, j = sel[0], sel[0] + delta
        if not (0 <= j < ol.size()):
            return
        val = ol.get(i)
        ol.delete(i)
        ol.insert(j, val)
        ol.selection_set(j)
        ol.activate(j)

    def _del_item():
        sel = ol.curselection()
        if sel:
            ol.delete(sel[0])

    def _insert_exam():
        sel = ol.curselection()
        i = sel[0] + 1 if sel else ol.size()
        nums = [int(m.group(1) or 0) for x in ol.get(0, tk.END)
                if (m := re.match(r'考试(\d*)$', x))]
        have_plain = any(x == '考试' for x in ol.get(0, tk.END))
        n = (max(nums) + 1) if nums else 1
        name = '考试' if (n == 1 and not have_plain) else f'考试{n}'
        ol.insert(i, name)

    def _gen_order():
        ol.delete(0, tk.END)
        n1, n2, n3 = _get_int(s_lec, 15), _get_int(s_exam, 1), _get_int(s_ck, 10)
        n1 = max(0, min(99, n1)); n2 = max(0, min(99, n2)); n3 = max(0, min(99, n3))
        order = [f"第{i:02d}讲" for i in range(1, n1 + 1)]
        order += ['考试'] if n2 == 1 else [f"考试{i}" for i in range(1, n2 + 1)]
        order += [f"打卡第{i:02d}天" for i in range(1, n3 + 1)]
        for x in order:
            ol.insert(tk.END, x)

    btn_col = tk.Frame(tab_struct)
    btn_col.grid(row=r, column=3, sticky='n', padx=(4, 8), pady=2)
    tk.Button(btn_col, text="上移", width=8, command=lambda: _move_item(-1)).pack(pady=1)
    tk.Button(btn_col, text="下移", width=8, command=lambda: _move_item(1)).pack(pady=1)
    tk.Button(btn_col, text="删除", width=8, command=_del_item).pack(pady=1)
    tk.Button(btn_col, text="插入考试", width=8, command=_insert_exam).pack(pady=1)
    tk.Button(btn_col, text="按数量生成", width=8, command=_gen_order).pack(pady=1)
    tk.Label(tab_struct, text="提示：考试可插在讲次中（如第05讲后）；目录名形如 第01讲/考试/考试1/打卡第01天",
             fg='#888888').grid(row=r + 1, column=0, columnspan=4, sticky=tk.W, padx=8, pady=4)

    # 讲次分类单项管理。origin 用于保存时区分新增、改名和删除。
    cat_row = r + 2
    tk.Label(tab_struct, text="讲次分类:", font=('', 10, 'bold')).grid(
        row=cat_row, column=0, columnspan=4, sticky=tk.W, padx=8, pady=(10, 2))
    cat_lb = tk.Listbox(tab_struct, height=5, exportselection=False)
    cat_lb.grid(row=cat_row + 1, column=0, columnspan=2, sticky='nsew', padx=(8, 0), pady=2)

    def _refresh_categories(select=None):
        cat_lb.delete(0, tk.END)
        for item in category_entries:
            cat_lb.insert(tk.END, item['name'])
        if category_entries:
            idx = min(select if select is not None else 0, len(category_entries) - 1)
            cat_lb.selection_set(idx)
            cat_lb.activate(idx)

    def _add_category():
        value = _prompt_text("添加分类", "分类名称:")
        if value is None:
            return
        err = _validate_category_name(value, [item['name'] for item in category_entries])
        if err:
            tk.messagebox.showwarning("添加分类", err, parent=win)
            return
        category_entries.append({'name': value, 'origin': None})
        _refresh_categories(len(category_entries) - 1)

    def _rename_category():
        sel = cat_lb.curselection()
        if not sel:
            tk.messagebox.showwarning("修改分类", "请先选择分类", parent=win)
            return
        idx = sel[0]
        old = category_entries[idx]['name']
        value = _prompt_text("修改分类", "新分类名称:", old)
        if value is None or value == old:
            return
        existing = [item['name'] for i, item in enumerate(category_entries) if i != idx]
        err = _validate_category_name(value, existing)
        if err:
            tk.messagebox.showwarning("修改分类", err, parent=win)
            return
        category_entries[idx]['name'] = value
        _refresh_categories(idx)

    def _delete_category():
        sel = cat_lb.curselection()
        if not sel:
            tk.messagebox.showwarning("删除分类", "请先选择分类", parent=win)
            return
        if len(category_entries) <= 1:
            tk.messagebox.showwarning("删除分类", "至少保留一个讲次分类", parent=win)
            return
        idx = sel[0]
        category_entries.pop(idx)
        _refresh_categories(max(0, idx - 1))

    def _move_category(delta):
        sel = cat_lb.curselection()
        if not sel:
            return
        i = sel[0]
        j = i + delta
        if not 0 <= j < len(category_entries):
            return
        category_entries[i], category_entries[j] = category_entries[j], category_entries[i]
        _refresh_categories(j)

    cat_buttons = tk.Frame(tab_struct)
    cat_buttons.grid(row=cat_row + 1, column=3, sticky='n', padx=(4, 8), pady=2)
    tk.Button(cat_buttons, text="添加", width=8, command=_add_category).pack(pady=1)
    tk.Button(cat_buttons, text="修改", width=8, command=_rename_category).pack(pady=1)
    tk.Button(cat_buttons, text="删除", width=8, command=_delete_category).pack(pady=1)
    tk.Button(cat_buttons, text="上移", width=8, command=lambda: _move_category(-1)).pack(pady=1)
    tk.Button(cat_buttons, text="下移", width=8, command=lambda: _move_category(1)).pack(pady=1)
    tk.Label(tab_struct,
             text="添加会补齐现有目录；修改会迁移目录、标准文件名和评分；删除会归档到 _待清理。",
             fg='#888888').grid(row=cat_row + 2, column=0, columnspan=4,
                                 sticky=tk.W, padx=8, pady=(2, 6))
    _refresh_categories()

    # ================= 班级/学生页（自定义增删改班级与学生，保存到 名单.json） =================
    tab_std = tk.Frame(nb)
    nb.add(tab_std, text=" 班级/学生 ")
    tab_std = _scrollable_tab(tab_std)

    r = 0
    tk.Label(tab_std, text="班级/学生管理（保存到 名单.json，重启后生效）:",
             font=('', 10, 'bold')).grid(row=r, column=0, columnspan=4, sticky=tk.W, padx=8, pady=(4, 2))
    r += 1
    tk.Label(tab_std, text="班级:").grid(row=r, column=0, sticky=tk.W, padx=8, pady=2)
    tk.Label(tab_std, text="学生(序号-姓名):").grid(row=r, column=2, sticky=tk.W, padx=(16, 0), pady=2)
    r += 1
    cls_lb = tk.Listbox(tab_std, height=7, exportselection=False)
    cls_lb.grid(row=r, column=0, columnspan=2, sticky='nsew', padx=8)
    cls_lb.bind('<<ListboxSelect>>', lambda _e: _refresh_students())
    cls_bt = tk.Frame(tab_std)
    cls_bt.grid(row=r, column=1, sticky='e', padx=8)
    std_lb = tk.Listbox(tab_std, height=7, exportselection=False)
    std_lb.grid(row=r, column=2, columnspan=2, sticky='nsew', padx=8)
    vsb3 = tk.Scrollbar(tab_std, orient=tk.VERTICAL, command=std_lb.yview)
    vsb3.grid(row=r, column=3, sticky='ns')
    std_lb.configure(yscrollcommand=vsb3.set)
    r += 1
    for c in sorted(STUDENTS.keys()):
        cls_lb.insert(tk.END, c)

    def _refresh_students():
        std_lb.delete(0, tk.END)
        sel = cls_lb.curselection()
        if not sel:
            return
        c = cls_lb.get(sel[0])
        for seq, name in STUDENTS.get(c, []):
            std_lb.insert(tk.END, f"{int(seq):02d}-{name}")

    def _roster_snapshot():
        return copy.deepcopy(STUDENTS), copy.deepcopy(STUDENT_LECTURES)

    def _save_roster(snapshot=None):
        try:
            save_students_file()
            return True
        except Exception as e:
            if snapshot is not None:
                STUDENTS.clear(); STUDENTS.update(snapshot[0])
                STUDENT_LECTURES.clear(); STUDENT_LECTURES.update(snapshot[1])
            tk.messagebox.showwarning("保存", f"名单保存失败，内存修改已撤销：{e}", parent=win)
            return False

    def _edit_student_dialog(cls, seq0=None, name0=None):
        dlg = tk.Toplevel(win)
        dlg.title("学生")
        dlg.transient(win)
        dlg.grab_set()
        tk.Label(dlg, text="序号:").grid(row=0, column=0, padx=8, pady=6)
        se = tk.Entry(dlg, width=8)
        se.insert(0, str(seq0) if seq0 is not None else '')
        se.grid(row=0, column=1, padx=4)
        tk.Label(dlg, text="姓名:").grid(row=1, column=0, padx=8, pady=6)
        ne = tk.Entry(dlg, width=14)
        ne.insert(0, name0 or '')
        ne.grid(row=1, column=1, padx=4)
        out = {}
        def ok():
            try:
                s = int(se.get().strip())
            except ValueError:
                tk.messagebox.showwarning("提示", "序号须为数字", parent=dlg)
                return
            n = ne.get().strip()
            if not n:
                tk.messagebox.showwarning("提示", "姓名不能为空", parent=dlg)
                return
            out['seq'], out['name'] = s, n
            dlg.destroy()
        tk.Button(dlg, text="确定", command=ok, width=6).grid(row=2, column=0, pady=8)
        tk.Button(dlg, text="取消", command=dlg.destroy, width=6).grid(row=2, column=1)
        dlg.wait_window()
        return out or None

    def _prompt_text(title, label, initial=''):
        dlg = tk.Toplevel(win)
        dlg.title(title)
        dlg.transient(win)
        dlg.grab_set()
        tk.Label(dlg, text=label).grid(row=0, column=0, padx=8, pady=6)
        ev = tk.Entry(dlg, width=20)
        ev.insert(0, initial)
        ev.grid(row=0, column=1, padx=4)
        out = {}
        def ok():
            v = ev.get().strip()
            if not v:
                tk.messagebox.showwarning("提示", "内容不能为空", parent=dlg)
                return
            out['v'] = v
            dlg.destroy()
        tk.Button(dlg, text="确定", command=ok, width=6).grid(row=1, column=0, pady=8)
        tk.Button(dlg, text="取消", command=dlg.destroy, width=6).grid(row=1, column=1)
        dlg.wait_window()
        return out.get('v')

    def _add_cls():
        v = _prompt_text("添加班级", "班级名（如 2001）:")
        if not v or v in STUDENTS:
            return
        snapshot = _roster_snapshot()
        STUDENTS[v] = []
        if _save_roster(snapshot):
            cls_lb.insert(tk.END, v)
            cls_lb.selection_clear(0, tk.END)
            cls_lb.selection_set(tk.END)
            _refresh_students()

    def _ren_cls():
        sel = cls_lb.curselection()
        if not sel:
            return
        old = cls_lb.get(sel[0])
        v = _prompt_text("重命名班级", "新班级名（如 2001）:", old)
        if not v or v == old or v in STUDENTS:
            return
        snapshot = _roster_snapshot()
        STUDENTS[v] = STUDENTS.pop(old)
        for (year, seq), lectures in list(STUDENT_LECTURES.items()):
            if year == old:
                STUDENT_LECTURES[(v, seq)] = lectures
                del STUDENT_LECTURES[(year, seq)]
        if _save_roster(snapshot):
            cls_lb.delete(sel[0])
            cls_lb.insert(sel[0], v)
            cls_lb.selection_set(sel[0])
            _refresh_students()

    def _del_cls():
        sel = cls_lb.curselection()
        if not sel:
            return
        c = cls_lb.get(sel[0])
        if not tk.messagebox.askyesno("删除班级", f"删除班级「{c}」及其全部学生？", parent=win):
            return
        snapshot = _roster_snapshot()
        STUDENTS.pop(c, None)
        for key in [key for key in STUDENT_LECTURES if key[0] == c]:
            STUDENT_LECTURES.pop(key, None)
        if _save_roster(snapshot):
            cls_lb.delete(sel[0])
            _refresh_students()

    def _add_std():
        sel = cls_lb.curselection()
        if not sel:
            tk.messagebox.showwarning("提示", "请先选择班级", parent=win)
            return
        c = cls_lb.get(sel[0])
        d = _edit_student_dialog(c)
        if not d:
            return
        entries = STUDENTS.setdefault(c, [])
        if any(int(e[0]) == d['seq'] for e in entries):
            tk.messagebox.showwarning("添加学生", f"序号 {d['seq']:02d} 已存在", parent=win)
            return
        entries = list(entries)
        entries.append((d['seq'], d['name']))
        entries.sort(key=lambda e: e[0])
        snapshot = _roster_snapshot()
        STUDENTS[c] = entries
        if _save_roster(snapshot):
            _refresh_students()

    def _edit_std():
        sel_c = cls_lb.curselection(); sel_s = std_lb.curselection()
        if not sel_c or not sel_s:
            tk.messagebox.showwarning("提示", "请先选择班级和要修改的学生", parent=win)
            return
        c = cls_lb.get(sel_c[0])
        seq, name = STUDENTS[c][sel_s[0]]
        d = _edit_student_dialog(c, seq, name)
        if not d:
            return
        if d['seq'] != int(seq) and any(int(e[0]) == d['seq'] for e in STUDENTS[c]):
            tk.messagebox.showwarning("修改学生", f"序号 {d['seq']:02d} 已存在", parent=win)
            return
        snapshot = _roster_snapshot()
        entries = [e for e in STUDENTS[c] if int(e[0]) != int(seq)]
        entries.append((d['seq'], d['name']))
        entries.sort(key=lambda e: e[0])
        STUDENTS[c] = entries
        if d['seq'] != int(seq):
            lectures = STUDENT_LECTURES.pop((c, int(seq)), None)
            if lectures is not None:
                STUDENT_LECTURES[(c, d['seq'])] = lectures
        if _save_roster(snapshot):
            _refresh_students()

    def _del_std():
        sel_c = cls_lb.curselection(); sel_s = std_lb.curselection()
        if not sel_c or not sel_s:
            tk.messagebox.showwarning("提示", "请先选择班级和要删除的学生", parent=win)
            return
        c = cls_lb.get(sel_c[0])
        seq, name = STUDENTS[c][sel_s[0]]
        if not tk.messagebox.askyesno("删除学生", f"删除学生「{name}」？", parent=win):
            return
        snapshot = _roster_snapshot()
        STUDENTS[c] = [e for e in STUDENTS[c] if int(e[0]) != int(seq)]
        STUDENT_LECTURES.pop((c, int(seq)), None)
        if _save_roster(snapshot):
            _refresh_students()

    def _edit_std_lectures():
        """设置学生自定义「学习讲次」（默认全部；勾选部分则只学习这些讲次）。
        弹出多选列表：可选 讲次/考试/打卡 目录项。"""
        sel_c = cls_lb.curselection(); sel_s = std_lb.curselection()
        if not sel_c or not sel_s:
            tk.messagebox.showwarning("提示", "请先选择班级和要修改的学生", parent=win)
            return
        c = cls_lb.get(sel_c[0])
        seq, name = STUDENTS[c][sel_s[0]]
        import common as _common
        cur = set(_common.get_student_lectures(c, seq) or [])

        dlg = tk.Toplevel(win)
        dlg.title(f"学习讲次 - {name}")
        dlg.transient(win)
        dlg.grab_set()
        tk.Label(dlg, text="勾选该学生学习的内容（默认全部；不勾选=全部）:",
                 font=('微软雅黑', 9)).pack(anchor=tk.W, padx=10, pady=(10, 4))
        frame = tk.Frame(dlg)
        frame.pack(fill=tk.BOTH, expand=True, padx=10)
        # 可选目录项 = 完整目录顺序（讲次/考试/打卡）
        check_vars = {}
        for i, item in enumerate(LECTURES):
            v = tk.BooleanVar(value=(item in cur))
            cb = tk.Checkbutton(frame, text=item, variable=v, anchor=tk.W)
            cb.grid(row=i // 3, column=i % 3, sticky=tk.W, padx=4, pady=2)
            check_vars[item] = v

        btns = tk.Frame(dlg)
        btns.pack(fill=tk.X, padx=10, pady=8)

        def _all():
            for v in check_vars.values():
                v.set(True)

        def _none():
            for v in check_vars.values():
                v.set(False)

        tk.Button(btns, text="全选", command=_all, width=6).pack(side=tk.LEFT)
        tk.Button(btns, text="全不选", command=_none, width=6).pack(side=tk.LEFT, padx=4)

        def _ok():
            sel = [item for item, v in check_vars.items() if v.get()]
            try:
                _common.set_student_lectures(c, seq, sel)
            except Exception as e:
                tk.messagebox.showwarning("保存", f"保存失败：{e}", parent=dlg)
                return
            dlg.destroy()

        tk.Button(btns, text="确定", command=_ok, width=6,
                  bg='lightgreen').pack(side=tk.RIGHT)
        tk.Button(btns, text="取消", command=dlg.destroy, width=6).pack(side=tk.RIGHT, padx=4)

    cbt = tk.Frame(tab_std)
    cbt.grid(row=r, column=0, columnspan=2, sticky='w', padx=8, pady=3)
    tk.Button(cbt, text="添加班级", command=_add_cls).pack(side=tk.LEFT, padx=2)
    tk.Button(cbt, text="重命名", command=_ren_cls).pack(side=tk.LEFT, padx=2)
    tk.Button(cbt, text="删除班级", command=_del_cls).pack(side=tk.LEFT, padx=2)
    sbt = tk.Frame(tab_std)
    sbt.grid(row=r, column=2, columnspan=2, sticky='w', padx=8, pady=3)
    tk.Button(sbt, text="添加学生", command=_add_std).pack(side=tk.LEFT, padx=2)
    tk.Button(sbt, text="修改学生", command=_edit_std).pack(side=tk.LEFT, padx=2)
    tk.Button(sbt, text="删除学生", command=_del_std).pack(side=tk.LEFT, padx=2)
    tk.Button(sbt, text="学习讲次", command=_edit_std_lectures).pack(side=tk.LEFT, padx=2)
    tk.Label(tab_std, text="提示：学生格式为 序号-姓名（序号固定，可跳号）；删除班级/学生不可撤销；"
                              "「学习讲次」默认全部，可选部分讲次", fg='#888888').grid(
        row=r + 1, column=0, columnspan=4, sticky=tk.W, padx=8, pady=2)

    # ================= 保存 =================
    def save_and_close():
        # 每次点击保存都从窗口打开时的原始配置派生候选值，取消确认不会污染下次保存。
        mon_new = copy.deepcopy(mon_cfg)
        mod_new = copy.deepcopy(mod_cfg)
        # ---- 监控器设置（数字字段容错：非法输入保留原配置值，保存总能成功） ----
        try:
            mon_new.update({
                'font_size': _clamp_int(m_font, mon_cfg.get('font_size', 12), 8, 24),
                'columns': _clamp_int(m_cols, mon_cfg.get('columns', 3), 1, 10),
                'danmaku_ms': _clamp_int(m_danmaku, mon_cfg.get('danmaku_ms', 3000), 1000, 10000),
                'auto_interval_sec': _clamp_int(m_interval, mon_cfg.get('auto_interval_sec', 5), 1, 60),
                'storage': _storage_values(),
                'copy_content': {
                    **_dict_value(mon_cfg.get('copy_content')),
                    **{scene: {k: bool(v.get()) for k, v in vars_.items()}
                       for scene, vars_ in cc_vars.items()},
                    'text_template': text_template_var.get().strip() or '{class}班 {seq}号 {name}的{lecture}的{sub}{capsule}',
                    'save_report_text': bool(save_report_text_var.get()),
                },
            })
        except Exception as e:
            tk.messagebox.showwarning("保存", f"监控器设置保存失败：{e}", parent=win)
            return
        # ---- 修改器配置（同样容错） ----
        try:
            color_values = [vc.get().strip() for vc, _vw in t_vars.values()]
            color_values += [tb_color.get().strip(), g_color.get().strip()]
            for value in color_values:
                try:
                    win.winfo_rgb(value)
                except tk.TclError:
                    raise ValueError(f"无效颜色：{value or '(空)'}")
            fill_mode = tl_fill.get().strip()
            if fill_mode not in ('contain', 'cover'):
                raise ValueError("联排填充只能是 contain 或 cover")
            shortcut_ids = [_shortcut_identity(v.get()) for v in key_vars.values()]
            if any(not x for x in shortcut_ids) or len(shortcut_ids) != len(set(shortcut_ids)):
                raise ValueError("快捷键不能为空或重复（字母不区分大小写）")
            if any(x in _FIXED_SHORTCUT_IDS for x in shortcut_ids):
                raise ValueError("快捷键与固定切图、撤销、重做或删除功能冲突")
            for action, identity in zip(key_vars, shortcut_ids):
                if any(other != action and identity == default_id
                       for other, default_id in _DEFAULT_ACTION_IDS.items()):
                    raise ValueError("附加快捷键不能占用其他动作的常驻默认键")

            tools_new = dict(_dict_value(mod_new.get('tools')))
            for mode, (vc, vw) in t_vars.items():
                old = dict(tools_new.get(mode, {}) or {})
                old.update({'color': vc.get().strip(),
                            'width': _clamp_int(vw, old.get('width', 3), 1, 20)})
                tools_new[mode] = old
            textbox_new = dict(_dict_value(mod_new.get('textbox')))
            textbox_new.update({'text': tb_text.get(), 'font': tb_font.get(),
                                 'size': _clamp_int(tb_size, textbox_new.get('size', 20), 8, 200),
                                 'color': tb_color.get().strip()})
            grading_new = dict(_dict_value(mod_new.get('grading')))
            grading_new.update({'font': g_font.get(),
                                'size': _clamp_int(g_size, grading_new.get('size', 60), 16, 200),
                                'color': g_color.get().strip()})
            tile_new = dict(_dict_value(mod_new.get('tile')))
            tile_new.update({'columns': _clamp_int(tl_cols, tile_new.get('columns', 2), 1, 6),
                             'spacing': _clamp_int(tl_spacing, tile_new.get('spacing', 0), 0, 100),
                             'show_labels': bool(tl_labels.get()),
                             'max_count': _clamp_int(tl_max, tile_new.get('max_count', 50), 5, 200),
                             'fill_mode': fill_mode,
                             'keep_drafts_on_group_switch': bool(tl_keep.get())})
            shortcuts_new = dict(_dict_value(mod_new.get('shortcuts')))
            shortcuts_new.update({k: v.get() for k, v in key_vars.items()})
            mod_new.update({
                'danmaku_ms': _clamp_int(m2_danmaku, mod_new.get('danmaku_ms', 3000), 1000, 10000),
                'tools': tools_new,
                'textbox': textbox_new,
                'grading': grading_new,
                'tile': tile_new,
                'shortcuts': shortcuts_new,
            })
        except Exception as e:
            tk.messagebox.showwarning("保存", f"修改器设置保存失败：{e}", parent=win)
            return
        # ---- 目录结构与讲次分类 ----
        candidate_configs_written = False
        structure_committed = False
        old_order = list(LECTURES)
        old_subs = list(LECTURE_SUB_TYPES)
        try:
            order_new = [ol.get(i) for i in range(ol.size())]
            subs_new = [item['name'] for item in category_entries]
            if not order_new:
                raise ValueError("目录顺序不能为空")
            if not subs_new:
                raise ValueError("至少保留一个讲次分类")
            if len(set(subs_new)) != len(subs_new):
                raise ValueError("讲次分类不能重复")
            for i, name in enumerate(subs_new):
                err = _validate_category_name(name, subs_new[:i])
                if err:
                    raise ValueError(err)

            renames, deleted, added = _category_change_plan(category_entries)
            _migrate_monitor_category_refs(mon_new, renames, deleted)
            fallback_sub = subs_new[0]
            if not mon_new.get('sub'):
                mon_new['sub'] = fallback_sub
            if not mon_new.get('student_cat'):
                mon_new['student_cat'] = fallback_sub
            errors = _preflight_category_changes(renames)
            if errors:
                shown = '\n'.join(errors[:5])
                if len(errors) > 5:
                    shown += f"\n……另有 {len(errors) - 5} 项冲突"
                raise ValueError("分类迁移存在目标冲突，请先处理：\n" + shown)

            for old, new in renames:
                usage = _category_usage(old)
                if usage['files'] and not tk.messagebox.askyesno(
                        "确认修改分类",
                        f"分类「{old}」包含 {usage['nonempty']} 个非空目录、"
                        f"{usage['files']} 个文件。\n\n"
                        f"将改名为「{new}」，并同步修改目录、标准文件名和评分数据。继续？",
                        parent=win):
                    return
            for name in deleted:
                usage = _category_usage(name)
                if usage['files'] and not tk.messagebox.askyesno(
                        "确认删除分类",
                        f"分类「{name}」包含 {usage['nonempty']} 个非空目录、"
                        f"{usage['files']} 个文件。\n\n"
                        "这些目录和评分数据会移入数据根目录的 _待清理，可恢复。继续？",
                        parent=win):
                    return

            # 候选配置先原子写入；后续结构操作失败时恢复窗口打开时的原始内容。
            _save_json(MONITOR_SETTINGS_FILE, mon_new)
            try:
                _save_json(MODIFIER_CONFIG_FILE, mod_new)
                candidate_configs_written = True
            except Exception:
                if mon_existed:
                    _save_json(MONITOR_SETTINGS_FILE, mon_cfg)
                else:
                    try: os.remove(MONITOR_SETTINGS_FILE)
                    except OSError: pass
                raise

            structure_changed = order_new != list(LECTURES)
            if renames or deleted or added or structure_changed:
                if not PROCESS_LOCK.acquire(blocking=False):
                    raise RuntimeError("图片正在被其他任务处理，请稍后再保存分类")
                completed_renames = []
                archives = []
                created_dirs = []
                try:
                    for old, new in renames:
                        _rename_category_on_disk(old, new)
                        completed_renames.append((old, new))
                    for name in deleted:
                        batch = _archive_category_on_disk(name)
                        archives.append((batch, name))
                    _ensure_structure_dirs(order_new, subs_new, created_dirs)
                    save_structure(order_new, subs_new)
                    structure_committed = True
                except Exception:
                    for path in reversed(created_dirs):
                        try:
                            os.rmdir(path)  # 新建目录应为空；有并发文件时保留，绝不删文件
                        except OSError:
                            pass
                    rollback_errors = []
                    for batch, name in reversed(archives):
                        try:
                            _restore_category_archive(batch, name)
                        except Exception as e:
                            rollback_errors.append(f"分类「{name}」归档恢复失败：{e}")
                    for old, new in reversed(completed_renames):
                        try:
                            _rename_category_on_disk(new, old)
                        except Exception as e:
                            rollback_errors.append(f"分类「{new}」恢复为「{old}」失败：{e}")
                    if rollback_errors:
                        raise RuntimeError("结构操作失败且回滚不完整：\n" + '\n'.join(rollback_errors))
                    raise
                finally:
                    PROCESS_LOCK.release()
            else:
                save_structure(order_new, subs_new)
                structure_committed = True
            # 缓存刷新不是持久化事务的一部分；失败时数据已正确提交，下次扫描会自然刷新。
            try:
                clear_filename_cache()
                clear_dir_scan_cache()
            except Exception:
                pass
        except Exception as e:
            if structure_committed:
                try:
                    save_structure(old_order, old_subs)
                except Exception:
                    pass
            if candidate_configs_written:
                try:
                    if mon_existed: _save_json(MONITOR_SETTINGS_FILE, mon_cfg)
                    else: os.remove(MONITOR_SETTINGS_FILE)
                except OSError:
                    pass
                try:
                    if mod_existed: _save_json(MODIFIER_CONFIG_FILE, mod_cfg)
                    else: os.remove(MODIFIER_CONFIG_FILE)
                except OSError:
                    pass
            tk.messagebox.showwarning("保存", f"目录结构或配置保存失败：{e}", parent=win)
            return
        # 当前仍存活的独立页面先应用，再关闭设置窗口；主窗口回首页时会按新配置重建页面。
        if apply_monitor:
            try:
                apply_monitor()
            except Exception as e:
                tk.messagebox.showwarning("应用设置", f"监视器设置已保存，但即时应用失败：{e}", parent=win)
        if apply_modifier:
            try:
                apply_modifier()
            except Exception as e:
                tk.messagebox.showwarning("应用设置", f"修改器设置已保存，但即时应用失败：{e}", parent=win)
        if on_close is not None:
            on_close()
        else:
            win.destroy()

    # bf 已在窗口构建开头创建并 pack(side=BOTTOM)，这里只填充按钮
    tk.Button(bf, text="保存", command=save_and_close, bg='lightgreen',
              width=10).pack(side=tk.RIGHT, padx=6)
    tk.Button(bf, text="取消",
              command=(on_close if on_close is not None else win.destroy),
              width=8).pack(side=tk.RIGHT)
    tk.Label(bf, text=f"（{'当前程序生效' if source == 'modifier' else ''}"
                      f" 修改器设置即时生效；监控器设置即时生效）",
             fg='#888888').pack(side=tk.LEFT)
    return win


if __name__ == '__main__':
    root = tk.Tk()
    root.withdraw()
    open_settings_window(root, 'modifier')
    root.mainloop()
