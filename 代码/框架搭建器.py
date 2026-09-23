# -*- coding: utf-8 -*-
"""
框架搭建器 - 名单与实际文件夹的对照管理工具（GUI）

用途：
    - 按权威名单创建/补齐学生文件夹结构（名单有 · 磁盘无 → 可创建文件夹）
    - 名单与实际文件夹全面对照，逐项自由选择处理方式：
        【名单有 · 磁盘无】→ 创建文件夹  / 删除名单条目
        【磁盘有 · 名单无】→ 加入名单    / 删除文件夹（可恢复）
    - 保留原命令行模式（python 框架搭建器.py --cli）：
        全量补齐 + 清理空的不合规/多余文件夹 + 差异报告

结构：
    学生文件夹 (年份-序号-姓名)
    ├── 第01~15讲 / 作业 / 课前小测 / 错题再练
    ├── 考试 （无子文件夹）
    └── 打卡第01~10天 （无子文件夹）

规则（重要）：
    - 名单与序号固定在 common.STUDENTS 中（名单.json）
    - 序号固定，不因人数变化自动补号/插号
    - 删除文件夹一律移入回收站（可恢复）；非空文件夹需二次确认
    - 删除名单条目只改 名单.json，绝不删除磁盘文件
"""
import os
import sys
import re

# 确保能导入同目录的公共模块
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (BASE_DIR, STUDENTS, LECTURES as lectures,
                    LECTURE_LECTURES, LECTURE_SUB_TYPES as sub_folders,
                    check_student_folders, check_sub_folders,
                    is_empty_dir, move_to_recycle_bin, PROJECT_VERSION,
                    STUDENT_FOLDER_RE, add_students_from_folders,
                    remove_students_by_folder, window_geometry,
                    save_students_file, student_folder_name,
                    get_student_lectures, set_student_lectures,
                    STUDENT_LECTURES)


# ============================================================
#  通用：确保单个学生的完整文件夹结构存在（GUI/命令行共用）
# ============================================================
def ensure_student_folder(year, seq, name, base_dir=None):
    """确保某个学生的完整文件夹结构存在（不存在则创建，含讲次/子类型/考试/打卡）。
    返回本次新建的目录数（学生文件夹 + 讲次 + 子类型），全已存在则返回 0。"""
    if base_dir is None:
        base_dir = BASE_DIR
    added = 0
    student_folder = f"{year}-{int(seq):02d}-{name}"
    student_path = os.path.join(base_dir, student_folder)
    if not os.path.isdir(student_path):
        os.makedirs(student_path, exist_ok=True)
        added += 1
    for lecture in lectures:
        lecture_path = os.path.join(student_path, lecture)
        if not os.path.isdir(lecture_path):
            os.makedirs(lecture_path, exist_ok=True)
            added += 1
        if lecture in LECTURE_LECTURES:
            for sub in sub_folders:
                sub_path = os.path.join(lecture_path, sub)
                if not os.path.isdir(sub_path):
                    os.makedirs(sub_path, exist_ok=True)
                    added += 1
    return added


# ============================================================
#  原命令行功能（--cli 保留，不改行为）
# ============================================================
def build_structure(base_dir=None):
    """
    创建/补齐学生文件夹结构（复用 ensure_student_folder）。
    返回 (新建学生数, 补齐的老学生数, 完整跳过数)。
    """
    if base_dir is None:
        base_dir = BASE_DIR
    created, repaired, skipped = 0, 0, 0
    for year, entries in STUDENTS.items():
        for seq, name in entries:
            student_folder = f"{year}-{int(seq):02d}-{name}"
            existed = os.path.isdir(os.path.join(base_dir, student_folder))
            added = ensure_student_folder(year, seq, name, base_dir)
            if not existed:
                created += 1
            elif added > 0:
                repaired += 1
            else:
                skipped += 1
    return created, repaired, skipped


def clean_irregular_folders(base_dir=None):
    """
    去除不合规文件夹（安全约束：只删空文件夹，含文件的一律不动）：
    - 空的不合规文件夹：询问用户后移入回收站（可恢复）
    - 含文件的不合规文件夹：仅报告，请用户手动处理（绝不删除/重命名）
    返回 (删除数, 含文件未处理数)。
    """
    if base_dir is None:
        base_dir = BASE_DIR
    bad, _, _ = check_student_folders(base_dir)
    if not bad:
        return 0, 0
    empty_bad = [d for d in bad if is_empty_dir(os.path.join(base_dir, d))]
    empty_bad_set = set(empty_bad)
    nonempty_bad = [d for d in bad if d not in empty_bad_set]
    removed = 0
    if empty_bad:
        print("⚠️ 发现空的、不符合命名格式的文件夹（可安全删除）：")
        for d in empty_bad:
            print(f"   · {d}")
        ans = input("是否将这些空文件夹移入回收站？[y/N]: ").strip().lower()
        if ans in ('y', 'yes'):
            for d in empty_bad:
                r = move_to_recycle_bin(os.path.join(base_dir, d))
                if r in ('recycled', 'moved'):
                    print(f"   ✅ 已处理: {d}")
                    removed += 1
                else:
                    print(f"   ❌ 处理失败（请手动删除）: {d}")
    if nonempty_bad:
        print("⚠️ 以下文件夹不符合命名格式但含有文件，为安全起见未删除、未重命名：")
        for d in nonempty_bad:
            print(f"   · {d}")
        print("   请人工确认后手动处理。")
    return removed, len(nonempty_bad)


def clean_irregular_sub_folders(base_dir=None):
    """
    去除学生文件夹内部多余/不合规的子文件夹（安全约束同顶层：只删空的）：
    - 空的、多余的子文件夹：询问用户后移入回收站
    - 含文件的：仅报告，请用户手动处理（绝不删除/重命名）
    返回 (删除数, 含文件未处理数)。
    """
    if base_dir is None:
        base_dir = BASE_DIR
    extra, _ = check_sub_folders(base_dir)
    if not extra:
        return 0, 0
    empty_extra = [e for e in extra if e[1]]
    nonempty_extra = [e for e in extra if not e[1]]
    removed = 0
    if empty_extra:
        print("⚠️ 发现空的、多余的子文件夹（可安全删除）：")
        for path, _ in empty_extra:
            print(f"   · {os.path.relpath(path, base_dir)}")
        ans = input("是否将这些空的子文件夹移入回收站？[y/N]: ").strip().lower()
        if ans in ('y', 'yes'):
            for path, _ in empty_extra:
                r = move_to_recycle_bin(path)
                if r in ('recycled', 'moved'):
                    print(f"   ✅ 已处理: {os.path.relpath(path, base_dir)}")
                    removed += 1
                else:
                    print(f"   ❌ 处理失败（请手动删除）: {os.path.relpath(path, base_dir)}")
    if nonempty_extra:
        print("⚠️ 以下多余的子文件夹含有文件，为安全起见未删除、未重命名：")
        for path, _ in nonempty_extra:
            print(f"   · {os.path.relpath(path, base_dir)}")
        print("   请人工确认后手动处理。")
    return removed, len(nonempty_extra)


# ============================================================
#  GUI：名单信息 ↔ 文件夹信息 两边对照（默认入口）
#  - 名单信息（左栏）：完整名单全部学生，名单有磁盘无的条目**标红**
#  - 文件夹信息（右栏）：磁盘全部学生文件夹，磁盘有名单无的**标红**
#  - 右键名单条目：修改信息 / 设置学习讲次 / 删除名单条目
#  - 右键文件夹条目：加入名单 / 删除文件夹
#  - 按钮：重新扫描 / 添加班级 / 添加学生 / 检验文件夹（自动补齐缺失+删除多余）
# ============================================================
def main_gui(container=None):
    """单窗口整合：container=None 独立运行；container 提供时嵌入主窗口内容区
    （UI 挂 container，root 仅作 Tk，跳过 title/geometry/minsize/mainloop）。"""
    import tkinter as tk
    from tkinter import messagebox

    class FrameworkBuilderApp:
        def __init__(self, root, container=None):
            self.root = root
            self._container = container or root
            self._all_roster = []      # 名单全部学生文件夹名（有序）
            self._all_disk = []        # 磁盘全部学生文件夹名（有序）
            self._missing = set()      # 名单有·磁盘无（右栏红底）
            self._extra = set()        # 磁盘有·名单无（左栏红底）
            self._bad = []
            self._rows = []            # 对齐行：('class', year) 或 ('student', year, seq, 名单名, 磁盘名)
            self._build_ui()
            self.scan()

        # ---------- 界面 ----------
        def _build_ui(self):
            root = self.root
            parent = self._container
            if parent is root:   # 独立运行才设置窗口标题/尺寸
                root.title(f"框架搭建器 v{PROJECT_VERSION} - 名单与文件夹对照")
                root.geometry(window_geometry(root, 900, 580))   # 相对屏幕尺寸
                root.minsize(700, 420)

            # 顶部：操作行（按钮重构：添加班级/添加学生/检验文件夹）
            top = tk.Frame(parent)
            top.pack(fill=tk.X, padx=10, pady=(8, 4))
            tk.Button(top, text="🔄 重新扫描", command=self.scan,
                      font=('微软雅黑', 10)).pack(side=tk.LEFT)
            tk.Button(top, text="➕ 添加班级", command=self.add_class,
                      font=('微软雅黑', 10)).pack(side=tk.LEFT, padx=(8, 0))
            tk.Button(top, text="➕ 添加学生", command=self.add_student,
                      font=('微软雅黑', 10)).pack(side=tk.LEFT, padx=(8, 0))
            tk.Button(top, text="✅ 检验文件夹", command=self.check_folders,
                      bg='#d1e7dd', font=('微软雅黑', 10)).pack(side=tk.LEFT, padx=(8, 0))
            self.status_var = tk.StringVar(value="准备就绪")
            tk.Label(top, textvariable=self.status_var, fg='#555555',
                     font=('微软雅黑', 9)).pack(side=tk.RIGHT)

            # 中部：左右对照列表（按 班级+序号 逐行对齐，滚动同步）
            mid = tk.Frame(parent)
            mid.pack(fill=tk.BOTH, expand=True, padx=10, pady=4)

            # 共享垂直滚动条（先 pack 占最右侧，两侧列表共用 → 滑动同步）
            sb = tk.Scrollbar(mid, orient=tk.VERTICAL)
            sb.pack(side=tk.RIGHT, fill=tk.Y, pady=4)
            self._shared_sb = sb

            # ---- 左栏：名单信息 ----
            self.left_frame = tk.LabelFrame(mid, text="📋 名单信息（红底=名单缺此学生）",
                                            font=('微软雅黑', 10))
            self.left_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
            self.lb_roster = tk.Listbox(self.left_frame, selectmode=tk.EXTENDED,
                                        font=('微软雅黑', 10), activestyle='none')
            self.lb_roster.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=4, pady=4)
            self.lb_roster.bind('<Button-3>', self._on_roster_menu)
            self.lb_roster.bind('<MouseWheel>', self._on_shared_wheel)
            self.roster_count_var = tk.StringVar(value="0 项")
            tk.Label(self.left_frame, textvariable=self.roster_count_var,
                     fg='#888888', font=('微软雅黑', 9)).pack(anchor=tk.W, padx=6, pady=(0, 4))
            lb_btns = tk.Frame(self.left_frame)
            lb_btns.pack(fill=tk.X, padx=4, pady=(0, 4))
            tk.Button(lb_btns, text="创建文件夹", command=self.create_folders,
                      bg='#d1e7dd', font=('微软雅黑', 9)).pack(side=tk.LEFT, padx=2)
            tk.Button(lb_btns, text="删除名单条目", command=self.remove_entries,
                      bg='#ffcccc', font=('微软雅黑', 9)).pack(side=tk.LEFT, padx=2)

            # ---- 右栏：文件夹信息 ----
            self.right_frame = tk.LabelFrame(mid, text="📁 文件夹信息（红底=磁盘缺此文件夹）",
                                             font=('微软雅黑', 10))
            self.right_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(5, 0))
            self.lb_disk = tk.Listbox(self.right_frame, selectmode=tk.EXTENDED,
                                      font=('微软雅黑', 10), activestyle='none')
            self.lb_disk.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=4, pady=4)
            self.lb_disk.bind('<Button-3>', self._on_disk_menu)
            self.lb_disk.bind('<MouseWheel>', self._on_shared_wheel)
            self.disk_count_var = tk.StringVar(value="0 项")
            tk.Label(self.right_frame, textvariable=self.disk_count_var,
                     fg='#888888', font=('微软雅黑', 9)).pack(anchor=tk.W, padx=6, pady=(0, 4))
            rb_btns = tk.Frame(self.right_frame)
            rb_btns.pack(fill=tk.X, padx=4, pady=(0, 4))
            tk.Button(rb_btns, text="加入名单", command=self.add_entries,
                      bg='#d1e7dd', font=('微软雅黑', 9)).pack(side=tk.LEFT, padx=2)
            tk.Button(rb_btns, text="删除文件夹", command=self.remove_folders,
                      bg='#ffcccc', font=('微软雅黑', 9)).pack(side=tk.LEFT, padx=2)

            # 两侧滚动同步（同一滚动条 + 滚轮联动）
            sb.config(command=self._sync_scroll)
            self.lb_roster.config(yscrollcommand=sb.set)
            self.lb_disk.config(yscrollcommand=sb.set)

            # ---- 不合规文件夹（格式不符）展示：具体是哪个一清二楚 ----
            self.bad_frame = tk.LabelFrame(parent, text="⚠ 不合规文件夹（格式不符，未自动处理，请人工确认）",
                                           fg='#cc0000', font=('微软雅黑', 9))
            self.bad_var = tk.StringVar(value='')
            tk.Label(self.bad_frame, textvariable=self.bad_var, fg='#cc0000',
                     font=('微软雅黑', 9), anchor=tk.W, justify=tk.LEFT,
                     wraplength=760).pack(fill=tk.X, padx=8, pady=2)

        # ---------- 扫描（名单信息 + 文件夹信息 两边对照，班级+序号 逐行对齐） ----------
        def scan(self):
            self._bad, self.missing_list, self.extra_list = check_student_folders(BASE_DIR)
            self._bad = list(self._bad)
            self._missing = set(self.missing_list)
            self._extra = set(self.extra_list)
            # 名单全部学生（按年份分组排序）
            roster = []
            roster_map = {}   # {(year, seq): name}
            for year in sorted(STUDENTS.keys()):
                for seq, name in sorted(STUDENTS[year], key=lambda x: x[0]):
                    roster.append(student_folder_name(year, seq, name))
                    roster_map[(str(year), int(seq))] = name
            self._all_roster = roster
            self._roster_map = roster_map
            # 磁盘全部学生文件夹（符合固定学生格式）
            disk = []
            disk_map = {}   # {year: {seq: 文件夹名}}
            if os.path.isdir(BASE_DIR):
                for d in sorted(os.listdir(BASE_DIR)):
                    if d.startswith('.'):
                        continue
                    if os.path.isdir(os.path.join(BASE_DIR, d)) and STUDENT_FOLDER_RE.match(d):
                        disk.append(d)
                        m = STUDENT_FOLDER_RE.match(d)
                        disk_map.setdefault(m.group(1), {})[int(m.group(2))] = d
            self._all_disk = disk
            self._disk_map = disk_map
            # 对齐行：班级标题行 + 学生行（同一 班级+序号 一行，缺边留空白）
            years = sorted(set(list(STUDENTS.keys())) | set(disk_map.keys()))
            rows = []
            for year in years:
                rows.append(('class', year))   # 班级标题行
                seqs = sorted(set(seq for (y, seq) in roster_map if y == str(year)) |
                              set(disk_map.get(str(year), {}).keys()))
                for seq in seqs:
                    name = roster_map.get((str(year), seq))
                    rf = student_folder_name(year, seq, name) if name else None
                    df = disk_map.get(str(year), {}).get(seq)
                    rows.append(('student', year, seq, rf, df))
            self._rows = rows
            self._refresh_lists()
            parts = [f"名单 {len(STUDENTS)} 班 / {len(self._all_roster)} 人",
                     f"文件夹 {len(self._all_disk)} 个"]
            if self._missing:
                parts.append(f"{len(self._missing)} 项缺失(红底)")
            if self._extra:
                parts.append(f"{len(self._extra)} 项多余(红底)")
            if self._bad:
                parts.append(f"{len(self._bad)} 个不合规文件夹(下方红字)")
            if not self._missing and not self._extra and not self._bad:
                parts.append("名单与文件夹完全一致 ✓")
            self.status_var.set('，'.join(parts))
            # 不合规文件夹（格式不符）具体是哪个：显示在下方红字区域
            if self._bad:
                self.bad_var.set('、'.join(self._bad))
                self.bad_frame.pack(fill=tk.X, padx=10, pady=(0, 4))
            else:
                self.bad_frame.pack_forget()

        # ---------- 两侧滚动同步（同一滚动条 + 滚轮联动） ----------
        def _sync_scroll(self, *args):
            """滚动条拖动：同时滚 名单/文件夹 两边，保证逐行对齐"""
            try:
                self.lb_roster.yview(*args)
                self.lb_disk.yview(*args)
            except Exception:
                pass

        def _on_shared_wheel(self, e):
            """滚轮：两边同步滚动（与滚动条一致），保证逐行对齐"""
            try:
                d = -1 if e.delta > 0 else 1
                self.lb_roster.yview_scroll(d, 'units')
                self.lb_disk.yview_scroll(d, 'units')
            except Exception:
                pass
            return 'break'

        # ---------- 渲染（班级标题行 + 学生行；缺边留空白标红） ----------
        def _refresh_lists(self):
            self.lb_roster.delete(0, tk.END)
            self.lb_disk.delete(0, tk.END)
            for row in self._rows:
                if row[0] == 'class':
                    _, year = row
                    title = f"【{year} 班】"
                    self.lb_roster.insert(tk.END, title)
                    self.lb_disk.insert(tk.END, title)
                    self.lb_roster.itemconfig(tk.END, fg='#3366aa', selectforeground='#3366aa')
                    self.lb_disk.itemconfig(tk.END, fg='#3366aa', selectforeground='#3366aa')
                else:
                    _, _year, _seq, rf, df = row
                    # 左栏：名单名（缺=留空白 + 红底标红）
                    self.lb_roster.insert(tk.END, rf if rf else '')
                    if not rf:
                        self.lb_roster.itemconfig(tk.END, bg='#ffe0e0', fg='#cc0000')
                    # 右栏：文件夹名（缺=留空白 + 红底标红）
                    self.lb_disk.insert(tk.END, df if df else '')
                    if not df:
                        self.lb_disk.itemconfig(tk.END, bg='#ffe0e0', fg='#cc0000')
            self.roster_count_var.set(f"{len(self._all_roster)} 项"
                                      + (f"（{len(self._missing)} 红）" if self._missing else ''))
            self.disk_count_var.set(f"{len(self._all_disk)} 项"
                                    + (f"（{len(self._extra)} 红）" if self._extra else ''))

        # ---------- 右键菜单 ----------
        def _on_roster_menu(self, event):
            idx, row = self._row_at(self.lb_roster, event)
            if row is None or row[0] != 'student':
                return   # 班级标题行 / 空白行不弹菜单
            _, _year, _seq, rf, df = row
            self.lb_roster.selection_clear(0, tk.END)
            self.lb_roster.selection_set(idx)
            menu = tk.Menu(self.root, tearoff=0)
            if rf:
                menu.add_command(label="修改信息", command=lambda: self._edit_student_at(idx))
                menu.add_command(label="设置学习讲次", command=lambda: self._edit_lectures_at(idx))
                menu.add_separator()
                menu.add_command(label="删除名单条目", command=self.remove_entries)
            elif df:
                # 名单缺·磁盘有：把磁盘文件夹补进名单
                menu.add_command(label="加入名单", command=lambda: self._add_disk_folder(df))
            try:
                menu.tk_popup(event.x_root, event.y_root)
            finally:
                menu.grab_release()

        def _on_disk_menu(self, event):
            idx, row = self._row_at(self.lb_disk, event)
            if row is None or row[0] != 'student':
                return   # 班级标题行 / 空白行不弹菜单
            _, _year, _seq, rf, df = row
            self.lb_disk.selection_clear(0, tk.END)
            self.lb_disk.selection_set(idx)
            menu = tk.Menu(self.root, tearoff=0)
            if df:
                menu.add_command(label="加入名单", command=self.add_entries)
                menu.add_separator()
                menu.add_command(label="删除文件夹", command=self.remove_folders)
            elif rf:
                # 磁盘缺·名单有：补建磁盘文件夹
                menu.add_command(label="创建文件夹", command=lambda: self._create_roster_folder(rf))
            try:
                menu.tk_popup(event.x_root, event.y_root)
            finally:
                menu.grab_release()

        def _row_at(self, lb, event):
            """把 Listbox 事件坐标映射为 (索引, 对齐行)；越界/无对应行返回 (None, None)"""
            idx = lb.nearest(event.y)
            if idx < 0 or idx >= len(self._rows):
                return None, None
            return idx, self._rows[idx]

        # ---------- 添加班级 / 添加学生 ----------
        def add_class(self):
            dlg = tk.Toplevel(self.root)
            dlg.title("添加班级")
            dlg.transient(self.root)
            dlg.grab_set()
            tk.Label(dlg, text="班级号（年份，如 1993/1994/2011/2676）:",
                     font=('微软雅黑', 10)).pack(anchor=tk.W, padx=10, pady=(10, 2))
            e_year = tk.Entry(dlg, width=14, font=('微软雅黑', 10))
            e_year.pack(anchor=tk.W, padx=10)
            err = tk.StringVar()
            tk.Label(dlg, textvariable=err, fg='#cc0000', font=('微软雅黑', 9)).pack(
                anchor=tk.W, padx=10)

            def _ok():
                year = e_year.get().strip()
                if not re.fullmatch(r'\d{4}', year):
                    err.set("班级号须为 4 位数字年份")
                    return
                if year in STUDENTS:
                    err.set(f"班级 {year} 已存在")
                    return
                STUDENTS[year] = []
                save_students_file()
                dlg.destroy()
                self.scan()
                self.status_var.set(f"已添加班级 {year}")

            btns = tk.Frame(dlg)
            btns.pack(fill=tk.X, padx=10, pady=8)
            tk.Button(btns, text="确定", command=_ok, width=8,
                      bg='lightgreen').pack(side=tk.RIGHT)
            tk.Button(btns, text="取消", command=dlg.destroy, width=8).pack(side=tk.RIGHT, padx=4)

        def add_student(self):
            dlg = tk.Toplevel(self.root)
            dlg.title("添加学生")
            dlg.transient(self.root)
            dlg.grab_set()
            tk.Label(dlg, text="班级（年份）:", font=('微软雅黑', 10)).pack(
                anchor=tk.W, padx=10, pady=(10, 2))
            e_year = tk.Entry(dlg, width=14, font=('微软雅黑', 10))
            e_year.pack(anchor=tk.W, padx=10)
            tk.Label(dlg, text="序号（1~99，可跳号）:", font=('微软雅黑', 10)).pack(
                anchor=tk.W, padx=10, pady=(8, 2))
            e_seq = tk.Entry(dlg, width=14, font=('微软雅黑', 10))
            e_seq.pack(anchor=tk.W, padx=10)
            tk.Label(dlg, text="姓名:", font=('微软雅黑', 10)).pack(
                anchor=tk.W, padx=10, pady=(8, 2))
            e_name = tk.Entry(dlg, width=20, font=('微软雅黑', 10))
            e_name.pack(anchor=tk.W, padx=10)
            err = tk.StringVar()
            tk.Label(dlg, textvariable=err, fg='#cc0000', font=('微软雅黑', 9)).pack(
                anchor=tk.W, padx=10)

            def _ok():
                year = e_year.get().strip()
                seq = e_seq.get().strip()
                name = e_name.get().strip()
                if not re.fullmatch(r'\d{4}', year):
                    err.set("班级号须为 4 位数字年份")
                    return
                try:
                    seq_i = int(seq)
                except ValueError:
                    err.set("序号须为整数")
                    return
                if not (1 <= seq_i <= 99):
                    err.set("序号范围 1~99")
                    return
                if not name:
                    err.set("姓名不能为空")
                    return
                entries = STUDENTS.setdefault(year, [])
                if (seq_i, name) in entries:
                    err.set(f"学生 {year}-{seq_i:02d}-{name} 已存在")
                    return
                entries.append((seq_i, name))
                entries.sort(key=lambda x: x[0])
                save_students_file()
                dlg.destroy()
                self.scan()
                self.status_var.set(f"已添加学生 {year}-{seq_i:02d}-{name}")

            btns = tk.Frame(dlg)
            btns.pack(fill=tk.X, padx=10, pady=8)
            tk.Button(btns, text="确定", command=_ok, width=8,
                      bg='lightgreen').pack(side=tk.RIGHT)
            tk.Button(btns, text="取消", command=dlg.destroy, width=8).pack(side=tk.RIGHT, padx=4)

        # ---------- 检验文件夹（自动补齐缺失 + 删除多余，仅限固定学生格式类型） ----------
        def check_folders(self):
            if self._missing:
                if not messagebox.askyesno(
                        "补齐缺失文件夹",
                        f"将自动创建 {len(self._missing)} 个缺失的学生文件夹结构：\n\n"
                        + '\n'.join(sorted(self._missing)[:15])
                        + ('\n…' if len(self._missing) > 15 else ''),
                        parent=self.root):
                    return
            if self._extra:
                if not messagebox.askyesno(
                        "删除多余文件夹",
                        f"将 {len(self._extra)} 个「磁盘有·名单无」的文件夹移入回收站"
                        f"（仅限固定学生格式类型，可恢复）：\n\n"
                        + '\n'.join(sorted(self._extra)[:15])
                        + ('\n…' if len(self._extra) > 15 else ''),
                        parent=self.root):
                    return
            # 补齐缺失
            created = 0
            for d in sorted(self._missing):
                m = STUDENT_FOLDER_RE.match(d)
                if not m:
                    continue
                ensure_student_folder(m.group(1), int(m.group(2)), m.group(3))
                created += 1
            # 删除多余（仅固定学生格式类型文件夹）
            deleted = 0
            for d in sorted(self._extra):
                r = move_to_recycle_bin(os.path.join(BASE_DIR, d))
                if r in ('recycled', 'moved'):
                    deleted += 1
            self.status_var.set(f"检验完成：补齐缺失 {created} 个，删除多余 {deleted} 个")
            self.scan()

        # ---------- 修改信息 / 学习讲次（右键） ----------
        def _student_of(self, idx):
            """由对齐行索引解析 (班级, 序号, 姓名, 名单文件夹名)；
            非学生行 / 名单缺（左栏空白）/ 越界 返回 None"""
            if not (0 <= idx < len(self._rows)):
                return None
            row = self._rows[idx]
            if row[0] != 'student':
                return None
            rf = row[3]
            if not rf:
                return None
            m = STUDENT_FOLDER_RE.match(rf)
            if not m:
                return None
            return m.group(1), int(m.group(2)), m.group(3), rf

        def _edit_student_at(self, idx):
            info = self._student_of(idx)
            if not info:
                return
            year, seq, name, folder = info
            dlg = tk.Toplevel(self.root)
            dlg.title(f"修改信息 - {folder}")
            dlg.transient(self.root)
            dlg.grab_set()
            tk.Label(dlg, text="班级（年份）:", font=('微软雅黑', 10)).pack(
                anchor=tk.W, padx=10, pady=(10, 2))
            e_year = tk.Entry(dlg, width=10, font=('微软雅黑', 10))
            e_year.insert(0, str(year)); e_year.pack(anchor=tk.W, padx=10)
            tk.Label(dlg, text="序号（1~99）:", font=('微软雅黑', 10)).pack(
                anchor=tk.W, padx=10, pady=(8, 2))
            e_seq = tk.Entry(dlg, width=8, font=('微软雅黑', 10))
            e_seq.insert(0, str(seq)); e_seq.pack(anchor=tk.W, padx=10)
            tk.Label(dlg, text="姓名:", font=('微软雅黑', 10)).pack(
                anchor=tk.W, padx=10, pady=(8, 2))
            e_name = tk.Entry(dlg, width=20, font=('微软雅黑', 10))
            e_name.insert(0, name); e_name.pack(anchor=tk.W, padx=10)
            tk.Label(dlg, text="若修改班级/序号/姓名，磁盘文件夹将一并重命名（已改文件不受影响）",
                     fg='#888888', font=('微软雅黑', 9)).pack(anchor=tk.W, padx=10, pady=(6, 0))
            err = tk.StringVar()
            tk.Label(dlg, textvariable=err, fg='#cc0000', font=('微软雅黑', 9)).pack(
                anchor=tk.W, padx=10)

            def _ok():
                new_year = e_year.get().strip()
                try:
                    new_seq = int(e_seq.get().strip())
                except ValueError:
                    err.set("序号须为整数")
                    return
                new_name = e_name.get().strip()
                if not re.fullmatch(r'\d{4}', new_year):
                    err.set("班级号须为 4 位数字年份")
                    return
                if not (1 <= new_seq <= 99):
                    err.set("序号范围 1~99")
                    return
                if not new_name:
                    err.set("姓名不能为空")
                    return
                old_folder = student_folder_name(year, seq, name)
                new_folder = student_folder_name(new_year, new_seq, new_name)
                # 从旧班移除
                entries = STUDENTS.get(year)
                if entries is None:
                    err.set("原班级不存在，请先添加班级")
                    return
                entries[:] = [(s, n) for s, n in entries if not (s == seq and n == name)]
                # 加入新班（班级可能变化；新班自动创建）
                new_entries = STUDENTS.setdefault(new_year, [])
                if (new_seq, new_name) not in new_entries:
                    new_entries.append((new_seq, new_name))
                    new_entries.sort(key=lambda x: x[0])
                # 迁移学习讲次记录（班级/序号任一变化时键随之迁移，保持学习讲次不丢）
                lec = get_student_lectures(year, seq)
                if lec:
                    if new_year != year or new_seq != seq:
                        STUDENT_LECTURES.pop((str(year), seq), None)
                        STUDENT_LECTURES[(str(new_year), new_seq)] = lec
                    # 班级与序号均未变：保留原记录
                save_students_file()
                # 磁盘文件夹重命名（若存在且目标不存在）
                if old_folder != new_folder:
                    old_path = os.path.join(BASE_DIR, old_folder)
                    new_path = os.path.join(BASE_DIR, new_folder)
                    if os.path.isdir(old_path) and not os.path.exists(new_path):
                        try:
                            os.rename(old_path, new_path)
                        except OSError as e2:
                            err.set(f"文件夹重命名失败：{e2}")
                            return
                dlg.destroy()
                self.scan()
                self.status_var.set(f"已修改为 {new_folder}")

            btns = tk.Frame(dlg)
            btns.pack(fill=tk.X, padx=10, pady=8)
            tk.Button(btns, text="确定", command=_ok, width=8,
                      bg='lightgreen').pack(side=tk.RIGHT)
            tk.Button(btns, text="取消", command=dlg.destroy, width=8).pack(side=tk.RIGHT, padx=4)

        def _edit_lectures_at(self, idx):
            info = self._student_of(idx)
            if not info:
                return
            year, seq, name, folder = info
            cur = set(get_student_lectures(year, seq) or [])
            dlg = tk.Toplevel(self.root)
            dlg.title(f"学习讲次 - {folder}")
            dlg.transient(self.root)
            dlg.grab_set()
            tk.Label(dlg, text="勾选该学生学习的内容（默认全部；不勾选=全部）:",
                     font=('微软雅黑', 9)).pack(anchor=tk.W, padx=10, pady=(10, 4))
            frame = tk.Frame(dlg)
            frame.pack(fill=tk.BOTH, expand=True, padx=10)
            check_vars = {}
            for i, item in enumerate(lectures):
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
                set_student_lectures(year, seq, sel)
                dlg.destroy()
                self.scan()
                self.status_var.set(f"已更新 {folder} 的学习讲次")

            tk.Button(btns, text="确定", command=_ok, width=6,
                      bg='lightgreen').pack(side=tk.RIGHT)
            tk.Button(btns, text="取消", command=dlg.destroy, width=6).pack(side=tk.RIGHT, padx=4)

        # ---------- 选中项操作 ----------
        def _selected_roster(self):
            """由对齐行索引收集选中的名单文件夹名（跳过班级标题行 / 名单缺空白行）"""
            out = []
            for i in self.lb_roster.curselection():
                if 0 <= i < len(self._rows):
                    row = self._rows[i]
                    if row[0] == 'student' and row[3]:
                        out.append(row[3])
            return out

        def _selected_disk(self):
            """由对齐行索引收集选中的磁盘文件夹名（跳过班级标题行 / 磁盘缺空白行）"""
            out = []
            for i in self.lb_disk.curselection():
                if 0 <= i < len(self._rows):
                    row = self._rows[i]
                    if row[0] == 'student' and row[4]:
                        out.append(row[4])
            return out

        # ---------- 右键单行快捷操作（针对当前行的磁盘/名单文件夹） ----------
        def _add_disk_folder(self, df):
            """名单缺·磁盘有：把当前行的磁盘文件夹补进名单（右键菜单用）"""
            if not df:
                return
            n = add_students_from_folders([df])
            self.status_var.set(f"已将 {df} 加入名单（名单.json 已保存）" if n
                                else f"{df} 已存在于名单")
            self.scan()

        def _create_roster_folder(self, rf):
            """磁盘缺·名单有：为当前行的名单学生补建磁盘文件夹（右键菜单用）"""
            if not rf:
                return
            m = STUDENT_FOLDER_RE.match(rf)
            if not m:
                return
            ensure_student_folder(m.group(1), int(m.group(2)), m.group(3))
            self.status_var.set(f"已创建 {rf} 学生文件夹（含讲次/子类型结构）")
            self.scan()

        def create_folders(self):
            sel = self._selected_roster()
            if not sel:
                self.status_var.set("请先在【名单信息】栏勾选要创建的文件夹")
                return
            created = 0
            for folder in sel:
                m = STUDENT_FOLDER_RE.match(folder)
                if not m:
                    continue
                ensure_student_folder(m.group(1), int(m.group(2)), m.group(3))
                created += 1
            self.status_var.set(f"已创建 {created} 个学生文件夹（含讲次/子类型结构）")
            self.scan()

        def remove_entries(self):
            sel = self._selected_roster()
            if not sel:
                self.status_var.set("请先在【名单信息】栏勾选要删除的名单条目")
                return
            if not messagebox.askyesno(
                    "确认删除名单",
                    f"将从名单.json 删除 {len(sel)} 条（仅改名单，绝不删除磁盘文件）：\n\n"
                    + '\n'.join(sel[:15]) + ('\n…' if len(sel) > 15 else ''),
                    parent=self.root):
                return
            n = remove_students_by_folder(sel)
            self.status_var.set(f"已从名单删除 {n} 条（名单.json 已保存）")
            self.scan()

        def add_entries(self):
            sel = self._selected_disk()
            if not sel:
                self.status_var.set("请先在【文件夹信息】栏勾选要加入名单的文件夹")
                return
            n = add_students_from_folders(sel)
            self.status_var.set(f"已将 {n} 个学生文件夹加入名单（名单.json 已保存）")
            self.scan()

        def remove_folders(self):
            sel = self._selected_disk()
            if not sel:
                self.status_var.set("请先在【文件夹信息】栏勾选要删除的文件夹")
                return
            empty = [d for d in sel if is_empty_dir(os.path.join(BASE_DIR, d))]
            nonempty = [d for d in sel if d not in empty]
            if nonempty:
                if not messagebox.askyesno(
                        "确认删除（含文件）",
                        f"{len(nonempty)} 个文件夹【含有文件】，删除将移入回收站（可恢复）：\n\n"
                        + '\n'.join(nonempty[:15]) + ('\n…' if len(nonempty) > 15 else ''),
                        parent=self.root):
                    return
            ok, failed = 0, []
            for d in sel:
                r = move_to_recycle_bin(os.path.join(BASE_DIR, d))
                if r in ('recycled', 'moved'):
                    ok += 1
                else:
                    failed.append(d)
            msg = f"已将 {ok} 个文件夹移入回收站"
            if failed:
                msg += f"；{len(failed)} 个失败：{', '.join(failed)}"
            self.status_var.set(msg)
            self.scan()

    if container is None:
        root = tk.Tk()
        app = FrameworkBuilderApp(root)
        root.mainloop()
        return app
    root = container.winfo_toplevel()
    return FrameworkBuilderApp(root, container)


if __name__ == '__main__':
    if '--cli' in sys.argv:
        created, repaired, skipped = build_structure()
        print(f"✅ 新建 {created} 个学生文件夹，补齐老文件夹 {repaired} 个，完整跳过 {skipped} 个。")

        removed, kept = clean_irregular_folders()
        if removed:
            print(f"✅ 已移入回收站 {removed} 个空的不合规文件夹。")
        if kept:
            print(f"ℹ️ 有 {kept} 个不合规文件夹含文件，未处理（请手动确认）。")

        removed2, kept2 = clean_irregular_sub_folders()
        if removed2:
            print(f"✅ 已移入回收站 {removed2} 个空的、多余的子文件夹。")
        if kept2:
            print(f"ℹ️ 有 {kept2} 个多余的子文件夹含文件，未处理（请手动确认）。")

        bad, missing, extra = check_student_folders(BASE_DIR)
        if missing:
            print("ℹ️ 名单中存在但磁盘上缺失的文件夹：", missing)
        if extra:
            print("ℹ️ 磁盘上存在但不在名单中的文件夹（未自动处理）：", extra)
        _, sub_missing = check_sub_folders(BASE_DIR)
        if sub_missing:
            print(f"ℹ️ 学生文件夹内缺失的预期子目录共 {len(sub_missing)} 个（本次已补齐，无需处理）。")
    else:
        main_gui()
