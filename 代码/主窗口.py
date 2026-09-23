# -*- coding: utf-8 -*-
"""
WorkBuddy 统一主窗口 —— 单窗口整合：所有窗口（情况监视器/作业修改器/设置中心/框架搭建器）
都在这一个窗口内以"页面导航"方式切换，监视器为首页，其余为页面。

- 顶部导航栏：监视器（首页）/ 修改器 / 设置 / 框架搭建器 + 「← 返回监视器」
- 全局 ESC = 返回监视器首页（文本框/下拉框等输入控件聚焦时除外；设置页快捷键录制期间除外）
- 各工具仍保留独立运行能力（各自 __main__ 直接运行）
- 页面切换 = 销毁内容区子控件 → 重建目标页 → 注入 container

设计契约（与各工具 build 接口对齐）：
- 情况监视器：FileMonitorApp(root, container=None) —— container 提供时 UI 构建进 container
- 作业修改器：main(container=None) —— container 提供时 paned_window/toggle_btn 构建进 container
- 设置中心：open_settings_window(master, source, apply_monitor, apply_modifier, container=None, on_close=None)
- 框架搭建器：main_gui(container=None)
"""
import os
import sys
import tkinter as tk

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

from common import PROJECT_VERSION, window_geometry

try:
    from tkinterdnd2 import TkinterDnD
    DND_AVAILABLE = True
except ImportError:
    TkinterDnD = None
    DND_AVAILABLE = False

# 延迟导入（页面首次进入才加载，避免启动即 import 四个工具）
import 情况监视器
import 作业修改器
import 设置中心
import 框架搭建器


# 输入类控件：聚焦时全局 ESC 返回不触发（让文本框/下拉框自己处理 ESC）
_INPUT_CLASSES = ('Entry', 'TEntry', 'Spinbox', 'TCombobox', 'Combobox',
                  'Listbox', 'TListbox', 'Scale', 'TScale')


class MainApp:
    def __init__(self, root):
        self.root = root
        self._page_frames = {}    # page_id -> 当前内容 Frame（重建时销毁旧的）
        self._page_builders = {
            'monitor': self._build_monitor,
            'modifier': self._build_modifier,
            'settings': self._build_settings,
            'framework': self._build_framework,
        }
        self._teardown = {}       # page_id -> 离开该页前的 root 级清理函数
        self._current = None
        self._closing = False

        root.title(f"WorkBuddy 作业批改工具 v{PROJECT_VERSION}（单窗口版）")
        root.geometry(window_geometry(root, 1280, 860))
        root.minsize(900, 620)

        self._build_navbar()
        self._content = tk.Frame(root)
        self._content.pack(fill=tk.BOTH, expand=True)

        # 全局 ESC 返回（含录制短路 + 输入控件聚焦排除）
        root.bind('<Escape>', self._on_esc)
        root.protocol('WM_DELETE_WINDOW', self._on_close)

        self.show_page('monitor')

    # ---------- 导航栏 ----------
    def _build_navbar(self):
        bar = tk.Frame(self.root, bg='#e8e8e8', padx=8, pady=4)
        bar.pack(fill=tk.X, side=tk.TOP)
        self._nav_buttons = {}

        def _mk(label, page):
            b = tk.Button(bar, text=label, relief=tk.RAISED, padx=10, pady=2,
                          command=lambda: self.show_page(page))
            b.pack(side=tk.LEFT, padx=2)
            self._nav_buttons[page] = b

        _mk("📋 监视器（首页）", 'monitor')
        _mk("✏ 修改器", 'modifier')
        _mk("⚙ 设置", 'settings')
        _mk("🏗 框架搭建器", 'framework')

        # 返回按钮：仅非首页页面时有效（始终显示，点击跳回监视器）
        self._back_btn = tk.Button(bar, text="← 返回监视器 (Esc)", padx=10, pady=2,
                                   command=self.go_home, bg='#d1e7dd')
        self._back_btn.pack(side=tk.LEFT, padx=(12, 2))

        self._page_label = tk.Label(bar, text="", bg='#e8e8e8', fg='#555555',
                                    font=('微软雅黑', 9))
        self._page_label.pack(side=tk.RIGHT, padx=8)

    # ---------- 页面切换 ----------
    def show_page(self, page_id):
        if page_id not in self._page_builders:
            return
        if page_id == self._current:
            return
        # 离开当前页前调用该页 teardown（取消定时器/解除全局绑定，防残留影响共享 root）
        if self._current is not None:
            t = self._teardown.get(self._current)
            if t is not None:
                try:
                    t()
                except Exception:
                    import traceback
                    traceback.print_exc()
        self._current = None
        # 销毁旧页内容
        for w in self._content.winfo_children():
            w.destroy()
        self._page_frames.clear()
        try:
            self._content.configure(bg='#f5f5f5')
        except Exception:
            pass
        # 构建新页（页面级绑定随 container 销毁自动清理，避免跨页 bind_all 冲突）
        container = tk.Frame(self._content, bg='#f5f5f5')
        container.pack(fill=tk.BOTH, expand=True)
        self._page_frames[page_id] = container
        try:
            self._page_builders[page_id](container)
        except Exception as e:
            import traceback
            traceback.print_exc()
            tk.Label(container, text=f"页面加载失败：{e}", fg='#cc4444',
                     font=('微软雅黑', 12)).pack(pady=40)
        self._current = page_id
        # 导航高亮
        for pid, b in self._nav_buttons.items():
            b.config(relief=tk.RAISED, bg='SystemButtonFace')
        if page_id in self._nav_buttons:
            self._nav_buttons[page_id].config(relief=tk.SUNKEN, bg='#d1e7dd')
        # 返回按钮可用性提示
        self._back_btn.config(state=tk.NORMAL if page_id != 'monitor' else tk.DISABLED)
        titles = {'monitor': '情况监视器（首页）', 'modifier': '作业修改器',
                  'settings': '设置中心', 'framework': '框架搭建器'}
        self._page_label.config(text=titles.get(page_id, ''))
        # 每次进入重新聚焦内容区，保证页面快捷键生效
        try:
            container.focus_set()
        except Exception:
            pass

    def go_home(self):
        self.show_page('monitor')

    # ---------- 页面构建（嵌入各工具；container=None 时独立运行） ----------
    def _build_monitor(self, container):
        app = 情况监视器.FileMonitorApp(self.root, container=container)
        self._current_monitor = app
        self._teardown['monitor'] = app.stop_page   # 离开监视器页：停止定时器/解绑滚轮
        # 嵌入路由：监视器页内「⚙设置」「✏打开修改器」按钮切到对应主窗口页面
        container._dsh_on_open_settings = lambda: self.show_page('settings')
        container._dsh_on_open_modifier = lambda: self.show_page('modifier')

    def _build_modifier(self, container):
        # 嵌入模式：修改器构建到 container；把监视器当前检索范围直接传入修改器
        # （修改器不再自行检索，直接继承监视器实时检索信息）
        container._dsh_on_back = self.go_home   # 供修改器嵌入「← 返回」按钮回调
        container._dsh_on_open_settings = lambda: self.show_page('settings')   # 独立入口兜底
        scope = None
        try:
            mon = getattr(self, '_current_monitor', None)
            if mon is not None:
                scope = mon._current_scope()
        except Exception:
            scope = None
        作业修改器.main(container=container, initial_scope=scope)
        self._current_modifier = True
        self._teardown['modifier'] = 作业修改器._unmount_page   # 离开修改器页：解绑快捷键/销毁页面树

    def _build_settings(self, container):
        # 切入设置页前旧页面已 teardown 并销毁；不能把旧实例回调传给设置页。
        # 保存后回首页会重新构建监视器，并自然读取最新配置。
        设置中心.open_settings_window(
            self.root, source='monitor', apply_monitor=None, apply_modifier=None,
            container=container, on_close=self.go_home, on_optimize=None)
        self._current_settings = True
        self._teardown['settings'] = 设置中心.cancel_recordings   # 离开设置页：解除录制监听

    def _optimize_now(self, storage_cfg=None):
        """设置中心「立即优化存储」回调，使用设置页刚校验的参数。"""
        try:
            mon = getattr(self, '_current_monitor', None)
            if mon is not None:
                if storage_cfg is not None:
                    mon.storage_cfg = dict(storage_cfg)
                mon._run_storage_optimize(force=True)
        except Exception:
            import traceback
            traceback.print_exc()

    def _build_framework(self, container):
        框架搭建器.main_gui(container=container)
        self._current_framework = True
        # 框架搭建器无全局绑定/定时器，无需 teardown（随 container 销毁自动清理）

    # ---------- ESC / 关闭 ----------
    def _is_input_focus(self):
        try:
            w = self.root.focus_get()
            if w is None:
                return False
            cls = w.winfo_class()
            return cls in _INPUT_CLASSES
        except Exception:
            return False

    def _on_esc(self, e=None):
        # 设置页快捷键录制期间：ESC = 取消录制，不返回（录制监听用 'all' 层，
        # 这里短路避免切页破坏录制，见 设置中心._recording）
        try:
            if getattr(设置中心, '_recording', False):
                return
        except Exception:
            pass
        if self._is_input_focus():
            return   # 输入控件聚焦：ESC 不触发返回
        if self._current != 'monitor':
            self.go_home()
            return 'break'

    def _on_close(self):
        self._closing = True
        if self._current == 'monitor':
            try:
                self._current_monitor.save_settings()
            except Exception:
                pass
        elif self._current == 'modifier':
            try:
                作业修改器.save_layout()
            except Exception:
                pass
        teardown = self._teardown.get(self._current)
        if teardown is not None:
            try:
                teardown()
            except Exception:
                import traceback
                traceback.print_exc()
        try:
            self.root.destroy()
        except Exception:
            pass


def run():
    """启动统一主窗口（唯一入口）。供 启动.py 调用。"""
    if DND_AVAILABLE:
        root = TkinterDnD.Tk()
    else:
        root = tk.Tk()
    app = MainApp(root)
    # 保留引用防回收
    globals()['_app'] = app
    if not DND_AVAILABLE:
        print("提示：未安装 tkinterdnd2，外部图片拖放功能不可用。")
    root.mainloop()


if __name__ == "__main__":
    run()
