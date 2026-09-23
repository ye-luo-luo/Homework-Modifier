# -*- coding: utf-8 -*-
"""
WorkBuddy 统一启动入口 —— 双击此文件即可启动「统一主窗口」（单窗口整合版）。
所有工具（情况监视器/作业修改器/设置中心/框架搭建器）都在这一个窗口内
以页面导航方式切换：监视器为首页，其余为页面；ESC 或「← 返回监视器」返回首页。
各工具仍保留独立运行能力（各自文件直接运行仍打开独立窗口）。

数据目录：优先取 配置目录 配置/data_dir.txt 记录的路径（程序与数据分离时）；
未配置时 = 程序根目录（程序与数据同目录）。也可用环境变量 DSH_DATA_DIR 覆盖。
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import 主窗口

if __name__ == '__main__':
    主窗口.run()
