import os
import sys
from concurrent.futures import ThreadPoolExecutor

# 输出编码兜底：脚本含 ✓/⚠️ 等字符，stdout 被重定向（管道/任务计划）时
# 按 GBK 编码会抛 UnicodeEncodeError 崩溃；errors='replace' 保证任何环境可运行
try:
    sys.stdout.reconfigure(errors='replace')
except Exception:
    pass

# 导入公共模块（图片扩展名、数据根目录、存储优化状态）
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (IMAGE_EXTENSIONS, BASE_DIR, check_filename_format,
                    smart_rename_folder, move_to_recycle_bin,
                    load_storage_opt_state, SKIP_SCAN_DIRS, PROCESS_LOCK,
                    PARALLEL_WORKERS)

# 尝试导入 Pillow，若未安装则给出提示并跳过缩放
try:
    from PIL import Image
except ImportError:
    Image = None
    print("警告：未安装 Pillow 库，图片缩放功能将被跳过。")
    print("如需使用缩放，请执行: pip install Pillow")

TARGET_SHORT_EDGE = 1080  # 目标窄边像素
# 所有自动旋转/摆正已取消（2026-08-06）：图片原样加载，仅等比缩放。
# 方向调整只在作业修改器里手动"旋转主图"完成。

# 缩放插值算法：优先 Pillow 10+ 的 Resampling 命名空间（旧 Image.LANCZOS 为兼容别名）
def _resample_method():
    return (Image.Resampling.LANCZOS if hasattr(Image, 'Resampling') else Image.LANCZOS)


def scale_image_to_short_edge(filepath, target=1080):
    """
    将图片等比缩放到窄边 = target 像素，覆盖原文件。
    不做任何旋转/摆正（EXIF 方向也被忽略，按原始像素处理）。
    只缩不放：窄边 ≤ target（小图/已缩略图）保持原样，避免无意义放大
    （upscale 模糊 + 体积膨胀，且会破坏存储优化的缩略效果）。
    """
    if Image is None:
        return  # 未安装 Pillow，跳过

    try:
        with Image.open(filepath) as raw:
            width, height = raw.size
            short_edge = min(width, height)
            if short_edge <= target:
                return   # 无需缩放（也不做任何方向处理）

            # 计算缩放比例
            ratio = target / short_edge
            new_width = int(round(width * ratio))
            new_height = int(round(height * ratio))

            # 使用高质量插值算法
            img_resized = raw.resize((new_width, new_height), _resample_method())

            # 保存覆盖原文件，保持原格式和质量
            ext = os.path.splitext(filepath)[1].lower()
            save_kwargs = {}
            if ext in ('.jpg', '.jpeg'):
                save_kwargs['quality'] = 95
                save_kwargs['subsampling'] = 0
            elif ext == '.png':
                save_kwargs['optimize'] = True
            elif ext == '.webp':
                save_kwargs['quality'] = 95

            img_resized.save(filepath, **save_kwargs)
            print(f"缩放: {filepath}  ({width}x{height} -> {new_width}x{new_height})")
    except Exception as e:
        print(f"处理图片 {filepath} 时出错: {e}")


# 并行线程数：按 CPU 自适应（上限 8），见 common.PARALLEL_WORKERS
def _scale_one(path, skip=()):
    if path in skip:
        return   # 已被存储优化处理（缩略/降质）：不参与自动缩放，避免把缩略图放大回 1080
    scale_image_to_short_edge(path, TARGET_SHORT_EDGE)

def _parallel_scale(paths, skip=()):
    """并行缩放一批图片（顺序无关，每文件独立）；skip=已优化文件路径集合"""
    if not paths:
        return
    workers = PARALLEL_WORKERS
    if workers <= 1 or len(paths) <= 1:
        for p in paths:
            _scale_one(p, skip)
        return
    with ThreadPoolExecutor(max_workers=workers) as ex:
        list(ex.map(lambda p: _scale_one(p, skip), paths))


def _convert_heic_in_folder(folder):
    """
    将文件夹内的 .heic/.heif 转为 .jpg（需要 pillow-heif 库）。
    转换成功后原 HEIC 移入回收站（可恢复，不直接删除）。返回转换数。
    """
    n = 0
    try:
        entries = os.listdir(folder)
    except OSError:
        return n
    heic_files = [f for f in entries if os.path.splitext(f)[1].lower() in ('.heic', '.heif')]
    if not heic_files:
        return n
    try:
        import pillow_heif
    except ImportError:
        print("提示：目录含 HEIC 文件但未安装 pillow-heif，无法转换。请执行: pip install pillow-heif")
        return n
    try:
        pillow_heif.register_heif_opener()
    except Exception:
        pass
    for f in heic_files:
        src = os.path.join(folder, f)
        try:
            with Image.open(src) as raw:
                img = raw.copy()   # 原样转换，不做任何旋转/摆正
                if img.mode != 'RGB':
                    img = img.convert('RGB')
            dst = os.path.splitext(src)[0] + '.jpg'
            img.save(dst, quality=95, subsampling=0)
            r = move_to_recycle_bin(src)   # 原 HEIC 移回收站（可恢复）
            print(f"HEIC→JPG: {f} -> {os.path.basename(dst)}（HEIC 已移至 {r}）")
            n += 1
        except Exception as e:
            print(f"HEIC 转换失败 {f}: {e}")
    return n


def normalize_folder(folder, base_dir=None, skip_optimized=()):
    """
    处理单个文件夹内的图片（供监控器按目录自动调用，也供全量流程复用）：
    1. HEIC/HEIF → JPG
    2. 窄边缩放到 1080（长边等比；不做任何旋转/摆正）
    3. 规范命名（已有编号保留，新编号 1,2,3 顺延）
    skip_optimized：已被存储优化处理（缩略/降质）的文件路径集合——跳过缩放，
    避免自动处理把缩略图放大回 1080（upscale 模糊 + 体积膨胀）。
    返回处理次数（文件数）。
    """
    if base_dir is None:
        base_dir = BASE_DIR
    count = 0
    count += _convert_heic_in_folder(folder)
    try:
        image_files = [f for f in os.listdir(folder)
                       if os.path.splitext(f)[1].lower() in IMAGE_EXTENSIONS]
    except OSError:
        return count
    if image_files:
        scale_paths = [os.path.join(folder, f) for f in image_files]
        _parallel_scale(scale_paths, skip_optimized)
        count += len(scale_paths)
    count += smart_rename_folder(folder, base_dir)
    return count


def normalize_images(base_dir=None):
    """全量规范化（命令行）：与监控器共用跨进程锁，避免同时写同一图片。"""
    if base_dir is None:
        base_dir = BASE_DIR
    base_dir = os.path.abspath(base_dir)

    # 与其他图片处理流程（监控器自动处理/存储优化等）互斥：
    # 拿不到锁说明有处理进行中，直接提示退出（避免双写冲突/重复处理）
    if not PROCESS_LOCK.acquire(blocking=False):
        print("⚠️ 其他图片处理正在进行（如监控器自动处理/存储优化），请稍后再试。")
        return
    try:
        _normalize_images_locked(base_dir)
    finally:
        PROCESS_LOCK.release()


def _normalize_images_locked(base_dir):
    # 已被存储优化处理（缩略/降质）的文件：跳过缩放，
    # 避免把缩略图放大回 1080（upscale 模糊 + 体积膨胀，破坏优化效果）
    try:
        skip_optimized = set(load_storage_opt_state().keys())
    except Exception:
        skip_optimized = set()

    total = 0
    for root, dirs, files in os.walk(base_dir):
        # 剪枝：不进入隐藏目录与保留目录（.workbuddy、登记、__pycache__、测试副本等），
        # 避免递归遍历整棵无用于树
        dirs[:] = [d for d in dirs if not d.startswith('.') and d not in SKIP_SCAN_DIRS]
        rel = os.path.relpath(root, base_dir)
        # 跳过保留/隐藏目录（.workbuddy、登记、__pycache__、测试副本等）
        if rel == '.' or rel.startswith('.') or rel.split(os.sep)[0] in SKIP_SCAN_DIRS:
            continue
        total += normalize_folder(root, base_dir, skip_optimized)
    print(f"完成：共处理 {total} 次文件操作")


if __name__ == "__main__":
    if '--check' in sys.argv:
        # 只检查命名格式，列出不规范文件，不修改任何文件
        bad = check_filename_format()
        if bad:
            print(f"发现 {len(bad)} 个不规范命名的图片文件（未修改，可手动处理或运行完整规范化）：")
            for path, fname in bad[:100]:
                print(f"  · {os.path.relpath(path, BASE_DIR)}")
            if len(bad) > 100:
                print(f"  … 其余 {len(bad)-100} 个略")
        else:
            print("所有图片文件名均符合规范 ✓（无需修改）")
        sys.exit(0)
    normalize_images()
