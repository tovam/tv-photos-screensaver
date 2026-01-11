#!/usr/bin/env python3
import os
import sys
import glob
import time
import json
import random
import threading
import subprocess
import urllib.request
import ipaddress
import base64
import hashlib
import re
import locale
from datetime import datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs, unquote

# --- Auto X11 env for running from tty/ssh/systemd ---
if not os.environ.get("DISPLAY"):
    os.environ["DISPLAY"] = ":0"
if not os.environ.get("XAUTHORITY"):
    os.environ["XAUTHORITY"] = os.path.expanduser("~/.Xauthority")

from PIL import Image, ImageOps
from PIL.ImageQt import ImageQt

from PyQt6.QtCore import Qt, QTimer, QMetaObject, Q_ARG, pyqtSlot
from PyQt6.QtGui import QPixmap, QFont, QKeySequence, QShortcut
from PyQt6.QtWidgets import QApplication, QLabel, QWidget, QGraphicsDropShadowEffect


# ----------------------------
# Config / Access control
# ----------------------------
DEFAULT_PORT = 8787
DEFAULT_DELAY_S = 60
MAX_UPLOAD_BYTES = 25 * 1024 * 1024  # 25MB

ALLOWED_NETS = [
    ipaddress.ip_network("10.0.0.0/8"),
    ipaddress.ip_network("192.168.0.0/16"),
    ipaddress.ip_network("127.0.0.0/8"),
]
ALLOWED_V6 = {ipaddress.ip_address("::1")}
STATE_FILENAME = ".fehb_state.json"
UPDATE_CONFIG_PATH = "~/.tvphotos.yml"
FIT_TAG_WIDTH = "__fitw"
FIT_TAG_HEIGHT = "__fith"
FIT_HEIGHT_RATIO_THRESHOLD = 0.76


def is_allowed_client_ip(ip_str):
    try:
        ip = ipaddress.ip_address(ip_str)
        if ip.version == 6:
            return ip in ALLOWED_V6
        return any(ip in net for net in ALLOWED_NETS)
    except Exception:
        return False


def now_ts():
    return int(time.time())


def read_config_value(key, required=False):
    path = os.path.expanduser(UPDATE_CONFIG_PATH)
    try:
        with open(path, "r", encoding="utf-8") as f:
            for raw in f:
                line = raw.strip()
                if not line or line.startswith("#"):
                    continue
                m = re.match(r"^([A-Za-z0-9_.-]+)\s*:\s*(.+)$", line)
                if not m:
                    continue
                k = m.group(1)
                if k != key:
                    continue
                val = m.group(2).strip()
                if len(val) >= 2 and val[0] == val[-1] and val[0] in ("'", '"'):
                    val = val[1:-1]
                return val
    except FileNotFoundError:
        if required:
            raise FileNotFoundError(f"Config not found: {path}")
        return None
    if required:
        raise KeyError(f"{key} not found in {path}")
    return None


def read_update_url():
    return read_config_value("update_url", required=True)


def read_locale_value():
    return read_config_value("locale", required=False)


def apply_locale_from_config():
    loc = read_locale_value()
    if not loc:
        return None

    candidates = [loc]
    alt = loc.replace("-", "_")
    if alt != loc:
        candidates.append(alt)
    if "." not in alt:
        candidates.append(alt + ".UTF-8")
    if "." not in loc:
        candidates.append(loc + ".UTF-8")

    for cand in candidates:
        try:
            locale.setlocale(locale.LC_TIME, cand)
            return cand
        except Exception:
            continue
    return None


def update_script_from_url(url):
    p = urlparse(url)
    if p.scheme not in ("http", "https"):
        raise ValueError("update_url must be http or https")

    req = urllib.request.Request(url, headers={"User-Agent": "fehb/1.5"})
    with urllib.request.urlopen(req, timeout=30) as resp:
        data = resp.read()

    if not data:
        raise ValueError("empty update payload")

    script_path = os.path.abspath(__file__)
    st = os.stat(script_path)
    tmp_path = script_path + ".tmp"
    try:
        with open(tmp_path, "wb") as f:
            f.write(data)
        os.replace(tmp_path, script_path)
        os.chmod(script_path, st.st_mode)
    finally:
        try:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
        except Exception:
            pass

    return len(data)


def get_ipv4_addrs():
    addrs = set()
    try:
        out = subprocess.check_output(["ip", "-o", "-4", "addr", "show"], text=True)
        for line in out.splitlines():
            parts = line.split()
            if "inet" in parts:
                i = parts.index("inet")
                cidr = parts[i + 1]
                ip = cidr.split("/")[0].strip()
                if ip:
                    addrs.add(ip)
    except Exception:
        pass

    if not addrs:
        try:
            out = subprocess.check_output(["hostname", "-I"], text=True)
            for ip in out.split():
                if ip.count(".") == 3:
                    addrs.add(ip.strip())
        except Exception:
            pass

    addrs.add("127.0.0.1")
    return sorted(addrs)


# ----------------------------
# Image helpers
# ----------------------------
def fit_cover(pil_img, target_w, target_h):
    # CONTAIN + letterbox (black bars) instead of cover/crop
    iw, ih = pil_img.size
    if target_w <= 0 or target_h <= 0 or iw <= 0 or ih <= 0:
        return pil_img

    scale = min(target_w / iw, target_h / ih)   # <- was max()
    nw, nh = max(1, int(iw * scale)), max(1, int(ih * scale))
    img = pil_img.resize((nw, nh), Image.Resampling.LANCZOS)

    canvas = Image.new("RGB", (target_w, target_h), (0, 0, 0))
    left = (target_w - nw) // 2
    top  = (target_h - nh) // 2
    canvas.paste(img, (left, top))
    return canvas

def fit_width_cover(pil_img, target_w, target_h):
    if target_w <= 0 or target_h <= 0:
        return pil_img
    iw, ih = pil_img.size
    if iw <= 0 or ih <= 0:
        return pil_img

    scale = target_w / iw
    nw = target_w
    nh = max(1, int(round(ih * scale)))
    img = pil_img.resize((nw, nh), Image.Resampling.LANCZOS)

    if nh == target_h:
        return img
    if nh > target_h:
        top = max(0, (nh - target_h) // 2)
        return img.crop((0, top, target_w, top + target_h))

    canvas = Image.new("RGB", (target_w, target_h), (0, 0, 0))
    top = (target_h - nh) // 2
    canvas.paste(img, (0, top))
    return canvas


def pil_to_qpixmap(pil_img):
    if pil_img.mode != "RGBA":
        pil_img = pil_img.convert("RGBA")
    qimg = ImageQt(pil_img)
    return QPixmap.fromImage(qimg)


def load_pixmap_cover(path, target_w, target_h):
    try:
        img = Image.open(path)
        img = ImageOps.exif_transpose(img)
        img = img.convert("RGB")
        mode = choose_fit_mode(os.path.basename(path), img.width, img.height)
        if mode == "width":
            img = fit_width_cover(img, target_w, target_h)
        else:
            img = fit_cover(img, target_w, target_h)
        return pil_to_qpixmap(img)
    except Exception:
        return None


def make_thumbnail_bytes(path, max_w=360, max_h=202, quality=75):
    img = Image.open(path)
    img = ImageOps.exif_transpose(img)
    img = img.convert("RGB")
    img.thumbnail((max_w, max_h), Image.Resampling.LANCZOS)

    from io import BytesIO
    buf = BytesIO()
    img.save(buf, format="JPEG", quality=quality, optimize=True)
    return buf.getvalue()


def safe_join(folder, name):
    folder = os.path.abspath(folder)
    p = os.path.abspath(os.path.join(folder, name))
    if not p.startswith(folder + os.sep):
        raise ValueError("bad path")
    return p


def sanitize_filename(name):
    name = os.path.basename(name or "")
    name = name.strip().replace("\x00", "")
    name = re.sub(r"[^A-Za-z0-9._-]+", "_", name)
    if not name or name in (".", ".."):
        name = f"upload-{time.strftime('%Y%m%d-%H%M%S')}.jpg"
    return name


def fit_mode_from_name(name):
    base = os.path.splitext(os.path.basename(name or ""))[0]
    if base.endswith(FIT_TAG_WIDTH):
        return "width"
    if base.endswith(FIT_TAG_HEIGHT):
        return "height"
    return "auto"


def strip_fit_tag(base):
    for tag in (FIT_TAG_WIDTH, FIT_TAG_HEIGHT):
        if base.endswith(tag):
            return base[:-len(tag)]
    return base


def name_with_fit_mode(name, mode):
    base, ext = os.path.splitext(os.path.basename(name or ""))
    base = strip_fit_tag(base)
    if mode == "width":
        base = base + FIT_TAG_WIDTH
    elif mode == "height":
        base = base + FIT_TAG_HEIGHT
    elif mode == "auto":
        pass
    else:
        raise ValueError("bad fit mode")
    return base + ext


def choose_fit_mode(name, iw, ih):
    mode = fit_mode_from_name(name)
    if mode != "auto":
        return mode
    if iw <= 0 or ih <= 0:
        return "width"
    if (ih / iw) > FIT_HEIGHT_RATIO_THRESHOLD:
        return "height"
    return "width"


# ----------------------------
# WebSocket (minimal RFC6455)
# ----------------------------
_WS_GUID = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"


def ws_make_accept(key):
    raw = (key + _WS_GUID).encode("utf-8")
    digest = hashlib.sha1(raw).digest()
    return base64.b64encode(digest).decode("ascii")


def ws_send_text(sock, text):
    payload = text.encode("utf-8", errors="ignore")
    b1 = 0x81
    ln = len(payload)
    header = bytearray([b1])

    if ln < 126:
        header.append(ln)
    elif ln < (1 << 16):
        header.append(126)
        header.extend(ln.to_bytes(2, "big"))
    else:
        header.append(127)
        header.extend(ln.to_bytes(8, "big"))

    sock.sendall(header + payload)


def ws_recv_frame(sock):
    try:
        h = sock.recv(2)
        if not h or len(h) < 2:
            return None, None
        b1, b2 = h[0], h[1]
        opcode = b1 & 0x0F
        masked = (b2 & 0x80) != 0
        ln = b2 & 0x7F

        if ln == 126:
            ext = sock.recv(2)
            if len(ext) < 2:
                return None, None
            ln = int.from_bytes(ext, "big")
        elif ln == 127:
            ext = sock.recv(8)
            if len(ext) < 8:
                return None, None
            ln = int.from_bytes(ext, "big")

        mask = b""
        if masked:
            mask = sock.recv(4)
            if len(mask) < 4:
                return None, None

        data = b""
        while len(data) < ln:
            chunk = sock.recv(min(4096, ln - len(data)))
            if not chunk:
                return None, None
            data += chunk

        if masked:
            data = bytes(data[i] ^ mask[i % 4] for i in range(len(data)))

        return opcode, data
    except Exception:
        return None, None


class WebSocketHub:
    def __init__(self):
        self.lock = threading.Lock()
        self.clients = set()

    def add(self, sock):
        with self.lock:
            self.clients.add(sock)

    def remove(self, sock):
        with self.lock:
            self.clients.discard(sock)

    def broadcast(self, obj):
        msg = json.dumps(obj, ensure_ascii=False)
        dead = []
        with self.lock:
            for s in list(self.clients):
                try:
                    ws_send_text(s, msg)
                except Exception:
                    dead.append(s)
            for s in dead:
                try:
                    s.close()
                except Exception:
                    pass
                self.clients.discard(s)


# ----------------------------
# Image manager
# ----------------------------
class ImageManager:
    def __init__(self, folder):
        self.folder = os.path.abspath(os.path.expanduser(folder))
        self.state_path = os.path.join(self.folder, STATE_FILENAME)
        self.lock = threading.Lock()
        self.disabled = set()
        self.active_source_x = 2
        self.delay_s = DEFAULT_DELAY_S
        self._files = []
        self.load_state()
        self.refresh_files()

    def load_state(self):
        with self.lock:
            self.disabled = set()
            self.active_source_x = 2
            self.delay_s = DEFAULT_DELAY_S
            try:
                with open(self.state_path, "r", encoding="utf-8") as f:
                    d = json.load(f)
                self.disabled = set(d.get("disabled", []))
                try:
                    self.active_source_x = int(d.get("active_source_x", 2))
                except Exception:
                    self.active_source_x = 2
                try:
                    self.delay_s = int(d.get("delay_s", DEFAULT_DELAY_S))
                except Exception:
                    self.delay_s = DEFAULT_DELAY_S
            except FileNotFoundError:
                pass
            except Exception:
                pass

    def save_state(self):
        with self.lock:
            tmp = {
                "disabled": sorted(list(self.disabled)),
                "active_source_x": int(self.active_source_x),
                "delay_s": int(self.delay_s),
                "saved_at": now_ts(),
            }
            try:
                with open(self.state_path, "w", encoding="utf-8") as f:
                    json.dump(tmp, f, indent=2)
            except Exception:
                pass

    def refresh_files(self):
        exts = ("*.jpg", "*.jpeg", "*.png", "*.JPG", "*.JPEG", "*.PNG")
        files = []
        for ext in exts:
            files.extend(glob.glob(os.path.join(self.folder, ext)))
        files = sorted(set(files))
        with self.lock:
            self._files = files
            present = set(os.path.basename(p) for p in files)
            self.disabled = set([n for n in self.disabled if n in present])
        self.save_state()

    def list_images(self):
        with self.lock:
            out = []
            for p in self._files:
                name = os.path.basename(p)
                enabled = name not in self.disabled
                fit_mode = fit_mode_from_name(name)
                width = 0
                height = 0
                ratio = 0.0
                try:
                    st = os.stat(p)
                    size = st.st_size
                    mtime = int(st.st_mtime)
                except Exception:
                    size = 0
                    mtime = 0
                try:
                    img = Image.open(p)
                    img = ImageOps.exif_transpose(img)
                    width, height = img.size
                    if height > 0:
                        ratio = width / height
                except Exception:
                    width = 0
                    height = 0
                    ratio = 0.0
                fit_effective = choose_fit_mode(name, width, height)
                out.append({
                    "name": name,
                    "enabled": enabled,
                    "fit_mode": fit_mode,
                    "fit_effective": fit_effective,
                    "width": width,
                    "height": height,
                    "ratio": ratio,
                    "size": size,
                    "mtime": mtime,
                })
            return out

    def enabled_paths(self):
        with self.lock:
            return [p for p in self._files if os.path.basename(p) not in self.disabled]

    def has_file(self, name):
        name = os.path.basename(name)
        with self.lock:
            return any(os.path.basename(p) == name for p in self._files)

    def path_for_name(self, name):
        name = os.path.basename(name)
        return safe_join(self.folder, name)

    def set_enabled(self, name, enabled):
        name = os.path.basename(name)
        with self.lock:
            if enabled:
                self.disabled.discard(name)
            else:
                self.disabled.add(name)
        self.save_state()

    def set_fit_mode(self, name, mode):
        name = os.path.basename(name)
        if mode not in ("auto", "width", "height"):
            raise ValueError("invalid fit mode")

        old_path = safe_join(self.folder, name)
        if not os.path.exists(old_path):
            raise FileNotFoundError("image not found")

        new_name = name_with_fit_mode(name, mode)
        if new_name == name:
            return new_name

        new_path = safe_join(self.folder, new_name)
        if os.path.exists(new_path):
            raise FileExistsError("target name exists")

        os.rename(old_path, new_path)
        with self.lock:
            if name in self.disabled:
                self.disabled.discard(name)
                self.disabled.add(new_name)
        self.save_state()
        self.refresh_files()
        return new_name

    def delete(self, name):
        name = os.path.basename(name)
        p = safe_join(self.folder, name)
        try:
            os.remove(p)
        except FileNotFoundError:
            pass
        with self.lock:
            self.disabled.discard(name)
        self.refresh_files()

    def download_picsum(self):
        url = "https://picsum.photos/1920/1080"
        ts = time.strftime("%Y%m%d-%H%M%S")
        fname = f"picsum-{ts}.jpg"
        out_path = safe_join(self.folder, fname)

        req = urllib.request.Request(url, headers={"User-Agent": "fehb/1.0"})
        with urllib.request.urlopen(req, timeout=30) as resp:
            data = resp.read()

        with open(out_path, "wb") as f:
            f.write(data)

        self.refresh_files()
        return fname

    def set_delay(self, delay_s):
        try:
            d = int(delay_s)
        except Exception:
            d = DEFAULT_DELAY_S
        if d < 1:
            d = 1
        if d > 24 * 3600:
            d = 24 * 3600
        with self.lock:
            self.delay_s = d
        self.save_state()
        return d

    def save_uploaded_image_bytes_as_jpeg(self, raw_bytes, suggested_name):
        from io import BytesIO
        try:
            img = Image.open(BytesIO(raw_bytes))
            img = ImageOps.exif_transpose(img)
            img = img.convert("RGB")
        except Exception:
            raise ValueError("Uploaded file is not a valid image")

        base = sanitize_filename(suggested_name)
        base_noext = os.path.splitext(base)[0] or "upload"
        ts = time.strftime("%Y%m%d-%H%M%S")
        out_name = f"{base_noext}-{ts}.jpg"
        out_path = safe_join(self.folder, out_name)
        img.save(out_path, format="JPEG", quality=92, optimize=True)
        self.refresh_files()
        return out_name


# ----------------------------
# CEC helpers
# ----------------------------
def run_cec(args):
    cmd = ["cec-ctl", "-d", "/dev/cec0"] + args
    p = subprocess.run(cmd, capture_output=True, text=True)
    return {
        "ok": (p.returncode == 0),
        "returncode": p.returncode,
        "stdout": p.stdout[-4000:],
        "stderr": p.stderr[-4000:],
        "cmd": " ".join(cmd),
    }


# ----------------------------
# Qt slideshow
# ----------------------------
class Slideshow(QWidget):
    def __init__(self, manager, hub, delay_s=None):
        super().__init__()
        self.mgr = manager
        self.hub = hub

        if delay_s is None:
            delay_s = self.mgr.delay_s

        self.delay_ms = max(1000, int(delay_s * 1000))
        self.margin = 20

        self._playlist = []
        self._idx = 0
        self.current_path = None

        self.setWindowTitle("Wallpaper Clock")
        self.setWindowFlags(Qt.WindowType.FramelessWindowHint | Qt.WindowType.WindowStaysOnTopHint)
        self.setCursor(Qt.CursorShape.BlankCursor)

        self.bg = QLabel(self)
        self.bg.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.bg.setGeometry(self.rect())

        self.clock = QLabel(self)
        self.clock.setAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignTop)
        self.clock.setFont(QFont("DejaVu Sans", 28, 700))
        self.clock.setStyleSheet("color: rgba(255,255,255,128);")
        self.clock.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)

        shadow = QGraphicsDropShadowEffect(self)
        shadow.setBlurRadius(10)
        shadow.setOffset(0, 2)
        shadow.setColor(Qt.GlobalColor.black)
        self.clock.setGraphicsEffect(shadow)

        QShortcut(QKeySequence("Esc"), self, activated=self.close)
        QShortcut(QKeySequence("Q"), self, activated=self.close)
        QShortcut(QKeySequence("Space"), self, activated=self.show_next)

        self.t_clock = QTimer(self)
        self.t_clock.timeout.connect(self.tick)
        self.t_clock.start(1000)

        self.t_slide = QTimer(self)
        self.t_slide.timeout.connect(self.show_next)

        self.showFullScreen()
        QTimer.singleShot(0, self._start_after_show)

    def _start_after_show(self):
        self.tick()
        self._rebuild_playlist()
        self.show_next()
        self.t_slide.start(self.delay_ms)
        self._broadcast_state()

    def _broadcast_state(self):
        name = os.path.basename(self.current_path) if self.current_path else ""
        self.hub.broadcast({
            "type": "state",
            "current": name,
            "delay_s": int(self.delay_ms / 1000),
            "ts": now_ts(),
        })

    @pyqtSlot(int)
    def apply_delay(self, delay_s):
        try:
            d = int(delay_s)
        except Exception:
            d = DEFAULT_DELAY_S
        if d < 1:
            d = 1
        if d > 24 * 3600:
            d = 24 * 3600
        self.delay_ms = max(1000, int(d * 1000))
        self.t_slide.stop()
        self.t_slide.start(self.delay_ms)
        self._broadcast_state()

    def set_delay(self, delay_s):
        d = self.mgr.set_delay(delay_s)
        self.apply_delay(d)

    def _rebuild_playlist(self):
        paths = self.mgr.enabled_paths()
        random.shuffle(paths)
        self._playlist = paths
        self._idx = 0

    def refresh_from_manager(self, prefer_name=None):
        self._rebuild_playlist()
        if prefer_name and self.mgr.has_file(prefer_name):
            if self.show_specific_name(prefer_name):
                return
        if self.current_path and not os.path.exists(self.current_path):
            self.current_path = None
        self.show_next()

    def resizeEvent(self, event):
        self.bg.setGeometry(self.rect())
        self.layout_clock()
        if self.current_path:
            self._show_path(self.current_path)
        super().resizeEvent(event)

    def layout_clock(self):
        self.clock.adjustSize()
        w = self.clock.width()
        self.clock.move(self.width() - w - self.margin, self.margin)

    def tick(self):
        self.clock.setText(datetime.now().strftime("%A %d %B %Y\n%H:%M:%S"))
        self.layout_clock()

    def _show_path(self, path):
        if self.width() <= 0 or self.height() <= 0:
            return False
        pix = load_pixmap_cover(path, self.width(), self.height())
        if pix is None:
            return False
        self.bg.setPixmap(pix)
        self.current_path = path
        return True

    @pyqtSlot(str)
    def show_specific_name(self, name):
        name = os.path.basename(name or "")
        if not name or not self.mgr.has_file(name):
            return False
        path = self.mgr.path_for_name(name)
        ok = self._show_path(path)
        if ok:
            self._broadcast_state()
        return ok

    def show_next(self):
        if self.width() <= 0 or self.height() <= 0:
            return

        if not self._playlist or self._idx >= len(self._playlist):
            self._rebuild_playlist()

        if not self._playlist:
            self.bg.setText("No enabled images")
            self.bg.setStyleSheet("color: white; background: black;")
            self.current_path = None
            self._broadcast_state()
            return
        else:
            self.bg.setStyleSheet("")
            self.bg.setText("")

        tries = 0
        while tries < max(10, len(self._playlist) + 2):
            if self._idx >= len(self._playlist):
                self._rebuild_playlist()
                if not self._playlist:
                    self.current_path = None
                    self._broadcast_state()
                    return
            path = self._playlist[self._idx]
            self._idx += 1
            if self._show_path(path):
                self._broadcast_state()
                return
            tries += 1


# ----------------------------
# Reverse-proxy safe routing
# ----------------------------
def strip_to_known_route(path):
    if not path:
        return "/"
    i = path.rfind("/api/")
    if i != -1:
        return path[i:]
    i = path.rfind("/thumb")
    if i != -1:
        return "/thumb"
    i = path.rfind("/ws")
    if i != -1:
        return "/ws"
    if path.endswith("/index.html"):
        return "/index.html"
    if path.endswith("/"):
        return "/"
    if path == "/":
        return "/"
    return path


# ----------------------------
# Multipart upload parsing
# ----------------------------
def parse_multipart_first_file(content_type, body_bytes):
    m = re.search(r'boundary="?([^";]+)"?', content_type or "", re.I)
    if not m:
        return None, None
    boundary = m.group(1).encode("utf-8")
    delim = b"--" + boundary

    parts = body_bytes.split(delim)
    for part in parts:
        if not part:
            continue
        if part.startswith(b"--"):
            continue
        if part.startswith(b"\r\n"):
            part = part[2:]
        if part.endswith(b"\r\n"):
            part = part[:-2]

        sep = part.find(b"\r\n\r\n")
        if sep == -1:
            continue
        header_blob = part[:sep].decode("utf-8", errors="ignore")
        data = part[sep + 4:]
        if data.endswith(b"\r\n"):
            data = data[:-2]

        hm = re.search(r'filename="([^"]*)"', header_blob, re.I)
        if not hm:
            continue
        filename = hm.group(1)
        return filename, data

    return None, None


# ----------------------------
# Web server + WebSocket upgrade
# ----------------------------
def make_handler(mgr, slideshow, hub):
    class Handler(BaseHTTPRequestHandler):
        server_version = "fehb/1.5"

        def _client_ip(self):
            xff = self.headers.get("X-Forwarded-For", "")
            if xff:
                ip = xff.split(",")[0].strip()
                if ip:
                    return ip
            return self.client_address[0]

        def _client_ok(self):
            return is_allowed_client_ip(self._client_ip())

        def log_message(self, fmt, *args):
            return

        def _deny(self, code=403, msg="Forbidden"):
            self.send_response(code)
            self.send_header("Content-Type", "text/plain; charset=utf-8")
            self.end_headers()
            self.wfile.write(msg.encode("utf-8", errors="ignore"))

        def _json(self, obj, code=200):
            data = json.dumps(obj).encode("utf-8")
            self.send_response(code)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)

        def _read_json(self):
            try:
                n = int(self.headers.get("Content-Length", "0"))
            except Exception:
                n = 0
            if n <= 0:
                return {}
            raw = self.rfile.read(n)
            try:
                return json.loads(raw.decode("utf-8", errors="ignore"))
            except Exception:
                return {}

        def _handle_ws(self):
            if not self._client_ok():
                return self._deny()

            if self.headers.get("Upgrade", "").lower() != "websocket":
                return self._deny(400, "Missing Upgrade: websocket")

            key = self.headers.get("Sec-WebSocket-Key", "")
            if not key:
                return self._deny(400, "Missing Sec-WebSocket-Key")

            accept = ws_make_accept(key)

            self.send_response(101, "Switching Protocols")
            self.send_header("Upgrade", "websocket")
            self.send_header("Connection", "Upgrade")
            self.send_header("Sec-WebSocket-Accept", accept)
            self.end_headers()

            sock = self.connection
            sock.settimeout(60)
            hub.add(sock)

            init = {
                "type": "state",
                "current": os.path.basename(slideshow.current_path) if slideshow.current_path else "",
                "delay_s": int(slideshow.delay_ms / 1000),
                "ts": now_ts(),
            }
            try:
                ws_send_text(sock, json.dumps(init, ensure_ascii=False))
            except Exception:
                hub.remove(sock)
                try:
                    sock.close()
                except Exception:
                    pass
                return

            try:
                while True:
                    opcode, payload = ws_recv_frame(sock)
                    if opcode is None:
                        break
                    if opcode == 0x8:
                        break
                    if opcode == 0x9:
                        try:
                            sock.sendall(b"\x8A\x00")
                        except Exception:
                            break
                        continue
                    if opcode != 0x1:
                        continue

                    try:
                        txt = payload.decode("utf-8", errors="ignore")
                        msg = json.loads(txt) if txt.strip().startswith("{") else {}
                    except Exception:
                        msg = {}

                    if msg.get("type") == "set_delay":
                        delay_s = msg.get("delay_s", DEFAULT_DELAY_S)
                        d = mgr.set_delay(delay_s)
                        QMetaObject.invokeMethod(slideshow, "apply_delay",
                            Qt.ConnectionType.QueuedConnection, Q_ARG(int, d))
                    elif msg.get("type") == "next":
                        QTimer.singleShot(0, slideshow.show_next)
                    elif msg.get("type") == "show":
                        name = msg.get("name", "")
#                        QTimer.singleShot(0, lambda n=name: slideshow.show_specific_name(n))
                        QMetaObject.invokeMethod(slideshow, "show_specific_name",
                            Qt.ConnectionType.QueuedConnection, Q_ARG(str, name))
                    elif msg.get("type") == "refresh":
                        mgr.refresh_files()
                        QTimer.singleShot(0, slideshow.refresh_from_manager)
            finally:
                hub.remove(sock)
                try:
                    sock.close()
                except Exception:
                    pass

        def do_GET(self):
            if not self._client_ok():
                return self._deny()

            u = urlparse(self.path)
            route = strip_to_known_route(u.path)

            if route == "/ws":
                return self._handle_ws()

            if route in ("/", "/index.html"):
                html = INDEX_HTML.encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(html)))
                self.end_headers()
                self.wfile.write(html)
                return

            if route == "/api/images":
                mgr.refresh_files()
                return self._json({
                    "ok": True,
                    "folder": mgr.folder,
                    "locale": read_locale_value(),
                    "delay_s": int(slideshow.delay_ms / 1000),
                    "current": os.path.basename(slideshow.current_path) if slideshow.current_path else "",
                    "images": mgr.list_images(),
                })

            if route == "/thumb":
                qs = parse_qs(u.query or "")
                name = (qs.get("name") or [""])[0]
                name = unquote(name)
                if not name:
                    return self._deny(400, "Missing name")

                try:
                    img_path = safe_join(mgr.folder, os.path.basename(name))
                    data = make_thumbnail_bytes(img_path)
                except FileNotFoundError:
                    return self._deny(404, "Not found")
                except Exception:
                    return self._deny(500, "thumb error")

                self.send_response(200)
                self.send_header("Content-Type", "image/jpeg")
                self.send_header("Content-Length", str(len(data)))
                self.end_headers()
                self.wfile.write(data)
                return

            return self._deny(404, "Not found")

        def do_POST(self):
            if not self._client_ok():
                return self._deny()

            u = urlparse(self.path)
            route = strip_to_known_route(u.path)

            # Upload: multipart/form-data (mobile compatible)
            if route == "/api/upload":
                try:
                    n = int(self.headers.get("Content-Length", "0"))
                except Exception:
                    n = 0
                if n <= 0:
                    return self._json({"ok": False, "error": "empty upload"}, 400)
                if n > MAX_UPLOAD_BYTES:
                    return self._json({"ok": False, "error": "upload too large"}, 413)

                ctype = self.headers.get("Content-Type", "")
                body = self.rfile.read(n)

                filename, file_bytes = parse_multipart_first_file(ctype, body)
                if not filename or file_bytes is None:
                    return self._json({"ok": False, "error": "bad multipart upload"}, 400)

                try:
                    saved = mgr.save_uploaded_image_bytes_as_jpeg(file_bytes, filename)
                except Exception as e:
                    return self._json({"ok": False, "error": str(e)}, 400)

                QTimer.singleShot(0, slideshow.refresh_from_manager)
                return self._json({"ok": True, "saved_as": saved})

            body = self._read_json()

            if route == "/api/images/toggle":
                name = body.get("name", "")
                enabled = bool(body.get("enabled", True))
                if not name:
                    return self._json({"ok": False, "error": "missing name"}, 400)
                mgr.set_enabled(name, enabled)
                QTimer.singleShot(0, slideshow.refresh_from_manager)
                return self._json({"ok": True})

            if route == "/api/images/fit":
                name = body.get("name", "")
                mode = body.get("mode", "auto")
                if not name:
                    return self._json({"ok": False, "error": "missing name"}, 400)
                was_current = os.path.basename(slideshow.current_path or "") == os.path.basename(name)
                try:
                    new_name = mgr.set_fit_mode(name, mode)
                except (FileNotFoundError, FileExistsError, ValueError) as e:
                    return self._json({"ok": False, "error": str(e)}, 400)
                except Exception as e:
                    return self._json({"ok": False, "error": str(e)}, 500)
                if was_current:
                    QTimer.singleShot(0, lambda n=new_name: slideshow.refresh_from_manager(n))
                else:
                    QTimer.singleShot(0, slideshow.refresh_from_manager)
                return self._json({"ok": True, "name": new_name})

            if route == "/api/images/delete":
                name = body.get("name", "")
                if not name:
                    return self._json({"ok": False, "error": "missing name"}, 400)
                try:
                    mgr.delete(name)
                except Exception as e:
                    return self._json({"ok": False, "error": str(e)}, 500)
                QTimer.singleShot(0, slideshow.refresh_from_manager)
                return self._json({"ok": True})

            if route == "/api/images/refresh":
                mgr.refresh_files()
                QTimer.singleShot(0, slideshow.refresh_from_manager)
                return self._json({"ok": True})

            if route == "/api/slideshow/next":
                QTimer.singleShot(0, slideshow.show_next)
                return self._json({"ok": True})

            if route == "/api/slideshow/show":
                name = body.get("name", "")
                QMetaObject.invokeMethod(slideshow, "show_specific_name",
                         Qt.ConnectionType.QueuedConnection, Q_ARG(str, name))
#                QTimer.singleShot(0, lambda n=name: slideshow.show_specific_name(n))
                return self._json({"ok": True})

            if route == "/api/picsum":
                try:
                    fname = mgr.download_picsum()
                except Exception as e:
                    return self._json({"ok": False, "error": str(e)}, 500)
                QTimer.singleShot(0, slideshow.refresh_from_manager)
                return self._json({"ok": True, "saved_as": fname})

            if route == "/api/update":
                try:
                    url = read_update_url()
                    n = update_script_from_url(url)
                except (FileNotFoundError, KeyError, ValueError) as e:
                    return self._json({"ok": False, "error": str(e)}, 400)
                except Exception as e:
                    return self._json({"ok": False, "error": str(e)}, 500)
                return self._json({"ok": True, "bytes": n, "url": url})

            if route == "/api/config/delay":
                d = mgr.set_delay(body.get("delay_s", DEFAULT_DELAY_S))
                QMetaObject.invokeMethod(slideshow, "apply_delay",
                    Qt.ConnectionType.QueuedConnection, Q_ARG(int, d))
                return self._json({"ok": True, "delay_s": d})

            if route == "/api/cec/playback":
                res = run_cec(["--playback", "-S"])
                return self._json(res, 200 if res["ok"] else 500)

            if route == "/api/cec/standby":
                res = run_cec(["--to", "0", "--standby"])
                return self._json(res, 200 if res["ok"] else 500)

            if route == "/api/cec/image_view_on":
                res = run_cec(["--to", "0", "--image-view-on"])
                return self._json(res, 200 if res["ok"] else 500)

            if route == "/api/cec/active_source":
                x = body.get("x", mgr.active_source_x)
                try:
                    x = int(x)
                except Exception:
                    x = mgr.active_source_x
                mgr.active_source_x = x
                mgr.save_state()

                phys = f"{x}.0.0.0"
                res = run_cec(["--to", "0", "--active-source", f"phys-addr={phys}"])
                res["phys_addr"] = phys
                return self._json(res, 200 if res["ok"] else 500)

            return self._deny(404, "Not found")

    return Handler

# IMPORTANT: all paths are RELATIVE (no leading slash) so reverse proxy base path works.
INDEX_HTML = r"""<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>fehb</title>
  <style>
    body { font-family: sans-serif; margin: 16px; background: #111; color: #eee; }
    .row { display: flex; gap: 8px; align-items: center; flex-wrap: wrap; }
    button { padding: 8px 10px; border: 0; border-radius: 8px; cursor: pointer; }
    button.primary { background: #3b82f6; color: #fff; }
    button.danger { background: #ef4444; color: #fff; }
    button.gray { background: #333; color: #eee; }
    input, select { padding: 7px 8px; border-radius: 10px; border: 1px solid #333; background:#0f0f0f; color:#eee; }
    .grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(260px, 1fr)); gap: 12px; margin-top: 12px; }
    .card { background: #1b1b1b; border-radius: 14px; padding: 10px; box-shadow: 0 0 0 1px rgba(255,255,255,0.06) inset; }
    .card.current { outline: 2px solid rgba(59,130,246,0.9); }
    .thumb { width: 100%; aspect-ratio: 16/9; background: #000; border-radius: 10px; object-fit: cover; display: block; }
    .meta { margin-top: 8px; font-size: 14px; opacity: 0.9; word-break: break-all; }
    .small { font-size: 12px; opacity: 0.7; }
    label { display: inline-flex; gap: 6px; align-items: center; cursor: pointer; }
    input[type="checkbox"] { transform: scale(1.2); }

    /* Current thumbnail (top-right) */
    #currentThumbWrap {
      position: fixed;
      top: 12px;
      right: 12px;
      width: 180px;
      aspect-ratio: 16/9;
      border-radius: 12px;
      overflow: hidden;
      box-shadow: 0 10px 30px rgba(0,0,0,0.55), 0 0 0 1px rgba(255,255,255,0.10) inset;
      background: #000;
      z-index: 9999;
      display: none;
      opacity: 0.5;
      pointer-events: none;
    }
    #currentThumb {
      width: 100%;
      height: 100%;
      object-fit: cover;
      display: block;
    }

    /* Hide file inputs but keep them accessible */
    .hiddenFile { display:none; }
  </style>
</head>
<body>
  <div id="currentThumbWrap" title="Currently showing">
    <img id="currentThumb" alt="current thumbnail">
  </div>

  <h2 style="margin:0 0 18px 0;">fehb control</h2> <!-- more margin below -->

  <div class="row" style="margin-bottom:10px;">
    <button class="primary" onclick="apiPost('api/slideshow/next', {})">Next image</button>
    <button class="gray" onclick="apiPost('api/images/refresh', {})">Refresh list</button>
    <button class="gray" onclick="updateSelf()">Update</button>
    <button class="primary" onclick="apiPost('api/picsum', {})">Download picsum 1920×1080</button>

    <span class="small">Delay (s):</span>
    <input id="delay" type="number" min="1" max="86400" value="15" style="width:90px;">
    <button class="gray" onclick="setDelay()">Apply</button>

    <span style="flex:1 1 auto;"></span>

    <!-- Mobile-friendly upload choice -->
    <input id="filePick" class="hiddenFile" type="file" accept="image/*">
    <input id="fileCam"  class="hiddenFile" type="file" accept="image/*" capture="environment">

    <button class="primary" onclick="document.getElementById('fileCam').click()">Take photo</button>
    <button class="primary" onclick="document.getElementById('filePick').click()">Choose file</button>
  </div>

  <h3>CEC</h3>
  <div class="row">
    <button class="gray" onclick="apiPost('api/cec/playback', {})">Playback (-S)</button>
    <button class="gray" onclick="apiPost('api/cec/image_view_on', {})">Image View On</button>
    <button class="danger" onclick="apiPost('api/cec/standby', {})">Standby (TV)</button>
    <span class="small">Active-source x:</span>
    <input id="asx" type="number" min="0" max="15" value="2" style="width:70px;">
    <button class="gray" onclick="setActiveSource()">Set active source</button>
  </div>

  <h3>Images</h3>
  <div id="status" class="small"></div>
  <div id="grid" class="grid"></div>

<script>
let ws = null;
let current = "";
let wsAttempts = 0;
let wsTimer = null;

function baseDirPath() {
  return location.pathname.replace(/[^\/]*$/, "");
}
function wsUrl() {
  const proto = (location.protocol === "https:") ? "wss://" : "ws://";
  return proto + location.host + baseDirPath() + "ws";
}

function scheduleReconnect(){
  if (wsTimer) return;
  // exponential backoff with jitter, capped
  const base = Math.min(30000, 500 * Math.pow(2, wsAttempts)); // 0.5s, 1s, 2s, ... up to 30s
  const jitter = Math.floor(Math.random() * 250);
  const delay = base + jitter;
  wsTimer = setTimeout(() => {
    wsTimer = null;
    connectWS();
  }, delay);
}

function connectWS(){
  try {
    if(ws && (ws.readyState === 0 || ws.readyState === 1)) return;

    ws = new WebSocket(wsUrl());

    ws.onopen = () => {
      wsAttempts = 0;
      setStatus("WS connected", false);
    };

    ws.onclose = () => {
      ws = null;
      wsAttempts++;
      setStatus("WS disconnected (reconnecting…)", true);
      scheduleReconnect();
    };

    ws.onerror = () => {
      // error will usually be followed by close
      setStatus("WS error (reconnecting…)", true);
    };

    ws.onmessage = (ev) => {
      let msg = null;
      try { msg = JSON.parse(ev.data); } catch(e) { return; }
      if(!msg || msg.type !== "state") return;

      if(typeof msg.delay_s === "number"){
        document.getElementById("delay").value = msg.delay_s;
      }
      if(typeof msg.current === "string"){
        setCurrent(msg.current);
      }
    };
  } catch(e) {
    ws = null;
    wsAttempts++;
    setStatus("WS failed (reconnecting…)", true);
    scheduleReconnect();
  }
}

function cssSafe(s){
  return btoa(unescape(encodeURIComponent(s))).replace(/=+$/,'').replace(/\+/g,'-').replace(/\//g,'_');
}

function setCurrent(name){
  current = name || "";

  // highlight card
  document.querySelectorAll(".card").forEach(c => c.classList.remove("current"));
  if(current){
    const el = document.getElementById("card_" + cssSafe(current));
    if(el) el.classList.add("current");
  }

  // top-right thumb
  const wrap = document.getElementById("currentThumbWrap");
  const img = document.getElementById("currentThumb");
  if(current){
    wrap.style.display = "block";
    img.src = `thumb?name=${encodeURIComponent(current)}&t=${Date.now()}`;
  } else {
    wrap.style.display = "none";
    img.removeAttribute("src");
  }
}

async function apiGet(url){
  const r = await fetch(url);
  const t = await r.text();
  try { return JSON.parse(t); } catch(e){ return {ok:false, raw:t}; }
}
async function apiPost(url, body){
  const r = await fetch(url, {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify(body||{})});
  const t = await r.text();
  let j; try { j = JSON.parse(t); } catch(e){ j = {ok:false, raw:t}; }
  if(!r.ok || j.ok === false){
    setStatus("Error: " + (j.error || j.stderr || j.raw || r.status), true);
  } else {
    setStatus("OK", false);
  }
  if(url.startsWith('api/images') || url.startsWith('api/picsum') || url.startsWith('api/upload')){
    await loadImages();
  }
  return j;
}
function setStatus(msg, bad){
  const el = document.getElementById('status');
  el.textContent = msg;
  el.style.color = bad ? '#f87171' : '#9ca3af';
}
function fmtBytes(n){
  if(!n) return "0 B";
  const u = ["B","KB","MB","GB"];
  let i=0; let x=n;
  while(x>=1024 && i<u.length-1){ x/=1024; i++; }
  return x.toFixed(i?1:0)+" "+u[i];
}
function fmtTime(ts){
  if(!ts) return "";
  const d = new Date(ts*1000);
  return d.toLocaleString();
}
function fmtRatio(r){
  if(!r || !isFinite(r)) return "";
  return r.toFixed(3);
}
function fmtDim(w,h){
  if(!w || !h) return "";
  return `${w}×${h}`;
}

async function loadImages(){
  const j = await apiGet('api/images');
  if(!j.ok){ setStatus("Failed to load images", true); return; }

  if(typeof j.delay_s === "number"){
    document.getElementById("delay").value = j.delay_s;
  }
  if(typeof j.current === "string"){
    setCurrent(j.current);
  }

  const grid = document.getElementById('grid');
  grid.innerHTML = "";
  const imgs = j.images || [];
  setStatus(`Folder: ${j.folder} — ${imgs.length} files`, false);

  for(const it of imgs){
    const card = document.createElement('div');
    card.className = 'card';
    card.id = "card_" + cssSafe(it.name);
    if(it.name === current) card.classList.add("current");

    const img = document.createElement('img');
    img.className = 'thumb';
    img.loading = 'lazy';
    img.src = `thumb?name=${encodeURIComponent(it.name)}`;

    const meta = document.createElement('div');
    meta.className = 'meta';
    meta.textContent = it.name;

    const small = document.createElement('div');
    small.className = 'small';
    {
      const parts = [];
      const sz = fmtBytes(it.size);
      if(sz) parts.push(sz);
      const tm = fmtTime(it.mtime);
      if(tm) parts.push(tm);
      const dim = fmtDim(it.width, it.height);
      if(dim) parts.push(dim);
      const r = fmtRatio(it.ratio);
      if(r) parts.push(`W/H ${r}`);
      small.textContent = parts.join(' • ');
    }

    const fitInfo = document.createElement('div');
    fitInfo.className = 'small';
    {
      const tag = (it.fit_mode || 'auto');
      const eff = (it.fit_effective || '');
      if(tag === 'auto' && eff){
        fitInfo.textContent = `Fit: ${eff} (auto)`;
      } else {
        fitInfo.textContent = `Fit: ${tag}`;
      }
    }

    const row = document.createElement('div');
    row.className = 'row';
    row.style.marginTop = "8px";

    const showBtn = document.createElement('button');
    showBtn.className = 'primary';
    showBtn.textContent = 'Show now';
    showBtn.onclick = async () => {
      if(ws && ws.readyState === 1){
        ws.send(JSON.stringify({type:"show", name: it.name}));
      } else {
        await apiPost('api/slideshow/show', {name: it.name});
      }
    };

    const fitLabel = document.createElement('span');
    fitLabel.className = 'small';
    fitLabel.textContent = 'Fit:';

    const fitSel = document.createElement('select');
    fitSel.innerHTML = `
      <option value="auto">Auto</option>
      <option value="width">Fit width</option>
      <option value="height">Fit height (bars)</option>
    `;
    fitSel.value = it.fit_mode || 'auto';
    fitSel.title = 'Auto: height/width > 0.76 => Fit height (bars); otherwise Fit width';
    fitSel.onchange = async () => {
      await apiPost('api/images/fit', {name: it.name, mode: fitSel.value});
    };

    const label = document.createElement('label');
    const cb = document.createElement('input');
    cb.type = 'checkbox';
    cb.checked = !!it.enabled;
    cb.onchange = () => apiPost('api/images/toggle', {name: it.name, enabled: cb.checked});
    label.appendChild(cb);
    label.appendChild(document.createTextNode('enabled'));

    const del = document.createElement('button');
    del.className = 'danger';
    del.textContent = 'Delete';
    del.onclick = async () => {
      if(confirm(`Delete ${it.name}?`)){
        await apiPost('api/images/delete', {name: it.name});
      }
    };

    row.appendChild(showBtn);
    row.appendChild(fitLabel);
    row.appendChild(fitSel);
    row.appendChild(label);
    row.appendChild(del);

    if(!it.enabled){
      card.style.opacity = "0.55";
    }

    card.appendChild(img);
    card.appendChild(meta);
    card.appendChild(small);
    card.appendChild(fitInfo);
    card.appendChild(row);
    grid.appendChild(card);
  }
}

async function setActiveSource(){
  const x = parseInt(document.getElementById('asx').value || "2", 10);
  await apiPost('api/cec/active_source', {x});
}

async function setDelay(){
  const d = parseInt(document.getElementById('delay').value || "15", 10);
  const j = await apiPost('api/config/delay', {delay_s:d});
  if(j && typeof j.delay_s === 'number'){
    document.getElementById('delay').value = j.delay_s;
  }
}

async function updateSelf(){
  if(!confirm("Update script from ~/.tvphotos.yml update_url?")) return;
  const j = await apiPost('api/update', {});
  if(j && j.ok){
    setStatus(`Updated script (${j.bytes} bytes)`, false);
  }
}

async function uploadFile(f){
  if(!f){
    setStatus("No file selected", true);
    return;
  }
  const fd = new FormData();
  fd.append("file", f, f.name);

  setStatus("Uploading...", false);
  const r = await fetch('api/upload', {method:'POST', body: fd});
  const t = await r.text();
  let j; try { j = JSON.parse(t); } catch(e){ j = {ok:false, raw:t}; }

  if(!r.ok || j.ok === false){
    setStatus("Upload error: " + (j.error || j.raw || r.status), true);
  } else {
    setStatus("Uploaded: " + j.saved_as, false);
    await loadImages();
  }
}

document.getElementById("filePick").addEventListener("change", (e) => {
  const f = e.target.files && e.target.files[0];
  e.target.value = "";
  uploadFile(f);
});
document.getElementById("fileCam").addEventListener("change", (e) => {
  const f = e.target.files && e.target.files[0];
  e.target.value = "";
  uploadFile(f);
});

// start
connectWS();
loadImages();
</script>
</body>
</html>
"""


def start_server(mgr, slideshow, hub, host="0.0.0.0", port=DEFAULT_PORT):
    Handler = make_handler(mgr, slideshow, hub)
    httpd = ThreadingHTTPServer((host, port), Handler)
    t = threading.Thread(target=httpd.serve_forever, daemon=True)
    t.start()
    return httpd


def main():
    delay = int(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_DELAY_S
    folder = sys.argv[2] if len(sys.argv) > 2 else "~/wallpapers"
    port = int(sys.argv[3]) if len(sys.argv) > 3 else DEFAULT_PORT

    mgr = ImageManager(folder)
    mgr.set_delay(delay)

    hub = WebSocketHub()
    app = QApplication(sys.argv)
    apply_locale_from_config()
    w = Slideshow(mgr, hub, delay_s=mgr.delay_s)

    start_server(mgr, w, hub, host="0.0.0.0", port=port)

    addrs = get_ipv4_addrs()
    print("[fehb] web ui URLs:")
    for ip in addrs:
        print(f"  http://{ip}:{port}/   (reverse-proxy safe; relative paths; WS at ./ws)")

    return app.exec()


if __name__ == "__main__":
    raise SystemExit(main())
