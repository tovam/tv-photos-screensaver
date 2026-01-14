#!/usr/bin/env python3
import os
import sys
import glob
import time
import json
import html
import random
import threading
import subprocess
import urllib.error
import urllib.parse
import urllib.request
import ipaddress
import base64
import hashlib
import re
import locale
import socket
import select
import secrets
import shutil
import atexit
import signal
import ctypes
import logging
from dataclasses import dataclass
from typing import Callable, Dict, Optional
from datetime import datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs, unquote, urlencode

# --- Auto X11 env for running from tty/ssh/systemd ---
if not os.environ.get("DISPLAY"):
    os.environ["DISPLAY"] = ":0"
if not os.environ.get("XAUTHORITY"):
    os.environ["XAUTHORITY"] = os.path.expanduser("~/.Xauthority")

_LOG_LEVEL = os.environ.get("TVPHOTOS_LOG_LEVEL", "INFO").upper()
if not logging.getLogger().handlers:
    logging.basicConfig(
        level=getattr(logging, _LOG_LEVEL, logging.INFO),
        format="%(asctime)s [%(levelname)s] %(message)s",
    )
log = logging.getLogger("tvphotos")

from PIL import Image, ImageOps
from PIL.ImageQt import ImageQt

from PyQt6.QtCore import Qt, QTimer, QMetaObject, Q_ARG, QUrl, pyqtSlot
from PyQt6.QtGui import QPixmap, QFont, QKeySequence, QShortcut
try:
    from PyQt6.QtMultimedia import QAudioOutput, QMediaPlayer
    from PyQt6.QtMultimediaWidgets import QVideoWidget
    QT_MULTIMEDIA_AVAILABLE = True
except Exception as exc:
    QAudioOutput = None
    QMediaPlayer = None
    QVideoWidget = None
    QT_MULTIMEDIA_AVAILABLE = False
    log.warning("QtMultimedia unavailable; live stream disabled: %s", exc)
from PyQt6.QtWidgets import (
    QApplication,
    QLabel,
    QWidget,
    QGraphicsDropShadowEffect,
    QProgressBar,
    QFrame,
    QVBoxLayout,
    QTabWidget,
    QListWidget,
    QListWidgetItem,
)


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
NAVIDROME_CONFIG_PATH = "./navidrome_credentials.yml"
FIT_TAG_WIDTH = "__fitw"
FIT_TAG_HEIGHT = "__fith"
FIT_HEIGHT_RATIO_THRESHOLD = 0.76
NAVIDROME_API_VERSION = "1.16.1"
NAVIDROME_CLIENT_NAME = "tvphotos"
NAVIDROME_RANDOM_SIZE = 50
MPV_SOCKET_PATH = "/tmp/tvphotos-mpv.sock"
MPV_CACHE_SECS = 30
MPV_CACHE_PAUSE_WAIT_SECS = 5
MPV_VOLUME_MAX = 200
LIVE_STREAM_VIDEO_ID = "x3b68jn"
LIVE_STREAM_USER_AGENT = (
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/120.0.0.0 Safari/537.36"
)
LIVE_STREAM_ORIGIN = "https://www.dailymotion.com"
LIVE_STREAM_REFERER = f"https://www.dailymotion.com/video/{LIVE_STREAM_VIDEO_ID}"
LIVE_STREAM_WIDTH_RATIO = 0.25
LIVE_STREAM_MIN_WIDTH = 280
LIVE_STREAM_ASPECT_RATIO = 16 / 9


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


def fetch_stream_url(video_id, referer_url):
    url = f"https://www.dailymotion.com/player/metadata/video/{video_id}"
    request = urllib.request.Request(
        url,
        headers={
            "User-Agent": LIVE_STREAM_USER_AGENT,
            "Accept": "application/json",
            "Referer": referer_url,
            "Origin": LIVE_STREAM_ORIGIN,
        },
    )
    with urllib.request.urlopen(request, timeout=10) as response:
        data = json.load(response)

    qualities = data.get("qualities", {})
    for quality in ("auto", "1080", "720", "480", "360", "240", "144"):
        options = qualities.get(quality) or []
        for option in options:
            stream_url = option.get("url")
            if stream_url:
                return stream_url

    return None


def _proxy_url(target_url, proxy_base):
    encoded = urllib.parse.quote(target_url, safe="")
    return f"{proxy_base}/proxy?u={encoded}"


def _rewrite_tag_uri(line, base_url, proxy_base):
    def replace(match):
        original = match.group(1)
        absolute = urllib.parse.urljoin(base_url, original)
        return f'URI="{_proxy_url(absolute, proxy_base)}"'

    return re.sub(r'URI="([^"]+)"', replace, line)


def rewrite_m3u8(text, base_url, proxy_base):
    lines = []
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line:
            lines.append("")
            continue
        if line.startswith("#"):
            lines.append(_rewrite_tag_uri(raw_line, base_url, proxy_base))
            continue

        absolute = urllib.parse.urljoin(base_url, line)
        lines.append(_proxy_url(absolute, proxy_base))

    return "\n".join(lines) + "\n"


class HLSProxyHandler(BaseHTTPRequestHandler):
    def do_GET(self):  # noqa: N802
        self._handle_request(head_only=False)

    def do_HEAD(self):  # noqa: N802
        self._handle_request(head_only=True)

    def log_message(self, format, *args):
        return

    def _handle_request(self, *, head_only):
        parsed = urllib.parse.urlparse(self.path)
        if parsed.path in ("/", "/index.m3u8"):
            upstream_url = self.server.master_url
        elif parsed.path == "/proxy":
            query = urllib.parse.parse_qs(parsed.query)
            target = query.get("u", [""])[0]
            if not target:
                self.send_error(400, "Missing proxy target")
                return
            upstream_url = urllib.parse.unquote(target)
        else:
            self.send_error(404, "Not found")
            return

        try:
            self._stream_upstream(upstream_url, head_only=head_only)
        except urllib.error.HTTPError as exc:
            self.send_error(exc.code, exc.reason)
        except Exception as exc:
            self.send_error(502, f"Proxy error: {exc}")

    def _stream_upstream(self, upstream_url, *, head_only):
        headers = dict(self.server.base_headers)
        range_header = self.headers.get("Range")
        if range_header:
            headers["Range"] = range_header

        request = urllib.request.Request(
            upstream_url,
            headers=headers,
            method="HEAD" if head_only else "GET",
        )

        with urllib.request.urlopen(request, timeout=15) as response:
            content_type = response.headers.get("Content-Type", "")
            is_playlist = "mpegurl" in content_type or upstream_url.endswith(".m3u8")

            if is_playlist and not head_only:
                body = response.read()
                text = body.decode("utf-8", errors="ignore")
                rewritten = rewrite_m3u8(
                    text,
                    base_url=upstream_url,
                    proxy_base=self.server.proxy_base,
                )
                payload = rewritten.encode("utf-8")

                self.send_response(response.status)
                self.send_header("Content-Type", "application/vnd.apple.mpegurl")
                self.send_header("Content-Length", str(len(payload)))
                self.send_header("Cache-Control", "no-store")
                self.end_headers()
                self.wfile.write(payload)
                return

            self.send_response(response.status)
            hop_by_hop = {
                "connection",
                "keep-alive",
                "proxy-authenticate",
                "proxy-authorization",
                "te",
                "trailers",
                "transfer-encoding",
                "upgrade",
            }
            for key, value in response.headers.items():
                if key.lower() in hop_by_hop:
                    continue
                self.send_header(key, value)
            if is_playlist:
                self.send_header("Cache-Control", "no-store")
            self.end_headers()

            if not head_only:
                shutil.copyfileobj(response, self.wfile)


def start_hls_proxy(master_url, referer_url):
    server = ThreadingHTTPServer(("127.0.0.1", 0), HLSProxyHandler)
    server.master_url = master_url
    server.base_headers = {
        "User-Agent": LIVE_STREAM_USER_AGENT,
        "Referer": referer_url,
        "Origin": LIVE_STREAM_ORIGIN,
        "Accept": "*/*",
    }
    host, port = server.server_address
    server.proxy_base = f"http://{host}:{port}"
    server.daemon_threads = True

    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()

    return server, f"{server.proxy_base}/index.m3u8"


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


def read_config_value_from(path, key, required=False):
    path = os.path.expanduser(path)
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


def read_delay_value():
    val = read_config_value("delay_s", required=False)
    if val is None:
        val = read_config_value("delay", required=False)
    if val is None:
        return None
    try:
        d = int(val)
    except Exception:
        return None
    if d < 1:
        d = 1
    if d > 24 * 3600:
        d = 24 * 3600
    return d


def read_navidrome_config():
    path = os.path.expanduser(NAVIDROME_CONFIG_PATH)
    url = read_config_value_from(path, "url", required=False)
    if url is None:
        url = read_config_value_from(path, "server", required=False)
    user = read_config_value_from(path, "user", required=False)
    if user is None:
        user = read_config_value_from(path, "username", required=False)
    password = read_config_value_from(path, "password", required=False)
    if not url or not user or not password:
        return None
    return {
        "url": url,
        "user": user,
        "password": password,
    }


def default_delay_s():
    d = read_delay_value()
    return d if d is not None else DEFAULT_DELAY_S


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
# Navidrome / Music helpers
# ----------------------------
class NavidromeClient:
    def __init__(self, base_url, user, password):
        self.base_url = base_url.rstrip("/")
        self.user = user
        self.password = password

    def _auth_params(self):
        salt = secrets.token_hex(6)
        token = hashlib.md5((self.password + salt).encode("utf-8")).hexdigest()
        return {
            "u": self.user,
            "t": token,
            "s": salt,
            "v": NAVIDROME_API_VERSION,
            "c": NAVIDROME_CLIENT_NAME,
            "f": "json",
        }

    def _request(self, endpoint, params=None):
        q = {}
        q.update(self._auth_params())
        if params:
            q.update(params)
        url = self.base_url + "/rest/" + endpoint + ".view?" + urlencode(q)
        req = urllib.request.Request(url, headers={"User-Agent": "tvphotos/1.0"})
        with urllib.request.urlopen(req, timeout=20) as resp:
            data = resp.read()
        try:
            j = json.loads(data.decode("utf-8", errors="ignore"))
        except Exception:
            raise ValueError("invalid navidrome response")
        rsp = j.get("subsonic-response", {})
        if rsp.get("status") != "ok":
            err = rsp.get("error", {}) or {}
            raise ValueError(err.get("message") or "navidrome error")
        return rsp

    def get_random_songs(self, size=NAVIDROME_RANDOM_SIZE):
        rsp = self._request("getRandomSongs", {"size": int(size)})
        songs = rsp.get("randomSongs", {}).get("song", []) or []
        if isinstance(songs, dict):
            songs = [songs]
        return songs

    def get_playlists(self):
        rsp = self._request("getPlaylists")
        playlists = rsp.get("playlists", {}).get("playlist", []) or []
        if isinstance(playlists, dict):
            playlists = [playlists]
        return playlists

    def get_playlist(self, playlist_id):
        rsp = self._request("getPlaylist", {"id": playlist_id})
        pl = rsp.get("playlist", {}) or {}
        entries = pl.get("entry") or pl.get("song") or []
        if isinstance(entries, dict):
            entries = [entries]
        return pl, entries

    def stream_url(self, song_id):
        q = self._auth_params()
        q["id"] = song_id
        return self.base_url + "/rest/stream.view?" + urlencode(q)


def _set_pdeathsig(sig=signal.SIGTERM):
    try:
        libc = ctypes.CDLL("libc.so.6")
        PR_SET_PDEATHSIG = 1
        libc.prctl(PR_SET_PDEATHSIG, sig)
    except Exception:
        pass


class MPVController:
    _cleanup_registered = False

    def __init__(self, socket_path=MPV_SOCKET_PATH):
        self.socket_path = socket_path
        self.proc = None
        self.lock = threading.Lock()
        self._register_cleanup()

    def _register_cleanup(self):
        if MPVController._cleanup_registered:
            return
        MPVController._cleanup_registered = True
        atexit.register(self.shutdown)

    def start(self):
        if self.proc and self.proc.poll() is None:
            return True
        if shutil.which("mpv") is None:
            return False
        try:
            if os.path.exists(self.socket_path):
                os.remove(self.socket_path)
        except Exception:
            pass
        cmd = [
            "mpv",
            "--no-video",
            "--idle=yes",
            "--force-window=no",
            "--input-ipc-server=" + self.socket_path,
            "--cache=yes",
            f"--cache-secs={MPV_CACHE_SECS}",
            "--cache-pause-initial=yes",
            f"--cache-pause-wait={MPV_CACHE_PAUSE_WAIT_SECS}",
            f"--volume-max={MPV_VOLUME_MAX}",
            "--quiet",
        ]
        preexec_fn = _set_pdeathsig if sys.platform.startswith("linux") else None
        try:
            self.proc = subprocess.Popen(
                cmd,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                preexec_fn=preexec_fn,
            )
        except Exception:
            self.proc = None
            return False
        for _ in range(50):
            if os.path.exists(self.socket_path):
                return True
            time.sleep(0.1)
        return False

    def _send(self, obj, expect_reply=True):
        with self.lock:
            try:
                s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                s.settimeout(1.5)
                s.connect(self.socket_path)
                payload = json.dumps(obj).encode("utf-8") + b"\n"
                s.sendall(payload)
                if not expect_reply:
                    s.close()
                    return None
                data = b""
                while not data.endswith(b"\n"):
                    chunk = s.recv(4096)
                    if not chunk:
                        break
                    data += chunk
                s.close()
                if not data:
                    return None
                return json.loads(data.decode("utf-8", errors="ignore"))
            except Exception:
                return None

    def load(self, url):
        self._send({"command": ["loadfile", url, "replace"]}, expect_reply=False)

    def set_pause(self, paused):
        self._send({"command": ["set_property", "pause", bool(paused)]})

    def stop(self):
        self._send({"command": ["stop"]})

    def set_volume(self, volume):
        self._send({"command": ["set_property", "volume", float(volume)]})

    def get_property(self, name):
        resp = self._send({"command": ["get_property", name]})
        if resp and resp.get("error") == "success":
            return resp.get("data")
        return None

    def shutdown(self):
        proc = self.proc
        if not proc:
            return
        try:
            if proc.poll() is None:
                try:
                    proc.terminate()
                except Exception:
                    pass
                try:
                    proc.wait(timeout=2)
                except Exception:
                    try:
                        proc.kill()
                    except Exception:
                        pass
        finally:
            self.proc = None
            try:
                if os.path.exists(self.socket_path):
                    os.remove(self.socket_path)
            except Exception:
                pass


class MusicManager:
    def __init__(self, hub, slideshow):
        self.hub = hub
        self.slideshow = slideshow
        self.lock = threading.Lock()
        self.client = None
        self.mpv = MPVController()
        self.enabled = False
        self.error = None
        self.queue = []
        self.current = None
        self.paused = False
        self.history = []
        self._override_next = None
        self._suppress_history_once = False
        self.volume = 70
        self.label = ""
        self.source = "random"
        self.playlist_id = None
        self.playlist_name = ""
        self.playlist_entries = []
        self.playlist_idx = 0
        self._last_ui_text = ""
        self._last_ui_progress = -1
        self._last_ui_duration = -1

        if self.slideshow:
            try:
                self.slideshow.attach_music(self)
            except Exception:
                pass

        cfg = read_navidrome_config()
        if not cfg:
            self.error = f"Missing or incomplete {NAVIDROME_CONFIG_PATH}"
            return
        self.client = NavidromeClient(cfg["url"], cfg["user"], cfg["password"])
        if not self.mpv.start():
            self.error = "mpv not available"
            return

        self.mpv.set_volume(self.volume)
        self.enabled = True
        t = threading.Thread(target=self._loop, daemon=True)
        t.start()

    def _set_ui_text(self, text):
        if not self.slideshow:
            return
        try:
            QMetaObject.invokeMethod(self.slideshow, "set_music_text",
                Qt.ConnectionType.QueuedConnection, Q_ARG(str, text))
        except Exception:
            pass

    def _set_ui_progress(self, value):
        if not self.slideshow:
            return
        try:
            QMetaObject.invokeMethod(self.slideshow, "set_music_progress",
                Qt.ConnectionType.QueuedConnection, Q_ARG(int, int(value)))
        except Exception:
            pass

    def _set_ui_duration(self, seconds):
        if not self.slideshow:
            return
        try:
            QMetaObject.invokeMethod(self.slideshow, "set_music_duration",
                Qt.ConnectionType.QueuedConnection, Q_ARG(int, int(seconds)))
        except Exception:
            pass

    def _notify_history(self):
        if not self.slideshow:
            return
        try:
            QMetaObject.invokeMethod(self.slideshow, "refresh_menu_history",
                Qt.ConnectionType.QueuedConnection)
        except Exception:
            pass

    def _fmt_clock(self, seconds):
        if seconds is None:
            return ""
        try:
            sec = int(seconds)
        except Exception:
            return ""
        if sec < 0:
            sec = 0
        h = sec // 3600
        m = (sec % 3600) // 60
        s = sec % 60
        if h > 0:
            return f"{h}:{m:02d}:{s:02d}"
        return f"{m}:{s:02d}"

    def _playback_times(self):
        if not self.enabled:
            return None, None
        pos = self.mpv.get_property("time-pos")
        dur = self.mpv.get_property("duration")
        try:
            pos = float(pos)
        except Exception:
            pos = None
        try:
            dur = float(dur)
        except Exception:
            dur = None
        if dur is not None and dur <= 0:
            dur = None
        if pos is not None and pos < 0:
            pos = 0
        return pos, dur

    def _progress_value_from_times(self, pos, dur):
        if pos is None or dur is None or dur <= 0:
            return None
        ratio = pos / dur
        if ratio < 0:
            ratio = 0
        if ratio > 1:
            ratio = 1
        return int(round(ratio * 1000))

    def _progress_value(self):
        pos, dur = self._playback_times()
        return self._progress_value_from_times(pos, dur)

    def _peek_next_track(self):
        with self.lock:
            source = self.source
            playlist_id = self.playlist_id
            playlist_entries = list(self.playlist_entries)
            playlist_idx = int(self.playlist_idx)
            queue = list(self.queue)

        if source == "playlist" and playlist_id:
            if not playlist_entries:
                return None
            if playlist_idx < 0 or playlist_idx >= len(playlist_entries):
                playlist_idx = 0
            for i in range(playlist_idx, len(playlist_entries)):
                song = playlist_entries[i]
                if not song or not isinstance(song, dict):
                    continue
                sid = song.get("id")
                if sid:
                    return {"id": sid, "title": song.get("title") or "", "artist": song.get("artist") or ""}
            return None

        for song in queue:
            if not song or not isinstance(song, dict):
                continue
            sid = song.get("id")
            if not sid:
                continue
            return {"id": sid, "title": song.get("title") or "", "artist": song.get("artist") or ""}
        return None

    def _next_label(self):
        track = self._peek_next_track()
        if not track:
            return ""
        return self._build_label(track)

    def _compose_ui_text(self, pos=None, dur=None):
        with self.lock:
            current = self.current
            label = self.label

        if not label and current:
            label = self._build_label(current)

        if current and (pos is None and dur is None):
            pos, dur = self._playback_times()
        pos_txt = self._fmt_clock(pos)
        dur_txt = self._fmt_clock(dur)
        if pos_txt and not dur_txt:
            dur_txt = "--:--"

        time_text = ""
        if pos_txt and dur_txt:
            time_text = f"{pos_txt} / {dur_txt}"
        elif pos_txt:
            time_text = pos_txt

        top_line = (label or "").strip()
        next_label = self._next_label()
        if not top_line and not time_text and not next_label:
            return ""

        parts = []
        if top_line:
            parts.append(f"<div>{html.escape(top_line)}</div>")
        if time_text:
            time_html = html.escape(time_text)
            parts.append(f"<div style=\"font-size:12pt; opacity:0.9;\">{time_html}</div>")
        if next_label:
            next_html = html.escape(f"Next: {next_label}")
            parts.append(f"<div style=\"font-size:9pt; opacity:0.8;\">{next_html}</div>")
        return "".join(parts)

    def _refresh_ui(self):
        pos = dur = None
        if self.current:
            pos, dur = self._playback_times()

        text = self._compose_ui_text(pos, dur)
        if text != self._last_ui_text:
            self._last_ui_text = text
            self._set_ui_text(text)
        progress = self._progress_value_from_times(pos, dur) if self.current else None
        progress_int = -1 if progress is None else progress
        if progress_int != self._last_ui_progress:
            self._last_ui_progress = progress_int
            self._set_ui_progress(progress_int)

        dur_int = -1
        if dur is not None:
            try:
                dur_int = int(dur)
            except Exception:
                dur_int = -1
        if dur_int != self._last_ui_duration:
            self._last_ui_duration = dur_int
            self._set_ui_duration(dur_int)

    def _broadcast(self):
        if not self.hub:
            return
        with self.lock:
            payload = {
                "type": "music",
                "track": self.current,
                "paused": self.paused,
                "volume": self.volume,
                "label": self.label,
                "source": self.source,
                "playlist": {"id": self.playlist_id, "name": self.playlist_name} if self.playlist_id else None,
                "playlist_idx": self.playlist_idx,
                "playlist_count": len(self.playlist_entries) if self.playlist_id else 0,
            }
        self.hub.broadcast(payload)

    def _build_label(self, song):
        if not song:
            return ""
        title = (song.get("title") or "").strip()
        artist = (song.get("artist") or "").strip()
        if artist.lower() == "unknown artist":
            artist = ""
        if title and artist:
            return f"{title} — {artist}"
        return title or artist

    def _song_label(self, song):
        label = self._build_label(song)
        with self.lock:
            if label:
                self.label = label
            return self.label

    def _next_song(self):
        with self.lock:
            if self._override_next:
                song = dict(self._override_next)
                self._override_next = None
                return song
            if self.source == "playlist" and self.playlist_id:
                playlist_id = self.playlist_id
                playlist_entries = list(self.playlist_entries)
                playlist_idx = int(self.playlist_idx)
            else:
                playlist_id = None
                playlist_entries = []
                playlist_idx = 0
                if self.queue:
                    return self.queue.pop(0)

        if playlist_id:
            entries = playlist_entries
            if not entries or playlist_idx >= len(entries):
                try:
                    pl, entries = self.client.get_playlist(playlist_id)
                except Exception:
                    return None
                entries = [s for s in entries if s.get("id")]
                if not entries:
                    return None
                playlist_idx = 0
                with self.lock:
                    name = (pl.get("name") or "").strip()
                    if name:
                        self.playlist_name = name
                    self.playlist_entries = entries

            song = entries[playlist_idx] if playlist_idx < len(entries) else None
            if not song:
                return None
            with self.lock:
                self.playlist_idx = playlist_idx + 1
            return song

        try:
            songs = self.client.get_random_songs()
        except Exception:
            return None
        songs = [s for s in songs if s.get("id")]
        if not songs:
            return None
        with self.lock:
            self.queue = songs
            return self.queue.pop(0)

    def _play_song(self, song):
        if not song:
            return
        track = {
            "id": song.get("id"),
            "title": song.get("title") or "",
            "artist": song.get("artist") or "",
        }
        url = self.client.stream_url(track["id"])
        self.mpv.load(url)
        self.mpv.set_pause(False)
        with self.lock:
            prev = self.current
            suppress_history = self._suppress_history_once
            self._suppress_history_once = False
            if not suppress_history and prev:
                self.history.append(dict(prev))
                if len(self.history) > 100:
                    self.history = self.history[-100:]
            self.current = track
            self.paused = False
        self._song_label(track)
        self._refresh_ui()
        self._broadcast()
        self._notify_history()

    def _loop(self):
        while True:
            if not self.enabled:
                time.sleep(2)
                continue

            if self.current is None:
                song = self._next_song()
                if song:
                    self._play_song(song)
                else:
                    time.sleep(2)
                self._refresh_ui()
                continue

            if not self.paused:
                idle = self.mpv.get_property("idle-active")
                if idle:
                    song = self._next_song()
                    if song:
                        self._play_song(song)
            self._refresh_ui()
            time.sleep(1)

    def state(self):
        if not self.enabled:
            return {"ok": False, "error": self.error or "music disabled"}
        with self.lock:
            return {
                "ok": True,
                "track": self.current,
                "paused": self.paused,
                "volume": self.volume,
                "label": self.label,
                "source": self.source,
                "playlist": {"id": self.playlist_id, "name": self.playlist_name} if self.playlist_id else None,
                "playlist_idx": self.playlist_idx,
                "playlist_count": len(self.playlist_entries) if self.playlist_id else 0,
            }

    def history_labels(self, max_items=40, include_current=True):
        if not self.enabled:
            return []
        with self.lock:
            hist = list(self.history)
            current = dict(self.current) if self.current else None

        if max_items and max_items > 0:
            hist = hist[-int(max_items):]

        labels = []
        if include_current and current:
            label = self._build_label(current).strip()
            if not label:
                label = "Unknown track"
            labels.append(f"Now: {label}")

        for track in reversed(hist):
            label = self._build_label(track).strip()
            if not label:
                label = "Unknown track"
            labels.append(label)
        return labels

    def playlists(self):
        if not self.enabled:
            return {"ok": False, "error": self.error or "music disabled"}
        try:
            playlists = self.client.get_playlists()
        except Exception as e:
            return {"ok": False, "error": str(e)}
        out = []
        for pl in playlists or []:
            pid = pl.get("id")
            if not pid:
                continue
            out.append({
                "id": str(pid),
                "name": pl.get("name") or "",
                "songCount": pl.get("songCount") or pl.get("song_count") or 0,
            })
        return {"ok": True, "playlists": out}

    def set_playlist(self, playlist_id):
        if not self.enabled:
            return self.state()
        try:
            pl, entries = self.client.get_playlist(playlist_id)
        except Exception as e:
            return {"ok": False, "error": str(e)}
        entries = [s for s in entries if s.get("id")]
        if not entries:
            return {"ok": False, "error": "empty playlist"}
        name = (pl.get("name") or "").strip()
        with self.lock:
            self.source = "playlist"
            self.playlist_id = str(playlist_id)
            self.playlist_name = name
            self.playlist_entries = entries
            self.playlist_idx = 0
            self.queue = []
            self.current = None
            self.paused = False
            self.history = []
            self._override_next = None
            self._suppress_history_once = False
        self.mpv.stop()
        self._broadcast()
        self._notify_history()
        return self.state()

    def clear_playlist(self):
        if not self.enabled:
            return self.state()
        with self.lock:
            self.source = "random"
            self.playlist_id = None
            self.playlist_name = ""
            self.playlist_entries = []
            self.playlist_idx = 0
            self.queue = []
            self.current = None
            self.paused = False
            self.history = []
            self._override_next = None
            self._suppress_history_once = False
        self.mpv.stop()
        self._broadcast()
        self._notify_history()
        return self.state()

    def toggle_pause(self):
        if not self.enabled:
            return self.state()
        with self.lock:
            self.paused = not self.paused
            paused = self.paused
        self.mpv.set_pause(paused)
        self._broadcast()
        return self.state()

    def pause(self):
        if not self.enabled:
            return self.state()
        with self.lock:
            self.paused = True
        self.mpv.set_pause(True)
        self._broadcast()
        return self.state()

    def resume(self):
        if not self.enabled:
            return self.state()
        with self.lock:
            self.paused = False
        self.mpv.set_pause(False)
        self._broadcast()
        return self.state()

    def previous(self):
        if not self.enabled:
            return self.state()
        with self.lock:
            target = None
            if self.history:
                target = self.history.pop()
                if self.source == "playlist" and self.playlist_id and self.playlist_entries:
                    target_id = str(target.get("id"))
                    idx = None
                    for i, song in enumerate(self.playlist_entries):
                        sid = song.get("id")
                        if sid is None:
                            continue
                        if str(sid) == target_id:
                            idx = i
                            break
                    if idx is not None:
                        self.playlist_idx = idx + 1
                    else:
                        self.playlist_idx = max(0, int(self.playlist_idx) - 2)
            elif self.source == "playlist" and self.playlist_id and self.playlist_entries:
                self.playlist_idx = max(0, int(self.playlist_idx) - 2)
            elif self.current:
                target = dict(self.current)
            else:
                return self.state()

            if target is not None:
                self._override_next = dict(target)
                self._suppress_history_once = True
            self.current = None
            self.paused = False

        self.mpv.stop()
        self._broadcast()
        self._notify_history()
        return self.state()

    def next(self):
        if not self.enabled:
            return self.state()
        self.mpv.stop()
        with self.lock:
            self.current = None
            self.paused = False
        self._broadcast()
        return self.state()

    def set_volume(self, volume):
        if not self.enabled:
            return self.state()
        try:
            v = float(volume)
        except Exception:
            v = self.volume
        if v < 0:
            v = 0
        if v > MPV_VOLUME_MAX:
            v = MPV_VOLUME_MAX
        with self.lock:
            self.volume = v
        self.mpv.set_volume(v)
        self._broadcast()
        return self.state()


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
WS_SEND_TIMEOUT_S = 5.0  # Bound WS sends so broadcasts cannot hang.


def ws_make_accept(key):
    raw = (key + _WS_GUID).encode("utf-8")
    digest = hashlib.sha1(raw).digest()
    return base64.b64encode(digest).decode("ascii")


def ws_send_all(sock, data, timeout_s=WS_SEND_TIMEOUT_S):
    if timeout_s is None:
        sock.sendall(data)
        return

    deadline = time.monotonic() + timeout_s
    total = 0
    flags = getattr(socket, "MSG_DONTWAIT", 0)
    while total < len(data):
        try:
            sent = sock.send(data[total:], flags)
        except (BlockingIOError, InterruptedError):
            sent = None
        if sent is None:
            pass
        elif sent == 0:
            raise OSError("socket closed")
        else:
            total += sent
            continue

        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise TimeoutError("ws send timeout")
        _, writable, _ = select.select([], [sock], [], remaining)
        if not writable:
            raise TimeoutError("ws send timeout")


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

    ws_send_all(sock, header + payload)


def ws_send_pong(sock):
    ws_send_all(sock, b"\x8A\x00")


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
        self.delay_s = default_delay_s()
        self.music_bar_strategy = MUSIC_BAR_STRATEGY_DEFAULT
        self.music_bar_ratio = MUSIC_BAR_WIDTH_RATIO_DEFAULT
        self._files = []
        self.load_state()
        self.refresh_files()

    def load_state(self):
        with self.lock:
            self.disabled = set()
            self.active_source_x = 2
            self.delay_s = default_delay_s()
            try:
                with open(self.state_path, "r", encoding="utf-8") as f:
                    d = json.load(f)
                self.disabled = set(d.get("disabled", []))
                try:
                    self.active_source_x = int(d.get("active_source_x", 2))
                except Exception:
                    self.active_source_x = 2
                try:
                    self.delay_s = int(d.get("delay_s", default_delay_s()))
                except Exception:
                    self.delay_s = default_delay_s()
                try:
                    self.music_bar_strategy = int(d.get("music_bar_strategy", MUSIC_BAR_STRATEGY_DEFAULT))
                except Exception:
                    self.music_bar_strategy = MUSIC_BAR_STRATEGY_DEFAULT
                try:
                    self.music_bar_ratio = float(d.get("music_bar_ratio", MUSIC_BAR_WIDTH_RATIO_DEFAULT))
                except Exception:
                    self.music_bar_ratio = MUSIC_BAR_WIDTH_RATIO_DEFAULT
                if self.music_bar_strategy not in (1, 2, 3):
                    self.music_bar_strategy = MUSIC_BAR_STRATEGY_DEFAULT
                if self.music_bar_ratio <= 0:
                    self.music_bar_ratio = MUSIC_BAR_WIDTH_RATIO_DEFAULT
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
                "music_bar_strategy": int(self.music_bar_strategy),
                "music_bar_ratio": float(self.music_bar_ratio),
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
            d = default_delay_s()
        if d < 1:
            d = 1
        if d > 24 * 3600:
            d = 24 * 3600
        with self.lock:
            self.delay_s = d
        self.save_state()
        return d

    def set_music_bar(self, strategy, ratio):
        try:
            s = int(strategy)
        except Exception:
            s = self.music_bar_strategy
        if s not in (1, 2, 3):
            s = self.music_bar_strategy

        try:
            r = float(ratio)
        except Exception:
            r = self.music_bar_ratio
        if r <= 0:
            r = self.music_bar_ratio
        r = max(0.05, min(0.8, r))

        with self.lock:
            self.music_bar_strategy = s
            self.music_bar_ratio = r
        self.save_state()
        return s, r

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
@dataclass(frozen=True)
class CecKeyEvent:
    """Represents one recognized CEC key DOWN event."""
    name: str
    code: int
    initiator: int
    destination: int
    raw: str


class CecKeyListener:
    """
    Listener that:
      - periodically asserts playback device name via cec-ctl
      - reads cec-client stdout line-by-line
      - parses key DOWN events and dispatches to callback
    """

    _TRAFFIC_RE = re.compile(
        r"TRAFFIC:.*>>\s+"
        r"(?P<hdr>[0-9a-fA-F]{2})"
        r"(?::(?P<op>[0-9a-fA-F]{2}))?"
        r"(?::(?P<param>[0-9a-fA-F]{2}))?"
        r"\s*$"
    )

    _OP_USER_CONTROL_PRESSED = 0x44
    _OP_USER_CONTROL_RELEASED = 0x45

    _KEYS: Dict[int, str] = {
        0x00: "SELECT",
        0x01: "UP",
        0x02: "DOWN",
        0x03: "LEFT",
        0x04: "RIGHT",
        0x0D: "EXIT",
        0x44: "PAUSE",
        0x45: "STOP",
        0x46: "PAUSE",
        0x48: "REWIND",
        0x49: "FAST_FORWARD",
        0x4B: "FORWARD",
        0x4C: "BACKWARD",
    }

    def __init__(
        self,
        callback: Callable[[CecKeyEvent], None],
        *,
        cec_device: str = "/dev/cec0",
        refresh_interval_s: float = 30.0,
        process_nice: bool = True,
    ):
        self._cb = callback
        self._cec_device = cec_device
        self._refresh_interval_s = float(refresh_interval_s)
        self._process_nice = process_nice

        self._stop = threading.Event()
        self._reader_thread: Optional[threading.Thread] = None
        self._refresh_thread: Optional[threading.Thread] = None
        self._proc: Optional[subprocess.Popen] = None

    def start(self):
        self._stop.clear()
        self._run_cec_ctl()
        self._start_cec_client()

        self._reader_thread = threading.Thread(
            target=self._reader_loop,
            name="cec-reader",
            daemon=True,
        )
        self._reader_thread.start()

        self._refresh_thread = threading.Thread(
            target=self._refresh_loop,
            name="cec-refresh",
            daemon=True,
        )
        self._refresh_thread.start()

    def stop(self):
        self._stop.set()

        if self._proc and self._proc.poll() is None:
            try:
                self._proc.terminate()
            except Exception:
                pass

        if self._reader_thread and self._reader_thread.is_alive():
            self._reader_thread.join(timeout=2.0)
        if self._refresh_thread and self._refresh_thread.is_alive():
            self._refresh_thread.join(timeout=2.0)

        if self._proc and self._proc.poll() is None:
            try:
                self._proc.kill()
            except Exception:
                pass

    def join(self):
        try:
            while not self._stop.is_set():
                time.sleep(0.2)
        except KeyboardInterrupt:
            self.stop()

    def __enter__(self):
        self.start()
        return self

    def __exit__(self, exc_type, exc, tb):
        self.stop()

    def _run_cec_ctl(self):
        cmd = ["cec-ctl", "-d", self._cec_device, "--playback", "-S", "-o", "raspberry"]
        try:
            subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
        except FileNotFoundError:
            pass
        except Exception:
            pass

    def _refresh_loop(self):
        interval = max(1.0, self._refresh_interval_s)
        while not self._stop.wait(interval):
            self._run_cec_ctl()

    def _start_cec_client(self):
        base_cmd = ["cec-client", self._cec_device]
        if self._process_nice:
            cmd = ["nice", "-n", "10"] + base_cmd
        else:
            cmd = base_cmd

        self._proc = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )

    def _reader_loop(self):
        if not self._proc or not self._proc.stdout:
            self._stop.set()
            return

        for line in self._proc.stdout:
            if self._stop.is_set():
                break

            evt = self._parse_line(line)
            if evt is None:
                continue

            try:
                self._cb(evt)
            except Exception:
                pass

        self._stop.set()

    def _parse_line(self, line: str) -> Optional[CecKeyEvent]:
        m = self._TRAFFIC_RE.search(line)
        if not m:
            return None

        hdr_s = m.group("hdr")
        op_s = m.group("op")
        param_s = m.group("param")

        if not hdr_s or not op_s:
            return None

        hdr = int(hdr_s, 16)
        op = int(op_s, 16)

        if op != self._OP_USER_CONTROL_PRESSED:
            return None

        if not param_s:
            return None

        key_code = int(param_s, 16)
        key_name = self._KEYS.get(key_code)
        if key_name is None:
            return None

        initiator = (hdr >> 4) & 0xF
        destination = hdr & 0xF

        return CecKeyEvent(
            name=key_name,
            code=key_code,
            initiator=initiator,
            destination=destination,
            raw=line.rstrip("\n"),
        )


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


def start_cec_key_listener(music, slideshow=None):
    if not slideshow and (not music or not music.enabled):
        return None

    def on_key(evt: CecKeyEvent):
        if evt.name == "SELECT":
            if slideshow:
                try:
                    QMetaObject.invokeMethod(slideshow, "toggle_menu",
                        Qt.ConnectionType.QueuedConnection)
                except Exception:
                    pass
            return
        if evt.name == "EXIT":
            if slideshow:
                try:
                    QMetaObject.invokeMethod(slideshow, "hide_menu",
                        Qt.ConnectionType.QueuedConnection)
                except Exception:
                    pass
            return
        if evt.name == "LEFT":
            if slideshow:
                try:
                    QMetaObject.invokeMethod(slideshow, "move_menu_tab",
                        Qt.ConnectionType.QueuedConnection, Q_ARG(int, -1))
                except Exception:
                    pass
            return
        if evt.name == "RIGHT":
            if slideshow:
                try:
                    QMetaObject.invokeMethod(slideshow, "move_menu_tab",
                        Qt.ConnectionType.QueuedConnection, Q_ARG(int, 1))
                except Exception:
                    pass
            return

        if not music or not music.enabled:
            return
        if evt.name == "PAUSE":
            music.toggle_pause()
        elif evt.name == "FORWARD":
            music.next()
        elif evt.name == "BACKWARD":
            music.previous()

    try:
        listener = CecKeyListener(on_key, refresh_interval_s=30)
        listener.start()
        return listener
    except Exception:
        return None


# ----------------------------
# Qt slideshow
# ----------------------------
# Music bar strategies
# 1) Match-label-width: bar width follows the music label width, with a minimum of 220px.
#    Placement: bottom-left, aligned to self.margin; bar sits directly under the label
#    with a 6px gap; bar height is fixed (10px). Padding is from the QProgressBar
#    stylesheet (border + rounded corners), not layout math.
# 2) Constant-width: bar width is a fixed ratio of the window width
#    (MUSIC_BAR_WIDTH_RATIO_DEFAULT). Placement matches strategy 1.
# 3) Duration-linear: bar width ratio scales linearly with track length.
#    3m30s (210s) => 25% width; max ratio caps at 40%. If duration is unknown,
#    it falls back to the configured ratio from strategy 2. Placement matches strategy 1.
MUSIC_BAR_STRATEGY_DEFAULT = 2
MUSIC_BAR_WIDTH_RATIO_DEFAULT = 0.25
MUSIC_BAR_DURATION_BASE_S = 210.0
MUSIC_BAR_DURATION_BASE_RATIO = 0.25
MUSIC_BAR_DURATION_MAX_RATIO = 0.40

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
        self.music_manager = None
        self.music_bar_strategy = int(getattr(self.mgr, "music_bar_strategy", MUSIC_BAR_STRATEGY_DEFAULT))
        self.music_bar_ratio = float(getattr(self.mgr, "music_bar_ratio", MUSIC_BAR_WIDTH_RATIO_DEFAULT))
        self.music_bar_duration_s = None

        self.setWindowTitle("TV UI")
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

        self.music = QLabel(self)
        self.music.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        self.music.setFont(QFont("DejaVu Sans", 18, 500))
        self.music.setStyleSheet(
            "color: rgba(255,255,255,220);"
            "background-color: rgba(0,0,0,0.35);"
            "border: 1px solid rgba(255,255,255,0.12);"
            "border-radius: 10px;"
            "padding: 6px 10px;"
        )
        self.music.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        self.music.setTextFormat(Qt.TextFormat.RichText)

        music_shadow = QGraphicsDropShadowEffect(self)
        music_shadow.setBlurRadius(16)
        music_shadow.setOffset(0, 2)
        music_shadow.setColor(Qt.GlobalColor.black)
        self.music.setGraphicsEffect(music_shadow)
        self.music.hide()

        self.music_bar = QProgressBar(self)
        self.music_bar.setRange(0, 1000)
        self.music_bar.setValue(0)
        self.music_bar.setTextVisible(False)
        self.music_bar.setFixedHeight(10)
        self.music_bar.setStyleSheet(
            "QProgressBar {"
            "  border: 1px solid rgba(255,255,255,0.12);"
            "  background-color: rgba(0,0,0,0.35);"
            "  border-radius: 6px;"
            "}"
            "QProgressBar::chunk {"
            "  background-color: rgba(255,255,255,200);"
            "  border-radius: 5px;"
            "}"
        )
        bar_shadow = QGraphicsDropShadowEffect(self)
        bar_shadow.setBlurRadius(16)
        bar_shadow.setOffset(0, 2)
        bar_shadow.setColor(Qt.GlobalColor.black)
        self.music_bar.setGraphicsEffect(bar_shadow)
        self.music_bar.hide()

        self.menu_overlay = None
        self.menu_panel = None
        self.menu_tabs = None
        self.menu_history_list = None
        self.menu_playlists_list = None
        self.menu_playlists_status = None
        self.menu_playlists_tab_index = None
        self._menu_playlists_refreshing = False
        self._menu_playlist_action_running = False
        self.live_container = None
        self.live_video = None
        self.live_player = None
        self.live_audio = None
        self.live_proxy_server = None
        self._live_stream_thread = None
        self._pending_live_proxy_url = None
        self._pending_live_proxy_server = None
        self._init_menu_ui()
        self._init_live_stream()

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
            d = default_delay_s()
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
        self._layout_live_stream()
        self._layout_menu()
        if self.current_path:
            self._show_path(self.current_path)
        super().resizeEvent(event)

    def layout_clock(self):
        self.clock.adjustSize()
        w = self.clock.width()
        self.clock.move(self.width() - w - self.margin, self.margin)
        if self.music.isVisible():
            self.music.adjustSize()
            mh = self.music.height()
            gap = 6
            bar_visible = self.music_bar.isVisible()
            bar_h = self.music_bar.height() if bar_visible else 0
            total_h = mh + (gap + bar_h if bar_visible else 0)
            y = self.height() - total_h - self.margin
            self.music.move(self.margin, y)
            if bar_visible:
                if self.music_bar_strategy == 2:
                    ratio = self.music_bar_ratio
                    bar_w = max(1, int(self.width() * ratio))
                elif self.music_bar_strategy == 3:
                    ratio = self._music_bar_ratio_for_duration()
                    bar_w = max(1, int(self.width() * ratio))
                else:
                    bar_w = max(220, self.music.width())
                self.music_bar.setFixedWidth(bar_w)
                self.music_bar.move(self.margin, y + mh + gap)

    def _layout_live_stream(self):
        if not self.live_container:
            return
        max_w = max(1, self.width() - (self.margin * 2))
        max_h = max(1, self.height() - (self.margin * 2))
        w = max(LIVE_STREAM_MIN_WIDTH, int(self.width() * LIVE_STREAM_WIDTH_RATIO))
        if w > max_w:
            w = max_w
        h = int(w / LIVE_STREAM_ASPECT_RATIO)
        if h > max_h:
            h = max_h
            w = int(h * LIVE_STREAM_ASPECT_RATIO)
        x = max(self.margin, self.width() - w - self.margin)
        y = max(self.margin, self.height() - h - self.margin)
        self.live_container.setGeometry(x, y, w, h)
        log.debug("Live stream geometry %sx%s at %s,%s", w, h, x, y)

    def _music_bar_ratio_for_duration(self):
        dur = self.music_bar_duration_s
        if dur is None or dur <= 0:
            return self.music_bar_ratio
        ratio = MUSIC_BAR_DURATION_BASE_RATIO * (float(dur) / MUSIC_BAR_DURATION_BASE_S)
        if ratio < 0:
            ratio = 0
        if ratio > MUSIC_BAR_DURATION_MAX_RATIO:
            ratio = MUSIC_BAR_DURATION_MAX_RATIO
        return ratio

    @pyqtSlot(int, float)
    def apply_music_bar_config(self, strategy, ratio):
        try:
            s = int(strategy)
        except Exception:
            s = self.music_bar_strategy
        if s not in (1, 2, 3):
            s = self.music_bar_strategy

        try:
            r = float(ratio)
        except Exception:
            r = self.music_bar_ratio
        if r <= 0:
            r = self.music_bar_ratio
        r = max(0.05, min(0.8, r))

        self.music_bar_strategy = s
        self.music_bar_ratio = r
        self.layout_clock()

    @pyqtSlot(int)
    def set_music_duration(self, seconds):
        try:
            s = int(seconds)
        except Exception:
            s = -1
        if s <= 0:
            self.music_bar_duration_s = None
        else:
            self.music_bar_duration_s = s
        self.layout_clock()

    @pyqtSlot(str)
    def set_music_text(self, text):
        text = text or ""
        if text:
            self.music.setText(text)
            self.music.show()
        else:
            self.music.hide()
            self.music_bar.hide()
        self.layout_clock()

    @pyqtSlot(int)
    def set_music_progress(self, value):
        if value is None or value < 0:
            self.music_bar.hide()
        else:
            if value > 1000:
                value = 1000
            self.music_bar.setValue(int(value))
            self.music_bar.show()
        self.layout_clock()

    def _init_menu_ui(self):
        self.menu_overlay = QWidget(self)
        self.menu_overlay.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        self.menu_overlay.setStyleSheet("background-color: rgba(0,0,0,0.3);")
        self.menu_overlay.hide()

        overlay_layout = QVBoxLayout(self.menu_overlay)
        overlay_layout.setContentsMargins(0, 0, 0, 0)
        overlay_layout.setSpacing(0)
        overlay_layout.setAlignment(Qt.AlignmentFlag.AlignCenter)

        self.menu_panel = QFrame(self.menu_overlay)
        self.menu_panel.setObjectName("menuPanel")
        self.menu_panel.setStyleSheet(
            "#menuPanel {"
            "  background-color: rgba(18,18,18,0.88);"
            "  border: 1px solid rgba(255,255,255,0.15);"
            "  border-radius: 16px;"
            "}"
            "QTabWidget::pane {"
            "  border: none;"
            "}"
            "QTabBar::tab {"
            "  background: rgba(255,255,255,0.08);"
            "  color: rgba(255,255,255,0.85);"
            "  padding: 8px 14px;"
            "  margin-right: 6px;"
            "  border-radius: 8px;"
            "}"
            "QTabBar::tab:selected {"
            "  background: rgba(255,255,255,0.18);"
            "  color: rgba(255,255,255,1.0);"
            "}"
            "QListWidget {"
            "  background: transparent;"
            "  color: rgba(255,255,255,0.9);"
            "  border: none;"
            "}"
            "QListWidget::item {"
            "  padding: 6px 4px;"
            "}"
        )
        self.menu_panel.setFont(QFont("DejaVu Sans", 13, 500))

        panel_layout = QVBoxLayout(self.menu_panel)
        panel_layout.setContentsMargins(18, 18, 18, 18)
        panel_layout.setSpacing(12)

        self.menu_tabs = QTabWidget(self.menu_panel)
        self.menu_tabs.setDocumentMode(True)
        self.menu_tabs.setElideMode(Qt.TextElideMode.ElideRight)
        panel_layout.addWidget(self.menu_tabs)

        self.menu_history_list = QListWidget()
        self.menu_history_list.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.menu_tabs.addTab(self.menu_history_list, "History")

        tab_playlists = self._make_playlist_tab()
        self.menu_playlists_tab_index = self.menu_tabs.addTab(tab_playlists, "Playlists")

        tab_notes = self._make_placeholder_tab(
            "Random notes",
            "Sample items:\n"
            "- Shuffle mode: on\n"
            "- Favorite genres: synth, ambient\n"
            "- Tip: LEFT/RIGHT switches tabs"
        )
        self.menu_tabs.addTab(tab_notes, "Notes")

        tab_status = self._make_placeholder_tab(
            "Random status",
            "Sample metrics:\n"
            "- Queue depth: 12\n"
            "- Images loaded: 248\n"
            "- Uptime: 3h 17m"
        )
        self.menu_tabs.addTab(tab_status, "Status")

        self.menu_tabs.currentChanged.connect(self._menu_tab_changed)

        overlay_layout.addWidget(self.menu_panel, alignment=Qt.AlignmentFlag.AlignCenter)
        self._layout_menu()

    def _init_live_stream(self):
        if not QT_MULTIMEDIA_AVAILABLE:
            log.info("QtMultimedia unavailable; skipping live stream overlay")
            return
        if self._live_stream_thread and self._live_stream_thread.is_alive():
            return
        log.info("Initializing live stream overlay")
        self._live_stream_thread = threading.Thread(
            target=self._load_live_stream_backend,
            daemon=True,
        )
        self._live_stream_thread.start()

    def _load_live_stream_backend(self):
        try:
            stream_url = fetch_stream_url(LIVE_STREAM_VIDEO_ID, LIVE_STREAM_REFERER)
        except Exception as exc:
            log.error("Live stream metadata fetch failed: %s", exc)
            return
        if not stream_url:
            log.error("Live stream metadata returned no stream URL")
            return

        try:
            proxy_server, proxy_url = start_hls_proxy(stream_url, LIVE_STREAM_REFERER)
        except Exception as exc:
            log.error("Live stream proxy start failed: %s", exc)
            return

        self._pending_live_proxy_server = proxy_server
        self._pending_live_proxy_url = proxy_url
        try:
            QMetaObject.invokeMethod(
                self,
                "_attach_live_stream",
                Qt.ConnectionType.QueuedConnection,
            )
        except Exception as exc:
            log.warning("Live stream UI attach failed: %s", exc)
            try:
                proxy_server.shutdown()
            except Exception:
                pass
            self._pending_live_proxy_server = None
            self._pending_live_proxy_url = None

    @pyqtSlot()
    def _attach_live_stream(self):
        if not QT_MULTIMEDIA_AVAILABLE:
            return
        if self.live_container:
            return
        proxy_server = self._pending_live_proxy_server
        proxy_url = self._pending_live_proxy_url
        if not proxy_server or not proxy_url:
            return
        self._pending_live_proxy_server = None
        self._pending_live_proxy_url = None
        self.live_proxy_server = proxy_server
        atexit.register(self.live_proxy_server.shutdown)

        self.live_container = QFrame(self)
        self.live_container.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.live_container.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        self.live_container.setStyleSheet(
            "background-color: #000;"
            "border: 1px solid rgba(255,255,255,0.18);"
            "border-radius: 12px;"
        )

        container_layout = QVBoxLayout(self.live_container)
        container_layout.setContentsMargins(0, 0, 0, 0)
        container_layout.setSpacing(0)

        self.live_video = QVideoWidget(self.live_container)
        container_layout.addWidget(self.live_video, 1)

        self.live_audio = QAudioOutput(self)
        self.live_audio.setVolume(0.5)
        self.live_audio.setMuted(False)

        self.live_player = QMediaPlayer(self)
        self.live_player.setAudioOutput(self.live_audio)
        self.live_player.setVideoOutput(self.live_video)
        self.live_player.setSource(QUrl(proxy_url))

        def _log_media_status(status):
            log.debug("Live stream media status: %s", status)

        def _log_playback(state):
            log.debug("Live stream playback state: %s", state)

        def _log_error(*args):
            log.error("Live stream player error: %s", args)

        try:
            self.live_player.mediaStatusChanged.connect(_log_media_status)
            self.live_player.playbackStateChanged.connect(_log_playback)
            self.live_player.errorOccurred.connect(_log_error)
        except Exception as exc:
            log.warning("Live stream signal hookup failed: %s", exc)

        self._layout_live_stream()
        self.live_container.show()
        self.live_container.raise_()
        self.live_player.play()
        log.info("Live stream overlay shown")

    def _make_placeholder_tab(self, title, body):
        w = QWidget()
        layout = QVBoxLayout(w)
        layout.setContentsMargins(6, 6, 6, 6)
        layout.setSpacing(8)

        label = QLabel(f"{title}\n\n{body}")
        label.setWordWrap(True)
        label.setStyleSheet("color: rgba(255,255,255,0.85);")
        label.setAlignment(Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignLeft)
        layout.addWidget(label, alignment=Qt.AlignmentFlag.AlignTop)
        layout.addStretch(1)
        return w

    def _make_playlist_tab(self):
        w = QWidget()
        layout = QVBoxLayout(w)
        layout.setContentsMargins(6, 6, 6, 6)
        layout.setSpacing(8)

        hint = QLabel("Select a Navidrome playlist to play. Use Random to return to shuffle.")
        hint.setWordWrap(True)
        hint.setStyleSheet("color: rgba(255,255,255,0.75);")
        layout.addWidget(hint)

        self.menu_playlists_list = QListWidget()
        self.menu_playlists_list.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.menu_playlists_list.setSelectionMode(QListWidget.SelectionMode.SingleSelection)
        self.menu_playlists_list.itemActivated.connect(self._menu_playlist_activate)
        self.menu_playlists_list.setMinimumHeight(160)
        layout.addWidget(self.menu_playlists_list, 1)

        self.menu_playlists_status = QLabel("")
        self.menu_playlists_status.setWordWrap(True)
        self.menu_playlists_status.setStyleSheet("color: rgba(255,255,255,0.6);")
        layout.addWidget(self.menu_playlists_status)

        return w

    @pyqtSlot(int)
    def _menu_tab_changed(self, idx):
        if idx == self.menu_playlists_tab_index:
            self.refresh_menu_playlists()

    def _set_menu_playlist_status(self, text):
        if not self.menu_playlists_status:
            return
        self.menu_playlists_status.setText(text or "")

    def refresh_menu_playlists(self):
        if not self.menu_playlists_list:
            return
        if self._menu_playlists_refreshing:
            return

        music = self.music_manager
        self.menu_playlists_list.clear()
        self._set_menu_playlist_status("")

        if not music or not music.enabled:
            item = QListWidgetItem("Music disabled")
            item.setFlags(item.flags() & ~Qt.ItemFlag.ItemIsEnabled & ~Qt.ItemFlag.ItemIsSelectable)
            self.menu_playlists_list.addItem(item)
            self.menu_playlists_list.setEnabled(False)
            return

        self.menu_playlists_list.setEnabled(False)
        self._menu_playlists_refreshing = True
        item = QListWidgetItem("Loading playlists...")
        item.setFlags(item.flags() & ~Qt.ItemFlag.ItemIsEnabled & ~Qt.ItemFlag.ItemIsSelectable)
        self.menu_playlists_list.addItem(item)

        def worker():
            try:
                playlists = music.playlists()
            except Exception as e:
                playlists = {"ok": False, "error": str(e)}
            try:
                state = music.state()
            except Exception as e:
                state = {"ok": False, "error": str(e)}
            payload = json.dumps({"playlists": playlists, "state": state})
            try:
                QMetaObject.invokeMethod(
                    self,
                    "_apply_menu_playlists_json",
                    Qt.ConnectionType.QueuedConnection,
                    Q_ARG(str, payload),
                )
            except Exception:
                self._menu_playlists_refreshing = False

        threading.Thread(target=worker, daemon=True).start()

    @pyqtSlot(str)
    def _apply_menu_playlists_json(self, payload):
        self._menu_playlists_refreshing = False
        try:
            data = json.loads(payload) if payload else {}
        except Exception:
            data = {}
        playlists = data.get("playlists") or {}
        state = data.get("state") or {}
        self._populate_menu_playlists(playlists, state)

    def _populate_menu_playlists(self, res, state):
        if not self.menu_playlists_list:
            return

        self.menu_playlists_list.clear()
        self.menu_playlists_list.setEnabled(True)

        refresh_item = QListWidgetItem("Refresh playlists")
        refresh_item.setData(Qt.ItemDataRole.UserRole, "__refresh__")
        self.menu_playlists_list.addItem(refresh_item)

        active_id = None
        active_name = ""
        if state and state.get("ok") and state.get("playlist"):
            pl = state.get("playlist") or {}
            pid = pl.get("id")
            if pid is not None:
                active_id = str(pid)
                active_name = (pl.get("name") or "").strip()

        random_label = "Random / Shuffle"
        if not active_id:
            random_label = "Now: " + random_label
        random_item = QListWidgetItem(random_label)
        random_item.setData(Qt.ItemDataRole.UserRole, "__random__")
        if not active_id:
            font = random_item.font()
            font.setBold(True)
            random_item.setFont(font)
        self.menu_playlists_list.addItem(random_item)

        if not res or not res.get("ok"):
            err = "Unable to load playlists"
            if res and res.get("error"):
                err = str(res.get("error"))
            self._set_menu_playlist_status(err)
            err_item = QListWidgetItem(err)
            err_item.setFlags(err_item.flags() & ~Qt.ItemFlag.ItemIsEnabled & ~Qt.ItemFlag.ItemIsSelectable)
            self.menu_playlists_list.addItem(err_item)
            return

        pls = res.get("playlists") or []
        if not pls:
            self._set_menu_playlist_status("No playlists found")
            none_item = QListWidgetItem("No playlists found")
            none_item.setFlags(none_item.flags() & ~Qt.ItemFlag.ItemIsEnabled & ~Qt.ItemFlag.ItemIsSelectable)
            self.menu_playlists_list.addItem(none_item)
            return

        for pl in pls:
            pid = pl.get("id")
            if pid is None:
                continue
            pid = str(pid)
            name = (pl.get("name") or "").strip() or pid
            count = pl.get("songCount") or 0
            if count:
                label = f"{name}  ({count} songs)"
            else:
                label = name
            if pid == active_id:
                label = "Now: " + label
            item = QListWidgetItem(label)
            item.setData(Qt.ItemDataRole.UserRole, pid)
            if pid == active_id:
                font = item.font()
                font.setBold(True)
                item.setFont(font)
            self.menu_playlists_list.addItem(item)

        if active_id:
            status = f"Playing: {active_name or 'playlist'}"
        else:
            status = "Random mode"
        status = f"{status} - {len(pls)} playlists"
        self._set_menu_playlist_status(status)

    def _menu_playlist_activate(self, item):
        if not item:
            return
        data = item.data(Qt.ItemDataRole.UserRole)
        if not data:
            return
        if data == "__refresh__":
            self.refresh_menu_playlists()
            return
        if data == "__random__":
            self._run_menu_playlist_action("clear")
            return
        self._run_menu_playlist_action("set", playlist_id=str(data))

    def _run_menu_playlist_action(self, action, playlist_id=None):
        if self._menu_playlist_action_running:
            return
        music = self.music_manager
        if not music or not music.enabled:
            self._set_menu_playlist_status("Music disabled")
            return

        self._menu_playlist_action_running = True
        if self.menu_playlists_list:
            self.menu_playlists_list.setEnabled(False)
        if action == "clear":
            self._set_menu_playlist_status("Switching to random...")
        else:
            self._set_menu_playlist_status("Starting playlist...")

        def worker():
            try:
                if action == "clear":
                    result = music.clear_playlist()
                else:
                    result = music.set_playlist(playlist_id)
            except Exception as e:
                result = {"ok": False, "error": str(e)}
            payload = json.dumps({"action": action, "result": result})
            try:
                QMetaObject.invokeMethod(
                    self,
                    "_apply_menu_playlist_action_json",
                    Qt.ConnectionType.QueuedConnection,
                    Q_ARG(str, payload),
                )
            except Exception:
                self._menu_playlist_action_running = False

        threading.Thread(target=worker, daemon=True).start()

    @pyqtSlot(str)
    def _apply_menu_playlist_action_json(self, payload):
        self._menu_playlist_action_running = False
        try:
            data = json.loads(payload) if payload else {}
        except Exception:
            data = {}
        res = data.get("result") or {}
        if not res.get("ok"):
            self._set_menu_playlist_status(res.get("error") or "Playlist action failed")
        else:
            if data.get("action") == "clear":
                self._set_menu_playlist_status("Random mode")
            else:
                pl = res.get("playlist") or {}
                name = (pl.get("name") or "").strip()
                if name:
                    self._set_menu_playlist_status(f"Playing: {name}")
                else:
                    self._set_menu_playlist_status("Playlist started")

        if self.menu_playlists_list:
            self.menu_playlists_list.setEnabled(True)
        self.refresh_menu_history()
        self.refresh_menu_playlists()

    def _layout_menu(self):
        if not self.menu_overlay or not self.menu_panel:
            return
        self.menu_overlay.setGeometry(self.rect())
        w = int(self.width() * 0.65)
        h = int(self.height() * 0.60)
        w = max(420, min(self.width() - 40, w))
        h = max(260, min(self.height() - 40, h))
        self.menu_panel.setFixedSize(w, h)

    def attach_music(self, music):
        self.music_manager = music
        self.refresh_menu_history()

    @pyqtSlot()
    def refresh_menu_history(self):
        if not self.menu_history_list:
            return
        self.menu_history_list.clear()
        music = self.music_manager
        if not music or not music.enabled:
            item = QListWidgetItem("Music disabled")
            item.setFlags(item.flags() & ~Qt.ItemFlag.ItemIsEnabled & ~Qt.ItemFlag.ItemIsSelectable)
            self.menu_history_list.addItem(item)
            return

        labels = music.history_labels(max_items=40, include_current=True)
        if not labels:
            item = QListWidgetItem("No history yet")
            item.setFlags(item.flags() & ~Qt.ItemFlag.ItemIsEnabled & ~Qt.ItemFlag.ItemIsSelectable)
            self.menu_history_list.addItem(item)
            return

        for i, label in enumerate(labels):
            item = QListWidgetItem(label)
            if i == 0 and label.startswith("Now:"):
                font = item.font()
                font.setBold(True)
                item.setFont(font)
            self.menu_history_list.addItem(item)

    @pyqtSlot()
    def toggle_menu(self):
        if self.menu_overlay and self.menu_overlay.isVisible():
            self.hide_menu()
        else:
            self.show_menu()

    @pyqtSlot()
    def show_menu(self):
        if not self.menu_overlay:
            return
        self._layout_menu()
        self.refresh_menu_history()
        self.refresh_menu_playlists()
        self.menu_overlay.show()
        self.menu_overlay.raise_()
        if self.menu_panel:
            self.menu_panel.raise_()
        if self.live_container:
            self.live_container.setVisible(False)
            log.debug("Live stream hidden (menu shown)")

    @pyqtSlot()
    def hide_menu(self):
        if self.menu_overlay:
            self.menu_overlay.hide()
        if self.live_container:
            self.live_container.setVisible(True)
            self.live_container.raise_()
            log.debug("Live stream shown (menu hidden)")

    @pyqtSlot(int)
    def move_menu_tab(self, delta):
        if not self.menu_overlay or not self.menu_overlay.isVisible():
            return
        if not self.menu_tabs:
            return
        count = self.menu_tabs.count()
        if count <= 0:
            return
        try:
            d = int(delta)
        except Exception:
            d = 0
        idx = (self.menu_tabs.currentIndex() + d) % count
        self.menu_tabs.setCurrentIndex(idx)

    def tick(self):
        self.clock.setText(datetime.now().strftime("%A %d %B %Y\n%H:%M"))
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
def make_handler(mgr, slideshow, hub, music):
    class Handler(BaseHTTPRequestHandler):
        server_version = "fehb/1.5"
        protocol_version = "HTTP/1.1"

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

        def _deny(self, code=403, msg="Forbidden", close=False):
            data = msg.encode("utf-8", errors="ignore")
            self.send_response(code)
            self.send_header("Content-Type", "text/plain; charset=utf-8")
            self.send_header("Content-Length", str(len(data)))
            if close:
                self.send_header("Connection", "close")
                self.close_connection = True
            self.end_headers()
            self.wfile.write(data)

        def _json(self, obj, code=200, close=False):
            data = json.dumps(obj).encode("utf-8")
            self.send_response(code)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", str(len(data)))
            if close:
                self.send_header("Connection", "close")
                self.close_connection = True
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

            upgrade = self.headers.get("Upgrade", "")
            if "websocket" not in upgrade.lower():
                return self._deny(400, "Missing Upgrade: websocket")

            key = self.headers.get("Sec-WebSocket-Key", "").strip()
            if not key:
                return self._deny(400, "Missing Sec-WebSocket-Key")

            accept = ws_make_accept(key)

            self.send_response(101, "Switching Protocols")
            self.send_header("Upgrade", "websocket")
            self.send_header("Connection", "Upgrade")
            self.send_header("Sec-WebSocket-Accept", accept)
            self.end_headers()

            sock = self.connection
            self.close_connection = False
            # Keep WS open indefinitely; browser may be idle for long periods.
            sock.settimeout(None)
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
                            ws_send_pong(sock)
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
                        delay_s = msg.get("delay_s", default_delay_s())
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

            if route == "/api/music/state":
                if music:
                    data = music.state()
                    data["music_bar_strategy"] = int(mgr.music_bar_strategy)
                    data["music_bar_ratio"] = float(mgr.music_bar_ratio)
                    return self._json(data)
                return self._json({"ok": False, "error": "music disabled"}, 400)

            if route == "/api/music/playlists":
                if music:
                    return self._json(music.playlists())
                return self._json({"ok": False, "error": "music disabled"}, 400)

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
                return self._deny(close=True)

            u = urlparse(self.path)
            route = strip_to_known_route(u.path)

            # Upload: multipart/form-data (mobile compatible)
            if route == "/api/upload":
                try:
                    n = int(self.headers.get("Content-Length", "0"))
                except Exception:
                    n = 0
                if n <= 0:
                    return self._json({"ok": False, "error": "empty upload"}, 400, close=True)
                if n > MAX_UPLOAD_BYTES:
                    return self._json({"ok": False, "error": "upload too large"}, 413, close=True)

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
                d = mgr.set_delay(body.get("delay_s", default_delay_s()))
                QMetaObject.invokeMethod(slideshow, "apply_delay",
                    Qt.ConnectionType.QueuedConnection, Q_ARG(int, d))
                return self._json({"ok": True, "delay_s": d})

            if route == "/api/config/music_bar":
                strategy = body.get("strategy", mgr.music_bar_strategy)
                ratio = body.get("ratio", mgr.music_bar_ratio)
                s, r = mgr.set_music_bar(strategy, ratio)
                QMetaObject.invokeMethod(slideshow, "apply_music_bar_config",
                    Qt.ConnectionType.QueuedConnection, Q_ARG(int, int(s)), Q_ARG(float, float(r)))
                return self._json({"ok": True, "strategy": s, "ratio": r})

            if route == "/api/music/next":
                if music:
                    return self._json(music.next())
                return self._json({"ok": False, "error": "music disabled"}, 400)

            if route == "/api/music/toggle":
                if music:
                    return self._json(music.toggle_pause())
                return self._json({"ok": False, "error": "music disabled"}, 400)

            if route == "/api/music/pause":
                if music:
                    return self._json(music.pause())
                return self._json({"ok": False, "error": "music disabled"}, 400)

            if route == "/api/music/resume":
                if music:
                    return self._json(music.resume())
                return self._json({"ok": False, "error": "music disabled"}, 400)

            if route == "/api/music/volume":
                if music:
                    return self._json(music.set_volume(body.get("volume")))
                return self._json({"ok": False, "error": "music disabled"}, 400)

            if route == "/api/music/playlist/set":
                if not music:
                    return self._json({"ok": False, "error": "music disabled"}, 400)
                pid = body.get("id") or body.get("playlist_id") or ""
                if not pid:
                    return self._json({"ok": False, "error": "missing playlist id"}, 400)
                res = music.set_playlist(pid)
                if res.get("ok") is False:
                    return self._json(res, 400)
                return self._json(res)

            if route == "/api/music/playlist/clear":
                if not music:
                    return self._json({"ok": False, "error": "music disabled"}, 400)
                return self._json(music.clear_playlist())

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
    :root {
      --bg: #0f1114;
      --panel: #15181d;
      --panel-2: #101418;
      --border: rgba(255,255,255,0.08);
      --muted: #9aa3ad;
      --text: #e6e8ea;
      --danger: #b14b4b;
      --shadow: 0 6px 14px rgba(0,0,0,0.35);
      --radius: 12px;
    }

    body {
      font-family: "Space Grotesk", "Figtree", "Avenir Next", "Segoe UI", sans-serif;
      margin: 0;
      color: var(--text);
      background: var(--bg);
      min-height: 100vh;
    }
    .page { padding: 16px; max-width: 1400px; margin: 0 auto; }
    .row { display: flex; gap: 8px; align-items: center; flex-wrap: wrap; }
    button {
      padding: 8px 10px;
      border: 1px solid #2a313a;
      border-radius: 8px;
      cursor: pointer;
      color: #e6e8ea;
      background: #1a1f25;
      font-weight: 600;
      letter-spacing: 0.1px;
    }
    button:hover { background: #20262d; }
    button.primary { background: #2a313a; border-color: #3a424c; }
    button.danger { background: #3a1f1f; border-color: #5a2a2a; color: #f3d5d5; }
    button.gray { background: #161a20; }
    input, select {
      padding: 6px 8px;
      border-radius: 8px;
      border: 1px solid #2a313a;
      background: #0c1014;
      color: #e6e8ea;
    }
    .grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(240px, 1fr)); gap: 10px; margin-top: 10px; }
    .card { background: var(--panel-2); border-radius: 10px; padding: 8px; box-shadow: var(--shadow); border: 1px solid #1c2228; }
    .card.current { outline: 2px solid rgba(230,232,234,0.25); }
    .thumb { width: 100%; aspect-ratio: 16/9; background: #000; border-radius: 10px; object-fit: cover; display: block; }
    .meta { margin-top: 6px; font-size: 13px; opacity: 0.9; word-break: break-all; }
    .small { font-size: 11px; opacity: 0.75; }
    .muted { font-size: 11px; opacity: 0.7; }
    label { display: inline-flex; gap: 6px; align-items: center; cursor: pointer; }
    input[type="checkbox"] { transform: scale(1.1); }

    .topbar {
      display: grid;
      grid-template-columns: minmax(0, 1fr) auto;
      gap: 12px;
      align-items: center;
      padding: 12px;
      border-radius: 12px;
      background: var(--panel);
      border: 1px solid #232a33;
      margin-bottom: 12px;
    }
    .title { font-size: 20px; font-weight: 600; letter-spacing: 0.2px; }
    .meta-line { margin-top: 4px; display: flex; flex-wrap: wrap; gap: 6px; align-items: center; }
    .status-line { margin-top: 4px; font-size: 11px; color: var(--muted); }
    .pill {
      display: inline-flex;
      align-items: center;
      gap: 6px;
      font-size: 10px;
      padding: 3px 8px;
      border-radius: 999px;
      background: #1b2026;
      border: 1px solid #2a313a;
      color: #c9d1d9;
      text-transform: uppercase;
      letter-spacing: 0.4px;
    }
    .pill.bad { background: #2a1616; border-color: #4a2525; color: #f0c8c8; }
    .pill.ok { background: #16251c; border-color: #284332; color: #cfe7d5; }

    .control-deck {
      margin-bottom: 12px;
      padding: 12px;
      border-radius: 12px;
      background: var(--panel-2);
      border: 1px solid #232a33;
    }
    .deck-head {
      display: grid;
      grid-template-columns: minmax(0, 1fr);
      gap: 4px;
      align-items: center;
      margin-bottom: 10px;
    }
    .deck-title { font-size: 15px; font-weight: 600; letter-spacing: 0.2px; }
    .deck-sub { font-size: 11px; color: var(--muted); }
    .deck-grid {
      display: grid;
      grid-template-columns: repeat(3, minmax(0, 1fr));
      gap: 10px;
    }
    .panel {
      padding: 10px;
      border-radius: 10px;
      background: #0f1317;
      border: 1px solid #232a33;
    }
    .panel-title {
      font-size: 10px;
      letter-spacing: 0.8px;
      text-transform: uppercase;
      color: #c7ced6;
      margin-bottom: 6px;
    }
    .panel-body { display: flex; flex-direction: column; gap: 8px; }
    .field-label { font-size: 10px; color: var(--muted); text-transform: uppercase; letter-spacing: 0.6px; }
    .chip {
      display: inline-flex;
      align-items: center;
      gap: 6px;
      font-size: 10px;
      padding: 2px 6px;
      border-radius: 999px;
      border: 1px solid #2a313a;
      background: #1b2026;
      color: #c9d1d9;
    }
    #musicNow { max-width: 200px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }

    .thumb-stack { display: flex; flex-direction: column; gap: 6px; align-items: flex-end; }
    #currentThumbWrap {
      width: 180px;
      aspect-ratio: 16/9;
      border-radius: 10px;
      overflow: hidden;
      box-shadow: var(--shadow);
      border: 1px solid #232a33;
      background: #0a0a0a;
      display: flex;
      align-items: center;
      justify-content: center;
    }
    #currentThumb {
      width: 100%;
      height: 100%;
      object-fit: cover;
      display: none;
    }
    #currentThumbWrap.has-current #currentThumb { display: block; }
    #currentThumbWrap.has-current .thumb-placeholder { display: none; }
    .thumb-placeholder { font-size: 10px; opacity: 0.6; text-transform: uppercase; letter-spacing: 0.8px; }

    .section-title { font-size: 16px; letter-spacing: 0.2px; margin: 8px 0 6px; }

    @media (max-width: 1100px) {
      .deck-grid { grid-template-columns: 1fr; }
    }
    @media (max-width: 820px) {
      .topbar { grid-template-columns: 1fr; }
      .thumb-stack { align-items: flex-start; }
      #currentThumbWrap { width: min(320px, 100%); }
    }

    /* Hide file inputs but keep them accessible */
    .hiddenFile { display:none; }
  </style>
</head>
<body>
  <div class="page">
    <header class="topbar">
      <div>
        <div class="title">fehb control</div>
        <div class="meta-line">
          <span id="wsStatus" class="pill">WS: connecting</span>
          <span id="folderInfo" class="muted">Folder: --</span>
          <span id="currentName" class="muted">Current: --</span>
        </div>
        <div id="status" class="status-line">Ready</div>
      </div>
      <div class="thumb-stack">
        <div id="currentThumbWrap" title="Currently showing">
          <div id="currentThumbPlaceholder" class="thumb-placeholder">No image</div>
          <img id="currentThumb" alt="current thumbnail">
        </div>
        <div id="currentThumbLabel" class="small">Currently showing</div>
      </div>
    </header>

  <section class="control-deck">
    <div class="deck-head">
      <div class="deck-title">Controls</div>
      <div class="deck-sub">Images / CEC / Music</div>
    </div>
    <div class="deck-grid">
      <div class="panel">
        <div class="panel-title">Images</div>
        <div class="panel-body">
          <div class="row">
            <button class="primary" onclick="apiPost('api/slideshow/next', {})">Next image</button>
            <button class="gray" onclick="apiPost('api/images/refresh', {})">Refresh list</button>
            <button class="gray" onclick="updateSelf()">Update</button>
            <button class="primary" onclick="apiPost('api/picsum', {})">Download picsum 1920×1080</button>
          </div>
          <div class="row">
            <span class="field-label">Delay (s)</span>
            <input id="delay" type="number" min="1" max="86400" value="15" style="width:90px;">
            <button class="gray" onclick="setDelay()">Apply</button>
          </div>

          <!-- Mobile-friendly upload choice -->
          <input id="filePick" class="hiddenFile" type="file" accept="image/*">
          <input id="fileCam"  class="hiddenFile" type="file" accept="image/*" capture="environment">

          <div class="row">
            <button class="primary" onclick="document.getElementById('fileCam').click()">Take photo</button>
            <button class="primary" onclick="document.getElementById('filePick').click()">Choose file</button>
          </div>
        </div>
      </div>
      <div class="panel">
        <div class="panel-title">CEC</div>
        <div class="panel-body">
          <div class="row">
            <button class="gray" onclick="apiPost('api/cec/playback', {})">Playback (-S)</button>
            <button class="gray" onclick="apiPost('api/cec/image_view_on', {})">Image View On</button>
            <button class="danger" onclick="apiPost('api/cec/standby', {})">Standby (TV)</button>
          </div>
          <div class="row">
            <span class="field-label">Active-source x</span>
            <input id="asx" type="number" min="0" max="15" value="2" style="width:70px;">
            <button class="gray" onclick="setActiveSource()">Set active source</button>
          </div>
        </div>
      </div>
        <div class="panel">
        <div class="panel-title">Music</div>
        <div class="panel-body">
          <div class="row">
            <button class="primary" onclick="musicToggle()">Play/Pause</button>
            <button class="gray" onclick="musicNext()">Next</button>
            <span class="field-label">Volume</span>
            <input id="musicVol" type="number" min="0" max="200" value="70" style="width:70px;">
            <button class="gray" onclick="setMusicVolume()">Set</button>
            <span id="musicNow" class="chip"></span>
          </div>
          <div class="row">
            <span class="field-label">Playlist</span>
            <select id="playlistSel" style="min-width:220px;"></select>
            <button class="gray" onclick="playlistStart()">Run playlist</button>
            <button class="gray" onclick="playlistClear()">Random</button>
            <button class="gray" onclick="loadPlaylists()">Refresh playlists</button>
            <span id="playlistStatus" class="small"></span>
          </div>
          <div class="row">
            <span class="field-label">Music bar</span>
            <select id="musicBarStrategy">
              <option value="1">1: Match label width</option>
              <option value="2">2: Constant width</option>
              <option value="3">3: Length-based width</option>
            </select>
            <span class="field-label">Width %</span>
            <input id="musicBarWidth" type="number" min="5" max="80" step="1" value="25" style="width:70px;">
            <button class="gray" onclick="setMusicBarConfig()">Apply</button>
            <span id="musicBarHint" class="small"></span>
          </div>
        </div>
      </div>
    </div>
  </section>

  <div class="section-title">Images</div>
  <div id="grid" class="grid"></div>

<script>
let ws = null;
let current = "";
let wsAttempts = 0;
let wsTimer = null;
let activePlaylistId = "";
let activePlaylistName = "";

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

    setWsStatus("WS connecting", "");

    ws = new WebSocket(wsUrl());

    ws.onopen = () => {
      wsAttempts = 0;
      setWsStatus("WS connected", "ok");
      setStatus("WS connected", false);
    };

    ws.onclose = () => {
      ws = null;
      wsAttempts++;
      setWsStatus("WS disconnected", "bad");
      setStatus("WS disconnected (reconnecting…)", true);
      scheduleReconnect();
    };

    ws.onerror = () => {
      // error will usually be followed by close
      setWsStatus("WS error", "bad");
      setStatus("WS error (reconnecting…)", true);
    };

    ws.onmessage = (ev) => {
      let msg = null;
      try { msg = JSON.parse(ev.data); } catch(e) { return; }
      if(!msg) return;
      if(msg.type === "state"){
        if(typeof msg.delay_s === "number"){
          document.getElementById("delay").value = msg.delay_s;
        }
        if(typeof msg.current === "string"){
          setCurrent(msg.current);
        }
      }
      if(msg.type === "music"){
        if(typeof msg.volume === "number"){
          document.getElementById("musicVol").value = msg.volume;
        }
        if(msg.track || msg.label){
          setMusicNow(msg.track || null, msg.label || "");
        }
        updatePlaylistState(msg);
      }
    };
  } catch(e) {
    ws = null;
    wsAttempts++;
    setWsStatus("WS failed", "bad");
    setStatus("WS failed (reconnecting…)", true);
    scheduleReconnect();
  }
}

function cssSafe(s){
  return btoa(unescape(encodeURIComponent(s))).replace(/=+$/,'').replace(/\+/g,'-').replace(/\//g,'_');
}

function setCurrent(name){
  current = name || "";

  const nameEl = document.getElementById("currentName");
  if(nameEl){
    nameEl.textContent = current ? `Current: ${current}` : "Current: --";
  }
  const labelEl = document.getElementById("currentThumbLabel");
  if(labelEl){
    labelEl.textContent = current ? "Currently showing" : "No image selected";
  }

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
    if(wrap) wrap.classList.add("has-current");
    if(img) img.src = `thumb?name=${encodeURIComponent(current)}&t=${Date.now()}`;
  } else {
    if(wrap) wrap.classList.remove("has-current");
    if(img) img.removeAttribute("src");
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
  if(!el) return;
  el.textContent = msg;
  el.style.color = bad ? '#f87171' : '#9ca3af';
}
function setWsStatus(msg, state){
  const el = document.getElementById('wsStatus');
  if(!el) return;
  el.textContent = msg;
  el.classList.remove('bad', 'ok');
  if(state === 'bad') el.classList.add('bad');
  if(state === 'ok') el.classList.add('ok');
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

function setMusicNow(track, label){
  const el = document.getElementById('musicNow');
  if(!el) return;
  let text = '';
  if(typeof label === 'string' && label.trim()){
    text = label.trim();
  } else if(track && (track.title || track.artist)){
    const t = (track.title || '').trim();
    let a = (track.artist || '').trim();
    if(a.toLowerCase() === 'unknown artist') a = '';
    text = (t && a) ? `${t} — ${a}` : (t || a);
  }
  if(text){
    el.textContent = text;
  }
}

function selectHasValue(sel, value){
  if(!sel) return false;
  for(const opt of sel.options){
    if(opt.value == value){
      sel.value = value;
      return true;
    }
  }
  return false;
}

function updatePlaylistState(state){
  const sel = document.getElementById('playlistSel');
  const status = document.getElementById('playlistStatus');
  if(!status) return;

  if(state && state.source === 'playlist' && state.playlist && state.playlist.id){
    activePlaylistId = String(state.playlist.id);
    activePlaylistName = String(state.playlist.name || '').trim();
    status.textContent = `Playlist: ${activePlaylistName || 'Unknown'}`;
    if(sel){
      selectHasValue(sel, activePlaylistId);
    }
  } else {
    activePlaylistId = "";
    activePlaylistName = "";
    status.textContent = "Playlist: Random";
  }
}

async function loadPlaylists(){
  const sel = document.getElementById('playlistSel');
  if(!sel) return;

  const prev = sel.value;
  sel.innerHTML = "";

  const j = await apiGet('api/music/playlists');
  if(!j || j.ok === false){
    const opt = document.createElement('option');
    opt.value = "";
    opt.textContent = "(playlists unavailable)";
    sel.appendChild(opt);
    sel.disabled = true;
    return;
  }

  sel.disabled = false;
  const pls = j.playlists || [];
  if(!pls.length){
    const opt = document.createElement('option');
    opt.value = "";
    opt.textContent = "(no playlists)";
    sel.appendChild(opt);
    return;
  }

  for(const p of pls){
    if(!p.id) continue;
    const opt = document.createElement('option');
    opt.value = String(p.id);
    const cnt = p.songCount ? ` (${p.songCount})` : '';
    opt.textContent = `${p.name || 'Untitled'}${cnt}`;
    sel.appendChild(opt);
  }

  if(!selectHasValue(sel, activePlaylistId)){
    selectHasValue(sel, prev);
  }
}

async function playlistStart(){
  const sel = document.getElementById('playlistSel');
  if(!sel || !sel.value){
    setStatus("Select a playlist", true);
    return;
  }
  await apiPost('api/music/playlist/set', {id: sel.value});
  await musicState();
}

async function playlistClear(){
  await apiPost('api/music/playlist/clear', {});
  await musicState();
}

function syncMusicBarControls(strategy){
  const sel = document.getElementById('musicBarStrategy');
  const width = document.getElementById('musicBarWidth');
  const hint = document.getElementById('musicBarHint');
  if(!sel || !width || !hint) return;

  const s = parseInt(strategy || sel.value || "2", 10);
  if(s === 2){
    width.disabled = false;
    hint.textContent = '';
  } else if(s === 3){
    width.disabled = true;
    hint.textContent = 'Length-based (3:30 => 25%, max 40%)';
  } else {
    width.disabled = true;
    hint.textContent = 'Width follows label';
  }
}

async function setMusicBarConfig(){
  const sel = document.getElementById('musicBarStrategy');
  const width = document.getElementById('musicBarWidth');
  if(!sel || !width) return;
  const strategy = parseInt(sel.value || "2", 10);
  let pct = parseFloat(width.value || "25");
  if(isNaN(pct)) pct = 25;
  const ratio = pct / 100.0;
  await apiPost('api/config/music_bar', {strategy, ratio});
  await musicState();
}

async function musicState(){
  const j = await apiGet('api/music/state');
  if(!j || j.ok === false){
    return;
  }
  if(typeof j.volume === "number"){
    document.getElementById("musicVol").value = j.volume;
  }
  if(typeof j.music_bar_strategy === "number"){
    const sel = document.getElementById("musicBarStrategy");
    if(sel) sel.value = String(j.music_bar_strategy);
    syncMusicBarControls(j.music_bar_strategy);
  }
  if(typeof j.music_bar_ratio === "number"){
    const w = document.getElementById("musicBarWidth");
    if(w) w.value = Math.round(j.music_bar_ratio * 100);
  }
  setMusicNow(j.track || null, j.label || "");
  updatePlaylistState(j);
}

async function musicToggle(){
  await apiPost('api/music/toggle', {});
  await musicState();
}

async function musicNext(){
  await apiPost('api/music/next', {});
  await musicState();
}

async function setMusicVolume(){
  const v = parseFloat(document.getElementById('musicVol').value || "70");
  await apiPost('api/music/volume', {volume: v});
  await musicState();
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
  const folderEl = document.getElementById('folderInfo');
  if(folderEl){
    folderEl.textContent = `Folder: ${j.folder} | ${imgs.length} files`;
  }
  setStatus("Images loaded", false);

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

const musicBarSel = document.getElementById("musicBarStrategy");
if(musicBarSel){
  musicBarSel.addEventListener("change", () => syncMusicBarControls());
  syncMusicBarControls(musicBarSel.value);
}

// start
connectWS();
loadImages();
loadPlaylists();
musicState();
setInterval(musicState, 5000);
</script>
  </div>
</body>
</html>
"""


def start_server(mgr, slideshow, hub, music, host="0.0.0.0", port=DEFAULT_PORT):
    Handler = make_handler(mgr, slideshow, hub, music)
    httpd = ThreadingHTTPServer((host, port), Handler)
    t = threading.Thread(target=httpd.serve_forever, daemon=True)
    t.start()
    return httpd


def main():
    delay = int(sys.argv[1]) if len(sys.argv) > 1 else default_delay_s()
    folder = sys.argv[2] if len(sys.argv) > 2 else "~/wallpapers"
    port = int(sys.argv[3]) if len(sys.argv) > 3 else DEFAULT_PORT

    mgr = ImageManager(folder)
    mgr.set_delay(delay)

    hub = WebSocketHub()
    app = QApplication(sys.argv)
    apply_locale_from_config()
    w = Slideshow(mgr, hub, delay_s=mgr.delay_s)
    music = MusicManager(hub, w)
    cec_listener = start_cec_key_listener(music, w)
    if cec_listener:
        atexit.register(cec_listener.stop)
        try:
            app.aboutToQuit.connect(cec_listener.stop)
        except Exception:
            pass

    start_server(mgr, w, hub, music, host="0.0.0.0", port=port)

    addrs = get_ipv4_addrs()
    print("[fehb] web ui URLs:")
    for ip in addrs:
        print(f"  http://{ip}:{port}/   (reverse-proxy safe; relative paths; WS at ./ws)")

    return app.exec()


if __name__ == "__main__":
    raise SystemExit(main())
