# main.py - النسخة الكاملة والنهائية مع نظام الترخيص (مصححة الأخطاء)
import io
import json
import math
import os
import queue
import random
import re
import sqlite3
import struct
import sys
import threading
import time
import traceback
import urllib.parse
import urllib.request
import zlib
import hashlib
import uuid
import webbrowser
import hmac
from kivy.core.clipboard import Clipboard

KM = 111.195
TILE = 256
MAX_LAT = 85.0511
MAX_ZOOM = 21
EST_KB = 20.0

# ============================================================
# نظام الترخيص
# ============================================================
LICENSE_SECRET = "b217cd6f199ef0e51c99c82a6da88962cbb1b2393c62a3820959c46333403db2a2328173bd55fa0a2425b54a3aa0a7e9e06a46af5b876247d31722a9bbdf88295ddad1e25b50f5d9c62cb728155ad1e5844bc2dfd2f6a4b8d73da165228c7008208bf1fc477d221f349b361dff6101796189306e32403161bb3014d58881749ca32716536bdb436fe295464c5eb4c7ed3d742ab23e838bd413e8e35f0a15ce48b46b6088686cf4f44a6a46bc9373762dd46c88ae3b1173ba808139cb338bdba1cbe0f106da63f22991a729c41ab9a61401df0f1682d9628f63c9c20d8ccb8f01aab0c0affdbd306e557da6103c5ac62eabb2d4b3469ebe7232dbfcc32d95624b"   # غيّره إلى سر خاص بك
LICENSE_PREFIX = "ELINT-"

# القيود الافتراضية (Free)
FREE_MAX_ZOOM = 14
FREE_DAILY_TILES_LIMIT = 1000
FREE_DAILY_EXPORT_LIMIT = 1

# حدود Pro
PRO_MAX_ZOOM = 21
PRO_DAILY_TILES_LIMIT = 10 ** 9
PRO_DAILY_EXPORT_LIMIT = 10 ** 9

def get_device_uid():
    """معرّف الجهاز الفريد (Android ID أو MAC)."""
    try:
        from jnius import autoclass
        PythonActivity = autoclass('org.kivy.android.PythonActivity')
        Secure = autoclass('android.provider.Settings$Secure')
        android_id = Secure.getString(
            PythonActivity.mActivity.getContentResolver(),
            Secure.ANDROID_ID
        )
        if android_id:
            return str(android_id)
    except Exception:
        pass
    return str(uuid.getnode())

def _hmac_raw(uid: str) -> str:
    raw = f"{str(uid).strip()}:{LICENSE_SECRET}".encode('utf-8')
    return hmac.new(LICENSE_SECRET.encode('utf-8'), raw, hashlib.sha256).hexdigest().upper()

def generate_valid_key(uid: str) -> str:
    """مفتاح التفعيل الصالح لهذا الجهاز (بصيغة ELINT-XXXXXXXXXX)."""
    return LICENSE_PREFIX + _hmac_raw(uid)[:12]

def normalize_key(key: str) -> str:
    return (key or '').strip().upper().replace(" ", "")

def validate_key(uid: str, key: str) -> bool:
    return normalize_key(key) == generate_valid_key(uid)
# ============================================================

USER_AGENTS = [
    'Mozilla/5.0 (Linux; Android 13; SM-S918B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/114.0.0.0 Mobile Safari/537.36',
    'Mozilla/5.0 (iPhone; CPU iPhone OS 16_5 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/16.5 Mobile/15E148 Safari/604.1',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/115.0.0.0 Safari/537.36',
    'Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:109.0) Gecko/20100101 Firefox/114.0'
]

def get_user_agent():
    return random.choice(USER_AGENTS)

SOURCES = {
    'Google Maps': 'https://mt0.google.com/vt/lyrs=m&x={x}&y={y}&z={z}',
    'Google Satellite': 'https://mt0.google.com/vt/lyrs=s&x={x}&y={y}&z={z}',
    'Google Hybrid': 'https://mt0.google.com/vt/lyrs=y&x={x}&y={y}&z={z}',
    'Custom URL': '',
}
LAYERS = ['Google Maps', 'Google Satellite', 'Google Hybrid']
LAYER_LABEL = {'Google Maps': 'Map', 'Google Satellite': 'Sat', 'Google Hybrid': 'Hybrid', 'Custom URL': 'Map'}
LAYER_DIR = {'Google Satellite': ('tiles_satellite', 'jpg'), 'Google Hybrid': ('tiles_hybrid', 'jpg')}

def layer_dir(source):
    return LAYER_DIR.get(source, ('tiles', 'png'))

def clamp(v, a, b):
    return max(a, min(v, b))

def lonlat_to_world(lon, lat, z):
    n = TILE * 2.0 ** z
    lat = clamp(lat, -MAX_LAT, MAX_LAT)
    x = (lon + 180.0) / 360.0 * n
    y = (1.0 - math.asinh(math.tan(math.radians(lat))) / math.pi) / 2.0 * n
    return x, y

def world_to_lonlat(x, y, z):
    n = TILE * 2.0 ** z
    lon = x / n * 360.0 - 180.0
    lat = math.degrees(math.atan(math.sinh(math.pi * (1.0 - 2.0 * y / n))))
    return lon, clamp(lat, -MAX_LAT, MAX_LAT)

def lonlat_to_tile(lon, lat, z):
    n = 1 << z
    x, y = lonlat_to_world(lon, lat, z)
    return (int(clamp(math.floor(x / TILE), 0, n - 1)), int(clamp(math.floor(y / TILE), 0, n - 1)))

def norm_bounds(b):
    la0, la1, lo0, lo1 = b
    la0, la1 = sorted((clamp(la0, -MAX_LAT, MAX_LAT), clamp(la1, -MAX_LAT, MAX_LAT)))
    lo0, lo1 = sorted((clamp(lo0, -180.0, 180.0), clamp(lo1, -180.0, 180.0)))
    return la0, la1, lo0, lo1

def point_range_bounds(lat, lon, range_km):
    dlat = range_km / KM
    dlon = range_km / (KM * max(math.cos(math.radians(clamp(lat, -MAX_LAT, MAX_LAT))), 0.01))
    return norm_bounds((lat - dlat, lat + dlat, lon - dlon, lon + dlon))

def tile_range(b, z):
    la0, la1, lo0, lo1 = norm_bounds(b)
    x0, y1 = lonlat_to_tile(lo0, la0, z)
    x1, y0 = lonlat_to_tile(lo1, la1, z)
    return x0, y0, x1, y1

def count_tiles(b, z0, z1):
    n = 0
    for z in range(z0, z1 + 1):
        x0, y0, x1, y1 = tile_range(b, z)
        n += (x1 - x0 + 1) * (y1 - y0 + 1)
    return n

def best_max_zoom(b, z0, limit, zcap=FREE_MAX_ZOOM):
    best = z0
    for z in range(z0, zcap + 1):
        if count_tiles(b, z0, z) > limit:
            break
        best = z
    return best

def list_tiles(b, z0, z1):
    out = []
    for z in range(z0, z1 + 1):
        x0, y0, x1, y1 = tile_range(b, z)
        out += [(z, x, y) for x in range(x0, x1 + 1) for y in range(y0, y1 + 1)]
    return out

def tile_path(folder, z, x, y, layer=('tiles', 'png')):
    return os.path.join(folder, layer[0], str(z), str(x), '%d.%s' % (y, layer[1]))

def ssl_context():
    try:
        import ssl
        import certifi
        return ssl.create_default_context(cafile=certifi.where())
    except Exception:
        return None

def fetch_bytes(url, ctx=None, timeout=15):
    req = urllib.request.Request(url, headers={'User-Agent': get_user_agent()})
    with urllib.request.urlopen(req, timeout=timeout, context=ctx) as r:
        data = r.read()
    if len(data) < 100 or not (data[:4] == b'\x89PNG' or data[:2] == b'\xff\xd8' or data[:4] == b'RIFF'):
        raise ValueError('not an image tile')
    return data

def folder_tile_bounds(folder, layer=('tiles', 'png')):
    root = os.path.join(folder, layer[0])
    ext = '.' + layer[1]
    try:
        zs = sorted(int(d) for d in os.listdir(root) if d.isdigit())
        for z in reversed(zs):
            xs = sorted(int(d) for d in os.listdir(os.path.join(root, str(z))) if d.isdigit())
            ys = []
            for x in xs:
                ys += [int(f[:-4]) for f in os.listdir(os.path.join(root, str(z), str(x))) if f.endswith(ext)]
            if xs and ys:
                lon0, lat1 = world_to_lonlat(xs[0] * TILE, min(ys) * TILE, z)
                lon1, lat0 = world_to_lonlat((xs[-1] + 1) * TILE, (max(ys) + 1) * TILE, z)
                return lat0, lat1, lon0, lon1
    except (OSError, ValueError):
        pass
    return None

class TileDownloader:
    def __init__(self, folder, url, workers=2, delay=0.05, layer=('tiles', 'png')):
        self.folder, self.url, self.workers, self.delay = folder, url, workers, delay
        self.layer = tuple(layer)
        self.cancel = threading.Event()
        self.ok = self.skipped = self.fail = 0
        self.blocked = 0
        self.aborted = ''

    def run(self, tiles, progress=None):
        ctx = ssl_context()
        q = queue.Queue()
        for t in tiles:
            q.put(t)
        lock = threading.Lock()
        total = len(tiles)

        def report():
            if progress:
                progress(self.ok + self.skipped + self.fail, total)

        def work():
            while not self.cancel.is_set():
                try:
                    z, x, y = q.get_nowait()
                except queue.Empty:
                    return
                p = tile_path(self.folder, z, x, y, self.layer)
                if os.path.isfile(p):
                    with lock:
                        self.skipped += 1
                    report()
                    continue
                try:
                    data = fetch_bytes(self.url.format(z=z, x=x, y=y), ctx)
                    os.makedirs(os.path.dirname(p), exist_ok=True)
                    with open(p + '.part', 'wb') as f:
                        f.write(data)
                    os.replace(p + '.part', p)
                    with lock:
                        self.ok += 1
                except Exception as ex:
                    with lock:
                        self.fail += 1
                        if getattr(ex, 'code', 0) in (403, 429):
                            self.blocked += 1
                            if self.blocked >= 5 and not self.aborted:
                                self.aborted = 'blocked'
                                self.cancel.set()
                        if self.ok == 0 and self.fail >= 8:
                            self.aborted = 'network'
                            self.cancel.set()
                report()
                time.sleep(self.delay)

        threads = [threading.Thread(target=work, daemon=True) for _ in range(max(1, self.workers))]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        if not self.aborted and self.cancel.is_set():
            self.aborted = 'cancelled'
        report()
        return dict(ok=self.ok, skipped=self.skipped, fail=self.fail, aborted=self.aborted, total=total)

def write_mbtiles(out_path, folder, layer, b, z0, z1, progress=None, cancelled=None):
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    if os.path.exists(out_path):
        os.remove(out_path)

    conn = sqlite3.connect(out_path)
    cursor = conn.cursor()
    cursor.execute("CREATE TABLE metadata (name text, value text);")
    cursor.execute("CREATE TABLE tiles (zoom_level integer, tile_column integer, tile_row integer, tile_data blob);")
    cursor.execute("CREATE UNIQUE index name on tiles (zoom_level, tile_column, tile_row);")

    cursor.execute("INSERT INTO metadata VALUES ('name', 'Elint Map Export');")
    cursor.execute("INSERT INTO metadata VALUES ('type', 'baselayer');")
    cursor.execute("INSERT INTO metadata VALUES ('version', '1.0');")
    cursor.execute("INSERT INTO metadata VALUES ('format', 'png');")

    tiles_list = []
    for z in range(z0, z1 + 1):
        x0, y0, x1, y1 = tile_range(b, z)
        for x in range(x0, x1 + 1):
            for y in range(y0, y1 + 1):
                tiles_list.append((z, x, y))

    total = len(tiles_list)
    done = 0
    missing = 0

    for z, x, y in tiles_list:
        if cancelled and cancelled():
            conn.close()
            return None
        p = tile_path(folder, z, x, y, layer)
        if os.path.isfile(p):
            try:
                with open(p, 'rb') as f:
                    data = f.read()
                y_tms = (1 << z) - 1 - y
                cursor.execute("INSERT OR IGNORE INTO tiles (zoom_level, tile_column, tile_row, tile_data) VALUES (?, ?, ?, ?);",
                               (z, x, y_tms, sqlite3.Binary(data)))
            except Exception:
                missing += 1
        else:
            missing += 1
        done += 1
        if progress and (done % 15 == 0 or done == total):
            progress(done, total)

    conn.commit()
    conn.close()
    return total, missing

MERC = 20037508.342789244
EXPORT_MAX_BYTES = 2 * 1024 ** 3
EXPORT_MAX_WIDTH = 60000
STRIP_ROWS = 64

try:
    from PIL import Image as PILImage
except Exception:
    PILImage = None

def export_geometry(b, z):
    x0, y0, x1, y1 = tile_range(b, z)
    w, h = (x1 - x0 + 1) * TILE, (y1 - y0 + 1) * TILE
    return x0, y0, x1, y1, w, h, w * h * 3

def export_fits(b, z):
    g = export_geometry(b, z)
    return g[6] <= EXPORT_MAX_BYTES and g[4] <= EXPORT_MAX_WIDTH

def decode_tile_rgb(path):
    try:
        if PILImage is not None:
            with PILImage.open(path) as im:
                im = im.convert('RGB')
                if im.size != (TILE, TILE):
                    im = im.resize((TILE, TILE))
                return im.tobytes()
        from kivy.core.image import ImageLoader
        d = ImageLoader.load(path)._data[0]
        w, h, fmt = d.width, d.height, d.fmt
        if fmt not in ('rgb', 'rgba', 'bgr', 'bgra') or (w, h) != (TILE, TILE):
            return None
        bpp, raw = len(fmt), bytes(d.data)
        stride = len(raw) // h
        if stride != w * bpp:
            raw = b''.join(raw[r * stride:r * stride + w * bpp] for r in range(h))
        ri, bi = (0, 2) if fmt[0] == 'r' else (2, 0)
        out = bytearray(w * h * 3)
        out[0::3], out[1::3], out[2::3] = raw[ri::bpp], raw[1::bpp], raw[bi::bpp]
        return bytes(out)
    except Exception:
        return None

def write_mapinfo_tab(tif_path, x0, y0, W, H, z):
    tile_m = 2.0 * MERC / (1 << z)
    px = tile_m / TILE
    ax, ay = -MERC + x0 * tile_m, MERC - y0 * tile_m
    bx, by = ax + W * px, ay - H * px
    pts = [(ax, ay, 0, 0), (bx, ay, W, 0), (bx, by, W, H), (ax, by, 0, H)]
    lines = ['!table', '!version 300', '!charset WindowsLatin1', '', 'Definition Table',
             '  File "%s"' % os.path.basename(tif_path), '  Type "RASTER"']
    for i, (x, y, c, r) in enumerate(pts):
        lines.append('  (%.3f,%.3f) (%d,%d) Label "Pt %d"%s' % (x, y, c, r, i + 1, ',' if i < 3 else ''))
    lines += ['  CoordSys Earth Projection 10, 157, 7, 0', '  Units "m"', '']
    with open(os.path.splitext(tif_path)[0] + '.tab', 'w', newline='\r\n') as f:
        f.write('\n'.join(lines))

def write_geotiff(out_path, folder, layer, b, z, progress=None, cancelled=None):
    x0, y0, x1, y1, W, H, raw = export_geometry(b, z)
    if raw > EXPORT_MAX_BYTES or W > EXPORT_MAX_WIDTH:
        raise ValueError('Too large (%dx%d px) - pick a lower zoom' % (W, H))
    nx, ny = x1 - x0 + 1, y1 - y0 + 1
    total, done, missing = nx * ny, 0, 0
    offsets, counts = [], []
    tmp = out_path + '.part'
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(tmp, 'wb') as f:
        f.write(b'II' + struct.pack('<HI', 42, 0))
        for ty in range(ny):
            band = bytearray(W * TILE * 3)
            for tx in range(nx):
                if cancelled and cancelled():
                    f.close()
                    os.remove(tmp)
                    return None
                rgb = decode_tile_rgb(tile_path(folder, z, x0 + tx, y0 + ty, layer))
                if rgb is None:
                    missing += 1
                else:
                    for r in range(TILE):
                        o = (r * W + tx * TILE) * 3
                        band[o:o + TILE * 3] = rgb[r * TILE * 3:(r + 1) * TILE * 3]
                done += 1
                if progress and (done % 8 == 0 or done == total):
                    progress(done, total)
            step = STRIP_ROWS * W * 3
            for s0 in range(0, len(band), step):
                comp = zlib.compress(bytes(band[s0:s0 + step]), 3)
                offsets.append(f.tell())
                counts.append(len(comp))
                f.write(comp)
        if f.tell() % 2:
            f.write(b'\0')
        ifd_at = f.tell()
        tile_m = 2.0 * MERC / (1 << z)
        px = tile_m / TILE
        geo_keys = [1, 1, 0, 4, 1024, 0, 1, 1, 1025, 0, 1, 1, 3072, 0, 1, 3857, 3076, 0, 1, 9001]
        tags = [
            (256, 4, 1, struct.pack('<I', W)),
            (257, 4, 1, struct.pack('<I', H)),
            (258, 3, 3, struct.pack('<3H', 8, 8, 8)),
            (259, 3, 1, struct.pack('<H', 8)),
            (262, 3, 1, struct.pack('<H', 2)),
            (273, 4, len(offsets), struct.pack('<%dI' % len(offsets), *offsets)),
            (277, 3, 1, struct.pack('<H', 3)),
            (278, 4, 1, struct.pack('<I', STRIP_ROWS)),
            (279, 4, len(counts), struct.pack('<%dI' % len(counts), *counts)),
            (284, 3, 1, struct.pack('<H', 1)),
            (33550, 12, 3, struct.pack('<3d', px, px, 0.0)),
            (33922, 12, 6, struct.pack('<6d', 0, 0, 0, -MERC + x0 * tile_m, MERC - y0 * tile_m, 0)),
            (34735, 3, len(geo_keys), struct.pack('<%dH' % len(geo_keys), *geo_keys)),
        ]
        extra_at = ifd_at + 2 + len(tags) * 12 + 4
        ifd, extra = struct.pack('<H', len(tags)), b''
        for tag, typ, cnt, data in tags:
            if len(data) <= 4:
                ifd += struct.pack('<HHI', tag, typ, cnt) + data.ljust(4, b'\0')
            else:
                ifd += struct.pack('<HHII', tag, typ, cnt, extra_at + len(extra))
                extra += data + (b'\0' if len(data) % 2 else b'')
        f.write(ifd + struct.pack('<I', 0) + extra)
        f.seek(4)
        f.write(struct.pack('<I', ifd_at))
    os.replace(tmp, out_path)
    try:
        write_mapinfo_tab(out_path, x0, y0, W, H, z)
    except Exception:
        pass
    return W, H, missing

from kivy.app import App
from kivy.clock import Clock
from kivy.core.image import Image as CoreImage
from kivy.core.text import Label as CoreLabel
from kivy.core.window import Window
from kivy.graphics import Color, Ellipse, Line, Rectangle, RoundedRectangle, Triangle
from kivy.metrics import dp
from kivy.uix.boxlayout import BoxLayout
from kivy.uix.button import Button
from kivy.uix.floatlayout import FloatLayout
from kivy.uix.gridlayout import GridLayout
from kivy.uix.label import Label
from kivy.uix.popup import Popup
from kivy.uix.progressbar import ProgressBar
from kivy.uix.relativelayout import RelativeLayout
from kivy.uix.screenmanager import NoTransition, Screen, ScreenManager
from kivy.uix.spinner import Spinner, SpinnerOption
from kivy.uix.stencilview import StencilView
from kivy.uix.switch import Switch
from kivy.uix.textinput import TextInput
from kivy.uix.widget import Widget
from kivy.uix.scrollview import ScrollView
from kivy.uix.behaviors import ButtonBehavior
from kivy.properties import BooleanProperty, ListProperty, NumericProperty, StringProperty
from kivy.utils import escape_markup, platform

BG = (0.047, 0.055, 0.075, 1)
PANEL = (0.090, 0.102, 0.133, 1)
RAISED = (0.125, 0.141, 0.184, 1)
TRACK = (0.160, 0.180, 0.230, 1)
ACCENT = (0.20, 0.54, 0.98, 1)
GREEN = (0.14, 0.66, 0.42, 1)
GREY = (0.21, 0.24, 0.31, 1)
ORANGE = (0.96, 0.58, 0.14, 1)
RED = (0.86, 0.27, 0.29, 1)
TXT = (0.90, 0.92, 0.95, 1)
MUTED = (0.56, 0.62, 0.70, 1)
GLASS = (0.07, 0.08, 0.11, 0.92)
YELLOW = (0.99, 0.85, 0.10, 1)
RADIUS = dp(12)

def _hex(c):
    return '%02x%02x%02x' % tuple(int(v * 255) for v in c[:3])

class RoundButton(Button):
    bg = ListProperty(ACCENT)
    radius = NumericProperty(RADIUS)

    def __init__(self, **kw):
        kw.update(background_normal='', background_down='', background_disabled_normal='',
                  background_disabled_down='', background_color=(0, 0, 0, 0))
        kw.setdefault('bold', True)
        kw.setdefault('color', (1, 1, 1, 1))
        super().__init__(**kw)
        with self.canvas.before:
            self._col = Color(*self.bg)
            self._rr = RoundedRectangle(pos=self.pos, size=self.size, radius=[self.radius])
        self.bind(pos=self._paint, size=self._paint, bg=self._paint, state=self._paint,
                  disabled=self._paint, radius=self._paint)
        self._paint()

    def _paint(self, *_):
        r, g, b, a = self.bg
        if self.disabled:
            r, g, b, a = r * 0.6, g * 0.6, b * 0.6, a * 0.6
        elif self.state == 'down':
            r, g, b = r * 0.78, g * 0.78, b * 0.78
        self._col.rgba = (r, g, b, a)
        self._rr.pos, self._rr.size, self._rr.radius = self.pos, (max(self.width, 0), max(self.height, 0)), [self.radius]

class Card(BoxLayout):
    bg = ListProperty(PANEL)
    edge = StringProperty('')
    edge_color = ListProperty([1, 1, 1, 0.08])
    radius = NumericProperty(0)

    def __init__(self, **kw):
        super().__init__(**kw)
        with self.canvas.before:
            self._col = Color(*self.bg)
            self._rr = RoundedRectangle(pos=self.pos, size=self.size, radius=[self.radius])
            self._ecol = Color(*self.edge_color)
            self._edge = Rectangle(pos=self.pos, size=(0, 0))
        self.bind(pos=self._paint, size=self._paint, bg=self._paint, edge=self._paint,
                  edge_color=self._paint, radius=self._paint)
        self._paint()

    def _paint(self, *_):
        w, h = max(self.width, 0), max(self.height, 0)
        t = dp(1.5)
        self._col.rgba = self.bg
        self._rr.pos, self._rr.size, self._rr.radius = self.pos, (w, h), [self.radius]
        self._ecol.rgba = self.edge_color
        if self.edge == 'top':
            self._edge.pos, self._edge.size = (self.x, self.top - t), (w, t)
        elif self.edge == 'bottom':
            self._edge.pos, self._edge.size = (self.x, self.y), (w, t)
        else:
            self._edge.size = (0, 0)

class Panel(Card):
    def on_touch_down(self, t):
        if self.collide_point(*t.pos):
            super().on_touch_down(t)
            return True
        return False

    def on_touch_move(self, t):
        return self.collide_point(*t.pos) or super().on_touch_move(t)

    def on_touch_up(self, t):
        if self.collide_point(*t.pos):
            super().on_touch_up(t)
            return True
        return False

class TileProgress(FloatLayout):
    max = NumericProperty(1)
    value = NumericProperty(0)

    def __init__(self, **kw):
        super().__init__(**kw)
        with self.canvas.before:
            Color(*TRACK)
            self._track = RoundedRectangle(radius=[dp(10)])
            self._fcol = Color(*ACCENT)
            self._fill = RoundedRectangle(radius=[dp(10)])
        self._lbl = Label(text='', bold=True, font_size='13sp', color=(1, 1, 1, 1))
        self.add_widget(self._lbl)
        self.bind(pos=self._paint, size=self._paint, value=self._paint, max=self._paint)
        self._paint()

    def _paint(self, *_):
        w, h = max(self.width, 0), max(self.height, 0)
        total = float(self.max) if self.max > 0 else 1.0
        frac = clamp(self.value / total, 0.0, 1.0)
        fw = w * frac
        self._track.pos, self._track.size, self._track.radius = self.pos, (w, h), [h / 2.0]
        self._fill.pos, self._fill.size = self.pos, (fw, h)
        self._fill.radius = [min(h / 2.0, fw / 2.0)]
        self._fcol.rgba = [a + (b - a) * frac for a, b in zip(ACCENT, GREEN)]
        done, all_ = format(int(self.value), ','), format(int(self.max), ',')
        if w >= dp(290):
            self._lbl.text = '%d%%     %s / %s tiles' % (int(frac * 100), done, all_)
        else:
            self._lbl.text = '%d%%    %s / %s' % (int(frac * 100), done, all_)

class FlatOption(SpinnerOption):
    def __init__(self, **kw):
        kw.update(background_normal='', background_down='', background_color=RAISED, color=TXT,
                  size_hint_y=None, height=dp(40), font_size='14sp')
        super().__init__(**kw)

class RoundSpinner(Spinner):
    def __init__(self, **kw):
        kw.update(background_normal='', background_down='', background_color=(0, 0, 0, 0), color=TXT)
        kw.setdefault('option_cls', FlatOption)
        kw.setdefault('size_hint_y', None)
        kw.setdefault('height', dp(40))
        super().__init__(**kw)
        with self.canvas.before:
            self._col = Color(*RAISED)
            self._rr = RoundedRectangle(pos=self.pos, size=self.size, radius=[dp(10)])
        with self.canvas.after:
            Color(*MUTED)
            self._tri = Triangle(points=[0, 0, 0, 0, 0, 0])
        self.bind(pos=self._paint, size=self._paint, state=self._paint)
        self._paint()

    def _paint(self, *_):
        self._col.rgba = (0.17, 0.19, 0.25, 1) if self.state == 'down' else RAISED
        self._rr.pos, self._rr.size = self.pos, self.size
        cx, cy = self.right - dp(18), self.center_y
        self._tri.points = [cx - dp(5), cy + dp(2.5), cx + dp(5), cy + dp(2.5), cx, cy - dp(3.5)]

class RoundInput(TextInput):
    def __init__(self, **kw):
        kw.update(background_normal='', background_active='', background_disabled_normal='',
                  background_color=(0, 0, 0, 0))
        super().__init__(**kw)
        with self.canvas.before:
            Color(*RAISED)
            self._rr = RoundedRectangle(pos=self.pos, size=self.size, radius=[dp(10)])
            self._lc = Color(1, 1, 1, 0)
            self._ln = Line(rounded_rectangle=(self.x, self.y, max(self.width, 1), max(self.height, 1), dp(10)),
                            width=dp(1.3))
        self.bind(pos=self._paint, size=self._paint, focus=self._paint)
        self._paint()

    def _paint(self, *_):
        self._rr.pos, self._rr.size = self.pos, self.size
        self._lc.rgba = ACCENT if self.focus else (1, 1, 1, 0.07)
        self._ln.rounded_rectangle = (self.x, self.y, max(self.width, 1), max(self.height, 1), dp(10))

class NavItem(ButtonBehavior, FloatLayout):
    title = StringProperty('')
    icon = StringProperty('')
    active = BooleanProperty(False)

    def __init__(self, **kw):
        super().__init__(**kw)
        self._lbl = Label(font_size='11sp', bold=True, size_hint=(1, None), height=dp(16),
                          pos_hint={'x': 0, 'y': 0.03})
        self.add_widget(self._lbl)
        self.bind(pos=self._paint, size=self._paint, active=self._paint, title=self._paint, state=self._paint)
        self._paint()

    def _paint(self, *_):
        on = self.active
        icol = (0.62, 0.80, 1.0, 1) if on else MUTED
        self._lbl.text = self.title
        self._lbl.color = TXT if on else MUTED
        c = self.canvas.before
        c.clear()
        pw, ph = dp(56), dp(28)
        cx = self.center_x
        py = self.top - dp(5) - ph
        icy = py + ph / 2.0
        with c:
            if on or self.state == 'down':
                Color(ACCENT[0], ACCENT[1], ACCENT[2], 0.22 if on else 0.10)
                RoundedRectangle(pos=(cx - pw / 2.0, py), size=(pw, ph), radius=[ph / 2.0])
            Color(*icol)
            k = self.icon
            if k == 'map':
                Ellipse(pos=(cx - dp(6), icy - dp(2)), size=(dp(12), dp(12)))
                Triangle(points=[cx - dp(5), icy + dp(2), cx + dp(5), icy + dp(2), cx, icy - dp(9)])
                Color(*PANEL)
                Ellipse(pos=(cx - dp(2.5), icy + dp(1.5)), size=(dp(5), dp(5)))
            elif k == 'download':
                Line(points=[cx, icy + dp(9), cx, icy - dp(2)], width=dp(1.8))
                Triangle(points=[cx - dp(6), icy - dp(1), cx + dp(6), icy - dp(1), cx, icy - dp(8)])
                Line(points=[cx - dp(9), icy - dp(10), cx + dp(9), icy - dp(10)], width=dp(1.8))
            elif k == 'library':
                for dy in (-7, 0, 7):
                    RoundedRectangle(pos=(cx - dp(9), icy + dp(dy) - dp(1.5)), size=(dp(18), dp(3)),
                                     radius=[dp(1.5)])
            elif k == 'settings':
                for dy, kx in ((7, -3), (0, 4), (-7, -2)):
                    Line(points=[cx - dp(9), icy + dp(dy), cx + dp(9), icy + dp(dy)], width=dp(1.6))
                    Ellipse(pos=(cx + dp(kx) - dp(3), icy + dp(dy) - dp(3)), size=(dp(6), dp(6)))
            else:
                Line(circle=(cx, icy, dp(8)), width=1.6)

def Btn(text, bg=ACCENT, **kw):
    kw.setdefault('font_size', '14sp')
    return RoundButton(text=text, bg=bg, **kw)

def label(text, **kw):
    kw.setdefault('color', TXT)
    kw.setdefault('font_size', '13sp')
    kw.setdefault('halign', 'left')
    kw.setdefault('valign', 'middle')
    lb = Label(text=text, **kw)
    lb.bind(size=lambda w, s: setattr(w, 'text_size', s))
    return lb

def entry(text='', **kw):
    return RoundInput(text=str(text), multiline=False, write_tab=False, size_hint_y=None, height=dp(40),
                      font_size='15sp', foreground_color=TXT, cursor_color=ACCENT,
                      padding=(dp(10), dp(9)), **kw)

def section(title):
    c = Card(orientation='vertical', size_hint_y=None, bg=PANEL, radius=dp(14), padding=(dp(12), dp(10)),
             spacing=dp(8))
    c.bind(minimum_height=c.setter('height'))
    c.add_widget(label(title.upper(), bold=True, color=MUTED, font_size='11sp', size_hint_y=None, height=dp(16)))
    return c

def scroll_col():
    sv = ScrollView(do_scroll_x=False, bar_width=dp(3))
    col = BoxLayout(orientation='vertical', size_hint_y=None, padding=(dp(12), dp(12)), spacing=dp(12))
    col.bind(minimum_height=col.setter('height'))
    sv.add_widget(col)
    return sv, col

def form_row(text, widget, h=40, wl=0.42):
    row = BoxLayout(size_hint_y=None, height=dp(h), spacing=dp(8))
    row.add_widget(label(text, size_hint_x=wl))
    row.add_widget(widget)
    return row

def fmt_area(b):
    la0, la1, lo0, lo1 = b
    return 'lat %.4f .. %.4f   lon %.4f .. %.4f' % (la0, la1, lo0, lo1)

def parse_num(s, name):
    try:
        return float(str(s).strip().replace(',', '.'))
    except ValueError:
        raise ValueError('%s is not a number' % name)

def parse_coords(text):
    t = str(text).translate(str.maketrans('٠١٢٣٤٥٦٧٨٩٫،', '0123456789.,')).upper()
    for ch in "°'\"′″’”":
        t = t.replace(ch, ' ')
    t = re.sub(r'[,;]', ' ', t)
    _NUM = r'[-+]?\d+(?:\.\d+)?'
    if not t.strip() or re.sub(r'%s|[NSEW]|\s' % _NUM, '', t):
        return None
    groups, cur = [], []
    for tk in re.findall(r'%s|[NSEW]' % _NUM, t):
        if tk.isalpha():
            if not cur:
                return None
            groups.append((cur, tk))
            cur = []
        else:
            cur.append(float(tk))
    if cur:
        groups.append((cur, ''))
    if len(groups) == 1 and groups[0][1] == '':
        nums = groups[0][0]
        if len(nums) not in (2, 4, 6):
            return None
        h = len(nums) // 2
        groups = [(nums[:h], ''), (nums[h:], '')]
    if len(groups) != 2 or any(not (1 <= len(g[0]) <= 3) for g in groups):
        return None
    vals = []
    for nums, hem in groups:
        if any(v < 0 or v >= 60 for v in nums[1:]):
            return None
        v = abs(nums[0]) + (nums[1] / 60.0 if len(nums) > 1 else 0.0) + (nums[2] / 3600.0 if len(nums) > 2 else 0.0)
        if math.copysign(1.0, nums[0]) < 0 or hem in ('S', 'W'):
            v = -v
        vals.append((v, hem))
    (a, ha), (b, hb) = vals
    if ha in ('E', 'W') or hb in ('N', 'S'):
        if ha in ('N', 'S') or hb in ('E', 'W'):
            return None
        lat, lon = b, a
    else:
        lat, lon = a, b
    if not (-90.0 <= lat <= 90.0 and -180.0 <= lon <= 180.0):
        return None
    return lat, lon

def geocode(query, ctx=None, limit=6, timeout=12):
    url = ('https://nominatim.openstreetmap.org/search?format=jsonv2&limit=%d&accept-language=en&q=%s'
           % (limit, urllib.parse.quote(query)))
    req = urllib.request.Request(url, headers={'User-Agent': get_user_agent()})
    with urllib.request.urlopen(req, timeout=timeout, context=ctx) as r:
        items = json.loads(r.read().decode('utf-8'))
    out = []
    for it in items:
        try:
            bb = it.get('boundingbox')
            out.append(dict(name=str(it.get('display_name') or query), lat=float(it['lat']), lon=float(it['lon']),
                            bbox=tuple(float(v) for v in bb) if bb else None))
        except (KeyError, TypeError, ValueError):
            pass
    return out

def tile_block_bounds(x0, y0, x1, y1, z, eps=1e-7):
    lon0, lat1 = world_to_lonlat(x0 * TILE, y0 * TILE, z)
    lon1, lat0 = world_to_lonlat((x1 + 1) * TILE, (y1 + 1) * TILE, z)
    return lat0 + eps, lat1 - eps, lon0 + eps, lon1 - eps

def _clusters(tiles):
    rest, out = set(tiles), []
    while rest:
        sx, sy = rest.pop()
        stack, x0, x1, y0, y1, n = [(sx, sy)], sx, sx, sy, sy, 1
        while stack:
            x, y = stack.pop()
            for dx in (-1, 0, 1):
                for dy in (-1, 0, 1):
                    q = (x + dx, y + dy)
                    if q in rest:
                        rest.remove(q)
                        stack.append(q)
                        n += 1
                        x0, x1 = min(x0, q[0]), max(x1, q[0])
                        y0, y1 = min(y0, q[1]), max(y1, q[1])
        out.append((x0, y0, x1, y1, n))
    return out

def scan_coverage(folder, layer=('tiles', 'png'), max_boxes=600):
    root, ext = os.path.join(folder, layer[0]), '.' + layer[1]
    try:
        zs = [int(d) for d in os.listdir(root) if d.isdigit()]
    except OSError:
        return []
    out, parents = [], set()
    for z in range(max(zs) if zs else -1, -1, -1):
        tiles, zdir = set(), os.path.join(root, str(z))
        try:
            xs = [d for d in os.listdir(zdir) if d.isdigit()]
        except OSError:
            xs = []
        for xd in xs:
            try:
                files = os.listdir(os.path.join(zdir, xd))
            except OSError:
                continue
            x = int(xd)
            for f in files:
                if f.endswith(ext) and f[:-len(ext)].isdigit():
                    tiles.add((x, int(f[:-len(ext)])))
        front = [t for t in tiles if t not in parents]
        for x0, y0, x1, y1, n in _clusters(front):
            out.append(dict(z=z, n=n, bounds=tile_block_bounds(x0, y0, x1, y1, z)))
        parents = {(x >> 1, y >> 1) for x, y in tiles}
    out.sort(key=lambda r: -r['n'])
    return out[:max_boxes]

class MapView(StencilView):
    def __init__(self, app, **kw):
        super().__init__(**kw)
        self.app = app
        self.clat, self.clon, self.zoom = 20.0, 0.0, 2.0
        self.area = None
        self.point = None
        self.draw_mode = False
        self.mem = {}
        self.disk_miss, self.pending, self.failed = set(), set(), set()
        self._q = queue.LifoQueue()
        self.gen = 0
        self._threads = 0
        self._tp = {}
        self._drawing = False
        self._a0 = None
        self._last = None
        self._pinch = None
        self.net_ok = self.net_bad = 0
        self.cov = []
        self.show_cov = False
        self._num = {}
        self._tap_start, self._tap_moved, self._multi = (0, 0), False, False
        self._trig = Clock.create_trigger(self.redraw, -1)
        self.bind(size=lambda *a: self._trig(), pos=lambda *a: self._trig())

    def update(self):
        self._trig()

    def _center_world(self):
        return lonlat_to_world(self.clon, self.clat, self.zoom)

    def to_screen(self, lat, lon):
        cx, cy = self._center_world()
        wx, wy = lonlat_to_world(lon, lat, self.zoom)
        return self.x + self.width / 2.0 + (wx - cx), self.y + self.height / 2.0 - (wy - cy)

    def from_screen(self, px, py):
        cx, cy = self._center_world()
        wx = cx + (px - (self.x + self.width / 2.0))
        wy = cy - (py - (self.y + self.height / 2.0))
        lon, lat = world_to_lonlat(wx, wy, self.zoom)
        return lat, lon

    def view_bounds(self):
        la1, lo0 = self.from_screen(self.x, self.top)
        la0, lo1 = self.from_screen(self.right, self.y)
        return norm_bounds((la0, la1, lo0, lo1))

    def set_zoom(self, z):
        self.zoom = max(1.0, min(z, float(MAX_ZOOM)))
        self.update()

    def set_center(self, lat, lon):
        self.clat = clamp(lat, -80.0, 80.0)
        self.clon = ((lon + 180.0) % 360.0) - 180.0
        self.update()

    def fit_bounds(self, b, margin=0.85):
        la0, la1, lo0, lo1 = norm_bounds(b)
        w, h = max(self.width, 50.0), max(self.height, 50.0)
        best = 1.0
        for z10 in range(10, MAX_ZOOM * 10 + 1):
            z = z10 / 10.0
            xa, ya = lonlat_to_world(lo0, la1, z)
            xb, yb = lonlat_to_world(lo1, la0, z)
            if (xb - xa) <= w * margin and (yb - ya) <= h * margin:
                best = z
            else:
                break
        self.zoom = best
        self.set_center((la0 + la1) / 2.0, (lo0 + lo1) / 2.0)

    def clear_cache(self):
        self.gen += 1
        self.mem.clear()
        self.pending.clear()
        self.disk_miss.clear()
        self.failed.clear()
        self.update()

    def _put(self, k, tex):
        if len(self.mem) > 250:
            keys_to_remove = list(self.mem.keys())[:50]
            for rk in keys_to_remove:
                self.mem.pop(rk, None)
        self.mem[k] = tex

    def _texture(self, z, x, y):
        k = (z, x, y)
        t = self.mem.get(k)
        if t is not None:
            return t
        if k not in self.disk_miss:
            p = tile_path(self.app.folder, z, x, y, self.app.layer())
            if os.path.isfile(p):
                try:
                    t = CoreImage(p).texture
                    self._put(k, t)
                    return t
                except Exception:
                    pass
            self.disk_miss.add(k)
        if self.app.online and k not in self.pending and k not in self.failed and len(self.pending) < 60:
            self.pending.add(k)
            self._q.put((self.gen, self.app.url(), k))
            if self._threads < 2:
                self._threads += 1
                threading.Thread(target=self._worker, daemon=True).start()
        return None

    def _worker(self):
        ctx = ssl_context()
        while True:
            gen, url, k = self._q.get()
            if gen != self.gen:
                continue
            z, x, y = k
            try:
                data = fetch_bytes(url.format(z=z, x=x, y=y), ctx)
            except Exception:
                data = None
            Clock.schedule_once(lambda dt, g=gen, k=k, d=data: self._got(g, k, d))

    def _got(self, gen, k, data):
        if gen != self.gen:
            return
        self.pending.discard(k)
        tex = None
        if data:
            try:
                tex = CoreImage(io.BytesIO(data), ext='jpg' if data[:2] == b'\xff\xd8' else 'png').texture
            except Exception:
                tex = None
        if tex is not None:
            self._put(k, tex)
            self.net_ok += 1
            self.net_bad = 0
        else:
            self.failed.add(k)
            self.net_bad += 1
        self.app.net_state(self.net_ok, self.net_bad)
        self.update()

    def _fallback(self, z, x, y):
        for dz in range(1, 5):
            zz = z - dz
            if zz < 0:
                return None
            t = self.mem.get((zz, x >> dz, y >> dz))
            if t is None:
                continue
            size = max(TILE >> dz, 1)
            px, py = (x % (1 << dz)) * size, (y % (1 << dz)) * size
            k = ('r', z, x, y)
            r = self.mem.get(k)
            if r is None:
                r = t.get_region(px * t.width / TILE, t.height - (py + size) * t.height / TILE,
                                 size * t.width / TILE, size * t.height / TILE)
                self._put(k, r)
            return r
        return None

    def _num_tex(self, z):
        t = self._num.get(z)
        if t is None:
            cl = CoreLabel(text=str(z), font_size=dp(14), bold=True, color=(0, 0, 0, 1))
            cl.refresh()
            t = self._num[z] = cl.texture
        return t

    def _cov_rect(self, r):
        la0, la1, lo0, lo1 = r['bounds']
        ax0, ay0 = self.to_screen(la0, lo0)
        ax1, ay1 = self.to_screen(la1, lo1)
        x, y, w, h = min(ax0, ax1), min(ay0, ay1), abs(ax1 - ax0), abs(ay1 - ay0)
        mn = dp(30)
        if w < mn:
            x, w = x - (mn - w) / 2.0, mn
        if h < mn:
            y, h = y - (mn - h) / 2.0, mn
        return x, y, w, h

    def cov_hit(self, px, py):
        best, area = None, None
        for r in self.cov:
            x, y, w, h = self._cov_rect(r)
            if x <= px <= x + w and y <= py <= y + h and (area is None or w * h < area):
                best, area = r, w * h
        return best

    def redraw(self, *_):
        self.canvas.clear()
        w, h = self.width, self.height
        if w < 2 or h < 2:
            return
        zi = int(max(0, min(round(self.zoom), MAX_ZOOM)))
        scale = 2.0 ** (self.zoom - zi)
        ts = TILE * scale
        cx, cy = self._center_world()
        f = 2.0 ** (zi - self.zoom)
        cxz, cyz = cx * f, cy * f
        hw, hh = w / 2.0 / scale, h / 2.0 / scale
        n = 1 << zi
        x0, x1 = int(math.floor((cxz - hw) / TILE)), int(math.floor((cxz + hw) / TILE))
        y0, y1 = int(math.floor((cyz - hh) / TILE)), int(math.floor((cyz + hh) / TILE))
        with self.canvas:
            Color(0.74, 0.80, 0.85, 1)
            Rectangle(pos=self.pos, size=self.size)
            for ty in range(max(y0, 0), min(y1, n - 1) + 1):
                for tx in range(x0, x1 + 1):
                    txw = tx % n
                    sx = self.x + w / 2.0 + (tx * TILE - cxz) * scale
                    sy = self.y + h / 2.0 - ((ty + 1) * TILE - cyz) * scale
                    tex = self._texture(zi, txw, ty) or self._fallback(zi, txw, ty)
                    if tex is not None:
                        Color(1, 1, 1, 1)
                        Rectangle(texture=tex, pos=(sx, sy), size=(ts, ts))
                    else:
                        Color(0.66, 0.72, 0.78, 1)
                        Line(rectangle=(sx, sy, ts, ts), width=1)
            if self.show_cov:
                for r in self.cov:
                    x, y, bw, bh = self._cov_rect(r)
                    if x > self.right or x + bw < self.x or y > self.top or y + bh < self.y:
                        continue
                    Color(YELLOW[0], YELLOW[1], YELLOW[2], 0.10)
                    Rectangle(pos=(x, y), size=(bw, bh))
                    Color(*YELLOW)
                    Line(rectangle=(x, y, bw, bh), width=dp(1.8))
                    tex = self._num_tex(r['z'])
                    tw, th = tex.size
                    cx = (max(x, self.x) + min(x + bw, self.right)) / 2.0
                    cy = (max(y, self.y) + min(y + bh, self.top)) / 2.0
                    bx, by = cx - (tw + dp(10)) / 2.0, cy - (th + dp(6)) / 2.0
                    Color(*YELLOW)
                    RoundedRectangle(pos=(bx, by), size=(tw + dp(10), th + dp(6)), radius=[dp(4)])
                    Color(1, 1, 1, 1)
                    Rectangle(texture=tex, pos=(bx + dp(5), by + dp(3)), size=(tw, th))
            if self.area:
                la0, la1, lo0, lo1 = self.area
                ax0, ay0 = self.to_screen(la0, lo0)
                ax1, ay1 = self.to_screen(la1, lo1)
                Color(0.17, 0.52, 0.96, 0.25)
                Rectangle(pos=(min(ax0, ax1), min(ay0, ay1)), size=(abs(ax1 - ax0), abs(ay1 - ay0)))
                Color(0.93, 0.55, 0.12, 1)
                Line(rectangle=(min(ax0, ax1), min(ay0, ay1), abs(ax1 - ax0), abs(ay1 - ay0)), width=dp(1.6))
            if self.point:
                px, py = self.to_screen(*self.point)
                Color(0.8, 0.1, 0.1, 1)
                Ellipse(pos=(px - dp(6), py - dp(6)), size=(dp(12), dp(12)))
                Color(1, 1, 1, 1)
                Line(circle=(px, py, dp(7)), width=1.2)
            Color(0.1, 0.1, 0.1, 0.55)
            mx, my = self.x + w / 2.0, self.y + h / 2.0
            Line(points=[mx - dp(9), my, mx + dp(9), my], width=1)
            Line(points=[mx, my - dp(9), mx, my + dp(9)], width=1)
        self.app.view_changed()

    def on_touch_down(self, t):
        if not self.collide_point(*t.pos):
            return False
        if getattr(t, 'is_mouse_scroll', False):
            self.set_zoom(self.zoom + (0.5 if t.button == 'scrolldown' else -0.5))
            return True
        t.grab(self)
        self._tp[t.uid] = t
        if len(self._tp) == 1:
            self._last = t.pos
            self._tap_start, self._tap_moved, self._multi = t.pos, False, False
            if self.draw_mode:
                self._a0 = self.from_screen(*t.pos)
                self._drawing = True
                self.area = None
        elif len(self._tp) == 2:
            self._multi = True
            a, b = list(self._tp.values())
            self._pinch = (math.hypot(a.x - b.x, a.y - b.y) or 1.0, self.zoom)
            self._drawing = False
        return True

    def on_touch_move(self, t):
        if t.grab_current is not self:
            return False
        if not self._tap_moved and math.hypot(t.pos[0] - self._tap_start[0], t.pos[1] - self._tap_start[1]) > dp(10):
            self._tap_moved = True
        if len(self._tp) >= 2 and self._pinch:
            a, b = list(self._tp.values())[:2]
            d = math.hypot(a.x - b.x, a.y - b.y) or 1.0
            self.set_zoom(self._pinch[1] + math.log(d / self._pinch[0], 2))
            return True
        if self._drawing and self._a0:
            la, lo = self.from_screen(*t.pos)
            self.area = norm_bounds((self._a0[0], la, self._a0[1], lo))
            self.update()
            return True
        if self._last is not None:
            dx, dy = t.pos[0] - self._last[0], t.pos[1] - self._last[1]
            self._last = t.pos
            cx, cy = self._center_world()
            lon, lat = world_to_lonlat(cx - dx, cy + dy, self.zoom)
            self.set_center(lat, lon)
        return True

    def on_touch_up(self, t):
        if t.grab_current is not self:
            return False
        t.ungrab(self)
        self._tp.pop(t.uid, None)
        tap = not self._tap_moved and not self._multi and not self._drawing and not self._tp
        if self._drawing and not self._tp:
            self._drawing = False
            a = self.area
            tiny = (not a) or (abs(self.to_screen(a[1], a[3])[0] - self.to_screen(a[0], a[2])[0]) < dp(8) or
                               abs(self.to_screen(a[1], a[3])[1] - self.to_screen(a[0], a[2])[1]) < dp(8))
            if tiny:
                self.area = None
            self.draw_mode = False
            self.app.area_drawn(self.area)
            self.update()
        if len(self._tp) < 2:
            self._pinch = None
        if len(self._tp) == 1:
            self._last = list(self._tp.values())[0].pos
        if not self._tp:
            self._multi = False
        if tap:
            self.app.map_tapped(t.pos)
        return True


# ============================================================
# التطبيق الرئيسي
# ============================================================
class MapDownloaderApp(App):
    title = 'Elint Map Downloader'

    def build(self):
        Window.clearcolor = BG
        try:
            Window.softinput_mode = ''
        except Exception:
            pass

        self.folder = self._default_folder()
        self.cfg = self._load_cfg()
        self.folder = self.cfg.get('folder', self.folder)
        self.online = bool(self.cfg.get('online', True))

        self.busy = False
        self.exporting = False
        self.dl = None
        self.job = None
        self._tiles = None
        self.state = ''
        self.pause_req = self.cancel_req = False
        self._wait_ev = None
        self._left = 0
        self.status_text = ''
        self._net = (0, 0)
        self._say_until, self._say_ev = 0.0, None
        self.cov_on = False
        self._cov_busy = self._cov_again = False
        self._lib_busy = False
        self.pr_open = False
        self.pages = {}

        self.is_pro = False
        self._check_license()

        root = BoxLayout(orientation='vertical')

        self.head_card = Card(orientation='vertical', size_hint_y=None, height=dp(80), bg=PANEL, edge='bottom',
                              edge_color=ACCENT, padding=(dp(14), dp(6), dp(14), dp(6)), spacing=dp(2))
        top = BoxLayout(size_hint_y=None, height=dp(20))
        top.add_widget(label('Map Downloader', bold=True, font_size='14sp'))
        self.head_page = label('Map', halign='right', color=MUTED, font_size='12sp')
        top.add_widget(self.head_page)
        self.head_card.add_widget(top)
        self.head_pos = label('', markup=True, bold=True, font_size='16sp', size_hint_y=None, height=dp(24))
        self.head_card.add_widget(self.head_pos)
        self.head = label('', markup=True, color=MUTED, font_size='12sp', size_hint_y=None, height=dp(18), shorten=True)
        self.head_card.add_widget(self.head)
        root.add_widget(self.head_card)

        self.sm = ScreenManager(transition=NoTransition())
        root.add_widget(self.sm)

        self.nav = Card(orientation='horizontal', size_hint_y=None, height=dp(62), bg=PANEL, edge='top',
                        edge_color=[1, 1, 1, 0.10], padding=(dp(6), dp(4), dp(6), dp(2)), spacing=dp(4))
        root.add_widget(self.nav)

        self.add_page('map', 'Map', 'map', self._build_map_page())
        self.add_page('download', 'Download', 'download', self._build_download_page(), on_show=self.dl_page_shown)
        self.add_page('library', 'Library', 'library', self._build_library_page(), on_show=self.lib_refresh)
        self.add_page('settings', 'Settings', 'settings', self._build_settings_page(), on_show=self.settings_load)
        self.show_page('map')
        Window.bind(size=lambda *a: Clock.schedule_once(self.apply_insets, 0.1))

        Clock.schedule_once(lambda dt: self._first_launch(), 0.6)
        return root

    # ---------------- الترخيص ----------------
    def _check_license(self):
        try:
            uid = get_device_uid()
            saved_key = self.cfg.get('license_key', '')
            if saved_key and validate_key(uid, saved_key):
                self.is_pro = True
            else:
                self.is_pro = False
        except Exception:
            self.is_pro = False

    def _first_launch(self):
        if not self.is_pro:
            self.show_activation_popup(first_launch=True)

    def _limits(self):
        if self.is_pro:
            return PRO_MAX_ZOOM, PRO_DAILY_TILES_LIMIT, PRO_DAILY_EXPORT_LIMIT
        return FREE_MAX_ZOOM, FREE_DAILY_TILES_LIMIT, FREE_DAILY_EXPORT_LIMIT

    def show_activation_popup(self, first_launch=False):
        uid = get_device_uid()
        expected_key = generate_valid_key(uid)

        box = BoxLayout(orientation='vertical', spacing=dp(8), padding=dp(12))

        title_txt = 'Welcome!' if first_launch else 'License / Activation'
        box.add_widget(label(
            f'[{title_txt}]',
            bold=True, font_size='15sp', size_hint_y=None, height=dp(24),
            halign='center', color=YELLOW
        ))

        status_txt = 'PRO ✓ Activated' if self.is_pro else 'FREE version'
        status_color = GREEN if self.is_pro else ORANGE
        box.add_widget(label(
            status_txt, bold=True, font_size='13sp', size_hint_y=None, height=dp(22),
            halign='center', color=status_color
        ))

        box.add_widget(label('Your Device UID:', color=MUTED, font_size='11sp',
                             size_hint_y=None, height=dp(16)))
        uid_row = BoxLayout(size_hint_y=None, height=dp(40), spacing=dp(6))
        uid_in = entry(uid, readonly=True)
        uid_in.font_size = '12sp'
        uid_row.add_widget(uid_in)
        uid_row.add_widget(Btn('Copy', GREY, size_hint_x=None, width=dp(74), font_size='12sp',
                               on_release=lambda *_: (Clipboard.copy(uid), self.say('UID copied'))))
        box.add_widget(uid_row)

        wa_msg = urllib.parse.quote(f"Hello, I want to activate Elint Map Downloader. UID: {uid}")
        wa_link = f"https://wa.me/213553762791?text={wa_msg}"
        box.add_widget(Btn(
            'Contact via WhatsApp (+213 553 76 27 91)',
            GREEN, size_hint_y=None, height=dp(42), font_size='12sp',
            on_release=lambda *_: webbrowser.open(wa_link)
        ))

        box.add_widget(label('Enter activation key:', color=MUTED, font_size='11sp',
                             size_hint_y=None, height=dp(16)))
        key_row = BoxLayout(size_hint_y=None, height=dp(40), spacing=dp(6))
        key_in = entry('', hint_text='ELINT-XXXXXXXXXXXX')
        key_in.font_size = '13sp'
        key_row.add_widget(key_in)
        key_row.add_widget(Btn('Paste', GREY, size_hint_x=None, width=dp(74), font_size='12sp',
                               on_release=lambda *_: setattr(key_in, 'text', Clipboard.paste())))
        box.add_widget(key_row)

        btn_row = BoxLayout(size_hint_y=None, height=dp(44), spacing=dp(8))
        holder = {}

        def verify(*_):
            entered = normalize_key(key_in.text)
            if not entered:
                return self.say('Enter a key first')
            if validate_key(uid, entered):
                self.cfg['license_key'] = entered
                self.cfg['activated'] = True
                self._save_cfg()
                self.is_pro = True
                holder['pop'].dismiss()
                self.say('✅ Pro activated — unlimited!')
                # تحديث الواجهات
                Clock.schedule_once(lambda dt: self._refresh_ui_after_activation(), 0.2)
            else:
                self.say('❌ Invalid key')

        def close(*_):
            holder['pop'].dismiss()

        if self.is_pro:
            btn_row.add_widget(Btn('Deactivate', RED, font_size='13sp',
                                   on_release=lambda *_: self._deactivate(holder)))
            btn_row.add_widget(Btn('Close', GREY, font_size='13sp', on_release=close))
        else:
            btn_row.add_widget(Btn('Close', GREY, font_size='13sp', on_release=close))
            btn_row.add_widget(Btn('Activate', GREEN, font_size='13sp', on_release=verify))
        box.add_widget(btn_row)

       

        holder['pop'] = self.popup(
            'Activation',
            box,
            dp(480 if first_launch else 470),
            auto_dismiss=not first_launch
        )

    def _deactivate(self, holder):
        self.cfg.pop('license_key', None)
        self.cfg['activated'] = False
        self._save_cfg()
        self.is_pro = False
        holder['pop'].dismiss()
        self.say('License removed — back to FREE version')
        Clock.schedule_once(lambda dt: self._refresh_ui_after_activation(), 0.2)

    def _refresh_ui_after_activation(self):
        """إعادة بناء واجهة التنزيل بعد التفعيل لتحديث الزووم"""
        try:
            max_z, _, _ = self._limits()
            zs = [str(z) for z in range(0, max_z + 1)]
            
            self.dl_s0.values = zs
            self.dl_s1.values = zs
            if int(self.dl_s0.text) > max_z:
                self.dl_s0.text = '0'
            if int(self.dl_s1.text) > max_z:
                self.dl_s1.text = str(max_z)

            # تحديث اسم القسم
            for child in self.sm.get_screen('download').children:
                if isinstance(child, ScrollView):
                    for col in child.children:
                        for section_card in col.children:
                            if hasattr(section_card, 'children') and len(section_card.children) > 0:
                                lbl = section_card.children[-1]
                                if isinstance(lbl, Label) and "ZOOM RANGE" in lbl.text:
                                    lbl.text = 'ZOOM RANGE (%s: MAX %d)' % ('PRO' if self.is_pro else 'FREE', max_z)
            
            self.dl_refresh()
            self.view_changed()
            self.say('License status updated')
        except Exception as e:
            print("Refresh UI Error:", e)

    def popup(self, title, content, height, auto_dismiss=False):
        pop = Popup(title=title, content=content, size_hint=(0.95, None), height=height,
                    auto_dismiss=auto_dismiss,
                    background='', background_color=PANEL, separator_color=ACCENT,
                    title_color=TXT, title_size='16sp', title_align='center')
        pop.open()
        return pop

    def add_page(self, key, title, icon, widget, on_show=None):
        scr = Screen(name=key)
        scr.add_widget(widget)
        self.sm.add_widget(scr)
        item = NavItem(title=title, icon=icon)
        item.bind(on_release=lambda *_: self.show_page(key))
        self.nav.add_widget(item)
        self.pages[key] = dict(item=item, title=title, on_show=on_show)

    def show_page(self, key):
        if key not in self.pages:
            return
        self.sm.current = key
        for k, p in self.pages.items():
            p['item'].active = (k == key)
        self.head_page.text = self.pages[key]['title']
        try:
            Window.release_all_keyboards()
        except Exception:
            pass
        cb = self.pages[key]['on_show']
        if cb:
            cb()

    def _system_insets(self):
        if platform != 'android':
            return 0, 0
        try:
            from jnius import autoclass
            act = autoclass('org.kivy.android.PythonActivity').mActivity
            res = act.getResources()

            def dim(name):
                i = res.getIdentifier(name, 'dimen', 'android')
                return int(res.getDimensionPixelSize(i)) if i > 0 else 0
            pt = autoclass('android.graphics.Point')()
            act.getWindowManager().getDefaultDisplay().getRealSize(pt)
            if Window.height >= pt.y - 2:
                return dim('status_bar_height'), dim('navigation_bar_height')
        except Exception:
            pass
        return 0, 0

    def apply_insets(self, *_):
        top, bot = self._system_insets()
        try:
            bot += dp(float(self.cfg.get('extra_bottom', 0)))
        except (TypeError, ValueError):
            pass
        self.head_card.height = dp(80) + top
        self.head_card.padding = (dp(14), top + dp(6), dp(14), dp(6))
        self.nav.height = dp(62) + bot
        self.nav.padding = (dp(6), dp(4), dp(6), bot + dp(2))

    def _build_map_page(self):
        holder = RelativeLayout()
        self.holder = holder
        self.map = MapView(self, size_hint=(1, 1), pos_hint={'x': 0, 'y': 0}, pos=(0, 0))
        holder.add_widget(self.map)

        zoom = BoxLayout(orientation='vertical', size_hint=(None, None), size=(dp(44), dp(6 * 44 + 5 * 8)),
                         pos_hint={'right': 0.975, 'top': 0.985}, spacing=dp(8))
        self.b_layer = Btn(LAYER_LABEL.get(self.cfg.get('source', 'Google Maps'), 'Map'), GLASS, radius=dp(10),
                           font_size='11sp', on_release=lambda *_: self.next_layer())
        zoom.add_widget(self.b_layer)
        self.b_cov = Btn('Saved', GLASS, radius=dp(10), font_size='11sp', on_release=lambda *_: self.toggle_cov())
        zoom.add_widget(self.b_cov)
        zoom.add_widget(Btn('+', GLASS, radius=dp(10), font_size='24sp',
                            on_release=lambda *_: self.map.set_zoom(self.map.zoom + 1)))
        zoom.add_widget(Btn('-', GLASS, radius=dp(10), font_size='24sp',
                            on_release=lambda *_: self.map.set_zoom(self.map.zoom - 1)))
        zoom.add_widget(Btn('Fit', GLASS, radius=dp(10), font_size='12sp',
                            on_release=lambda *_: self.fit_area()))
        zoom.add_widget(Btn('World', GLASS, radius=dp(10), font_size='10sp',
                            on_release=lambda *_: self.go_world()))
        holder.add_widget(zoom)

        sbar = BoxLayout(size_hint=(0.70, None), height=dp(40), pos_hint={'x': 0.02, 'top': 0.985}, spacing=dp(6))
        self.search_in = entry('', hint_text='Search...', text_validate_unfocus=True)
        self.search_in.bind(on_text_validate=lambda *_: self.do_search())
        sbar.add_widget(self.search_in)
        sbar.add_widget(Btn('Go', ACCENT, size_hint_x=None, width=dp(50), on_release=lambda *_: self.do_search()))
        holder.add_widget(sbar)

        self.chips = Panel(orientation='horizontal', size_hint=(0.96, None), height=dp(52),
                           pos_hint={'center_x': 0.5, 'y': 0.015}, bg=GLASS, radius=dp(18),
                           padding=dp(6), spacing=dp(6))
        self.b_draw = Btn('Draw box', ACCENT, font_size='12sp', radius=dp(13),
                          on_release=lambda *_: self.toggle_draw())
        self.b_pr = Btn('Point + Range', ACCENT, font_size='12sp', radius=dp(13),
                        on_release=lambda *_: self.point_panel())
        self.chips.add_widget(self.b_draw)
        self.chips.add_widget(self.b_pr)
        self.chips.add_widget(Btn('Visible', ACCENT, font_size='12sp', radius=dp(13),
                                  on_release=lambda *_: self.use_view()))
        holder.add_widget(self.chips)

        self.pr_box = Panel(orientation='vertical', size_hint=(1, None), height=dp(126),
                            pos_hint={'x': 0, 'y': 0}, bg=PANEL, edge='top',
                            padding=(dp(10), dp(8)), spacing=dp(6))
        lrow = BoxLayout(size_hint_y=None, height=dp(14), spacing=dp(6))
        erow = BoxLayout(size_hint_y=None, height=dp(40), spacing=dp(6))
        self.pr_lat, self.pr_lon, self.pr_rng = entry(''), entry(''), entry(self.cfg.get('range_km', 50))
        for t, e in (('Latitude', self.pr_lat), ('Longitude', self.pr_lon), ('Range (km)', self.pr_rng)):
            lrow.add_widget(label(t, color=MUTED, font_size='11sp'))
            erow.add_widget(e)
        brow = BoxLayout(size_hint_y=None, height=dp(38), spacing=dp(6))
        brow.add_widget(Btn('Map center', GREY, font_size='13sp', on_release=lambda *_: self.pr_center()))
        brow.add_widget(Btn('Close', GREY, font_size='13sp', on_release=lambda *_: self.close_pr()))
        brow.add_widget(Btn('Apply', GREEN, font_size='13sp', on_release=lambda *_: self.apply_pr()))
        for w in (lrow, erow, brow):
            self.pr_box.add_widget(w)

        self.bar_box = Panel(size_hint=(1, None), height=dp(62), pos_hint={'x': 0, 'y': 0},
                             bg=PANEL, edge='top', padding=(dp(10), dp(9)), spacing=dp(8))
        self.bar = TileProgress()
        self.bar_box.add_widget(self.bar)
        self.pause_btn = Btn('Pause', GREY, size_hint_x=None, width=dp(78), font_size='13sp',
                             on_release=lambda *_: self.toggle_pause())
        self.bar_box.add_widget(self.pause_btn)
        self.cancel_btn = Btn('Cancel', RED, size_hint_x=None, width=dp(78), font_size='13sp',
                              on_release=lambda *_: self.cancel_download())
        self.bar_box.add_widget(self.cancel_btn)
        return holder

    def _default_folder(self):
        if platform == 'android':
            for base in ('/storage/emulated/0/Documents/Elint', os.path.join(self.user_data_dir, 'Elint')):
                try:
                    os.makedirs(base, exist_ok=True)
                    if os.access(base, os.W_OK):
                        return base
                except Exception:
                    pass
        try:
            return os.path.dirname(os.path.abspath(__file__))
        except NameError:
            return os.path.expanduser('~')

    def _cfg_path(self):
        return os.path.join(self.folder, '.map_downloader_config.json')

    def _load_cfg(self):
        cfg = dict(
            source='Google Maps', custom_url='', folder=self.folder,
            max_tiles=5000, batch_delay=10, online=True,
            last_active_date='', daily_tiles_used=0, daily_exports_used=0,
            license_key='', activated=False,
        )
        path = self._cfg_path()
        try:
            if os.path.exists(path):
                with open(path, 'r', encoding='utf-8') as f:
                    cfg.update(json.load(f))
        except Exception:
            pass

        today = time.strftime('%Y-%m-%d')
        if cfg.get('last_active_date') != today:
            cfg['last_active_date'] = today
            cfg['daily_tiles_used'] = 0
            cfg['daily_exports_used'] = 0
            self._save_cfg_dict(cfg)

        if cfg.get('source') not in SOURCES:
            cfg['source'] = 'Google Maps'
        return cfg

    def _save_cfg(self):
        self._save_cfg_dict(self.cfg)

    def _save_cfg_dict(self, cfg_dict):
        try:
            path = self._cfg_path()
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, 'w', encoding='utf-8') as f:
                json.dump(cfg_dict, f)
        except Exception:
            pass

    def layer(self):
        return layer_dir(self.cfg['source'])

    def tiles_dir(self):
        return os.path.join(self.folder, self.layer()[0])

    def next_layer(self):
        if self.busy:
            return self.say('Wait for download to finish')
        src = self.cfg['source']
        self.cfg['source'] = LAYERS[(LAYERS.index(src) + 1) % len(LAYERS)] if src in LAYERS else LAYERS[0]
        self._save_cfg()
        self.b_layer.text = LAYER_LABEL[self.cfg['source']]
        self.map.clear_cache()
        if self.cov_on:
            self.refresh_coverage()
        self.say('Map type: %s' % self.cfg['source'])

    def url(self):
        u = SOURCES.get(self.cfg['source'], '') if self.cfg['source'] != 'Custom URL' else self.cfg['custom_url']
        return u or SOURCES['Google Maps']

    def on_start(self):
        if platform == 'android':
            self.ask_permissions()
        Clock.schedule_once(lambda dt: self.initial_view(), 0.3)
        Clock.schedule_once(self.apply_insets, 0.2)
        Clock.schedule_once(self.apply_insets, 1.2)

    def initial_view(self):
        b = folder_tile_bounds(self.folder, self.layer())
        if b:
            self.map.fit_bounds(b)
            self.say('Showing saved maps in %s' % self.tiles_dir())
        else:
            self.map.zoom = 2.0
            self.map.set_center(20.0, 10.0)
            self.say('No saved tiles yet - online preview.')
        self.map.update()
        self.load_job()

    _files_asked = False

    def ask_permissions(self):
        try:
            from android.permissions import Permission, request_permissions
            request_permissions([Permission.READ_EXTERNAL_STORAGE, Permission.WRITE_EXTERNAL_STORAGE],
                                lambda p, r: Clock.schedule_once(self._ask_all_files, 0.5))
        except Exception:
            pass
        Clock.schedule_once(self._ask_all_files, 6.0)

    def _ask_all_files(self, *_):
        if self._files_asked:
            return
        self._files_asked = True
        try:
            from jnius import autoclass
            if autoclass('android.os.Build$VERSION').SDK_INT < 30:
                return
            if autoclass('android.os.Environment').isExternalStorageManager():
                return
            act = autoclass('org.kivy.android.PythonActivity').mActivity
            Intent, Settings, Uri = (autoclass('android.content.Intent'),
                                     autoclass('android.provider.Settings'),
                                     autoclass('android.net.Uri'))
            it = Intent(Settings.ACTION_MANAGE_APP_ALL_FILES_ACCESS_PERMISSION)
            it.setData(Uri.parse('package:' + act.getPackageName()))
            act.startActivity(it)
        except Exception:
            pass

    def say(self, text):
        self.status_text = text
        self._say_until = time.time() + 5.0
        if self._say_ev is not None:
            self._say_ev.cancel()
        self._say_ev = Clock.schedule_once(lambda dt: self.view_changed(), 5.1)
        self.view_changed()

    def net_state(self, ok, bad):
        self._net = (ok, bad)
        if self.online and ok == 0 and bad >= 6:
            self.status_text = 'No internet connection'
        self.view_changed()

    def view_changed(self):
        m = self.map
        if m.point:
            self.head_pos.text = '[color=#f59424]Point[/color]  %.5f, %.5f' % (m.point[0], m.point[1])
        else:
            self.head_pos.text = '%.4f, %.4f' % (m.clat, m.clon)
        line2 = ''
        if self.busy or time.time() <= self._say_until:
            line2 = self.status_text
        if (m.area and not self.busy and time.time() > self._say_until and not line2.startswith('No internet')):
            line2 = 'Area: ' + fmt_area(m.area)
        zoom_text = 'zoom %.1f' % m.zoom
        pro_tag = '  [color=#23a86b][b]PRO[/b][/color]' if self.is_pro else ''
        if line2:
            self.head.text = '[b]%s[/b]%s    |    %s' % (zoom_text, pro_tag, escape_markup(line2))
        else:
            self.head.text = '[b]%s[/b]%s' % (zoom_text, pro_tag)

    def toggle_draw(self):
        m = self.map
        m.draw_mode = not m.draw_mode
        self.b_draw.bg = ORANGE if m.draw_mode else ACCENT
        self.say('Drag on map to draw box' if m.draw_mode else 'Box drawing off')

    def area_drawn(self, area):
        self.b_draw.bg = ACCENT
        if area:
            self.map.point = None
            self.say('Box set. Open Download tab.')
        else:
            self.say('Box too small')

    def use_view(self):
        self.map.point = None
        self.map.area = self.map.view_bounds()
        self.map.update()
        self.say('Visible area selected.')

    def fit_area(self):
        if self.map.area:
            self.map.fit_bounds(self.map.area)

    def go_world(self):
        self.map.zoom = 2.0
        self.map.set_center(20.0, 10.0)

    def set_point(self, lat, lon):
        m = self.map
        m.point = (lat, lon)
        if self.pr_open:
            self.pr_lat.text, self.pr_lon.text = '%.5f' % lat, '%.5f' % lon
        m.update()
        self.view_changed()

    def map_tapped(self, pos):
        m = self.map
        lat, lon = m.from_screen(*pos)
        self.set_point(lat, ((lon + 180.0) % 360.0) - 180.0)
        if self.cov_on:
            r = m.cov_hit(*pos)
            if r:
                self.region_dialog(r)

    def point_panel(self):
        if self.pr_open:
            return self.close_pr()
        if self.busy:
            return self.say('Download running')
        m = self.map
        p = m.point or (m.clat, m.clon)
        self.pr_lat.text, self.pr_lon.text = '%.5f' % p[0], '%.5f' % p[1]
        self.pr_rng.text = '%g' % float(self.cfg.get('range_km', 50))
        self.holder.add_widget(self.pr_box)
        self.pr_open = True
        self.b_pr.bg = ORANGE
        self.say('Tap map to fill coordinates, then Apply')

    def close_pr(self):
        if self.pr_open:
            self.holder.remove_widget(self.pr_box)
            self.pr_open = False
            self.b_pr.bg = ACCENT

    def pr_center(self):
        self.set_point(self.map.clat, self.map.clon)

    def apply_pr(self):
        m = self.map
        try:
            try:
                lat, lon = parse_num(self.pr_lat.text, 'Latitude'), parse_num(self.pr_lon.text, 'Longitude')
            except ValueError:
                c = parse_coords(self.pr_lat.text + ' ' + self.pr_lon.text)
                if c is None:
                    raise ValueError('Invalid coordinates')
                lat, lon = c
            rng = parse_num(self.pr_rng.text, 'Range')
            if not (-90 <= lat <= 90 and -180 <= lon <= 180):
                raise ValueError('Latitude must be -90..90')
            if rng <= 0:
                raise ValueError('Range must be > 0')
        except ValueError as ex:
            return self.say(str(ex))
        self.cfg['range_km'] = rng
        self._save_cfg()
        self.close_pr()
        m.point = (lat, lon)
        m.area = point_range_bounds(lat, lon, rng)
        m.fit_bounds(m.area)
        self.say('Point + range set.')

    def do_search(self):
        q = self.search_in.text.strip()
        if not q:
            return
        self.search_in.focus = False
        self.map.focus = True
        Window.release_all_keyboards()
        c = parse_coords(q)
        if c:
            return self.go_to(c[0], c[1])
        self.say('Searching "%s" ...' % q)
        threading.Thread(target=self._geocode_work, args=(q,), daemon=True).start()

    def _geocode_work(self, q):
        try:
            res, err = geocode(q, ssl_context()), ''
        except Exception as ex:
            res, err = [], str(ex) or ex.__class__.__name__
        Clock.schedule_once(lambda dt: self._search_done(q, res, err))

    def _search_done(self, q, res, err):
        if err:
            return self.say('Search failed: %s' % err)
        if not res:
            return self.say('Nothing found')
        if len(res) == 1:
            return self.go_to(res[0]['lat'], res[0]['lon'], res[0]['bbox'])
        box = BoxLayout(orientation='vertical', spacing=dp(6), padding=dp(8))
        holder = {}

        def pick(r):
            holder['pop'].dismiss()
            self.go_to(r['lat'], r['lon'], r['bbox'])

        for r in res:
            b = Btn(r['name'], GREY, size_hint_y=None, height=dp(48), font_size='12sp',
                    halign='left', valign='middle', shorten=True, shorten_from='right',
                    on_release=lambda w, r=r: pick(r))
            b.bind(size=lambda w, sz: setattr(w, 'text_size', (sz[0] - dp(16), sz[1])))
            box.add_widget(b)
        box.add_widget(Btn('Cancel', GREEN, size_hint_y=None, height=dp(44),
                           on_release=lambda *_: holder['pop'].dismiss()))
        holder['pop'] = self.popup('Choose place', box, dp(110 + 54 * len(res)))

    def go_to(self, lat, lon, bbox=None):
        m = self.map
        self.set_point(lat, lon)
        if bbox:
            m.fit_bounds(bbox, margin=0.9)
            if m.zoom > 17:
                m.set_zoom(17)
        else:
            m.zoom = max(max(m.zoom, 13.0), 1.0)
            m.set_center(lat, lon)
        self.say('Point %.5f, %.5f' % (lat, lon))

    def toggle_cov(self):
        self.cov_on = not self.cov_on
        self.map.show_cov = self.cov_on
        self.b_cov.bg = YELLOW if self.cov_on else GLASS
        self.b_cov.color = (0, 0, 0, 1) if self.cov_on else (1, 1, 1, 1)
        if self.cov_on:
            self.say('Scanning saved tiles ...')
            self.refresh_coverage()
        else:
            self.say('Boxes hidden')
            self.map.update()

    def refresh_coverage(self):
        if self._cov_busy:
            self._cov_again = True
            return
        self._cov_busy, self._cov_again = True, False
        folder, layer = self.folder, self.layer()

        def work():
            try:
                res = scan_coverage(folder, layer)
            except Exception:
                res = []
            Clock.schedule_once(lambda dt: self._cov_done(res, folder, layer))
        threading.Thread(target=work, daemon=True).start()

    def _cov_done(self, res, folder, layer):
        self._cov_busy = False
        if self._cov_again or folder != self.folder or layer != self.layer():
            return self.refresh_coverage()
        self.map.cov = res
        self.map.update()
        if self.cov_on and not self.busy:
            self.say('%d saved area(s)' % len(res) if res else 'No saved tiles')

    def region_dialog(self, r):
        z, a = r['z'], r['bounds']
        if self.busy or z >= MAX_ZOOM:
            return self.export_dialog(r)
        limit = int(self.cfg['max_tiles'])
        max_z, _, _ = self._limits()
        box = BoxLayout(orientation='vertical', spacing=dp(6), padding=dp(8))
        box.add_widget(label('Saved up to zoom %d  (%s tiles)' % (z, format(r['n'], ',')),
                             size_hint_y=None, height=dp(24), bold=True))
        box.add_widget(label(fmt_area(a), size_hint_y=None, height=dp(34), color=MUTED, font_size='11sp'))

        zoom_values = [str(i) for i in range(z + 1, min(MAX_ZOOM, max_z) + 1)]
        if not zoom_values:
            zoom_values = [str(z)]

        grid = GridLayout(cols=2, size_hint_y=None, height=dp(46), spacing=dp(6), row_default_height=dp(40))
        s1 = RoundSpinner(text=str(min(best_max_zoom(a, z + 1, limit, max_z), max_z)), values=zoom_values)
        grid.add_widget(label('Download up to zoom (max %d)' % max_z))
        grid.add_widget(s1)
        box.add_widget(grid)
        info = label('', size_hint_y=None, height=dp(52))
        box.add_widget(info)
        row = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(8))
        start = Btn('Download', GREEN)
        holder = {}

        def refresh(*_):
            n = count_tiles(a, z + 1, int(s1.text))
            info.text = 'zoom %d..%s: %s tiles (~%.1f MB)' % (z + 1, s1.text, format(n, ','), n * EST_KB / 1024.0)

        def select(*_):
            holder['pop'].dismiss()
            self.map.point = None
            self.map.area = a
            self.map.update()
            self.say('Saved area selected.')

        def go(*_):
            holder['pop'].dismiss()
            self.start_download(a, z + 1, int(s1.text))

        def to_export(*_):
            holder['pop'].dismiss()
            self.export_dialog(r)

        s1.bind(text=refresh)
        start.bind(on_release=go)
        row.add_widget(Btn('Cancel', GREY, on_release=lambda *_: holder['pop'].dismiss()))
        row.add_widget(Btn('Use box', GREY, font_size='12sp', on_release=select))
        row.add_widget(Btn('Export', GREY, font_size='12sp', on_release=to_export))
        row.add_widget(start)
        box.add_widget(row)
        refresh()
        holder['pop'] = self.popup('Saved area - zoom %d' % z, box, dp(320))

    def export_dialog(self, r):
        if self.exporting:
            return self.say('Export already running')

        _, _, max_exports = self._limits()
        if not self.is_pro and self.cfg.get('daily_exports_used', 0) >= max_exports:
            return self.popup('Limit Reached',
                              label('Daily export limit reached (1 per day).\nUpgrade to Pro for unlimited exports.',
                                    halign='center'), dp(150))

        z, a = r['z'], r['bounds']
        folder, layer = self.folder, self.layer()
        max_z, _, _ = self._limits()
        zdef = max([i for i in range(1, min(z, max_z) + 1) if export_fits(a, i)] or [1])
        box = BoxLayout(orientation='vertical', spacing=dp(6), padding=dp(8))
        box.add_widget(label('Saved up to zoom %d' % z, size_hint_y=None, height=dp(24), bold=True))
        box.add_widget(label(fmt_area(a), size_hint_y=None, height=dp(34), color=MUTED, font_size='11sp'))

        grid_fmt = GridLayout(cols=2, size_hint_y=None, height=dp(46), spacing=dp(6), row_default_height=dp(40))
        sp_fmt = RoundSpinner(text='GeoTIFF', values=['GeoTIFF', 'MBTiles'])
        grid_fmt.add_widget(label('Export Format'))
        grid_fmt.add_widget(sp_fmt)
        box.add_widget(grid_fmt)

        zoom_values = [str(i) for i in range(1, min(z, max_z) + 1)]
        if not zoom_values:
            zoom_values = ['1']

        grid = GridLayout(cols=2, size_hint_y=None, height=dp(46), spacing=dp(6), row_default_height=dp(40))
        sp = RoundSpinner(text=str(min(zdef, max_z)), values=zoom_values)
        grid.add_widget(label('Export at zoom (max %d)' % max_z))
        grid.add_widget(sp)
        box.add_widget(grid)
        info = label('', size_hint_y=None, height=dp(70), font_size='12sp')
        box.add_widget(info)
        row = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(8))
        go_btn = Btn('Export', GREEN)
        holder = {}

        def refresh(*_):
            ez = int(sp.text)
            fmt = sp_fmt.text
            if fmt == 'GeoTIFF':
                w, h, raw = export_geometry(a, ez)[4:7]
                ok = export_fits(a, ez)
                info.color = TXT if ok else RED
                info.text = ('%d x %d px (~%.0f MB)\nGeoTIFF + MapInfo .tab' % (w, h, raw / 1048576.0)
                             if ok else 'Too large')
                go_btn.disabled = not ok
            else:
                info.color = TXT
                info.text = 'MBTiles Database (SQLite)'
                go_btn.disabled = False

        def go(*_):
            holder['pop'].dismiss()
            self.cfg['daily_exports_used'] = self.cfg.get('daily_exports_used', 0) + 1
            self._save_cfg()
            if sp_fmt.text == 'GeoTIFF':
                self.start_export(a, int(sp.text), folder, layer)
            else:
                self.start_mbtiles_export(a, int(sp.text), folder, layer)

        sp.bind(text=refresh)
        sp_fmt.bind(text=refresh)
        go_btn.bind(on_release=go)
        row.add_widget(Btn('Cancel', GREY, on_release=lambda *_: holder['pop'].dismiss()))
        row.add_widget(go_btn)
        box.add_widget(row)
        refresh()
        holder['pop'] = self.popup('Export Map Data', box, dp(330))

    def start_export(self, a, ez, folder, layer):
        self.exporting = True
        out = os.path.join(folder, 'export', '%s_z%d_%s.tif' % (layer[0], ez, time.strftime('%Y%m%d_%H%M%S')))
        state = {'cancel': False}
        box = BoxLayout(orientation='vertical', spacing=dp(8), padding=dp(10))
        info = label('Preparing ...', size_hint_y=None, height=dp(40), halign='center')
        bar = ProgressBar(max=100, value=0, size_hint_y=None, height=dp(14))
        box.add_widget(info)
        box.add_widget(bar)
        holder = {}

        def cancel(*_):
            state['cancel'] = True
            info.text = 'Cancelling ...'
        box.add_widget(Btn('Cancel', RED, size_hint_y=None, height=dp(44), on_release=cancel))
        holder['pop'] = self.popup('Exporting GeoTIFF', box, dp(210))

        def show(d, t):
            bar.value = 100.0 * d / max(t, 1)
            if not state['cancel']:
                info.text = 'Stitching tiles %d / %d' % (d, t)

        def prog(d, t):
            Clock.schedule_once(lambda dt: show(d, t))

        def finished(res, err):
            self.exporting = False
            holder['pop'].dismiss()
            if err:
                return self.export_result('Export failed', err, dp(200))
            if res is None:
                return self.say('Export cancelled')
            w, h, miss = res
            self.export_result('GeoTIFF Saved', '%s\n(%d x %d px)' % (out, w, h), dp(250))

        def work():
            res = err = None
            try:
                res = write_geotiff(out, folder, layer, a, ez, progress=prog, cancelled=lambda: state['cancel'])
            except Exception as ex:
                err = str(ex) or ex.__class__.__name__
            Clock.schedule_once(lambda dt: finished(res, err))
        threading.Thread(target=work, daemon=True).start()

    def start_mbtiles_export(self, a, ez, folder, layer):
        self.exporting = True
        out = os.path.join(folder, 'export', '%s_z%d_%s.mbtiles' % (layer[0], ez, time.strftime('%Y%m%d_%H%M%S')))
        state = {'cancel': False}
        box = BoxLayout(orientation='vertical', spacing=dp(8), padding=dp(10))
        info = label('Creating MBTiles ...', size_hint_y=None, height=dp(40), halign='center')
        bar = ProgressBar(max=100, value=0, size_hint_y=None, height=dp(14))
        box.add_widget(info)
        box.add_widget(bar)
        holder = {}

        def cancel(*_):
            state['cancel'] = True
            info.text = 'Cancelling ...'
        box.add_widget(Btn('Cancel', RED, size_hint_y=None, height=dp(44), on_release=cancel))
        holder['pop'] = self.popup('Exporting MBTiles', box, dp(210))

        def show(d, t):
            bar.value = 100.0 * d / max(t, 1)
            if not state['cancel']:
                info.text = 'Packaging tiles %d / %d' % (d, t)

        def prog(d, t):
            Clock.schedule_once(lambda dt: show(d, t))

        def finished(res, err):
            self.exporting = False
            holder['pop'].dismiss()
            if err:
                return self.export_result('Export failed', err, dp(200))
            if res is None:
                return self.say('Export cancelled')
            total, miss = res
            self.export_result('MBTiles Saved', '%s\n(%d tiles packaged)' % (out, total), dp(250))

        def work():
            res = err = None
            try:
                # تم إصلاح الخطأ هنا: تمرير ez مرتين (لـ z0 و z1)
                res = write_mbtiles(out, folder, layer, a, ez, ez, progress=prog, cancelled=lambda: state['cancel'])
            except Exception as ex:
                err = str(ex) or ex.__class__.__name__
            Clock.schedule_once(lambda dt: finished(res, err))
        threading.Thread(target=work, daemon=True).start()

    def export_result(self, title, text, height):
        box = BoxLayout(orientation='vertical', spacing=dp(8), padding=dp(8))
        box.add_widget(label(text, halign='center'))
        holder = {}
        box.add_widget(Btn('OK', GREEN, size_hint_y=None, height=dp(44),
                           on_release=lambda *_: holder['pop'].dismiss()))
        holder['pop'] = self.popup(title, box, height)

    def _build_settings_page(self):
        sv, col = scroll_col()
        s = section('Map source')
        self.st_src = RoundSpinner(text=self.cfg.get('source', 'Google Maps'), values=list(SOURCES))
        s.add_widget(form_row('Tile source', self.st_src))
        self.st_url = entry('')
        s.add_widget(form_row('Custom URL', self.st_url))
        col.add_widget(s)

        s = section('Storage')
        self.st_folder = entry('')
        s.add_widget(form_row('Save folder', self.st_folder))
        col.add_widget(s)

        s = section('Download')
        self.st_max = entry('')
        self.st_delay = entry('')
        s.add_widget(form_row('Max tiles / batch', self.st_max))
        s.add_widget(form_row('Pause between batches (s)', self.st_delay))
        col.add_widget(s)

        s = section('Display')
        self.st_online = Switch(active=self.online, size_hint_x=None, width=dp(90))
        s.add_widget(form_row('Online preview', self.st_online))
        self.st_extra = entry('')
        s.add_widget(form_row('Extra bottom margin (dp)', self.st_extra))
        col.add_widget(s)

        col.add_widget(Btn('Save settings', GREEN, size_hint_y=None, height=dp(48),
                           on_release=lambda *_: self.settings_save()))

        s = section('License')
        self.st_license = label('', size_hint_y=None, height=dp(26), bold=True)
        s.add_widget(self.st_license)
        s.add_widget(Btn('Manage License', ORANGE, size_hint_y=None, height=dp(42),
                         on_release=lambda *_: self.show_activation_popup()))
        col.add_widget(s)
        col.add_widget(Widget(size_hint_y=None, height=dp(8)))

        self.settings_load()
        return sv

    def settings_load(self):
        c = self.cfg
        self.st_src.text = c.get('source', 'Google Maps')
        self.st_url.text = c.get('custom_url', '')
        self.st_folder.text = c.get('folder', self.folder)
        self.st_max.text = str(c.get('max_tiles', 5000))
        self.st_delay.text = str(c.get('batch_delay', 10))
        self.st_online.active = bool(c.get('online', True))
        self.st_extra.text = '%g' % float(c.get('extra_bottom', 0))
        if hasattr(self, 'st_license'):
            if self.is_pro:
                self.st_license.text = 'Status: [b][color=#23a86b]PRO ✓[/color][/b]'
            else:
                self.st_license.text = 'Status: [b][color=#f59424]FREE[/color][/b]'
            self.st_license.markup = True

    def settings_save(self):
        try:
            mx = int(parse_num(self.st_max.text, 'Max tiles'))
            if mx < 1:
                raise ValueError('Max tiles must be >= 1')
            dly = int(parse_num(self.st_delay.text, 'Pause'))
            if dly < 0:
                raise ValueError('Pause must be >= 0')
            extra = parse_num(self.st_extra.text or '0', 'Bottom margin')
            if not (0 <= extra <= 120):
                raise ValueError('Margin must be 0..120')
        except ValueError as ex:
            return self.say(str(ex))
        src_name = self.st_src.text
        folder = self.st_folder.text.strip() or self._default_folder()
        try:
            os.makedirs(os.path.join(folder, layer_dir(src_name)[0]), exist_ok=True)
        except Exception as ex:
            return self.say('Folder error: %s' % ex)
        self.cfg.update(source=src_name, custom_url=self.st_url.text.strip(), folder=folder, max_tiles=mx,
                        batch_delay=dly, online=bool(self.st_online.active), extra_bottom=extra)
        self._save_cfg()
        self.folder, self.online = folder, bool(self.st_online.active)
        self.b_layer.text = LAYER_LABEL.get(src_name, 'Map')
        self.map.clear_cache()
        if self.cov_on:
            self.refresh_coverage()
        self.apply_insets()
        try:
            Window.release_all_keyboards()
        except Exception:
            pass
        self.say('Settings saved.')

    def _build_download_page(self):
        sv, col = scroll_col()
        s = section('Selected area')
        self.dl_area = label('', size_hint_y=None, height=dp(52))
        s.add_widget(self.dl_area)
        s.add_widget(Btn('Show on map', GREY, size_hint_y=None, height=dp(38), font_size='13sp',
                         on_release=lambda *_: (self.show_page('map'), self.fit_area())))
        col.add_widget(s)

        max_z, _, _ = self._limits()
        zs = [str(z) for z in range(0, max_z + 1)]
        s = section('Zoom range (%s: max %d)' % ('PRO' if self.is_pro else 'Free', max_z))
        self.dl_s0 = RoundSpinner(text='0', values=zs)
        self.dl_s1 = RoundSpinner(text='10', values=zs)
        s.add_widget(form_row('Min zoom', self.dl_s0))
        s.add_widget(form_row('Max zoom', self.dl_s1))
        self.dl_info = label('', size_hint_y=None, height=dp(56))
        s.add_widget(self.dl_info)
        col.add_widget(s)

        s = section('Destination')
        self.dl_folder = label('', color=MUTED, font_size='12sp', size_hint_y=None, height=dp(40))
        s.add_widget(self.dl_folder)
        col.add_widget(s)

        self.dl_start = Btn('Start download', GREEN, size_hint_y=None, height=dp(50),
                            on_release=lambda *_: self.dl_start_clicked())
        col.add_widget(self.dl_start)
        col.add_widget(Widget(size_hint_y=None, height=dp(8)))
        self.dl_s0.bind(text=self.dl_refresh)
        self.dl_s1.bind(text=self.dl_refresh)
        return sv

    def dl_page_shown(self):
        a = self.map.area
        self.dl_folder.text = 'Folder: %s' % self.tiles_dir()
        max_z, _, _ = self._limits()
        if a and a != getattr(self, '_dl_seen', None):
            self._dl_seen = a
            self.dl_s0.text = '0'
            self.dl_s1.text = str(best_max_zoom(a, 0, int(self.cfg['max_tiles']), max_z))
        self.dl_refresh()

    _dl_seen = None

    def dl_refresh(self, *_):
        a, ok = self.map.area, False
        max_z, max_tiles, _ = self._limits()
        self.dl_info.color = TXT
        if self.busy:
            self.dl_area.text = 'Download running or paused.'
            self.dl_info.text = ''
        elif not a:
            self.dl_area.text = 'No area selected.'
            self.dl_info.text = ''
        else:
            self.dl_area.text = fmt_area(a)
            try:
                z0, z1 = int(self.dl_s0.text), int(self.dl_s1.text)
            except ValueError:
                z0 = z1 = 0
            if z1 < z0 or z1 > max_z:
                self.dl_info.text, self.dl_info.color = 'Zoom must be 0..%d' % max_z, RED
            else:
                n = count_tiles(a, z0, z1)
                daily_used = self.cfg.get('daily_tiles_used', 0)
                remaining = max_tiles - daily_used

                if n > remaining:
                    self.dl_info.text, self.dl_info.color = (
                        'Daily limit exceeded (%s/%s tiles left)' % (format(remaining, ','), format(max_tiles, ',')),
                        RED
                    )
                else:
                    self.dl_info.text = '%s tiles (~%.1f MB)\nDaily limit left: %s tiles' % (
                        format(n, ','), n * EST_KB / 1024.0, format(remaining, ',')
                    )
                    ok = True
        self.dl_start.disabled = not ok

    def dl_start_clicked(self):
        a = self.map.area
        if self.busy or not a:
            return
        max_z, max_tiles, _ = self._limits()
        try:
            z0, z1 = int(self.dl_s0.text), int(self.dl_s1.text)
        except ValueError:
            return
        if z1 < z0 or z1 > max_z:
            return

        n = count_tiles(a, z0, z1)
        daily_used = self.cfg.get('daily_tiles_used', 0)
        if daily_used + n > max_tiles:
            return self.popup('Limit Reached',
                              label('Area exceeds the daily limit (%s tiles).' % format(max_tiles, ','),
                                    halign='center'), dp(150))

        self.cfg['daily_tiles_used'] = daily_used + n
        self._save_cfg()
        self.start_download(a, z0, z1)

    def _build_library_page(self):
        page = BoxLayout(orientation='vertical')
        bar = BoxLayout(size_hint_y=None, height=dp(52), padding=(dp(14), dp(8)), spacing=dp(8))
        self.lib_title = label('Saved areas', bold=True, font_size='15sp')
        bar.add_widget(self.lib_title)
        bar.add_widget(Btn('Rescan', GREY, size_hint_x=None, width=dp(84), font_size='13sp',
                           on_release=lambda *_: self.lib_refresh()))
        page.add_widget(bar)
        sv, self.lib_col = scroll_col()
        page.add_widget(sv)
        return page

    def lib_refresh(self):
        if self._lib_busy:
            return
        self._lib_busy = True
        self.lib_title.text = 'Scanning saved tiles ...'
        folder, layer = self.folder, self.layer()

        def work():
            try:
                res = scan_coverage(folder, layer)
            except Exception:
                res = []
            Clock.schedule_once(lambda dt: self._lib_done(res))
        threading.Thread(target=work, daemon=True).start()

    def _lib_done(self, res):
        self._lib_busy = False
        self.lib_col.clear_widgets()
        self.lib_title.text = 'Saved areas - %s  (%d)' % (LAYER_LABEL.get(self.cfg['source'], 'Map'), len(res))
        if not res:
            self.lib_col.add_widget(label('Nothing saved yet', halign='center',
                                          color=MUTED, size_hint_y=None, height=dp(80)))
            return
        for r in res[:80]:
            self.lib_col.add_widget(self._lib_row(r))

    def _lib_row(self, r):
        z, a = r['z'], r['bounds']
        row = Card(orientation='horizontal', size_hint_y=None, height=dp(76), bg=PANEL, radius=dp(14),
                   padding=dp(10), spacing=dp(8))
        badge = Card(bg=YELLOW, radius=dp(10), size_hint=(None, 1), width=dp(50))
        badge.add_widget(Label(text='z%d' % z, bold=True, color=(0, 0, 0, 1), font_size='15sp'))
        row.add_widget(badge)
        row.add_widget(label('%s tiles\nlat %.2f..%.2f' % (format(r['n'], ','), a[0], a[1]), font_size='11sp'))
        row.add_widget(Btn('Show', GREY, size_hint_x=None, width=dp(58), font_size='12sp',
                           on_release=lambda *_, r=r: self.lib_show(r)))
        row.add_widget(Btn('More', ACCENT, size_hint_x=None, width=dp(58), font_size='12sp',
                           on_release=lambda *_, r=r: self.region_dialog(r)))
        return row

    def lib_show(self, r):
        self.show_page('map')
        self.map.fit_bounds(r['bounds'])
        if not self.cov_on:
            self.toggle_cov()

    def _job_path(self):
        return os.path.join(self.folder, '.map_job.json')

    def _save_job(self):
        try:
            os.makedirs(self.folder, exist_ok=True)
            with open(self._job_path(), 'w', encoding='utf-8') as f:
                json.dump(self.job, f)
        except Exception:
            pass

    def _clear_job(self):
        self._stop_wait()
        self.job, self._tiles, self.state, self.busy = None, None, '', False
        self.pause_req = self.cancel_req = False
        self._show_bar(False)
        try:
            os.remove(self._job_path())
        except OSError:
            pass

    def _show_bar(self, on):
        if on and self.bar_box.parent is None:
            self.holder.add_widget(self.bar_box)
        elif not on and self.bar_box.parent is not None:
            self.holder.remove_widget(self.bar_box)

    def _refresh_map(self):
        m = self.map
        m.disk_miss.clear()
        m.failed.clear()
        m.mem.clear()
        m.update()
        if self.cov_on:
            self.refresh_coverage()

    def _job_status(self, extra=''):
        j = self.job
        if not j:
            return
        head = 'Batch %d/%d' % (min(j['next'] + 1, j['nb']), j['nb'])
        if self.state == 'running':
            self.say('Downloading... %s' % head)
        elif self.state == 'waiting':
            self.say('Batch done - next in %ds' % self._left)
        elif self.state == 'paused':
            self.say(extra or 'Paused - %s. Press Resume' % head)

    def start_download(self, area, z0, z1):
        total = count_tiles(area, z0, z1)
        B = max(1, int(self.cfg.get('max_tiles', 5000)))
        try:
            os.makedirs(self.tiles_dir(), exist_ok=True)
        except Exception as ex:
            return self.say('Cannot write: %s' % ex)
        self.job = dict(area=list(area), z0=z0, z1=z1, url=self.url(), folder=self.folder, batch=B,
                        layer=list(self.layer()), delay=int(self.cfg.get('batch_delay', 10)), total=total,
                        nb=int(math.ceil(total / float(B))), next=0, ok=0, fail=0)
        self._tiles = None
        self.close_pr()
        self.busy = True
        self._save_job()
        self.bar.max, self.bar.value = max(total, 1), 0
        self._show_bar(True)
        self.show_page('map')
        self._run_batch()

    def load_job(self):
        try:
            path = self._job_path()
            if os.path.exists(path):
                with open(path, 'r', encoding='utf-8') as f:
                    j = json.load(f)
                if j['next'] < j['nb']:
                    self.job, self._tiles, self.busy = j, None, True
                    self.map.point = None
                    self.map.area = tuple(j['area'])
                    self.bar.max, self.bar.value = max(j['total'], 1), min(j['next'] * j['batch'], j['total'])
                    self._show_bar(True)
                    self._set_paused()
                    self.map.fit_bounds(self.map.area)
        except Exception:
            pass

    def _run_batch(self):
        j = self.job
        if not j or j['next'] >= j['nb']:
            return self._job_finished()
        if self._tiles is None:
            self._tiles = list_tiles(tuple(j['area']), j['z0'], j['z1'])
        B, i = j['batch'], j['next']
        chunk = self._tiles[i * B:(i + 1) * B]
        self.state, self.pause_req, self.cancel_req = 'running', False, False
        self.pause_btn.text, self.pause_btn.bg = 'Pause', GREY
        self.bar.value = i * B
        self.dl = dl = TileDownloader(j['folder'], j['url'], layer=j.get('layer', ['tiles', 'png']))
        self._job_status()
        last = [0.0]

        def prog(k, n):
            now = time.time()
            if k == n or now - last[0] >= 0.1:
                last[0] = now
                Clock.schedule_once(lambda dt: self._progress(i * B + k))

        def work():
            try:
                res = dl.run(chunk, prog)
            except Exception:
                res = dict(ok=0, skipped=0, fail=0, aborted='error', total=len(chunk), err=traceback.format_exc())
            Clock.schedule_once(lambda dt: self._batch_done(res, i))
        threading.Thread(target=work, daemon=True).start()

    def _progress(self, done):
        if self.state != 'running' or not self.job:
            return
        self.bar.value = done
        self._job_status('%s / %s' % (format(done, ','), format(self.job['total'], ',')))

    def _batch_done(self, res, i):
        j = self.job
        if not j or j['next'] != i:
            return
        j['ok'] += res['ok']
        j['fail'] += res['fail']
        self._refresh_map()
        if res['aborted'] == 'error':
            self._save_job()
            return self._set_paused('Error encountered.')
        if res['aborted'] == 'blocked':
            self._save_job()
            return self._set_paused('Server blocked (403/429). Paused.')
        if res['aborted'] == 'network':
            self._save_job()
            return self._set_paused('Network error. Paused.')
        if res['aborted'] == 'cancelled':
            if self.cancel_req:
                return self._job_cancelled()
            self._save_job()
            return self._set_paused()
        j['next'] = i + 1
        self._save_job()
        self.bar.value = min(j['next'] * j['batch'], j['total'])
        if j['next'] >= j['nb']:
            return self._job_finished()
        if self.cancel_req:
            return self._job_cancelled()
        if self.pause_req:
            return self._set_paused()
        self._wait(j['delay'])

    def _wait(self, secs):
        self.state, self._left = 'waiting', int(secs)
        self.pause_btn.text, self.pause_btn.bg = 'Pause', GREY
        self._job_status()
        if self._left <= 0:
            return self._run_batch()
        self._stop_wait()
        self._wait_ev = Clock.schedule_interval(self._tick, 1.0)

    def _tick(self, dt):
        self._left -= 1
        if self._left <= 0:
            self._stop_wait()
            self._run_batch()
            return False
        self._job_status()

    def _stop_wait(self):
        if self._wait_ev is not None:
            self._wait_ev.cancel()
            self._wait_ev = None

    def _set_paused(self, msg=''):
        self._stop_wait()
        self.state = 'paused'
        self.pause_btn.text, self.pause_btn.bg = 'Resume', GREEN
        self._job_status(msg)

    def toggle_pause(self):
        if not self.job:
            return
        if self.state == 'running':
            self.pause_req = True
            self.pause_btn.text = '...'
            if self.dl:
                self.dl.cancel.set()
            self.say('Pausing...')
        elif self.state == 'waiting':
            self._set_paused()
        elif self.state == 'paused':
            self._run_batch()

    def cancel_download(self):
        if not self.job:
            return
        if self.state == 'running':
            self.cancel_req = True
            if self.dl:
                self.dl.cancel.set()
        else:
            self._job_cancelled()

    def _job_cancelled(self):
        saved = self.job['ok'] if self.job else 0
        self._clear_job()
        self.say('Cancelled. Saved: %s tiles' % format(saved, ','))
        self._refresh_map()

    def _job_finished(self):
        j = self.job
        msg = 'Done! %s new tiles saved.' % format(j['ok'], ',')
        self._clear_job()
        self.say(msg)
        self._refresh_map()

# ============================================================
# مولّد المفاتيح (للمطور فقط)
# ============================================================
def _cli_keygen():
    if len(sys.argv) >= 3 and sys.argv[1] == '--keygen':
        uid = sys.argv[2]
        print(f"UID : {uid}")
        print(f"KEY : {generate_valid_key(uid)}")
        return True
    return False

if __name__ == '__main__':
    if _cli_keygen():
        sys.exit(0)
    try:
        MapDownloaderApp().run()
    except Exception:
        traceback.print_exc()
        raise