#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ربات چت ناشناس تلگرام — نسخه Python برای Railway
=================================================
- زبان: Python 3.11+ | کتابخانه: python-telegram-bot >= 22.7 (پشتیبانی رسمی style دکمه‌ها / Bot API 9.4)
- ذخیره‌سازی: فایل‌های JSON ساختاریافته روی Railway Volume در مسیر DATA_DIR (پیش‌فرض /data) — بدون هیچ SQL
- اجرا: Long Polling دائمی با دستور «python bot.py»
- منطقه زمانی: Asia/Tehran + تاریخ شمسی (jdatetime یا fallback داخلی بدون وابستگی)
- رابط کاربری: کاملاً فارسی و راست‌چین

متغیرهای محیطی:
  BOT_TOKEN  (الزامی) توکن ربات
  OWNER_ID   (الزامی) شناسه عددی تلگرام مالک
  DATA_DIR   (اختیاری) مسیر ذخیره‌سازی پایدار — پیش‌فرض /data
"""

import os
import re
import json
import copy
import shutil
import random
import hashlib
import logging
import threading
import asyncio
import fcntl
import time as _time
import unicodedata
from logging.handlers import RotatingFileHandler
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo

# تاریخ شمسی: در محیط‌هایی که «jdatetime» نصب نیست (مثل برخی دیپلوی‌های Railway که
# requirements ناقص دارند) ربات با تبدیل شمسی داخلی استاندارد بالا می‌آید — کرش نمی‌کند.
try:
    import jdatetime
except ModuleNotFoundError:
    jdatetime = None

from telegram import (
    Update, InlineKeyboardButton, InlineKeyboardMarkup,
    KeyboardButton, ReplyKeyboardMarkup, BotCommand,
)
from telegram.constants import ParseMode
from telegram.error import TelegramError, BadRequest, Forbidden, RetryAfter, TimedOut
from telegram.ext import (
    Application, ApplicationHandlerStop, CommandHandler, MessageHandler,
    CallbackQueryHandler, ContextTypes, TypeHandler, filters,
)

# ============================================================
# 1) پیکربندی و ثابت‌ها
# ============================================================

TEHRAN = ZoneInfo("Asia/Tehran")
UTC = timezone.utc
SCHEMA_VERSION = 1
PROFANITY_VERSION = "2.0"
BOT_VERSION = "2.4.0"
PAGE_SIZE = 8

DATA_DIR = os.environ.get("DATA_DIR", "/data").rstrip("/") or "/data"
OWNER_ID = int(os.environ.get("OWNER_ID", "0") or 0)
BOT_TOKEN_ENV = os.environ.get("BOT_TOKEN", "")

RETENTION_HOURS_DEFAULT = 72          # نگهداری پیام کاربران عادی (ساعت)
MAX_BACKUP_UPLOAD_BYTES = 400 * 1024 * 1024
MESSAGE_PREVIEW_LEN = 60

# ============================================================
# 2) لاگ‌گذاری (بدون اطلاعات محرمانه)
# ============================================================

LOG = logging.getLogger("anonbot")
LOG.setLevel(logging.INFO)
_LOG_FMT = logging.Formatter("%(asctime)s | %(levelname)s | %(name)s | %(message)s")
_ch = logging.StreamHandler()
_ch.setFormatter(_LOG_FMT)
LOG.addHandler(_ch)

LOG_DIR = os.path.join(DATA_DIR, "logs")
try:
    os.makedirs(LOG_DIR, exist_ok=True)
    os.makedirs(DATA_DIR, exist_ok=True)
except OSError as _e:
    LOG.error("ایجاد مسیر ذخیره‌سازی «%s» ناموفق بود (%s)؛ init_storage بعداً با خطای واضح متوقف می‌شود.",
              DATA_DIR, _e)
try:
    _fh = RotatingFileHandler(os.path.join(LOG_DIR, "bot.log"), maxBytes=5 * 1024 * 1024,
                              backupCount=3, encoding="utf-8")
    _fh.setFormatter(_LOG_FMT)
    LOG.addHandler(_fh)
except OSError as _e:  # اگر Volume در دسترس نیست، حداقل در کنسول می‌نویسیم
    LOG.error("قابل نوشتن نبود مسیر لاگ: %s", _e)

logging.getLogger("httpx").setLevel(logging.WARNING)
logging.getLogger("telegram").setLevel(logging.WARNING)

def log_exc(msg: str, *args):
    LOG.exception(msg, *args)

# ============================================================
# 3) ابزارهای زمان (UTC در ذخیره‌سازی، Tehran + شمسی در نمایش)
# ============================================================

def now_utc() -> datetime:
    return datetime.now(UTC)

def now_teh() -> datetime:
    return datetime.now(TEHRAN)

def iso_utc(dt: datetime) -> str:
    return dt.astimezone(UTC).isoformat()

def parse_iso(s: str) -> datetime:
    return datetime.fromisoformat(s)

def to_tehran(dt_utc: datetime) -> datetime:
    return dt_utc.astimezone(TEHRAN)

_FA_DIGITS = str.maketrans("0123456789", "۰۱۲۳۴۵۶۷۸۹")
_EN_DIGITS = str.maketrans("۰۱۲۳۴۵۶۷۸۹", "0123456789")

def fa_num(s) -> str:
    return str(s).translate(_FA_DIGITS)

def en_num(s: str) -> str:
    return str(s).translate(_EN_DIGITS)


def _gregorian_to_jalali(gy: int, gm: int, gd: int) -> tuple:
    """تبدیل میلادی به جلالی با الگوریتم استاندارد ۳۳ساله (بدون وابستگی خارجی).
    بازه معتبر: سال‌های میلادی ۱۹۰۰ تا ۲۱۰۰ (کافی برای ربات)."""
    g_d_m = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
    if gy > 1600:
        jy = 979
        gy -= 1600
    else:
        jy = 0
        gy -= 621
    gy2 = gy + 1 if gm > 2 else gy
    days = (365 * gy) + ((gy2 + 3) // 4) - ((gy2 + 99) // 100) \
        + ((gy2 + 399) // 400) - 80 + gd + g_d_m[gm - 1]
    jy += 33 * (days // 12053)
    days %= 12053
    jy += 4 * (days // 1461)
    days %= 1461
    if days > 365:
        jy += (days - 1) // 365
        days = (days - 1) % 365
    if days < 186:
        jm = 1 + (days // 31)
        jd = 1 + (days % 31)
    else:
        jm = 7 + ((days - 186) // 30)
        jd = 1 + ((days - 186) % 30)
    return jy, jm, jd


def _jdate_parts(dt: datetime) -> tuple:
    """(سال، ماه، روز، هفته) جلالی — jdatetime اگر نصب باشد، وگرنه fallback داخلی.
    هفته: ۰=شنبه ... ۶=جمعه (همان قرارداد jdatetime)."""
    d = dt.date() if isinstance(dt, datetime) else dt
    if jdatetime is not None:
        try:
            jd = jdatetime.date.fromgregorian(date=d)
            return jd.year, jd.month, jd.day, jd.weekday()
        except Exception:
            pass
    jy, jm, jd = _gregorian_to_jalali(d.year, d.month, d.day)
    return jy, jm, jd, (d.weekday() + 2) % 7


def jalali(dt_utc: datetime, with_time: bool = True) -> str:
    """تبدیل UTC به تاریخ شمسی + ساعت تهران."""
    if dt_utc is None:
        return "—"
    try:
        teh = dt_utc.astimezone(TEHRAN)
        jy, jm, jd = _jdate_parts(teh)[:3]
        s = f"{jy}/{jm:02d}/{jd:02d}"
        if with_time:
            s += f" - {teh.hour:02d}:{teh.minute:02d}"
        return fa_num(s)
    except Exception:
        return "—"

def te_hm() -> str:
    t = now_teh()
    return f"{t.hour:02d}:{t.minute:02d}"

def te_date_key() -> str:
    t = now_teh()
    return f"{t.year:04d}{t.month:02d}{t.day:02d}"

def weekday_teh() -> int:
    """0=شنبه ... 6=جمعه بر اساس تقویم جلالی."""
    return _jdate_parts(now_teh())[3]

WEEKDAY_LABELS = ["شنبه", "یکشنبه", "دوشنبه", "سه‌شنبه", "چهارشنبه", "پنج‌شنبه", "جمعه"]

def in_active_window(hours_list, weekdays) -> bool:
    """آیا الان داخل بازه‌های فعالیت تعریف‌شده هستیم؟ (منطقه تهران)"""
    if weekdays:
        if weekday_teh() not in weekdays:
            return False
    if not hours_list:
        return True
    t = now_teh()
    cur = t.hour * 60 + t.minute
    for item in hours_list:
        try:
            a, b = str(item).split("-")
            sh, sm = a.strip().split(":")
            eh, em = b.strip().split(":")
            start = int(sh) * 60 + int(sm)
            end = int(eh) * 60 + int(em)
        except Exception:
            continue
        if start <= end:
            if start <= cur <= end:
                return True
        else:  # بازه شب‌هنگام که از نیمه‌شب می‌گذرد
            if cur >= start or cur <= end:
                return True
    return False

def valid_hhmm(s: str) -> bool:
    m = re.fullmatch(r"([01]?\d|2[0-3]):([0-5]\d)", en_num(str(s)).strip())
    return bool(m)

def norm_hhmm(s: str) -> str:
    h, m = en_num(str(s)).strip().split(":")
    return f"{int(h):02d}:{int(m):02d}"

def valid_interval(s: str) -> bool:
    try:
        a, b = en_num(str(s)).strip().split("-")
        return valid_hhmm(a.strip()) and valid_hhmm(b.strip())
    except Exception:
        return False

# ============================================================
# 4) لایه ذخیره‌سازی JSON امن (Atomic Replace + بازیابی از نسخه سالم)
# ============================================================

def _atomic_write(path: str, payload: str):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(payload)
        f.flush()
        os.fsync(f.fileno())
    json.loads(payload)  # اعتبارسنجی JSON پیش از جایگزینی
    os.replace(tmp, path)
    try:
        d = os.path.dirname(path)
        dfd = os.open(d, os.O_RDONLY)
        try:
            os.fsync(dfd)
        finally:
            os.close(dfd)
    except OSError:
        pass

class SafeFile:
    """یک فایل JSON با قفل، نوشتن اتمیک و نسخه پشتیبان .bak برای بازیابی."""

    def __init__(self, path: str, default):
        self.path = path
        self.bak_path = path + ".bak"
        self.default = default
        self.lock = threading.RLock()
        self.data = self._load()

    def _load(self):
        recovered = False
        for p in (self.path, self.bak_path):
            if os.path.exists(p):
                try:
                    with open(p, "r", encoding="utf-8") as f:
                        d = json.load(f)
                    if not isinstance(d, type(self.default)):
                        raise ValueError("type mismatch")
                    if p == self.bak_path:
                        recovered = True
                        LOG.warning("فایل اصلی خراب بود؛ بازیابی از نسخه سالم: %s", os.path.basename(self.path))
                    return d
                except Exception as e:
                    LOG.error("خطا در خواندن %s: %s", os.path.basename(p), e)
        if recovered is False and os.path.exists(self.path):
            LOG.error("فایل %s قابل بازیابی نبود؛ با مقدار پیش‌فرض ادامه می‌دهیم", self.path)
        return copy.deepcopy(self.default)

    def save(self, data):
        with self.lock:
            _atomic_write(self.path, json.dumps(data, ensure_ascii=False, separators=(",", ":")))
            self.data = data
            try:
                if os.path.exists(self.path):
                    shutil.copy2(self.path, self.bak_path)
            except OSError:
                pass

    def reload(self):
        self.data = self._load()


class Store:
    """مدیر فایل‌های JSON + قفل سراسری تراکنش‌های چندفایلی.
    کلیدهای منطقی بدون پسوند هستند (مثلاً «users») و روی دیسک به «users.json» نوشته می‌شوند."""

    def __init__(self, root: str):
        self.root = root
        os.makedirs(root, exist_ok=True)
        for sub in ("backups", "tmp", "messages", "logs"):
            os.makedirs(os.path.join(root, sub), exist_ok=True)
        self.glock = threading.RLock()
        self.files = {}
        for name, default in FILE_DEFAULTS.items():
            bare = name[:-5] if name.endswith(".json") else name
            self.files[bare] = SafeFile(os.path.join(root, bare + ".json"), default)

    def get(self, name: str):
        with self.glock:
            return copy.deepcopy(self.files[name].data)

    def update(self, name: str, mutator):
        """خواندن-اصلاح-نوشتن اتمیک. mutator(data) -> data جدید."""
        with self.glock:
            f = self.files[name]
            with f.lock:
                new = mutator(copy.deepcopy(f.data))
                f.save(new)
                return copy.deepcopy(new)

    def mutate(self, name: str, mutator):
        """مثل update اما روی خودِ شیء کش‌شده (برای داده‌های بزرگ)."""
        with self.glock:
            f = self.files[name]
            with f.lock:
                mutator(f.data)
                f.save(f.data)
                return f.data

    def reload_all(self):
        with self.glock:
            for f in self.files.values():
                f.reload()

    def snapshot_files(self) -> dict:
        """محتوای همه فایل‌ها برای بکاپ (کلیدها: نام کامل فایل با پسوند .json)."""
        with self.glock:
            out = {}
            for name, f in self.files.items():
                out[name + ".json"] = copy.deepcopy(f.data)
            return out


class MsgStore:
    """پیام‌های هر مکالمه در فایل جداگانه: messages/conv-<id>.json"""

    CONV_RE = re.compile(r"^[A-Za-z0-9_-]{1,64}$")

    def __init__(self, root: str):
        self.dir = os.path.join(root, "messages")
        os.makedirs(self.dir, exist_ok=True)
        self.glock = threading.RLock()
        self.cache = {}

    def _path(self, conv_id: str) -> str:
        if not self.CONV_RE.match(str(conv_id)):
            raise ValueError("شناسه مکالمه نامعتبر است")
        return os.path.join(self.dir, f"conv-{conv_id}.json")

    def _sf(self, conv_id: str) -> SafeFile:
        with self.glock:
            if conv_id not in self.cache:
                self.cache[conv_id] = SafeFile(self._path(conv_id), {"schema": 1, "messages": []})
            return self.cache[conv_id]

    def get(self, conv_id: str):
        with self.glock:
            return copy.deepcopy(self._sf(conv_id).data)

    def update(self, conv_id: str, mutator):
        with self.glock:
            sf = self._sf(conv_id)
            with sf.lock:
                new = mutator(copy.deepcopy(sf.data))
                sf.save(new)
                return copy.deepcopy(new)

    def mutate(self, conv_id: str, mutator):
        with self.glock:
            sf = self._sf(conv_id)
            with sf.lock:
                mutator(sf.data)
                sf.save(sf.data)
                return sf.data

    def list_convs(self):
        with self.glock:
            out = []
            for fn in os.listdir(self.dir):
                m = re.match(r"^conv-([A-Za-z0-9_-]{1,64})\.json$", fn)
                if m:
                    out.append(m.group(1))
            return sorted(out)

    def drop(self, conv_id: str):
        with self.glock:
            sf = self.cache.pop(conv_id, None)
            try:
                if os.path.exists(self._path(conv_id)):
                    os.remove(self._path(conv_id))
                if os.path.exists(self._path(conv_id) + ".bak"):
                    os.remove(self._path(conv_id) + ".bak")
            except OSError as e:
                LOG.error("حذف فایل پیام‌های %s ناموفق: %s", conv_id, e)

    def snapshot_messages(self) -> dict:
        with self.glock:
            out = {}
            for cid in self.list_convs():
                out["messages/conv-" + cid + ".json"] = copy.deepcopy(self._sf(cid).data)
            return out

    def replace_all(self, files: dict, keep_missing: bool = False):
        """بازیابی: نوشتن همه فایل‌های پیام از بکاپ؛ حذف فایل‌هایی که در بکاپ نیستند."""
        with self.glock:
            wanted = {}
            for key, data in files.items():
                m = re.match(r"^messages/conv-([A-Za-z0-9_-]{1,64})\.json$", key)
                if not m:
                    continue
                cid = m.group(1)
                wanted[cid] = data
                path = self._path(cid)
                _atomic_write(path, json.dumps(data, ensure_ascii=False, separators=(",", ":")))
                try:
                    shutil.copy2(path, path + ".bak")
                except OSError:
                    pass
                sf = self.cache.get(cid)
                if sf is None:
                    sf = SafeFile(path, {"schema": 1, "messages": []})
                    self.cache[cid] = sf
                else:
                    sf.data = data
            if not keep_missing:
                for cid in self.list_convs():
                    if cid not in wanted:
                        self.drop(cid)


STORE: Store = None
MSGS: MsgStore = None

def init_storage(root: str = None):
    """راه‌اندازی لایه ذخیره‌سازی؛ اگر مسیر در دسترس نباشد با خطای واضح متوقف می‌شویم."""
    global STORE, MSGS
    root = root or DATA_DIR
    test_path = os.path.join(root, ".write_test")
    try:
        os.makedirs(root, exist_ok=True)
        with open(test_path, "w", encoding="utf-8") as f:
            f.write("ok")
        os.remove(test_path)
    except OSError as e:
        LOG.critical("مسیر ذخیره‌سازی «%s» قابل نوشتن نیست (%s). ربات برای جلوگیری از کار ناامن متوقف می‌شود.", root, e)
        raise SystemExit(2)
    STORE = Store(root)
    MSGS = MsgStore(root)
    LOG.info("ذخیره‌سازی آماده است: %s", root)
    return STORE


def ensure_storage():
    if STORE is None or MSGS is None:
        raise RuntimeError("لایه ذخیره‌سازی مقداردهی نشده است (init_storage فراخوانی نشده).")


# متن پیش‌فرض هشدار لینک برای دریافت‌کننده (قابل ویرایش از پنل ← مدیریت فرمت‌ها)
LINK_WARNING_DEFAULT = (
    "🔗 <b>لینک دریافت شد</b>\n\n"
    "این پیام حاوی لینک است و ممکن است ناامن یا آلوده باشد.\n"
    "قبل از باز کردن آن حتماً مراقب باشید:\n"
    "• روی لینک‌های ناشناس کلیک نکنید\n"
    "• اطلاعات شخصی و رمز خود را در هیچ سایتی وارد نکنید\n"
    "• در صورت تکرار، می‌توانید کاربر را بلاک یا گزارش کنید"
)


DEFAULT_SETTINGS = {
    "bot_enabled": True,
    "maintenance": False,
    "warning_cap": 3,
    "profanity_enabled": True,
    "profanity_action": "warn",          # warn | mute | ban | perm
    "punishment_minutes": 60,
    "profanity_hours": [],               # مثال: ["22:00-06:00"] — خالی = همیشه فعال
    "profanity_weekdays": [0, 1, 2, 3, 4, 5, 6],
    "queue_timeout_minutes": 30,
    "request_timeout_minutes": 10,
    "rate_limit_per_minute": 20,
    "retention_hours": RETENTION_HOURS_DEFAULT,
    "backup_interval_hours": 24,
    "backup_keep": 30,
    "auto_backup_enabled": False,   # بکاپ خودکار پیش‌فرض خاموش است (پرهیز از مصرف حجم دیسک)
    "allow_unknown_files": False,
    "link_warning_enabled": True,          # هشدار لینک برای دریافت‌کننده
    "link_warning_text": LINK_WARNING_DEFAULT,
    "sched_on": {"enabled": False, "time": "08:00"},
    "sched_off": {"enabled": False, "time": "02:00"},
    "sched_last_fired": {},
    "owner_name": "پشتیبانی",
    "owner_bio": "",
    "last_auto_backup": None,
}

FORMAT_KEYS = [
    "photo", "gif", "video", "voice", "audio", "sticker", "video_note",
    "pdf", "zip", "rar", "apk", "exe", "contact", "location", "web_link",
    "forward", "phone", "tg_id", "bot_id", "invite_link",
]

FORMAT_LABELS = {
    "photo": "عکس", "gif": "GIF", "video": "ویدئو", "voice": "ویس",
    "audio": "فایل صوتی", "sticker": "استیکر", "video_note": "ویدئوی گرد",
    "pdf": "PDF", "zip": "ZIP", "rar": "RAR", "apk": "APK",
    "exe": "فایل اجرایی", "contact": "مخاطب تلگرام", "location": "موقعیت مکانی",
    "web_link": "لینک وب", "forward": "پیام فورواردشده", "phone": "شماره تلفن",
    "tg_id": "شناسه عددی تلگرام", "bot_id": "شناسه اختصاصی ربات",
    "invite_link": "لینک دعوت گروه و کانال",
}

_DEFAULT_FORMATS = {k: True for k in FORMAT_KEYS}
_DEFAULT_FORMATS["exe"] = False
_DEFAULT_FORMATS["apk"] = False

# ============================================================
# 4.5) سیستم محافظت هوشمند کاربران — تنظیمات پیش‌فرض
# ============================================================

DEFAULT_PROTECTION = {
    "enabled": True,
    "level_enabled": {"1": True, "2": True, "3": True},   # روشن بودن هر سطح تخلف
    "mute_minutes": {"1": 17, "2": 43, "3": 50},          # سکوت پیش‌فرض هر سطح
    "stage_ban_hours": {"1": 6, "2": 24, "3": 72, "4": 120, "5": 168},
    "stage_super_minutes": {"1": 5, "2": 120, "3": 6000, "4": 28800, "5": 86400},
    "girl_block_enabled": True,
    "girl_block_stage4_hours": 168,    # ۰ = دائمی
    "girl_block_stage5_hours": 0,      # ۰ = دائمی
    "escalation_threshold": 1,         # هر چند تخلف سطح ۳ یک مرحله ارتقا
    "appeal_mode": "manual",           # manual | auto_approve | auto_reject
}


FILE_DEFAULTS = {
    "users": {},    "settings": dict(DEFAULT_SETTINGS, formats=dict(_DEFAULT_FORMATS)),
    "button_styles": {"styles": {}, "texts": {}, "disabled": [], "layouts": {}, "draft": None},
    "conversations": {},
    "blocks": {"by": {}, "entries": []},
    "reports": [],
    "warnings": [],
    "bans": [],
    "friend_requests": [],
    "tickets": [],
    "support_messages": [],
    "relationships": {},
    "processed_updates": {},
    "audit": [],
    "moderation_logs": [],
    "backup_history": [],
    "mandatory_channels": {"enabled": False, "channels": []},
    "profanity_words": {"custom_blocked": [], "custom_whitelist": [], "removed_defaults": []},
    "protection": dict(DEFAULT_PROTECTION),
    "violations": [],
    "scheduled_tasks": [],
    "broadcast_jobs": [],
    "commands": [],
    "owner_code": {},
}

# ============================================================
# 5) رجیستری دکمه‌ها — متن/رنگ/چیدمان/فعال بودن (مدیریت کامل از پنل)
#    متن و رنگ کاملاً مستقل‌اند؛ رنگ فقط با استایل رسمی Bot API 9.4
#    (primary آبی | success سبز | danger قرمز | بدون استایل خاکستری پیش‌فرض)
# ============================================================

VALID_STYLES = ["", "primary", "success", "danger"]
STYLE_LABELS = {"primary": "آبی (primary)", "success": "سبز (success)",
                "danger": "قرمز (danger)", "": "پیش‌فرض خاکستری"}

# key: (متن پیش‌فرض بدون ایموجی تزئینی, استایل پیش‌فرض, نوع, قابل جابه‌جایی)
# kind: reply=کیبورد معمولی | inline=دکمه اینلاین
STYLE_KEYS = {
    "menu_chat":   ("شروع چت ناشناس", "primary", "reply", True),
    "menu_info":   ("اطلاعات من", "success", "reply", True),
    "menu_guide":  ("دستورات", "", "reply", True),
    "conv_next":   ("چت بعدی", "primary", "reply", True),
    "conv_block":  ("بلاک", "danger", "reply", True),
    "conv_end":    ("پایان مکالمه", "", "reply", True),
    "btn_confirm": ("تأیید و ادامه", "success", "inline", False),
    "btn_reject":  ("رد کردن", "danger", "inline", False),
    "btn_back":    ("بازگشت", "", "inline", False),
    "btn_cancel":  ("لغو", "", "inline", False),
    "btn_next":    ("ادامه", "primary", "inline", False),
    "btn_appeal":  ("ثبت اعتراض", "success", "inline", False),   # دکمه سبز اعتراض
}

# چیدمان پیش‌فرض کیبوردهای Reply (هر ردیف = فهرست کلیدها)
LAYOUT_DEFAULTS = {
    "main_menu": [["menu_chat"], ["menu_info"], ["menu_guide"]],
    "conv": [["conv_next", "conv_block"], ["conv_end"]],
}

# سازگاری با تست‌ها و کدهای قدیمی
DEFAULT_BUTTON_STYLES = {k: v[1] for k, v in STYLE_KEYS.items()}


def kb_allowed_keys(kb_name: str) -> set:
    """کلیدهای مجاز هر کیبورد — منوی اصلی فقط menu_*، کیبورد چت فقط conv_*.
    ریشه‌گیری پیش‌نمایش اشتباه: دکمه‌های «چت بعدی/بلاک» نباید در منوی اصلی ظاهر شوند."""
    if kb_name == "main_menu":
        return {k for k in STYLE_KEYS if k.startswith("menu_")}
    if kb_name == "conv":
        return {k for k in STYLE_KEYS if k.startswith("conv_")}
    return set(STYLE_KEYS)


def _new_button_config() -> dict:
    return {"styles": {}, "texts": {}, "disabled": [], "layouts": {}, "draft": None}


def get_button_config() -> dict:
    """پیکربندی کامل دکمه‌ها با مهاجرت خودکار از فرمت قدیمی (فقط استایل)."""
    if STORE is None:
        return _new_button_config()
    raw = STORE.get("button_styles")
    if raw is None or not isinstance(raw, dict):
        return _new_button_config()
    if raw.get("styles") is None and raw.get("texts") is None:
        # فرمت قدیمی: {key: style} → مهاجرت به ساختار جدید بدون از دست دادن داده
        old_styles = {k: v for k, v in raw.items()
                      if k in STYLE_KEYS and v in VALID_STYLES}
        migrated = _new_button_config()
        migrated["styles"] = old_styles
        STORE.update("button_styles", lambda d: migrated)
        return migrated
    cfg = _new_button_config()
    cfg["styles"] = {k: v for k, v in (raw.get("styles") or {}).items()
                     if k in STYLE_KEYS and v in VALID_STYLES}
    cfg["texts"] = {k: v for k, v in (raw.get("texts") or {}).items()
                    if k in STYLE_KEYS and isinstance(v, str) and v.strip()}
    cfg["disabled"] = [k for k in (raw.get("disabled") or []) if k in STYLE_KEYS]
    cfg["layouts"] = {k: v for k, v in (raw.get("layouts") or {}).items()
                      if k in LAYOUT_DEFAULTS and isinstance(v, list)}
    cfg["draft"] = raw.get("draft")
    return cfg


def get_styles() -> dict:
    if STORE is None:
        return {}
    return get_button_config()["styles"]

def style_of(key: str) -> str:
    """استایل رنگی دکمه. اولویت: استایل ذخیره‌شده پنل (حتی "" صریح برای
    اجبار خاکستری) → استایل پیش‌فرض STYLE_KEYS."""
    if key not in STYLE_KEYS:
        return ""
    saved = get_styles().get(key)
    return saved if saved is not None else STYLE_KEYS[key][1]

def text_of(key: str) -> str:
    """متن نمایشی دکمه: متن سفارشی مالک یا متن پیش‌فرض (بدون ایموجی)."""
    if key not in STYLE_KEYS:
        return ""
    cfg = get_button_config()
    custom = cfg["texts"].get(key)
    if custom:
        return custom
    return STYLE_KEYS[key][0]

def is_enabled(key: str) -> bool:
    if key not in STYLE_KEYS:
        return True
    return key not in get_button_config()["disabled"]

def style_label(s: str) -> str:
    return STYLE_LABELS.get(s, "پیش‌فرض خاکستری")

def set_style(key: str, style: str) -> bool:
    if key not in STYLE_KEYS or style not in VALID_STYLES:
        return False
    cfg = get_button_config()  # مهاجرت/ساخت صحیح ساختار پیش از هر تغییر
    cfg["styles"][key] = style
    STORE.update("button_styles", lambda d: cfg)
    return True

def set_text(key: str, text: str) -> bool:
    if key not in STYLE_KEYS:
        return False
    text = (text or "").strip()
    if not text or len(text) > 40 or has_decorative_emoji(text):
        return False
    cfg = get_button_config()
    cfg["texts"][key] = text
    STORE.update("button_styles", lambda d: cfg)
    return True

def set_enabled(key: str, enabled: bool) -> bool:
    if key not in STYLE_KEYS:
        return False
    cfg = get_button_config()
    if enabled:
        cfg["disabled"] = [k for k in cfg["disabled"] if k != key]
    else:
        if key not in cfg["disabled"]:
            cfg["disabled"].append(key)
    STORE.update("button_styles", lambda d: cfg)
    return True

def get_layout(kb_name: str):
    """چیدمان فعلی کیبورد؛ دکمه‌های ناشناخته یا خارج از محدوده این کیبورد حذف می‌شوند
    (بازیابی خودکار چیدمان‌های آلوده قدیمی)."""
    cfg = get_button_config()
    layout = cfg["layouts"].get(kb_name) or LAYOUT_DEFAULTS.get(kb_name)
    allowed = kb_allowed_keys(kb_name)
    rows = [[k for k in row if k in STYLE_KEYS and k in allowed] for row in (layout or [])]
    if kb_name in LAYOUT_DEFAULTS and not any(rows):
        rows = [list(r) for r in LAYOUT_DEFAULTS[kb_name]]
    return rows

def set_layout(kb_name: str, rows) -> bool:
    if kb_name not in LAYOUT_DEFAULTS or not isinstance(rows, list):
        return False
    allowed = kb_allowed_keys(kb_name)
    clean = []
    seen = set()
    for row in rows:
        r = []
        for k in row:
            if k in STYLE_KEYS and k in allowed and k not in seen:
                r.append(k)
                seen.add(k)
        if r:  # ردیف‌های خالی هرگز ذخیره نمی‌شوند (باعث کیبورد خالی می‌شوند)
            clean.append(r)
    if not clean:
        return False

    cfg = get_button_config()
    cfg["layouts"][kb_name] = clean
    STORE.update("button_styles", lambda d: cfg)
    return True

def reset_style(key: str = None):
    """بازگرداندن یک دکمه (یا همه) به حالت اولیه؛ دکمه‌های اضافه از چیدمان حذف می‌شوند."""
    if key is None:
        STORE.update("button_styles", lambda d: _new_button_config())
        return

    cfg = get_button_config()
    cfg["styles"].pop(key, None)
    cfg["texts"].pop(key, None)
    cfg["disabled"] = [k for k in cfg["disabled"] if k != key]
    is_default_btn = any(key in row for rows in LAYOUT_DEFAULTS.values() for row in rows)
    if not is_default_btn:
        for name, rows in (cfg.get("layouts") or {}).items():
            for i, row in enumerate(rows):
                if key in row:
                    rows[i] = [x for x in row if x != key]
    STORE.update("button_styles", lambda d: cfg)

def label_of(key: str, override: str = None) -> str:
    if override:
        return override
    return text_of(key)

# متن‌های قدیمی دکمه‌ها — کاربرانی که کیبورد کش‌شده نسخه‌های قبلی را دارند
# با زدن متن قدیمی، عملکرد دکمه جدید اجرا می‌شود (سازگاری روان).
BUTTON_ALIASES = {
    "راهنما و دستورات": "menu_guide",
    "راهنمای دستورات": "menu_guide",
}


def resolve_button_key(text: str):
    """تشخیص کلید دکمه Reply از متن فشرده‌شده (تغییر نام هرگز عملکرد را نمی‌شکند)."""
    if not text:
        return None
    t = text.strip()
    if not t:
        return None
    for key in STYLE_KEYS:
        if key.startswith("menu_") or key.startswith("conv_"):
            if t == text_of(key) or t == STYLE_KEYS[key][0]:
                return key
    return BUTTON_ALIASES.get(t)

def ib(key: str, callback_data: str = None, text: str = None, style: str = None) -> InlineKeyboardButton:
    """دکمه Inline با استایل رنگی واقعی تلگرام (Bot API 9.4).
    اولویت رنگ:
      1) style صریح (حتی "" برای اجبار خاکستری)
      2) استایل ذخیره‌شده در پنل برای این کلید
      3) استایل پیش‌فرض STYLE_KEYS
    قاعده رنگ معنادار:
      • primary (آبی)  → ورود/رفتن به بخش، صفحه بعد/قبلی
      • success (سبز)  → تأیید، ذخیره، فعال‌سازی، روشن کردن
      • danger (قرمز)  → حذف، بن، لغو دائمی، خاموش کردن، خطرناک
      • "" (خاکستری)   → بازگشت، انصراف، اطلاع خنثی
    """
    if style is not None:
        st = style
    else:
        saved = get_styles().get(key)
        st = saved if saved is not None else STYLE_KEYS.get(key, ("", "", "", False))[1]
    kwargs = {}
    if st:
        kwargs["style"] = st
    return InlineKeyboardButton(text=label_of(key, text), callback_data=callback_data or "noop", **kwargs)

def imarkup(rows) -> InlineKeyboardMarkup:
    """rows = [[(key, callback_data, text?, style?) | InlineKeyboardButton], ...]"""
    kb_rows = []
    for row in rows:
        r = []
        for item in row:
            if isinstance(item, InlineKeyboardButton):
                r.append(item)
            elif isinstance(item, (tuple, list)):
                key, cd = item[0], item[1]
                txt = item[2] if len(item) > 2 else None
                st = item[3] if len(item) > 3 else None
                r.append(ib(key, cd, txt, st))
        kb_rows.append(r)
    return InlineKeyboardMarkup(kb_rows)

def kbtn(key: str, text: str = None) -> KeyboardButton:
    """دکمه Reply با استایل رنگی واقعی (Bot API 9.4)."""
    style = style_of(key)
    kwargs = {}
    if style:
        kwargs["style"] = style
    return KeyboardButton(label_of(key, text), **kwargs)

def rmark(rows) -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup([[kbtn(k, t) for (k, t) in row] for row in rows],
                               resize_keyboard=True, one_time_keyboard=False)

def build_reply_kb(kb_name: str) -> ReplyKeyboardMarkup:
    """ساخت کیبورد Reply از رجیستری (متن/رنگ/چیدمان/فعال بودن از پنل مالک).
    اگر همه ردیف‌ها خالی شوند (مثلاً همه دکمه‌ها غیرفعال)، چیدمان پیش‌فرض استفاده می‌شود."""
    rows_out = []
    for row in get_layout(kb_name):
        r = [kbtn(key) for key in row if is_enabled(key)]
        if r:
            rows_out.append(r)
    if not rows_out:
        return rmark([[ (k, None) for k in row ] for row in LAYOUT_DEFAULTS[kb_name]])
    return ReplyKeyboardMarkup(rows_out, resize_keyboard=True, one_time_keyboard=False)

def main_menu_kb() -> ReplyKeyboardMarkup:
    return build_reply_kb("main_menu")

def conv_kb() -> ReplyKeyboardMarkup:
    return build_reply_kb("conv")

CANCEL_KB_TEXTS = ("❌ لغو", "لغو", "بازگشت", "بازگشت", "رد کردن")

# ایموجی‌های رنگی/تزئینی در متن دکمه‌ها مجاز نیستند — اعتبارسنجی پنل و تست‌ها
_COLOR_EMOJI_RE = re.compile(
    "["
    "\U0001F534\U0001F535\U0001F536\U0001F537\U0001F538\U0001F539\U0001F53A\U0001F53B"
    "\U0001F7E0-\U0001F7EB\U0001F7E5\U0001F7E6\U0001F7E7\U0001F7E8\U0001F7E9\U0001F7EA\U0001F7EB"
    "\U0001F300-\U0001F5FF\U0001F600-\U0001F64F\U0001F680-\U0001F6FF"
    "\U0001F900-\U0001F9FF\U0001FA70-\U0001FAFF"
    "\u2705\u274C\u274E\u26D4\u2728\u2B50\u2B1B\u2B1C\u25FC\u25FD\u25FE"
    "\u2600-\u27BF\u3030\u203C\u2049"
    "]", flags=re.UNICODE)


def has_decorative_emoji(text: str) -> bool:
    return bool(_COLOR_EMOJI_RE.search(text or ""))

# ============================================================
# 6) متن‌های فارسی
# ============================================================

import html as _html_mod


def esc(s) -> str:
    """Escape امن متن کاربران پیش از قرارگیری در پیام‌های HTML."""
    return _html_mod.escape(str(s if s is not None else ""), quote=False)


_TAG_RE = re.compile(r"</?[a-zA-Z][^>]*>|&[a-zA-Z#0-9]+;")


def strip_tags(s: str) -> str:
    """حذف کامل تگ‌ها برای ارسال جایگزین بدون Parse Mode (هیچ تگ خامی نمایش داده نمی‌شود)."""
    return _TAG_RE.sub("", str(s or "")).replace("<", "＜").replace(">", "＞")


PRIVACY_TEXT = (
    "❤️ <b>حریم خصوصی شما برای ما مهم است</b>\n\n"
    "ما اینجا هستیم تا تجربه‌ای امن و دوستانه از گفت‌وگوی ناشناس داشته باشید.\n\n"
    "• اطلاعات حساب شما فقط برای عملکرد ربات و مدیریت امنیت استفاده می‌شود.\n"
    "• پیام‌های چت کاربران عادی حداکثر تا ۷۲ ساعت نگهداری و سپس حذف می‌شوند.\n"
    "• پیام‌های مالک تابع سیاست نگهداری جداگانه هستند.\n"
    "• اطلاعات شخصی خود مثل شماره تلفن، رمز عبور و آدرس را برای دیگران ارسال نکنید.\n"
    "• اگر کسی رفتار نامناسبی داشت، می‌توانید با نوشتن «گزارش» چت را ببندید و گزارش کنید.\n"
    "• اطلاعات گزارش‌ها فقط برای بررسی امنیتی در اختیار مدیریت مجاز قرار می‌گیرد.\n"
    "• امکان ثبت اعتراض به تصمیم‌های مدیریتی از طریق بخش اعتراض وجود دارد.\n\n"
    "با احترام، تیم مدیریت ربات 💕"
)

def start_search_text():
    return "🔍 در حال جست‌وجوی مخاطب مناسب...\n\nدر صورت پیدا شدن، به‌صورت خودکار متصل می‌شوید.\n\nمی‌توانید جست‌وجو را لغو کنید:"

MAIN_HINT = (
    "👋 <b>خوش آمدید!</b>\n\n"
    "برای شروع گفت‌وگوی ناشناس، دکمه «شروع چت ناشناس» را بزنید.\n"
    "برای چت با دوست، شناسه اختصاصی ۹ رقمی او را همین‌جا ارسال کنید.\n"
    "«اطلاعات من» شامل شناسه اختصاصی و تنظیمات جست‌وجو است.\n"
    "برای دیدن فهرست دستورات و راهنمای کامل، دکمه «دستورات» را بزنید یا /guide را بفرستید.\n"
    "برای ارتباط با مدیریت، کافی است کلمه «پشتیبانی» یا دستور /support را ارسال کنید."
)

# ============================================================
# 6.1) رجیستری دستورات — فقط عنوان/توضیح/نمونه/ترتیب/فعال بودن از پنل قابل تغییر است؛
#      عملکرد واقعی دستورها در کد ثابت می‌ماند (محدودیت امنیتی).
# ============================================================

CATEGORY_LABELS = {
    "general": "دستورات عمومی کاربران",
    "profile": "ثبت‌نام و پروفایل",
    "chat": "چت ناشناس",
    "security": "امنیت و گزارش",
    "owner": "دستورات مالک",
    "usermgmt": "مدیریت کاربران",
    "system": "تنظیمات و پشتیبان‌گیری",
}

COMMANDS_DEFAULT = [
    {"name": "/start", "title": "شروع / منوی اصلی", "category": "general",
     "desc": "نمایش صفحه اصلی ربات، منوی دکمه‌ها و ادامه ثبت‌نام نیمه‌کاره.",
     "usage": "دستور /start را ارسال کنید.", "example": "/start",
     "secret": False, "changeable": False, "enabled": True, "order": 1},
    {"name": "/info", "title": "اطلاعات من", "category": "profile",
     "desc": "مشاهده کامل اطلاعات حساب: کد اختصاصی، مشخصات، تنظیمات جست‌وجو و آمار.",
     "usage": "دستور /info را ارسال کنید یا دکمه «اطلاعات من» را بزنید.",
     "example": "/info", "secret": False, "changeable": True, "enabled": True, "order": 2},
    {"name": "/guide", "title": "دستورات", "category": "general",
     "desc": "راهنمای جست‌وجویی و فهرست کامل دستورات ربات.",
     "usage": "دستور /guide را ارسال کنید یا دکمه «دستورات» را بزنید.",
     "example": "/guide", "secret": False, "changeable": True, "enabled": True, "order": 3},
    {"name": "/support", "title": "پشتیبانی", "category": "general",
     "desc": "ارتباط مستقیم با مدیریت ربات؛ پاسخ فقط برای خود شما ارسال می‌شود.",
     "usage": "کلمه «پشتیبانی» را ارسال کنید یا دستور /support را بزنید.",
     "example": "/support", "secret": False, "changeable": True, "enabled": True, "order": 4},
    {"name": "/report", "title": "گزارش تخلف", "category": "security",
     "desc": "قطع فوری مکالمه و ثبت گزارش؛ هویت شما هرگز فاش نمی‌شود.",
     "usage": "در حین چت، واژه «گزارش» را بنویسید یا /report را ارسال کنید.",
     "example": "/report", "secret": False, "changeable": False, "enabled": True, "order": 5},
    {"name": "/panel", "title": "پنل مدیریت", "category": "owner",
     "desc": "ورود به پنل مدیریت ربات (فقط مالک).",
     "usage": "دستور /panel را ارسال کنید.", "example": "/panel",
     "secret": True, "changeable": False, "enabled": True, "order": 6},
    # دستورات محرمانه متنی مالک — فقط در راهنمای مالک نمایش داده می‌شوند
    {"name": "روشن", "title": "دستور محرمانه مدیر", "category": "owner",
     "desc": "در حین مکالمه، اعلام وضعیت ادمین به طرف مقابل.",
     "usage": "در حین مکالمه کلمه «روشن» را بنویسید.", "example": "روشن",
     "secret": True, "changeable": False, "enabled": True, "order": 7},
    {"name": "سکوت{دقیقه}", "title": "سکوت کاربر", "category": "usermgmt",
     "desc": "سکوت کردن یک کاربر برای مدت مشخص (در پیام به کاربر در پنل).",
     "usage": "در زمینه ارسال پیام به کاربر: سکوت30", "example": "سکوت 30",
     "secret": True, "changeable": False, "enabled": True, "order": 8},
    {"name": "بن{دقیقه}", "title": "بن کاربر", "category": "usermgmt",
     "desc": "مسدودسازی موقت یک کاربر (در پیام به کاربر در پنل).",
     "usage": "در زمینه ارسال پیام به کاربر: بن60", "example": "بن 60",
     "secret": True, "changeable": False, "enabled": True, "order": 9},
    {"name": "اخطار", "title": "اخطار به کاربر", "category": "usermgmt",
     "desc": "ثبت اخطار مدیریتی برای کاربر.",
     "usage": "در زمینه ارسال پیام به کاربر: اخطار", "example": "اخطار",
     "secret": True, "changeable": False, "enabled": True, "order": 10},
    {"name": "حذف سکوت", "title": "رفع سکوت", "category": "usermgmt",
     "desc": "برداشتن سکوت کاربر.", "usage": "در زمینه ارسال پیام به کاربر.",
     "example": "حذف سکوت", "secret": True, "changeable": False, "enabled": True, "order": 11},
    {"name": "حذف بن", "title": "رفع بن", "category": "usermgmt",
     "desc": "برداشتن مسدودی کاربر.", "usage": "در زمینه ارسال پیام به کاربر.",
     "example": "حذف بن", "secret": True, "changeable": False, "enabled": True, "order": 12},
    {"name": "گزارش", "title": "گزارش‌های کاربر", "category": "owner",
     "desc": "مشاهده گزارش‌های ثبت‌شده درباره کاربر.",
     "usage": "در زمینه ارسال پیام به کاربر در پنل.", "example": "گزارش",
     "secret": True, "changeable": False, "enabled": True, "order": 13},
]


def get_commands() -> list:
    ensure_storage()
    saved = STORE.get("commands")
    if not saved:
        return copy.deepcopy(COMMANDS_DEFAULT)
    by_name = {c["name"]: c for c in COMMANDS_DEFAULT}
    out = []
    for c in saved:
        base = by_name.get(c.get("name"))
        if base is None:
            continue
        merged = dict(base)
        # فقط متادیتای مجاز از تنظیمات پنل می‌آید؛ عملکرد دستور هرگز تغییر نمی‌کند
        for field in ("title", "desc", "usage", "example", "enabled", "order"):
            if c.get(field) is not None:
                merged[field] = c[field]
        out.append(merged)
    for name, base in by_name.items():
        if name not in {c["name"] for c in out}:
            out.append(dict(base))
    out.sort(key=lambda c: c.get("order", 99))
    return out


def save_commands_meta(cmd_name: str, fields: dict) -> bool:
    rec = next((c for c in COMMANDS_DEFAULT if c["name"] == cmd_name), None)
    if rec is None:
        return False

    def _m(lst):
        for c in lst:
            if c.get("name") == cmd_name:
                c.update({k: v for k, v in fields.items()})
                return lst
        fields["name"] = cmd_name
        lst.append(fields)
        return lst
    STORE.update("commands", _m)
    return True

# ============================================================
# 6.2) سیستم راهنمای هوشمند — موضوعات جست‌وجوپذیر با سطح دسترسی
# ============================================================

GUIDE_TOPICS = [
    {"title": "شروع و پایان چت ناشناس", "access": "user",
     "keys": ["چت", "chat", "شروع چت", "پایان چت", "چت بعدی", "اتصال", "مکالمه"],
     "body": ("با دکمه «شروع چت ناشناس» وارد صف انتظار می‌شوید و به‌محض پیدا شدن مخاطب مناسب، "
              "اتصال برقرار می‌شود. برای رفتن به مخاطب بعدی «چت بعدی»، برای قطع رابطه «بلاک» و "
              "برای پایان گفت‌وگو «پایان مکالمه» را بزنید.\n"
              "دسترسی: همه کاربران ثبت‌نام‌شده")},
    {"title": "چت با دوست با کد اختصاصی", "access": "user",
     "keys": ["کد اختصاصی", "شناسه اختصاصی", "دوست", "کد دوست", "friend", "id"],
     "body": ("هر کاربر یک کد اختصاصی ۹ رقمی دائمی دارد که در «اطلاعات من» (/info) دیده می‌شود. "
              "کد اختصاصی دوستتان را در منوی اصلی ارسال کنید؛ پس از پذیرش او، مکالمه دوستانه ساخته می‌شود. "
              "درخواست‌ها پس از ۱۰ دقیقه بی‌پاسخ، منقضی می‌شوند.\n"
              "دسترسی: همه کاربران ثبت‌نام‌شده")},
    {"title": "ثبت‌نام و تکمیل پروفایل", "access": "user",
     "keys": ["ثبت‌نام", "register", "نام", "جنسیت", "سن", "استان", "پروفایل", "profile"],
     "body": ("با اولین /start، سیاست حریم خصوصی نمایش داده می‌شود؛ پس از تأیید، مراحل ثبت‌نام "
              "(نام ← جنسیت ← سن ← استان) طی می‌شود. اگر ثبت‌نام را نیمه‌کاره رها کنید، با /start "
              "از همان مرحله ادامه می‌دهید. تغییر مشخصات هر ۶ ماه یک بار از «اطلاعات من» ممکن است.\n"
              "دسترسی: همه کاربران")},
    {"title": "گزارش تخلف و امنیت", "access": "user",
     "keys": ["گزارش", "report", "تخلف", "امنیت", "اخطار", "بن", "مسدود"],
     "body": ("در حین چت، واژه «گزارش» یا دستور /report را بفرستید؛ مکالمه فوراً بسته می‌شود و گزارش "
              "با وضعیت «جدید» ثبت می‌گردد. هویت شما برای طرف مقابل هرگز فاش نمی‌شود. نقض قوانین "
              "منجر به اخطار، سکوت یا مسدودی می‌شود و سیستم ضد فحاشی فعال است.\n"
              "دسترسی: همه کاربران")},
    {"title": "کد اختصاصی حساب", "access": "user",
     "keys": ["کد اختصاصی", "کد من", "internal", "کد ۹ رقمی", "شناسه ربات"],
     "body": ("کد اختصاصی، شناسه دائمی و یکتای شما در ربات است و با تغییر نام یا شناسه تلگرام "
              "تغییر نمی‌کند. آن را از /info ببینید و برای دریافت درخواست چت دوستانه در اختیار "
              "دوستانتان بگذارید.\n"
              "دسترسی: همه کاربران")},
    {"title": "پشتیبانی و ارتباط با مدیریت", "access": "user",
     "keys": ["پشتیبانی", "support", "مدیر", "مشکل", "تماس با مدیریت"],
     "body": ("برای گفت‌وگو با مدیریت، کلمه «پشتیبانی» را ارسال کنید یا دستور /support را بزنید؛ "
              "راهنما فقط برای خود شما ارسال می‌شود. گفت‌وگو تا زدن «پایان گفت‌وگو» ادامه دارد و "
              "پیام‌های شما در سیستم پشتیبانی ثبت می‌شود.\n"
              "دسترسی: همه کاربران")},
    {"title": "حذف پیام و حریم خصوصی", "access": "user",
     "keys": ["حذف پیام", "delete", "حریم خصوصی", "privacy", "۷۲ ساعت", "نگهداری پیام"],
     "body": ("با ریپلای روی پیام و نوشتن «حذف»، پیام از نمایش شما و سوابق مجاز حذف می‌شود. "
              "پیام‌های مکالمه‌ها ۷۲ ساعت نگهداری و سپس دائمی حذف می‌شوند (مگر مکالمه دارای گزارش باز).\n"
              "دسترسی: همه کاربران")},
    {"title": "فیلترهای جست‌وجو (جنسیت و سن)", "access": "user",
     "keys": ["فیلتر", "جنسیت مخاطب", "سن مخاطب", "هم‌سن", "سن بالاتر", "filter"],
     "body": ("از «اطلاعات من» می‌توانید فیلتر جنسیت و فیلتر سن مخاطب را تنظیم کنید. "
              "قانون امنیتی زیر ۱۸ / ۱۸+ همیشه برقرار است و غیرقابل تغییر است.\n"
              "دسترسی: همه کاربران ثبت‌نام‌شده")},
    {"title": "دستور محرمانه «روشن»", "access": "owner",
     "keys": ["روشن", "ادمین", "reveal"],
     "body": ("در حین مکالمه، با نوشتن «روشن» پیام سیستمی «کاربر مورد نظر ادمین است. 💯» برای "
              "طرف مقابل ارسال می‌شود و در گزارش امنیتی ثبت می‌گردد.\n"
              "دسترسی: فقط مالک")},
    {"title": "دستورات مدیریتی متنی (سکوت، بن، اخطار)", "access": "owner",
     "keys": ["سکوت", "بن", "اخطار", "حذف سکوت", "حذف بن", "دستور متنی", "moderation"],
     "body": ("دستورات ساده در «سه زمینه» کار می‌کنند: «ارسال پیام به کاربر» (پرونده کاربر)، «پاسخ به تیکت» "
              "و «داخل مکالمه» (روی مخاطب فعلی مالک).\n"
              "• سکوت{دقیقه} — مثال: «سکوت30» یا «سکوت ۳۰» (حداکثر ۵ رقم)\n"
              "• بن{دقیقه} — مثال: «بن60» یا «بن ۶۰»\n"
              "• اخطار — ثبت اخطار مدیریتی\n"
              "• حذف سکوت — رفع سکوت (فاصله بین دو کلمه الزامی)\n"
              "• حذف بن — رفع بن (فاصله الزامی)\n"
              "• گزارش — فهرست گزارش‌های همان کاربر (فقط برای مالک)\n"
              "«داخل مکالمه»: مالک در چت ناشناس همان دستور را می‌فرستد و روی مخاطب فعلی‌اش اجرا می‌شود؛ "
              "پیام هرگز به طرف مقابل منتقل نمی‌شود.\n"
              "این دستورها هرگز به‌عنوان پیام عادی ارسال نمی‌شوند، رسید نتیجه برای مالک می‌آید و "
              "اعمال آن‌ها روی حساب خود مدیر مجاز نیست. اعداد فارسی و انگلیسی پشتیبانی می‌شوند.\n"
              "مجازات اختصاصی (در وضعیت امنیتی کاربر) با قالب «نوع:عدد[ساعت]»: «سکوت:۳۰» | «بن:۲۴ساعت» | "
              "«فوق‌العاده:۱۲۰» (دقیقه) | «دختر:۱۶۸» (ساعت؛ ۰=دائمی).\n"
              "دسترسی: فقط مالک")},
    {"title": "تنظیمات پیشرفته دکمه‌ها و دستورات", "access": "owner",
     "keys": ["دکمه", "تنظیمات پیشرفته", "چیدمان", "رنگ دکمه", "استایل", "رنگ"],
     "body": ("در پنل مالک ← «تنظیمات پیشرفته» می‌توانید متن، رنگ رسمی (primary/success/danger)، "
              "چیدمان ردیف‌ها و فعال بودن هر دکمه را تغییر دهید؛ قبل از ذخیره، پیش‌نمایش نمایش داده "
              "می‌شود. مدیریت دستورات هم فقط عنوان/توضیح/نمونه را تغییر می‌دهد و عملکرد دستورها "
              "دست‌نخورده می‌ماند.\n"
              "دسترسی: فقط مالک")},
    {"title": "کد اختصاصی مالک و لغو آن", "access": "owner",
     "keys": ["کد مالک", "لغو کد", "revoke", "کد اختصاصی مالک"],
     "body": ("کد اختصاصی مالک در پنل مالک نمایش داده می‌شود؛ می‌توانید آن را لغو و کد جدید بگیرید. "
              "کد قبلی فوراً نامعتبر می‌شود و دیگر قابل استفاده نیست.\n"
              "دسترسی: فقط مالک")},
    {"title": "حریم خصوصی (نسخه جدید)", "access": "user",
     "keys": ["حریم خصوصی", "privacy", "حریم", "داده", "نگهداری", "حذف پیام", "۷۲ ساعت"],
     "body": ("حریم خصوصی شما برای ما مهم است ❤️ اطلاعات حساب فقط برای عملکرد ربات و مدیریت امنیت "
              "استفاده می‌شود؛ پیام‌های چت کاربران عادی حداکثر تا ۷۲ ساعت نگهداری و سپس حذف می‌شوند؛ "
              "پیام‌های مالک سیاست نگهداری جداگانه دارند؛ گزارش‌ها فقط برای بررسی امنیتی در دسترس "
              "مدیریت مجاز است؛ و ثبت اعتراض به تصمیم‌های مدیریتی از طریق بخش اعتراض ممکن است.\n"
              "دسترسی: همه کاربران")},
    {"title": "اعتراض به مجازات (سامانه محافظت)", "access": "user",
     "keys": ["اعتراض", "ap", "مجازات", "سکوت", "لغو تصمیم", "پرونده"],
     "body": ("اگر به دلیل تخلف در چت دختر-پسر مجازات شده‌اید، روی پیام مجازات دکمه سبز «ثبت اعتراض» "
              "می‌بینید: توضیحات را بنویسید و در صورت تمایل تصویر پیوست کنید. هر پرونده فقط یک بار "
              "قابل اعتراض است؛ پس از ارسال، رسید می‌گیرید. ارسال اعتراض رفع خودکار مجازات نیست و "
              "پشتیبانی عادی برای دور زدن محدودیت استفاده نمی‌شود.\n"
              "دسترسی: کاربران دارای مجازات قابل اعتراض")},
    {"title": "محدودیت فوق‌العاده و سکوت", "access": "user",
     "keys": ["محدودیت فوق‌العاده", "سکوت", "شروع چت", "صف انتظار", "بازه", "سیستم محدودیت", "مجازات"],
     "body": ("ربات چند «سیستم محدودیت» مستقل دارد که همگی سمت سرور بررسی می‌شوند:\n"
              "• <b>سکوت</b> — محدودیت کامل گفت‌وگو: نمی‌توانید چت جدید شروع کنید، «چت بعدی» بزنید یا وارد صف انتظار شوید؛ زمان باقی‌مانده به شما نمایش داده می‌شود.\n"
              "• <b>محدودیت فوق‌العاده</b> — در هر بازه ۶۰ دقیقه‌ای فقط یک چت جدید؛ بعد از اولین اتصال، شروع بعدی تا پایان بازه بسته است.\n"
              "• <b>منع چت با دختران</b> — متخلفان جنسیتی برای مدتی (یا دائمی) فقط با کاربران پسر متصل می‌شوند.\n"
              "• <b>مجازات مرحله‌ای</b> — تکرار تخلف سطح ۳ (آزار جنسی کلامی) به مرحله ۱ تا ۵ ارتقا می‌یابد: بن چندساعته + محدودیت فوق‌العاده طولانی‌تر و در مرحله ۴/۵ منع دائمی چت با دختران.\n"
              "این محدودیت‌ها مستقل‌اند، با پایان زمان به‌صورت خودکار برداشته می‌شوند و سایر قابلیت‌های ربات (مشاهده اطلاعات، پشتیبانی) طبق تنظیمات باقی می‌مانند.\n"
              "دسترسی: همه کاربران")},
    {"title": "ارسال همگانی پیشرفته (زمان‌بندی، سنجاق، واکنش)", "access": "owner",
     "keys": ["ارسال همگانی", "اطلاع‌رسانی", "زمان‌بندی", "تکرار", "سنجاق", "واکنش", "broadcast"],
     "body": ("پنل ← اطلاع‌رسانی: متن پیام را بفرستید (فرمت‌های تلگرام مثل Bold حفظ می‌شوند)؛ سپس می‌توانید "
              "«📌 سنجاق» و «👍 واکنش» را روشن کنید (پیام در چت هر کاربر سنجاق و واکنش رسمی تلگرام روی آن "
              "ثبت می‌شود) یا «⏰ ارسال زمان‌بندی‌شده» را انتخاب کنید با قالب «30/6/5» = ۳۰ دقیقه تأخیر، "
              "تکرار هر ۶ ساعت، ۵ بار (هر بخش اختیاری؛ مثل «0/6» یعنی هر ۶ ساعت به‌صورت بی‌نهایت). "
              "ارسال‌ها در دیتابیس ذخیره می‌شوند، پس از Restart هم به موقع اجرا می‌شوند. "
              "فهرست و لغو: پنل ← ⏰ ارسال‌های زمان‌بندی‌شده.\n"
              "دسترسی: فقط مالک")},
    {"title": "هشدار لینک و فرمت دامنه", "access": "user",
     "keys": ["لینک", "هشدار لینک", "دامنه", "وب", "http", "www", "وب‌سایت"],
     "body": ("اگر طرف مقابل پیام حاوی لینک (www، http، https یا دامنه ساده) بفرستد، زیر آن یک هشدار "
              "امنیتی فقط برای شما نمایش داده می‌شود: لینک ممکن است آلوده باشد؛ روی لینک‌های ناشناس "
              "کلیک نکنید و اطلاعات شخصی خود را وارد نکنید. متن دقیق هشدار را مدیریت تعیین می‌کند و "
              "در صورت بسته بودن فرمت «لینک وب»، خودِ پیامِ دارای لینک اصلاً ارسال نمی‌شود.\n"
              "دسترسی: همه کاربران در چت")},
    {"title": "پیشنهاد تغییر چت پس از پیام نامناسب", "access": "user",
     "keys": ["تغییر چت", "فحاشی", "پیشنهاد چت", "بلاک", "چت بعدی"],
     "body": ("اگر پیامی نامناسب دریافت کنید و فیلتر فحاشی توسط مدیریت خاموش باشد، پیام به شما "
              "می‌رسد اما زیرش یک پیام خصوصی «آیا مایل به تغییر چت خود هستید؟» با دو دکمه در یک ردیف "
              "می‌آید: «بلاک ⛔» (قطع دائمی ارتباط با این کاربر) و «چت بعدی ⏭️» (بستن چت و جست‌وجوی "
              "مخاطب جدید). این پیشنهاد فقط برای شماست و طرف مقابل آن را نمی‌بیند.\n"
              "دسترسی: دریافت‌کننده پیام در چت فعال")},
    {"title": "سیستم محافظت خانم‌ها (سه‌سطحی)", "access": "user",
     "keys": ["سیستم محافظت", "محافظت خانم ها", "توهین جنسیتی", "آزار جنسی", "اعتراض", "سطح"],
     "body": ("در گفت‌وگوهای دختر-پسر یک سیستم محافظت هوشمند سه‌سطحی فعال است:\n"
              "• <b>سطح ۱</b> — توهین جنسیتی: تحقیر به دلیل جنسیت (مثل «دخترا همه...»)؛ نتیجه: پایان چت + سکوت کوتاه.\n"
              "• <b>سطح ۲</b> — توهین شدید جنسیتی + فحاشی رکیک؛ نتیجه: پایان چت + سکوت طولانی‌تر + ثبت در سابقه امنیتی.\n"
              "• <b>سطح ۳</b> — آزار جنسی کلامی (درخواست صریح رابطه/تصویر)؛ نتیجه: پایان فوری چت + سکوت + اخطار ویژه + در صورت سابقه، مجازات مرحله‌ای (بن تا ۱۶۸ ساعت، محدودیت فوق‌العاده طولانی و منع چت با دختران در مرحله ۴/۵).\n"
              "درخواست‌های جنسی صریح (سطح ۳) در «همه» گفت‌وگوها مسدود می‌شوند؛ توهین‌های جنسیتی فقط در چت دختر-پسر بررسی می‌شوند. جنسیت فقط از ثبت‌نام خوانده می‌شود، پیام‌های نقل‌قول‌شده بررسی نمی‌شوند و برای هر پرونده یک بار امکان ثبت اعتراض با تصویر وجود دارد.\n"
              "دسترسی: همه کاربران (به‌طور خودکار فعال)")},
    {"title": "بکاپ و بازیابی", "access": "owner",
     "keys": ["بکاپ", "backup", "بازیابی", "restore", "پشتیبان"],
     "body": ("پنل مالک ← «مدیریت بکاپ»: ایجاد دستی، دریافت فایل، بررسی سلامت SHA-256 و آپلود/بازیابی "
              "با بازگشت امن. از نسخه ۲.۳.۰ بکاپ خودکار پیش‌فرض خاموش است (برای صرفه‌جویی در حجم دیسک) "
              "و از «تنظیمات سیستمی ← بکاپ خودکار» قابل روشن‌کردن است.\n"
              "دسترسی: فقط مالک")},
    {"title": "همه سیستم‌های امنیتی و محدودیت‌های ربات", "access": "user",
     "keys": ["سیستم", "امنیت", "محدودیت", "سکوت", "بن", "محدودیت فوق‌العاده",
              "منع چت دختر", "پرونده", "اعتراض", "مرحله", "مجازات"],
     "body": ("این ربات چند لایه محافظت دارد:\n"
              "• سکوت: نمی‌توانید چت جدید/چت بعدی/صف انتظار بزنید؛ فقط چت‌های موجود.\n"
              "• بن موقت/دائمی: کل ربات برای شما بسته می‌شود.\n"
              "• محدودیت فوق‌العاده: در هر بازه ۶۰ دقیقه‌ای فقط یک چت جدید؛ "
              "زمان باقی‌مانده نمایش داده می‌شود.\n"
              "• منع چت با دختران: اگر فعال شود نمی‌توانید با کاربران دختر جفت شوید "
              "(زمان‌دار یا دائمی).\n"
              "• سیستم محافظت هوشمند: توهین جنسیتی، آزار کلامی و فحاشی رکیک را "
              "تشخیص می‌دهد و مجازات می‌کند؛ درخواست جنسی صریح حتی در چت هم‌جنس مسدود است.\n"
              "• پرونده و مرحله: تخلفات سطح ۳ سابقه‌دار می‌شوند و مرحله ۱ تا ۵ "
              "مجازات مرحله‌ای (بن + محدودیت فوق‌العاده + منع چت دختر) را فعال می‌کنند.\n"
              "• اعتراض: روی پیام مجازات، دکمه سبز «ثبت اعتراض» دارید؛ هر پرونده "
              "فقط یک بار قابل اعتراض است.\n"
              "همه این‌ها سمت سرور اعمال می‌شوند و از طریق پشتیبانی عادی قابل دور زدن نیستند.\n"
              "دسترسی: همه کاربران")},
]


def search_guide(query: str, is_owner: bool):
    """جست‌وجوی راهنما با نادیده گرفتن ي/ی و ك/ک و فاصله‌ها. خروجی: (نتیجه‌ها, پیشنهادها)"""
    q = normalize_text(query)
    if not q:
        return [], []
    exact, fuzzy, suggestions = [], [], []
    for topic in GUIDE_TOPICS:
        if topic["access"] == "owner" and not is_owner:
            continue
        hay_keys = normalize_text(" ".join(topic["keys"]))
        hay_title = normalize_text(topic["title"])
        hay_body = normalize_text(topic["body"])
        hay = " ".join([hay_keys, hay_title, hay_body])
        q_words = q.split()
        if q in hay_keys or q in hay_title:
            exact.append(topic)
        elif all(w in hay for w in q_words) or q in hay:
            fuzzy.append(topic)
        elif any(w in hay for w in q_words):
            suggestions.append(topic)
    if not exact and not fuzzy and not suggestions:
        visible = [t for t in GUIDE_TOPICS if t["access"] == "user" or is_owner]
        suggestions = visible[:3]
    return exact + fuzzy, suggestions[:4]


def guide_topic_by_title(title: str):
    t = normalize_text(title)
    for topic in GUIDE_TOPICS:
        if normalize_text(topic["title"]) == t:
            return topic
    return None

def ban_notice(user) -> str:
    if user.get("ban"):
        if user["ban"].get("perm"):
            return "⛔ حساب شما به‌صورت دائمی مسدود شده است.\n\nدر صورت اعتراض با پشتیبانی تماس بگیرید."
        until = user["ban"].get("until")
        try:
            dt = parse_iso(until)
            return f"⛔ حساب شما موقتاً مسدود شده است.\n⏳ تا: <b>{jalali(dt)}</b>"
        except Exception:
            return "⛔ حساب شما موقتاً مسدود شده است."
    return "⛔ حساب شما مسدود است."

def mute_notice(user) -> str:
    mu = user.get("mute_until")
    try:
        dt = parse_iso(mu)
        rem = dt - now_utc()
        mins = max(0, int(rem.total_seconds() // 60) + 1)
        return f"🤫 حساب شما تا {fa_num(mins)} دقیقه دیگر در سکوت است و نمی‌توانید پیام بفرستید."
    except Exception:
        return "🤫 حساب شما در سکوت است."
# ============================================================
# 7) موتور نرمال‌سازی + تشخیص محتوای توهین‌آمیز (ضد فحاشی)
# ============================================================

_AR_TO_FA = str.maketrans({
    "ي": "ی", "ك": "ک", "أ": "ا", "إ": "ا", "آ": "ا", "ٱ": "ا",
    "ة": "ه", "ؤ": "و", "ئ": "ی", "ٔ": "", "ٰ": "",
    "ً": "", "ٌ": "", "ٍ": "", "َ": "", "ُ": "", "ِ": "", "ّ": "", "ْ": "",
    "ۀ": "ه",
})

_ZERO_WIDTH = ("\u200c", "\u200d", "\u200e", "\u200f", "\u2066", "\u2067", "\u2068", "\u2069", "\ufeff", "\u0640")

_LEET = str.maketrans({
    "4": "a", "@": "a", "3": "e", "1": "i", "!": "i", "0": "o",
    "$": "s", "5": "s", "7": "t", "8": "b", "6": "g", "9": "g",
})

# واژه‌های پایه (نرمال‌شده) — فهرست مالک از طریق پنل مدیریت افزوده/کاسته می‌شود
BASE_PROFANITY = [
    # ---------- فارسی: واژه‌های رکیک پایه (ادغام نسخه ۲.۳ و پچ ۲.۴) ----------
    "کس", "کوس", "کیر", "کون", "کص", "کوص", "جنده", "قحبه", "فاحشه", "روسپی",
    "هرزه", "لوده", "خارکوسه", "خارکس", "خارکصه", "خارکون", "کسخل", "کصخل",
    "کوسخل", "کسکش", "کصکش", "کوسکش", "کوصکش", "کسده", "کسنن", "کسننه",
    "کسخوار", "کوسخوار", "کونخوار", "کونده", "کونکش", "کیرخور", "کیرکش",
    "کیرخوار", "خایه", "خایمال", "خایهمال", "خایهکش", "خرخایه", "چوچول",
    "چوچوله", "دودول", "دودوله", "پکینه", "النگ", "دلنگ", "دول", "دولچه",
    "ممه", "ممهکش", "مملی", "ممریده", "پستون", "پستونکش", "ساک", "ساکزن",
    "سکس", "سکسکش", "حشری", "حشریه", "حشریباش", "شق", "شقه", "شقشق",
    "فحش", "فحاش", "فحشباز", "فحاشه", "شرمده", "قحبهزاده", "قحب", "جندک",
    "جندهپسر", "جندهبچه", "جندهزاده", "لوسکص", "معوج", "معوجه", "گوده",
    "گایید", "گاییده", "گاییدن", "گاییدنی", "گاید", "گایدنت", "گاییدم",
    "میکصم", "بکص", "مکص", "بکصمت", "میکونمت", "بکنت", "ساکز",
    # ترکیب‌های چسبیده به خانواده (بدون نیم‌فاصله تا تطبیق کار کند)
    "کیرم", "کوسم", "کونم", "کسیم", "کسش", "کونش",
    "ننهکس", "ننهکص", "مامانکس", "مامانکص", "مادرکس", "مادرکص", "مادرجنده",
    "مادرقحبه", "مادرفاحشه", "مادرشلوش", "مادرسوخته", "مادرسوختگی",
    "خواهرکس", "خواهرکص", "خواهرجنده", "خواهرقحبه", "خواهرکون",
    "عمهکس", "عمهکص", "مامهکس", "مامهکص", "داییکس", "عموکس",
    "پدرفاحشه", "پدرجنده", "پدرقحبه", "پدرسوخته", "پدرسوختگی",
    "جونکس", "جونکص", "جونکیر", "جونمادر", "جونننه", "کیریاد", "کصجادو",
    "کصکیر", "کصکون", "کصممه", "کصخواهر", "کصمادر", "کصننه", "کصعمه",
    "کصمامه", "کصدایی", "کصعمو", "کصپدر", "کصجد", "کصجون",
    "کونمادر", "کونننه", "کونخواهر", "کونممه", "کونپدر", "کونعمه",
    "کسشوهر", "کسشهر", "کسکار", "کسطلا", "کسبل", "کسحوض",
    "کیرمادر", "کیرننه", "کیرخواهر", "کیرممه", "کیرپدر", "کیرعمه",
    "کیرخر", "کیراسب", "کیربز", "کیرگاو", "کیرگربه", "کیرسگ",
    "کونخر", "کوناسب", "کونبز", "کسخر", "کساسب", "کسبز", "کسگاو",
    "کیری", "کونی", "کونیها", "کونیکس", "کونیکص", "کونیزاده",
    "کسزده", "کونزده", "کصزده", "کونگشاد", "کسگشاد", "کسلیس",
    "کسلیسها", "عوضیکس", "عوضیکون", "پستکص", "پستکون", "پستکس",
    "احمقننه", "ابلهکص", "اسکلجنده", "اسکلکس", "اسکلکون",
    "لاشیکس", "لاشیگور", "لاشیسگ", "دوروغگویکص", "عوضیجنده",
    # حرومزاده و حرامزاده
    "حرومزاده", "حرومزه", "حرومکص", "حرومقحبه", "حرامزاده", "حرامزه",
    "حرامکار", "حرامخور", "حرامخوار", "حرومکیر", "ناموس",
    # توهین‌های عمومی
    "احمق", "احمقی", "ابله", "ابلهی", "اسکل", "اعضال", "بیشعور", "بیشعورها",
    "بیمغز", "بیمغزکص", "دنیاقلم", "رذل", "زفت", "زفتها", "سفیله",
    "سگ", "سگی", "سگص", "سگصفت", "سگزاده", "سگکص", "سگجنده", "سگکس",
    "سگصها", "شغال", "شغالها", "عوضی", "عوضیها", "غلطکار", "کثیف",
    "کثیفی", "کثافت", "کثافتی", "چرک", "چرکین", "پلید", "پلیدی",
    "لاشی", "لوشی", "لوشها", "لاشیها", "مفتخور", "ملعون", "ملعونها",
    "منحرف", "منحرفها", "هیز", "هیزها", "ولگرد", "ولگردها",
    "بیپدر", "بیمادر", "بیپدرمادر", "دوزاری", "دوزاریها", "دوروغگو",
    "جوخالی", "جوخالیها", "چسپ", "چسپها", "بیناموس", "بیحیاط",
    "بیعفت", "بیعفتی", "بیحیا", "بیشرم", "بیشرمی", "بیغیرت", "بیشرف",
    "بیادب", "بیتربیت", "بیعرضه", "بیکمال", "بیناموسی",
    "مردهخور", "مردارخور", "گوربگور", "گوردریا", "پستفاز", "پستشهر",
    "پستفطرت", "پستذات", "پستنژاد", "بیشخصیت",
    # حیوان‌صفت‌ها و تشبیهات رکیک
    "خوک", "خوکی", "خوکصفت", "خوکزاده", "الاغ", "الاغی", "خر", "خری",
    "خرک", "خرکی", "گاگول", "گاگولی", "روبه", "روباه", "روباهصفت",
    "مارصفت", "افعی", "عقرب", "عقربصفت", "گاوصفتی",
    # کلاهبرداری و فحش‌های اخلاقی
    "کلاش", "کلاشی", "کلاهبردار", "دغلباز", "دغلی", "حقهباز", "شارلاتان",
    "چاپلوس", "چاپلوسی", "متملق", "چشمسفید", "رشوهخور", "رشوهبگیر",
    "دزد", "دزدی", "دزدک", "حرامزادگی", "زنا", "زنازاده", "زنازادگی",
    "ناموسفروش", "بیعفتیها", "عفتفروش", "کسناز", "کصناز", "کسنازها",
    "آبروریز", "آبروریزی", "بیآبرو", "رسوا", "رسوایی", "گوه", "گوهی",
    "گوهخور", "گوهخوار", "قحبهها", "جندهها", "فاحشهها", "حشریها",
    "لودهها", "کسخلها", "کسکشها", "خارکوسهها",
    # ---------- انگلیسی ----------
    "fuck", "fucked", "fucker", "fucking", "fuk", "fukk", "fck", "fcks",
    "bitch", "bitches", "bitchy", "bastard", "bastards", "asshole",
    "assholes", "ass", "asses", "arse", "arses", "cunt", "cunts",
    "dick", "dicks", "dickhead", "dickheads", "pussy", "pussies",
    "slut", "sluts", "slutty", "skank", "whore", "whores", "whoring",
    "motherfucker", "motherfuckers", "shit", "shits", "shitty",
    "shitting", "bullshit", "horseshit", "crap", "crappy", "piss",
    "pissed", "pissing", "wanker", "wankers", "bollocks", "bugger",
    "buggers", "bloody", "nigg", "nigger", "niggers", "nigga", "niggas",
    "fag", "fags", "faggot", "faggots", "retard", "retards", "retarded",
    "moron", "morons", "idiot", "idiots", "idiotic", "stupid",
    "dumbass", "dumbasses", "jackass", "jackasses", "scumbag", "douche",
    "twat", "twats", "prick", "pricks", "cock", "cocks", "cocksucker",
    "cocksuckers", "cum", "cums", "cumming", "cumshot", "cumshots",
    "horny", "hornier", "horniest", "sexy", "sex", "sexes", "sexual",
    "screw", "screwed", "screwing", "screws", "rape", "raped", "raping",
    "rapist", "rapists", "molest", "molested", "molester", "molesters",
    "pedo", "pedos", "pedophile", "pedophiles", "pedophilia",
    "damn", "damned", "damning", "dammit", "goddamn", "jerk", "jerks",
    "jerkoff", "jerkoffs", "suck", "sucks", "sucked", "sucking",
    "sucky", "sucker", "suckers", "blowjob", "blowjobs", "handjob",
    "handjobs", "footjob", "footjobs", "rimjob", "rimjobs", "balls",
    "ballsy", "ballsack", "ballsacks", "scrotum", "testicle",
    "testicles", "testis", "testes", "penis", "penises", "vagina",
    "vaginas", "vulva", "vulvas", "clitoris", "clits", "clit", "boob",
    "boobs", "booby", "boobies", "tit", "tits", "titties", "titty",
    "nipple", "nipples", "areola", "areolas", "breast", "breasts",
    "butt", "butts", "butthole", "buttholes", "anus", "anuses", "anal",
    "orgasm", "orgasms", "orgasmic", "masturbate", "masturbated",
    "masturbating", "masturbation", "masturbator", "masturbators",
    "porn", "porno", "pornos", "pornography", "pornographic", "nsfw",
    "hentai", "hentais", "incest", "incests", "bestiality", "zoophile",
    "zoophiles", "zoophilia", "bdsm", "bondage", "fetish", "fetishes",
    "fetishist", "fetishists", "milf", "milfs", "dilf", "dilfs",
    "gilf", "gilfs", "camgirl", "camgirls", "camwhore", "camwhores",
    "escort", "escorts", "escorting", "prostitute", "prostitutes",
    "prostitution", "hooker", "hookers", "streetwalker",
    "streetwalkers", "gigolo", "gigolos", "pimp", "pimps", "pimping",
    "thot", "tramp", "wank", "tosser", "git", "nob", "arsed",
    "pillock", "plonker", "sod", "jizz", "fap",
]

# عبارت‌های چندکلمه‌ای (با حذف فاصله‌ها هم بررسی می‌شوند)
BASE_PHRASES = [
    "کس خوار", "کس ده", "کس ننه", "کس مامان", "کس خواهر",
    "کون خوار", "کون ده", "کون مامان", "کون خواهر",
    "کیر خور", "کیر مامان", "کیر خواهر", "کیر ننه",
    "خار کوسه", "خار کس", "خار کون", "خار کیر", "کس خار", "کس خیس",
    "جون کس", "جون کیر", "جون کون",
    "کیر کون", "کیر تو کون", "کیر تو کس", "کیر تو دهن", "کس تو کون",
    "دختر کس", "پسر کس", "دختر کون", "پسر کون",
    "مادر کص", "مادر کس", "مادر قحبه", "مادر جنده", "مادر خراب", "مادر سگ",
    "ننه کص", "ننه کس", "خواهر کص", "خواهر کس",
    "پدر سگ", "پدر سوخته", "پدر قحبه", "پدر جنده",
    "حرومزاده", "حروم زاده", "حرام زاده", "حروم خور", "حرام خور",
    "حرومزاده کص", "کیر مامه",
    "بی ناموس", "بی ناموسی", "ناموس فروش",
    "بی غیرت", "بی غیرتی", "بی شرف", "بی شرفی",
    "بی آبرو", "بی آبرویی", "آبرو ریز", "آبرو ریزی",
    "پست فطرت", "پست ذات", "پست نژاد",
    "سگ صفت", "سگ زاده", "خوک صفت", "خوک زاده",
    "برو بمیر", "گور بگور", "میری جهنم", "جهنمی", "لعنتت", "لعنت بهت",
    "ناموست", "ناموسیت", "اجدادت", "جدت", "جدت رو", "آب جو",
    "کیر اسب", "کون گشاد", "ممه بگیر",
    "fuck you", "fuck off", "screw you", "go to hell", "son of a",
    "son of a bitch", "son of a whore",
    "mother fucker", "mother fuckers", "go fuck yourself",
    "kiss my ass", "shut the fuck up", "shut your mouth", "shut up",
    "piece of shit", "piece of crap", "pile of shit", "pile of crap",
    "holy shit", "holy crap", "bull shit", "bull crap",
    "jack off", "jerk off", "beat off", "beat it", "damn you", "you suck",
    "blow job", "hand job", "foot job", "rim job",
    "ball sack", "balls sack", "sack of balls",
    "dick head", "dick heads", "cock sucker", "cock suckers",
    "ass hole", "ass holes", "ass wipe", "ass wipes",
    "cum shot", "cum shots", "cum bag", "cum bags",
    "sugar daddy", "sugar daddies", "sugar baby", "sugar babies",
    "sugar mommy", "sugar mommies", "cam girl", "cam girls",
    "cam whore", "cam whores", "street walker", "street walkers",
]

# واژه‌های سالمی که نباید به اشتباه مسدود شوند — محافظ substring:
# هر واژه مسدودِ ۳نویسه‌به‌بالا که داخل یکی از این‌ها بیاید، به‌کلی از تطبیق
# substring خارج می‌شود (توکن دقیق همچنان گرفته می‌شود).
BASE_WHITELIST = [
    "نمک", "نمکی", "شخص", "شخصی", "شخصیت", "مکث", "سکسکه", "سکسکهها",
    "همکار", "همکاری", "کسالت", "کسالتی", "مکس", "دکس", "ساکس", "پکینک",
    "فوکس", "مرکسب", "دکستر", "دوست", "دوستی", "دوستانه", "دوستت",
    "مادر", "مادری", "مادران", "مادرانه", "مادرت", "مادرش",
    "معوجات", "فحشا", "فحشایی", "شقایق", "دلقک", "دلقکی",
    "قلم", "کیس", "بیمار", "پدر", "پدرم", "خواهر", "خواهرم", "برادر",
    "عمه", "مامه", "دایی", "عمو", "جد", "ننه", "مامان", "جون", "دل", "جانم",
    "شغل", "شاخه", "شاخهها", "درخت", "گیاه", "حیوان", "پستاندار",
    "کفشدوزک", "اسباب", "بزغاله", "گاوصندوق", "مغز", "شعور", "احترام",
    "آدم", "انسانی", "بشر", "بشریت",
    # محافظ واژه‌های مسدود پرخطا (خرید/نفهمید/دولت/زنان/گوهر/الاغ/دزد...)
    "خرید", "خریدم", "خریدی", "خریدیم", "خریدند", "خریدن", "خریدار",
    "خریده", "خریدهها", "خریدنی", "خریدهای",
    "نفهمید", "نفهمیدم", "نفهمیدی", "نفهمیدیم", "نفهمیدید", "نفهمیدند",
    "نفهمیدن",
    "دولت", "دولتی", "دولتها", "دولتمرد", "دولتمردان",
    "زنان", "زنانه", "زنانی", "زنانگی", "زنانها", "زناند",
    "گوهر", "گوهری", "گوهرها", "گوهرشاد", "گوهرهاش",
    "روبهرو", "هیزم", "هیزمها", "دزدگیر", "دزدگیرها", "دزدگیری",
    "احمقانه", "احمقانهتر", "دیوانهوار", "دیوانهوارتر",
    "کوسه", "کوسهها", "کصه", "کونیا", "کونیاک", "خوکچه", "خوکچهها",
    "سگماهی", "سگماهیان", "الاغچه", "خربزه",
    "سگدستی", "خریدارها", "فحاشا",
    # محافظ واژه‌های انگلیسی مسدود (ass/cum/tit/hoe/anal/rape/cock/arse/
    # nob/sod/git/butt/balls/breast/penis/anus/pimp)
    "pass", "password", "passport", "class", "classes", "classic",
    "glass", "glasses", "grass", "bass", "mass", "masses", "embassy",
    "passage", "passive", "assault", "assassin", "asset", "assets",
    "document", "documents", "documentation", "circumstance",
    "circumstances", "cumulative", "accumulate", "accumulated",
    "succumb", "circumvent",
    "title", "titles", "institution", "institutions", "titan",
    "titanic", "titanium",
    "peacock", "cocktail", "cocktails", "shoe", "shoes", "horseshoe",
    "analysis", "analyses", "analytics", "analyze", "analogue",
    "arsenal", "arsenic", "noble", "nobel", "nobility", "snob",
    "snobs", "sodium", "soda", "sodas", "digit", "digits", "digital",
    "legitimate", "button", "buttons", "butter", "butterfly",
    "basketball", "basketballs", "baseballs", "volleyballs",
    "breastcancer", "breastfeeding", "breastfeed", "breastfed",
    "breaststroke", "pimple", "pimples", "pimply", "grape", "grapes",
    "grapefruit", "scrape", "scraped", "scrapes", "drape", "drapes",
    "peninsula", "peninsulas", "uranus", "janus", "trampoline",
]

WORD_RE = re.compile(r"[\w\u0600-\u06FF]+", re.UNICODE)


def normalize_text(text: str) -> str:
    """نرمال‌سازی حروف فارسی/عربی، حذف نقطه‌های حرکتی، کشیدگی و کاراکترهای نامرئی."""
    if not text:
        return ""
    t = unicodedata.normalize("NFC", str(text))
    for zw in _ZERO_WIDTH:
        t = t.replace(zw, "")
    t = t.translate(_AR_TO_FA)
    t = t.lower()
    # جداکننده‌های متداول نقطه‌گذاری به فاصله تبدیل می‌شوند
    t = re.sub(r"[\W_]+", " ", t, flags=re.UNICODE)
    t = re.sub(r"\s+", " ", t).strip()
    return t

def _collapse(s: str) -> str:
    return re.sub(r"(.)\1+", r"\1", s)

def _leet_norm(tok: str) -> str:
    return tok.translate(_LEET)

def get_word_sets():
    """(blocked_set, phrases, whitelist_set) — ترکیب پایه + تنظیمات مالک (واژه‌ها نرمال‌سازی می‌شوند)."""
    cfg = STORE.get("profanity_words")
    removed = set(cfg.get("removed_defaults", []))
    blocked = {w for w in BASE_PROFANITY if w not in removed}
    phrases = [p for p in BASE_PHRASES if p not in removed]
    whitelist = set(BASE_WHITELIST)
    for w in cfg.get("custom_blocked", []):
        nw = normalize_text(w)
        if not nw:
            continue
        if " " in nw:
            phrases.append(nw)
        else:
            blocked.add(nw)
    for w in cfg.get("custom_whitelist", []):
        nw = normalize_text(w)
        if nw:
            whitelist.add(nw)
    blocked.update(w.lower() for w in cfg.get("custom_blocked", []) if normalize_text(w) == w.lower())
    return blocked, phrases, whitelist


_URL_RE = re.compile(r"(?:https?://|www\.)\S+", re.IGNORECASE)


def strip_urls(text: str) -> str:
    """حذف لینک‌ها پیش از بررسی فحاشی. الحاق توکن‌های URL به کلمات عادی
    (مثل sex داخل httpsexample) false-positive می‌ساخت."""
    return _URL_RE.sub(" ", text or "")


def detect_profanity(text: str):
    """
    تشخیص محتوای توهین‌آمیز فارسی/انگلیسی.
    خروجی: None اگر پاک باشد؛ در غیر این صورت (matched_terms, version).
    کاهش تشخیص اشتباه: whitelist روی تک‌واژه‌ها و عبارت‌ها اعمال می‌شود.
    """
    norm = normalize_text(strip_urls(text))
    if not norm:
        return None
    blocked, phrases, whitelist = get_word_sets()

    tokens = norm.split()
    matched = []
    for tok in tokens:
        cands = {tok, _collapse(tok), _leet_norm(tok), _leet_norm(_collapse(tok))}
        hit = None
        for c in cands:
            if c in whitelist:
                hit = None
                break
            if c in blocked:
                hit = c
        if hit:
            matched.append(hit)

    # عبارت‌های چندکلمه‌ای + فاصله‌گذاری غیرعادی (حذف کامل فاصله‌ها)
    squeezed = norm.replace(" ", "")
    for ph in phrases:
        ph_s = ph.replace(" ", "")
        if not ph_s:
            continue
        # تطبیق مقاوم: حروف هر عبارت ممکن است تکرار شده باشند («کووون خوار»)
        # اما الگوی حروف باید دقیقاً و به‌ترتیب بیاید؛ «ممه بده» در «مهربان بده» نمی‌گیرد.
        pat = "".join(re.escape(ch) + "+" for ch in ph_s)
        if re.search(pat, squeezed):
            # اگر تک‌واژه‌ی کاملاً سالمی کل عبارت را پوشش داده باشد، صرف‌نظر
            if any(ph_s in w and w in whitelist for w in whitelist):
                continue
            matched.append(ph)

    # جداسازی با نقطه‌گذاری/جداکننده‌ها («ک.ی.ر») — فقط واژه‌های ۳ نویسه به بالا
    # تا اعداد و متن‌های عادی به اشتباه مسدود نشوند
    for term in blocked:
        if len(term) >= 3 and term not in whitelist:
            term_pat = "".join(re.escape(ch) + "+" for ch in term)
            if not re.search(term_pat, squeezed):
                continue
            # محافظت whitelist span-محور: اگر واژه سالمی (مثل «سکسکه» در برابر «سکس»)
            # همه وقوع‌های این ترم را در بر بگیرد، تخلف نیست؛ وقوع بیرون واژه سالم
            # (مثل «ک س ک س») همچنان مسدود می‌شود.
            guard_words = [w for w in whitelist if len(w) > len(term) and term in w]
            if guard_words:
                spans = [m.span() for m in re.finditer(term_pat, squeezed)]
                covered = []
                for w in guard_words:
                    w_pat = "".join(re.escape(ch) + "+" for ch in w)
                    covered += [m.span() for m in re.finditer(w_pat, squeezed)]
                if all(any(cs[0] <= ts[0] and ts[1] <= cs[1] for cs in covered)
                       for ts in spans):
                    continue
            matched.append(term)

    if matched:
        return (sorted(set(matched)), PROFANITY_VERSION)
    return None

# ============================================================
# 7.5) سیستم محافظت هوشمند کاربران — تشخیص سه‌سطحی توهین جنسیتی /
#      آزار جنسی کلامی در گفت‌وگوهای دختر-پسر + سکوت دقیق، محدودیت
#      فوق‌العاده (۱ چت در بازه ۶۰ دقیقه)، منع چت با دختران و
#      مجازات مرحله‌ای. مستقل از فیلتر فحاشی عمومی است.
#      جنسیت فقط از اطلاعات ثبت‌نام استفاده می‌شود.
# ============================================================

# عبارت‌های تحقیر جنسیتی (سطح ۱) — پس از نرمال‌سازی و حذف فاصله‌ها بررسی می‌شوند
GENDER_CONTEMPT_PHRASES = [
    "دخترا همه", "دختر ها همه", "پسرا همه", "پسر ها همه",
    "زنا همه", "زن ها همه", "مردا همه", "مرد ها همه",
    "همه دخترا", "همه پسرا", "همه زنا", "همه مردا",
    "دخترا کلا", "پسرا کلا", "زنا کلا", "مردا کلا",
    "همه تون مثل هم", "همه تون یکی", "همتون یکی", "همتون مثل هم",
    "ننگ زن بودن", "ننگ مرد بودن", "ننگ دختر بودن", "ننگ پسر بودن",
    "ننگ جنسیت", "حالت دخترانه", "حالت پسرانه",
    "مثل همه دخترا", "مثل همه پسرا",
    # تکمیلی — تحقیر جنسیتی رایج (سیستم محافظت خانم‌ها)
    "دخترا بیارزش", "دخترا کیسه", "دخترا حریص", "دخترا مادی",
    "زنا بیارزش", "زنا حریص", "زنا مادی", "زنا عوضی",
    "دخترا مال", "زنا مال", "دخترا وسیله", "زنا وسیله",
    "شغل دخترا", "شغل زنا", "کارت چیه دختر", "همه دخترا مثل هم",
    "دختر واقعی نمی", "زن واقعی نمی", "دخترا همیشه", "زنا همیشه",
    "بدبخت از زنا", "بدبختی از زنا", "دردسر از زنا", "دغدغه از زنا",
    "دخترا دروغگو", "زنا دروغگو", "دخترا خیانتکار", "زنا خیانتکار",
    "بدون دخترا بهتر", "بدون زنا بهتر", "دنیا بدون زنا",
    "زن زن است", "دختر دختر است", "همهشون یکی", "همه‌شون یکی",
]

# آزار جنسی کلامی مستقیم و درخواست جنسی صریح (سطح ۳)
SEXUAL_HARASS_PHRASES = [
    "عکس کیر", "عکس کون", "عکس سینه", "عکس سکس", "عکس لخت", "عکس دونده",
    "عکس بدن بده", "عکس بدنت", "عکس نده",
    "ویدیو سکس", "وید سکس", "ویدیو لخت", "وید لخت",
    "بدنت نشون", "بدن نشون بده", "سینه نشون", "خودت لخت", "لخت شو",
    "لخت کن", "کیر بده", "کیر نشون", "کون نشون", "سکس بده",
    "سکس کنیم", "سکس کنیم", "بیا سکس", "چت سکسی", "چت سکس",
    "میخوام سکس", "می خوام سکس", "میخوام کیر", "می خوام کون",
    "ببین کیر", "ببین سینه", "سینه ببین", "بدن ببین",
    # تکمیلی — درخواست‌های جنسی رایج (سیستم محافظت خانم‌ها)
    "بیا کیر", "کیرتو", "کیرت رو", "کص کنیم", "بیا کص", "میخوام کص",
    "می خوام کص", "کون بده", "کونتو", "کونت رو", "کس بده", "کستو", "کست رو",
    "سینه بده", "سینه‌هات", "سینه هات", "ممه بده", "ممه‌هات", "ممه هات",
    "بکنیم", "میخوام بکنمت", "می خوام بکنمت", "بکنمت", "گایدنت", "میخوام گایدنت",
    "بخواب", "بخوابم باهات", "بخواب باهات", "بیا بخوابیم", "همبخوابی",
    "شب باهام", "بیا خونه", "بیا خونه ام", "تنهایی هستی", "پارتنر سکسی",
    "رابطه بده", "رابطه جنسی", "رابطه داشته باشیم", "بیا رابطه",
    "فری سکس", "سکس فون", "سکس تلفنی", "سکس چت", "سکسی چت",
    "هات چت", "هات چی", "دلخوری سکسی", "چت بزرگسالا", "چت جندها",
    "تن‌خواه", "تن خواه", "فقط سکس", "دنبال سکس", "هدفم سکس",
    # انگلیسی
    "send nudes", "send nude", "nude pic", "dick pic", "show boobs",
    "show tits", "show body", "wanna sex", "want sex", "sex chat",
    "horny", "sexy pic", "nudes", "trade nudes", "cam sex", "phone sex",
    "sext me", "send pic", "send pics", "boobs pic", "tits pic",
    "come sex", "let's sex", "fuck me", "fuck you", "suck my", "blow me",
    "come here sex", "sleep with me", "hookup", "one night",
]

# توهین‌های جنسی (سطح ۱ و ۲) — ترکیب با فحاشی شدید سطح را بالا می‌برد
SEXUAL_INSULT_TERMS = [
    "جنده", "قحبه", "فاحشه", "حشری", "کسخل", "کوسخل", "خارکوسه",
    "خارکس", "بی حیا", "بیحیا", "چوچول", "لوده", "ساه", "گایید",
    # تکمیلی — توهین جنسیتی مستقیم به خانم‌ها
    "دخترفاحشه", "زنفاحشه", "دخترجنده", "زنجنده", "دخترقحبه", "زنقحبه",
    "کسناز", "کصناز", "دستمال", "دستمالکص", "بیعفت", "بیعفت",
    "عفتفروش", "لوش", "لاشی", "سودوفروش", "کسباز", "کونباز",
    "پرتیت", "پرتیت ها", "مردبار", "مردآبار", "ولگرد",
]

# نشانه‌های نقل‌قول/توضیح/آموزش — اگر پیش از عبارتِ یافت‌شده بیایند، آن
# مورد «زمینه سالم» حساب می‌شود و تخلف شمرده نمی‌شود
CONTEXT_SAFE_PRECEDERS = {
    "مثل", "مثلا", "مثلاً", "یعنی", "توضیح", "قانون", "قوانین", "هشدار",
    "ممنوع", "فیلتر", "تخلف", "گزارش", "دوری", "اجتناب", "نکنید", "نکن",
    "نباید", "بدون", "حتی", "بنام", "بهنام", "سیستم", "سامانه", "ربات",
}

WINDOW_MINUTES_SUPER = 60   # بازهٔ محدودیت فوق‌العاده: ۱ چت جدید در هر ۶۰ دقیقه


def get_protection() -> dict:
    """تنظیمات سیستم محافظت با ادغام عمیق پیش‌فرض‌ها (سازگار با دیتای قدیمی)."""
    ensure_storage()
    p = STORE.get("protection")
    if not isinstance(p, dict):
        p = {}
    out = dict(DEFAULT_PROTECTION)
    for k, v in p.items():
        if isinstance(DEFAULT_PROTECTION.get(k), dict) and isinstance(v, dict):
            merged = dict(DEFAULT_PROTECTION[k])
            merged.update(v)
            out[k] = merged
        else:
            out[k] = v
    return out


def set_protection(mutator) -> dict:
    def _m(d):
        mutator(d)
        return d
    return STORE.update("protection", _m)


def _phrase_hits(phrases, tokens, squeezed, squeezed_c, whitelist) -> list:
    """یافتن عبارت‌ها با مقاومت در برابر فاصله‌گذاری غیرعادی و تکرار حروف؛
    مواردی که با «نشانه زمینه سالم» (نقل‌قول/توضیح) آمده‌اند حذف می‌شوند.
    تطبیق تکرار حروف با الگوی regex دقیق است تا «ممه بده» در «مهربان بده» گیر نیفتد."""
    hits = []
    for ph in phrases:
        ph_n = normalize_text(ph)
        ph_s = ph_n.replace(" ", "")
        if not ph_s or ph_s in whitelist:
            continue
        pat = "".join(re.escape(ch) + "+" for ch in ph_s)
        if not re.search(pat, squeezed):
            continue
        # بررسی زمینه: توکن پیش از محل وقوع (نقل‌قول/توضیح/ممنوع/قانون...)
        ctx_ok = True
        first = ph_n.split()[0] if ph_n.split() else ""
        if first:
            for i, tok in enumerate(tokens):
                if tok == first:
                    prev = tokens[i - 1] if i > 0 else ""
                    if prev in CONTEXT_SAFE_PRECEDERS:
                        ctx_ok = False
                    break
        if ctx_ok:
            hits.append(ph)
    return hits


def _token_hits(blocked: set, whitelist: set, tokens) -> list:
    hits = []
    for tok in tokens:
        cands = {tok, _collapse(tok), _leet_norm(tok), _leet_norm(_collapse(tok))}
        hit, safe = None, False
        for c in cands:
            if c in whitelist:
                safe = True
                break
            if c in blocked:
                hit = c
        if hit and not safe:
            hits.append(hit)
    return hits


def analyze_protection(sender: dict, partner: dict, text: str,
                       is_reply: bool = False):
    """
    تشخیص سه‌سطحی تخلف در گفت‌وگوهای دختر-پسر.
    خروجی: None یا (level, matched_terms)
      سطح ۱: توهین جنسیتی / فحاشی مکرر (۲+ واژه رکیک در یک پیام)
      سطح ۲: توهین شدید + فحاشی رکیک
      سطح ۳: آزار جنسی کلامی / تحقیر جنسیتی + فحاشی رکیک / ترکیب بسیار شدید
    قواعد کاهش تشخیص اشتباه:
      • جنسیت فقط از ثبت‌نام (هرگز از نام یا متن حدس زده نمی‌شود)
      • پیام‌های نقل‌قول‌شده (ریپلای) بررسی نمی‌شوند
      • عبارت‌های دارای «نشانه زمینه سالم» (توضیح/مثال/ممنوع/قانون...) نادیده
      • واژه‌های دارای کاربرد عادی (whitelist مثل «سکسکه») مسدود نمی‌شوند
    """
    prot = get_protection()
    if not prot.get("enabled", True):
        return None
    gs, gp = sender.get("gender"), partner.get("gender")
    if not gs or not gp:
        return None  # جنسیت فقط از ثبت‌نام (هرگز از نام یا متن حدس زده نمی‌شود)
    mixed = gs != gp
    if is_reply:
        return None
    norm = normalize_text(strip_urls(text))
    if not norm:
        return None
    blocked, _phrases, whitelist = get_word_sets()
    tokens = norm.split()
    squeezed = norm.replace(" ", "")
    squeezed_c = _collapse(squeezed)

    harass = _phrase_hits(SEXUAL_HARASS_PHRASES, tokens, squeezed, squeezed_c, whitelist)
    # آزار جنسی کلامی (سطح ۳) در «همه» گفت‌وگوها محافظت می‌شود —
    # قربانیِ هم‌جنس هم از درخواست‌های جنسی صریح محفوظ است (تقویت سیستم محافظت خانم‌ها).
    if harass:
        if not prot.get("level_enabled", {}).get("3", True):
            return None
        return 3, (harass)[:6]
    if not mixed:
        return None  # توهین جنسیتی فقط در گفت‌وگوهای دختر-پسر
    insults = _phrase_hits(SEXUAL_INSULT_TERMS, tokens, squeezed, squeezed_c, whitelist)
    contempt = _phrase_hits(GENDER_CONTEMPT_PHRASES, tokens, squeezed, squeezed_c, whitelist)
    heavy = [h for h in _token_hits(blocked, whitelist, tokens)
             if h not in whitelist]
    # فحاشی نیم‌فاصله‌ای/چسبیده در عبارت‌ها هم پوشش داده می‌شود
    # (تطبیق تکرار حروف با الگوی regex دقیق تا واژه‌های دوبل false-positive ندهند؛
    # محافظ whitelist span-محور وقوع داخل واژه سالم را مجاز می‌کند)
    if not heavy:
        for w in blocked:
            if len(w) < 4 or w in whitelist:
                continue
            w_pat = "".join(re.escape(ch) + "+" for ch in w)
            if not re.search(w_pat, squeezed):
                continue
            guard_words = [g for g in whitelist if len(g) > len(w) and w in g]
            if guard_words:
                spans = [m.span() for m in re.finditer(w_pat, squeezed)]
                covered = []
                for g in guard_words:
                    g_pat = "".join(re.escape(ch) + "+" for ch in g)
                    covered += [m.span() for m in re.finditer(g_pat, squeezed)]
                if all(any(cs[0] <= ts[0] and ts[1] <= cs[1] for cs in covered)
                       for ts in spans):
                    continue
            heavy.append(w)

    level = None
    if harass:
        level = 3
    elif contempt and heavy:
        level = 3   # تحقیر جنسیتی + فحاشی رکیک = بسیار شدید
    elif insults and heavy:
        level = 2
    elif len(insults) >= 2:
        level = 2
    elif contempt or insults:
        level = 1
    elif len(heavy) >= 2:
        level = 1   # فحاشی مکرر (۲+ واژه رکیک) در چت دختر-پسر
    if level is None:
        return None
    if not prot.get("level_enabled", {}).get(str(level), True):
        return None  # این سطح توسط مالک خاموش شده است
    matched = (harass + insults + contempt + heavy)[:6]
    return level, matched


# ---------- سکوت دقیق (محدودیت کامل شروع گفت‌وگوی جدید) ----------

def mute_remaining_minutes(u) -> int:
    """دقیقه باقی‌مانده سکوت؛ ۰ یعنی فعال نیست (وضعیت منقضی نیز پاک می‌شود)."""
    if not u:
        return 0
    mu = u.get("mute_until")
    if not mu:
        return 0
    try:
        rem = parse_iso(mu) - now_utc()
    except Exception:
        return 0
    if rem.total_seconds() <= 0:
        update_user(u["tg"], lambda x: x.update({"mute_until": None}))
        return 0
    return int(rem.total_seconds() // 60) + 1


# ---------- محدودیت فوق‌العاده (۱ چت جدید در هر بازه ۶۰ دقیقه) ----------

def super_limit_active(u) -> bool:
    if not u:
        return False
    su = u.get("super_until")
    if not su:
        return False
    try:
        if parse_iso(su) > now_utc():
            return True
    except Exception:
        return True
    update_user(u["tg"], lambda x: x.update(
        {"super_until": None, "super_last_chat": None, "super_case": None}))
    return False


def super_start_block_minutes(u):
    """اگر شروع چت جدید در بازه ۶۰ دقیقه‌ای بسته باشد، دقیقه باقی‌مانده؛ وگرنه None.
    فقط شروع چت جدید را کنترل می‌کند و مستقل از سکوت و بن است."""
    if not super_limit_active(u):
        return None
    last = u.get("super_last_chat")
    if not last:
        return None  # هنوز در این محدودیت چت جدیدی شروع نکرده است
    try:
        elapsed = now_utc() - parse_iso(last)
    except Exception:
        return None
    window = timedelta(minutes=WINDOW_MINUTES_SUPER)
    if elapsed >= window:
        return None
    return int((window - elapsed).total_seconds() // 60) + 1


def mark_new_chat_started(tg: int):
    """ثبت شروع چت جدید برای کنترل بازه محدودیت فوق‌العاده."""
    update_user(tg, lambda u: u.update({"super_last_chat": iso_utc(now_utc())}))


def apply_super_limit(tg_id: int, minutes: int, case: str = None,
                      by: str = "system:protection") -> bool:
    if is_owner(int(tg_id)) or minutes <= 0:
        return False
    until = iso_utc(now_utc() + timedelta(minutes=minutes))
    update_user(int(tg_id), lambda u: u.update(
        {"super_until": until, "super_case": case or u.get("super_case")}))
    modlog(by, f"super_limit_{minutes}m", tg_id, case or "")
    return True


def release_super_limit(tg_id: int, by: str = "owner") -> bool:
    update_user(int(tg_id), lambda u: u.update(
        {"super_until": None, "super_last_chat": None, "super_case": None}))
    modlog(by, "super_limit_remove", tg_id)
    return True


# ---------- منع چت با دختران (قابل مدیریت از پنل) ----------

def girl_block_state(u) -> str:
    """none | timed | perm"""
    if not u:
        return "none"
    gb = u.get("girl_block_until")
    if gb == "perm":
        return "perm"
    if gb:
        try:
            if parse_iso(gb) > now_utc():
                return "timed"
        except Exception:
            return "timed"
        update_user(u["tg"], lambda x: x.update(
            {"girl_block_until": None, "girl_block_case": None}))
    return "none"


def apply_girl_block(tg_id: int, hours: int = 0, case: str = None,
                     by: str = "system:protection") -> bool:
    """hours=0 یعنی دائمی (همچنین از پنل مالک هر زمان قابل لغو است)."""
    if is_owner(int(tg_id)):
        return False
    until = "perm" if hours <= 0 else iso_utc(now_utc() + timedelta(hours=hours))
    update_user(int(tg_id), lambda u: u.update(
        {"girl_block_until": until, "girl_block_case": case or u.get("girl_block_case")}))
    modlog(by, "girl_block_perm" if hours <= 0 else f"girl_block_{hours}h", tg_id)
    return True


def release_girl_block(tg_id: int, by: str = "owner") -> bool:
    update_user(int(tg_id), lambda u: u.update(
        {"girl_block_until": None, "girl_block_case": None}))
    modlog(by, "girl_block_remove", tg_id)
    return True


# ---------- پرونده‌های تخلف (سابقه امنیتی) و مجازات مرحله‌ای ----------

def confirmed_level3_count(uid: int, exclude_case: str = None) -> int:
    out = 0
    for v in STORE.get("violations"):
        if (str(v.get("uid")) == str(int(uid)) and int(v.get("level") or 0) == 3
                and not v.get("revoked") and v.get("case") != exclude_case):
            out += 1
    return out


def protection_stage_of(uid: int) -> int:
    """مرحله فعلی مجازات مرحله‌ای بر اساس تخلفات تأییدشده سطح ۳."""
    prot = get_protection()
    thr = max(1, int(prot.get("escalation_threshold", 1)))
    prior = confirmed_level3_count(uid)
    return min(5, prior // thr)


def create_violation(uid: int, level: int, matched: list, conv_id: str,
                     mute_minutes: int, stage: int = 0, ban_hours: int = 0) -> dict:
    vid = "v" + os.urandom(5).hex()
    case = "pc" + os.urandom(5).hex()
    rec = {
        "vid": vid, "case": case, "uid": str(int(uid)), "level": int(level),
        "matched": [str(m)[:40] for m in (matched or [])][:6],
        "conv": conv_id or "", "created": iso_utc(now_utc()),
        "mute_minutes": int(mute_minutes), "stage": int(stage),
        "ban_hours": int(ban_hours), "revoked": False,
        "revoked_by": None, "revoke_reason": None, "appeal": None,
    }

    def _m(lst):
        lst.append(rec)
        return lst
    STORE.update("violations", _m)
    return rec


def appealable_violation(uid: int):
    """پرونده‌ای از این کاربر که مجازات فعالِ قابل اعتراض دارد و هنوز اعتراضی ثبت نشده."""
    for v in reversed(STORE.get("violations")):
        if str(v.get("uid")) != str(int(uid)) or v.get("revoked") or v.get("appeal"):
            continue
        case = v.get("case")
        u = get_user(int(uid))
        if not u:
            continue
        has_active = False
        for b in STORE.get("bans"):
            if b.get("case") == case and b.get("active"):
                has_active = True   # بن یا سکوتِ فعالِ همین پرونده
        if u.get("super_case") == case and super_limit_active(u):
            has_active = True
        if u.get("girl_block_case") == case and girl_block_state(u) != "none":
            has_active = True
        if has_active:
            return v
    return None


def register_appeal(case: str, text: str, photo_id=None) -> bool:
    """ثبت اعتراض؛ هر پرونده فقط یک بار قابل اعتراض است."""
    ok = [False]

    def _m(lst):
        for v in lst:
            if v.get("case") == case:
                if v.get("appeal") or v.get("revoked"):
                    ok[0] = False
                    return lst
                v["appeal"] = {
                    "status": "pending", "text": (text or "")[:1000],
                    "photo_id": photo_id, "created": iso_utc(now_utc()),
                    "decided": None, "note": "",
                }
                ok[0] = True
                return lst
        return lst
    STORE.update("violations", _m)
    return ok[0]


def fix_case_punishments(uid: int, case: str, by: str):
    """لغو همه مجازات‌های مرتبط با یک پرونده (پس از تأیید اعتراض یا اصلاح مدیریتی)."""
    key = str(int(uid))
    now_iso = iso_utc(now_utc())
    had_mute = False

    def _m(lst):
        nonlocal had_mute
        for b in lst:
            if b.get("uid") == key and b.get("active") and b.get("case") == case:
                b["active"] = False
                b["removed_at"] = now_iso
                if b.get("type") == "mute":
                    had_mute = True
        return lst
    STORE.update("bans", _m)
    if had_mute:
        update_user(int(uid), lambda x: x.update({"mute_until": None}))
    u = get_user(int(uid))
    if u:
        if u.get("super_case") == case and super_limit_active(u):
            release_super_limit(int(uid), by=by)
        if u.get("girl_block_case") == case and girl_block_state(u) != "none":
            release_girl_block(int(uid), by=by)
    modlog(by, "case_punishments_fixed", int(uid), case)


def revoke_violation(vid: str, by: str, reason: str) -> bool:
    """لغو یک تخلف تأییدشده (تشخیص اشتباه) — دیگر در مرحله‌بندی شمرده نمی‌شود."""
    rec = next((v for v in STORE.get("violations") if v.get("vid") == vid), None)
    if not rec or rec.get("revoked"):
        return False

    def _m(lst):
        for v in lst:
            if v.get("vid") == vid:
                v["revoked"] = True
                v["revoked_by"] = by
                v["revoke_reason"] = (reason or "")[:300]
                if isinstance(v.get("appeal"), dict):
                    v["appeal"]["status"] = "approved"
                    v["appeal"]["decided"] = iso_utc(now_utc())
                return lst
        return lst
    STORE.update("violations", _m)
    fix_case_punishments(int(rec["uid"]), rec["case"], by=by)
    modlog(by, "violation_revoked", int(rec["uid"]), f"{vid} {reason}")
    return True


def decide_appeal(vid: str, decision: str, by: str, note: str = "") -> bool:
    """تأیید/رد/نگه‌داشتن اعتراض. تأیید → لغو خودکار مجازات مرتبط."""
    rec = next((v for v in STORE.get("violations") if v.get("vid") == vid), None)
    if not rec or not isinstance(rec.get("appeal"), dict):
        return False

    def _m(lst):
        for v in lst:
            if v.get("vid") == vid:
                v["appeal"]["status"] = decision
                v["appeal"]["decided"] = iso_utc(now_utc())
                v["appeal"]["note"] = (note or "")[:300]
                return lst
        return lst
    STORE.update("violations", _m)
    if decision == "approved":
        fix_case_punishments(int(rec["uid"]), rec["case"], by=by)
        revoke_violation(vid, by, f"تأیید اعتراض: {note}" if note else "تأیید اعتراض")
    modlog(by, f"appeal_{decision}", int(rec["uid"]), vid)
    return True


def appeal_kb_rows(uid: int) -> list:
    """دکمه «ثبت اعتراض» فقط وقتی پرونده قابل اعتراضی با مجازات فعال وجود دارد."""
    v = appealable_violation(uid)
    if not v:
        return []
    return [[("btn_next", f"apl_start:{v['case']}", "✉️ ثبت اعتراض")]]


def appeal_kb_rows(uid: int) -> list:
    """دکمه «ثبت اعتراض» فقط وقتی پرونده قابل اعتراضی با مجازات فعال وجود دارد."""
    v = appealable_violation(uid)
    if not v:
        return []
    return [[("btn_appeal", f"apl_start:{v['case']}", "ثبت اعتراض")]]


def notice_kb(u):
    """کیبورد اعلان‌های محدودیت: فقط اگر پرونده قابل اعتراضی باشد دکمه اعتراض می‌آید."""
    if not u:
        return None
    rows = appeal_kb_rows(int(u["tg"]))
    return imarkup(rows) if rows else None


def super_block_text(rem_minutes: int) -> str:
    return (f"⏱ <b>محدودیت فوق‌العاده فعال است:</b> در هر بازه {fa_num(WINDOW_MINUTES_SUPER)} دقیقه‌ای "
            f"فقط یک چت جدید مجاز است.\n⏳ زمان باقی‌مانده: {fa_num(rem_minutes)} دقیقه")


def protection_restriction_active(u) -> bool:
    """آیا مجازات فعالِ ناشی از سیستم محافظت (با شماره پرونده) روی کاربر است؟
    مبنای جلوگیری از دور زدن محدودیت از طریق پشتیبانی عادی."""
    if not u:
        return False
    key = str(int(u["tg"]))
    for b in STORE.get("bans"):
        if b.get("uid") == key and b.get("active") and b.get("case"):
            if b.get("type") == "mute":
                if mute_remaining_minutes(u) > 0:
                    return True
            else:
                try:
                    if b.get("type") == "perm" or parse_iso(b.get("until")) > now_utc():
                        return True
                except Exception:
                    pass
    if u.get("super_case") and super_limit_active(u):
        return True
    if u.get("girl_block_case") and girl_block_state(u) != "none":
        return True
    return False


async def handle_protection_violation(update, context, user, conv, partner,
                                      level: int, matched: list):
    """
    اجرای مجازات‌های سیستم محافظت:
      سطح ۱: خروج خودکار از چت + سکوت ۱۷ دقیقه (تنظیم‌پذیر)
      سطح ۲: خروج + سکوت ۴۳ دقیقه + ثبت در سابقه امنیتی
      سطح ۳: خروج فوری + سکوت ۵۰ دقیقه + اخطار ویژه + مجازات مرحله‌ای تکرار
    """
    bot = context.bot
    sender_tg = int(user["tg"])
    partner_tg = int(partner["tg"])
    prot = get_protection()
    minutes = int(prot.get("mute_minutes", {}).get(str(level), 17))
    stage = protection_stage_of(sender_tg)
    ban_hours = 0
    if level == 3 and stage >= 1:
        ban_hours = int(prot.get("stage_ban_hours", {}).get(str(stage), 6))

    # پایان مکالمه (هر دو طرف مطلع می‌شوند؛ جزئیات برای طرف مقابل فاش نمی‌شود)
    notifs = close_conversation(conv["id"], "protection", sender_tg)

    # ثبت پرونده و مجازات‌ها
    rec = create_violation(sender_tg, level, matched, conv["id"], minutes,
                           stage=stage, ban_hours=ban_hours)
    case = rec["case"]
    apply_mute(sender_tg, minutes, by="system:protection",
               reason=f"سیستم محافظت — سطح {fa_num(level)}", case=case)
    if ban_hours > 0:
        apply_ban(sender_tg, minutes=ban_hours * 60, by="system:protection",
                  reason=f"مجازات مرحله {fa_num(stage)} تخلف سطح ۳", case=case)
        su = prot.get("stage_super_minutes", {}).get(str(stage), 5)
        apply_super_limit(sender_tg, int(su), case=case)
        if prot.get("girl_block_enabled", True):
            if stage >= 5:
                apply_girl_block(sender_tg,
                                 int(prot.get("girl_block_stage5_hours", 0)), case=case)
            elif stage == 4:
                apply_girl_block(sender_tg,
                                 int(prot.get("girl_block_stage4_hours", 168)), case=case)
    if level == 3:
        # اخطار ویژه (سابقه اخطارها هم افزایش می‌یابد)
        wid = "w" + os.urandom(5).hex()

        def _m(lst):
            lst.append({
                "wid": wid, "uid": str(sender_tg),
                "reason": "اخطار ویژه سامانه محافظت (آزار جنسی کلامی)",
                "matched": "،".join(matched)[:200], "source": "protection",
                "special": True, "by": "system", "case": case,
                "created": iso_utc(now_utc()), "filter_version": None,
            })
            return lst
        STORE.update("warnings", _m)
        update_user(sender_tg, lambda u: u.update({"warnings": u.get("warnings", 0) + 1}))
    modlog("system:protection", f"protection_L{level}", sender_tg,
           f"case:{case} stage:{stage} ban:{ban_hours}h")

    # پیام به متخلف + دکمه اعتراض
    level_fa = {1: "توهین جنسیتی", 2: "توهین شدید جنسیتی و فحاشی رکیک",
                3: "آزار جنسی کلامی (تخلف بسیار شدید)"}[level]
    lines = [
        f"🛡 <b>مکالمه به دلیل نقض قوانین امنیتی پایان یافت.</b>",
        f"نوع تخلف: <b>{level_fa}</b>",
        f"🤫 سکوت شما: <b>{fa_num(minutes)} دقیقه</b> (شروع چت جدید، چت بعدی و صف انتظار بسته است)",
    ]
    if ban_hours > 0:
        lines.append(f"⛔ بن مرحله‌ای: <b>{fa_num(ban_hours)} ساعت</b> "
                     f"(مرحله {fa_num(stage)} تکرار)")
        su_min = int(prot.get("stage_super_minutes", {}).get(str(stage), 5))
        su_txt = f"{fa_num(su_min // 60)} ساعت" if su_min >= 60 else f"{fa_num(su_min)} دقیقه"
        lines.append(f"⏱ محدودیت فوق‌العاده فعال شد "
                     f"(در هر ۶۰ دقیقه فقط یک چت جدید، مدت کل: {su_txt})")
    if level == 3:
        lines.append("⚠️ یک اخطار ویژه در پرونده امنیتی شما ثبت شد.")
        if stage >= 1:
            lines.append("سابقه تخلفات قبلی شما بررسی و مجازات مرحله‌ای اعمال شد.")
    lines.append("اگر تصمیم را اشتباه می‌دانید، فقط یک بار برای این پرونده می‌توانید اعتراض ثبت کنید.")
    kb = imarkup([[("btn_appeal", f"apl_start:{case}", "ثبت اعتراض")]])
    await send_text(bot, sender_tg, "\n".join(lines), kb)
    for tg, t in notifs:
        if tg != sender_tg:
            await send_text(bot, tg, t, main_menu_kb())

# ============================================================

_IR_MOBILE_RE = re.compile(
    r"(?<!\d)(?:\+{0,2}9\s?8|0[\s.\-]?|9\s?8)[\s.\-]?9[\s.\-]?\d{2}[\s.\-]?\d{3}[\s.\-]?\d{4}(?!\d)"
)
_INTL_RE = re.compile(r"(?<![\d])(\+[\d\s.\-]{7,17}\d)(?!\d)")
_TG_LINK_RE = re.compile(
    r"(?:https?://)?(?:www\.)?(?:t\.me|telegram\.me|telegram\.dog)/\S+", re.IGNORECASE
)
_INVITE_RE = re.compile(r"(?:t\.me|telegram\.me|telegram\.dog)/(?:\+|joinchat/)", re.IGNORECASE)
_WEB_RE = re.compile(
    r"(?:https?://[^\s]+)|(?:www\.[A-Za-z0-9\-_]+\.[A-Za-z]{2,}[^\s]*)|"
    r"(?<![\w@.])[A-Za-z0-9\-]{2,}(?:\.[A-Za-z0-9\-]{2,})*\."
    r"(com|org|net|ir|io|co|me|gg|xyz|info|site|online|shop|app|dev|blog|news|tv|cc|ru|uk|de|fr|us|top|club|link|store|tech|space|website|live|vip|biz|pro|ai|fun|page|wang|art)(?![\w])",
    re.IGNORECASE,
)
_HANDLE_RE = re.compile(r"(?<![\w@])@([A-Za-z0-9_]{4,32})\b")
_DIGITS_RE = re.compile(r"(?<![\d.])\d{7,14}(?![\d.])")

CONTACT_LABELS = {
    "ir_mobile": "شماره موبایل ایران",
    "intl_phone": "شماره بین‌المللی",
    "tg_numeric": "شناسه عددی تلگرام",
    "bot_id": "شناسه اختصاصی ربات",
    "handle": "آیدی متنی (@)",
    "tg_link": "لینک تلگرام",
    "invite_link": "لینک دعوت گروه و کانال",
    "web_link": "لینک وب",
}

# هر دسته تشخیص به کدام تنظیم فرمت (پنل مدیریت فرمت‌ها) متصل است
CONTACT_TO_FORMAT = {
    "ir_mobile": "phone",
    "intl_phone": "phone",
    "tg_numeric": "tg_id",
    "handle": "tg_id",
    "bot_id": "bot_id",
    "tg_link": "invite_link",
    "invite_link": "invite_link",
    "web_link": "web_link",
}


def detect_contacts(text: str) -> dict:
    """دسته‌بندی اطلاعات تماس در متن؛ خروجی: {category: [نمونه‌ها]}"""
    if not text:
        return {}
    raw = str(text)
    norm = en_num(raw)
    found = {}

    def add(cat, sample):
        found.setdefault(cat, [])
        if sample not in found[cat]:
            found[cat].append(sample[:48])

    # لینک‌های تلگرام (دعوت یا ساده)
    tg_spans = []
    for m in _TG_LINK_RE.finditer(norm):
        span = (m.start(), m.end())
        tg_spans.append(span)
        s = m.group(0)
        if _INVITE_RE.search(s):
            add("invite_link", s)
        else:
            add("tg_link", s)

    def in_tg_span(s, e):
        return any(not (e <= a or s >= b) for a, b in tg_spans)

    # لینک وب
    for m in _WEB_RE.finditer(norm):
        if in_tg_span(m.start(), m.end()):
            continue
        add("web_link", m.group(0))

    # آیدی متنی
    for m in _HANDLE_RE.finditer(norm):
        add("handle", m.group(0))

    # شماره موبایل ایران (نمونه‌ها با جداکننده‌های متفاوت)
    for m in _IR_MOBILE_RE.finditer(norm):
        digits = re.sub(r"\D", "", m.group(0))
        if digits.startswith("98") and len(digits) == 12:
            pass
        elif len(digits) != 11 and len(digits) != 10:
            continue
        add("ir_mobile", m.group(0).strip())

    # شماره بین‌المللی
    for m in _INTL_RE.finditer(norm):
        s = m.group(1)
        digits = re.sub(r"\D", "", s)
        if 8 <= len(digits) <= 15 and not digits.startswith("989") and not digits.startswith("09"):
            add("intl_phone", s.strip())

    # شناسه‌های عددی
    for m in _DIGITS_RE.finditer(norm):
        s = m.group(0)
        if in_tg_span(m.start(), m.end()):
            continue
        digits = re.sub(r"\D", "", s)
        if digits.startswith("09") and len(digits) == 11:
            continue
        if len(digits) == 9 and digits[0] in "3456789":
            add("bot_id", s)
        elif len(digits) >= 8:
            add("tg_numeric", s)

    return found

# ============================================================
# 9) تشخیص نوع محتوای پیام (۲۰ فرمت) — بر اساس MIME + نام فایل + ساختار
# ============================================================

EXEC_MIMES = ("x-msdownload", "x-dosexec", "x-executable", "x-elf", "ms-installer",
              "vnd.microsoft.portable-executable", "x-sh", "x-csh")
EXEC_EXTS = (".exe", ".msi", ".com", ".bat", ".cmd", ".scr", ".ps1", ".vbs", ".sh", ".jar", ".apk", ".appimage", ".deb", ".rpm")
APK_MIMES = ("vnd.android.package-archive",)
RAR_MIMES = ("x-rar-compressed", "vnd.rar", "x-rar")
ZIP_MIMES = ("zip", "x-zip-compressed", "x-7z-compressed")
PDF_MIMES = ("pdf",)
AUDIO_MIMES = ("audio/",)
VIDEO_MIMES = ("video/",)
IMAGE_MIMES = ("image/",)


def _ext_of(file_name: str) -> str:
    if not file_name:
        return ""
    return os.path.splitext(file_name.lower())[1]


def classify_message(msg) -> set:
    """انواع محتوای یک پیام تلگرام را تشخیص می‌دهد (فقط بر اساس ساختار، نه صرفاً نام)."""
    kinds = set()
    if msg is None:
        return kinds
    if getattr(msg, "forward_origin", None) is not None or getattr(msg, "forward_date", None) is not None:
        kinds.add("forward")
    if getattr(msg, "photo", None):
        kinds.add("photo")
    if getattr(msg, "animation", None):
        kinds.add("gif")
    if getattr(msg, "video", None):
        kinds.add("video")
    if getattr(msg, "voice", None):
        kinds.add("voice")
    if getattr(msg, "audio", None):
        kinds.add("audio")
    if getattr(msg, "video_note", None):
        kinds.add("video_note")
    if getattr(msg, "sticker", None):
        kinds.add("sticker")
    if getattr(msg, "contact", None):
        kinds.add("contact")
        if getattr(msg.contact, "phone_number", None):
            kinds.add("phone")
    if getattr(msg, "location", None) or getattr(msg, "venue", None):
        kinds.add("location")
    doc = getattr(msg, "document", None)
    if doc is not None:
        mime = (doc.mime_type or "").lower()
        ext = _ext_of(doc.file_name or "")
        if "gif" in mime:
            kinds.add("gif")
        elif any(x in mime for x in PDF_MIMES) or ext == ".pdf":
            kinds.add("pdf")
        elif any(x in mime for x in RAR_MIMES) or ext == ".rar":
            kinds.add("rar")
        elif any(x in mime for x in ZIP_MIMES) or ext == ".zip":
            kinds.add("zip")
        elif any(x in mime for x in APK_MIMES) or ext == ".apk":
            kinds.add("apk")
        elif any(x in mime for x in EXEC_MIMES) or ext in EXEC_EXTS:
            kinds.add("exe")
        elif any(mime.startswith(x) for x in AUDIO_MIMES):
            kinds.add("audio")
        elif any(mime.startswith(x) for x in VIDEO_MIMES):
            kinds.add("video")
        elif any(mime.startswith(x) for x in IMAGE_MIMES):
            kinds.add("photo")
        else:
            kinds.add("unknown_file")
    return kinds


def contact_kinds_of(msg) -> dict:
    """تشخیص اطلاعات تماس در متن یا کپشن پیام."""
    text = msg.text if (msg and getattr(msg, "text", None)) else (msg.caption if msg else None)
    return detect_contacts(text or "")


def check_allowed(msg, settings, owner: bool = False):
    """
    بررسی مجاز بودن پیام بر اساس تنظیمات فرمت‌ها.
    خروجی: (ok, blocked_labels) — پیام ممنوع هرگز منتقل نمی‌شود.
    مدیر هم مشمول محدودیت فرمت‌هاست (مگر تشخیص فحاشی که برای او غیرفعال است).
    """
    formats = settings.get("formats", {})
    blocked = []
    kinds = classify_message(msg)
    for k in kinds:
        if k == "unknown_file":
            if not settings.get("allow_unknown_files", False):
                blocked.append("فایل‌های غیرمجاز")
            continue
        if not formats.get(k, True):
            blocked.append(FORMAT_LABELS.get(k, k))
    contacts = contact_kinds_of(msg)
    for cat in contacts:
        fmt = CONTACT_TO_FORMAT.get(cat)
        if fmt and not formats.get(fmt, True):
            blocked.append(CONTACT_LABELS.get(cat, cat))
    return (len(blocked) == 0), blocked
# ============================================================
# 10) کاربران، ثبت‌نام مرحله‌ای، حریم خصوصی و پروفایل
# ============================================================

def new_user_record(tg_id: int) -> dict:
    return {
        "tg": int(tg_id),
        "internal": None,
        "name": None,
        "username": None,
        "gender": None,          # male | female
        "age": None,
        "province": None,
        "consent": None,         # None | accepted | declined
        "consent_at": None,
        "registered": False,
        "form": None,            # وضعیت فرم/پنل (پایدار پس از Restart)
        "created": iso_utc(now_utc()),
        "last_seen": iso_utc(now_utc()),
        "last_profile_edit": None,
        "chats": 0,
        "blocks_made": 0,
        "warnings": 0,
        "ban": None,             # {"perm": bool, "until": iso, "reason": str, "bid": str}
        "mute_until": None,
        "conv": None,
        "searching": False,
        "queue_since": None,
        "prefs": {"gender": "any", "age": "any"},
        "support_open": None,
        # ---------- سیستم محافظت هوشمند ----------
        "super_until": None,       # پایان محدودیت فوق‌العاده (iso UTC) یا None
        "super_last_chat": None,   # آخرین شروع چت در بازه محدودیت فوق‌العاده
        "super_case": None,        # پرونده‌ای که محدودیت فوق‌العاده را ایجاد کرده
        "girl_block_until": None,  # منع چت با دختران (iso UTC) یا "perm" یا None
        "girl_block_case": None,
    }


def is_owner(tg_id: int) -> bool:
    return OWNER_ID and int(tg_id) == int(OWNER_ID)


def ensure_owner_record() -> dict:
    """رکورد مالک بدون ثبت‌نام: حساب آماده با رضایت تأییدشده و شناسه اختصاصی.
    مالک معاف از گیت ثبت‌نام است؛ مشخصاتش فقط از پنل (مشخصات من) ویرایش می‌شود."""
    u = get_user(OWNER_ID)
    if not u:
        u = ensure_user(OWNER_ID)

    def _m(x):
        if not x.get("registered"):
            x["registered"] = True
        if x.get("consent") != "accepted":
            x["consent"] = "accepted"
        return x

    update_user(OWNER_ID, _m)
    if not get_user(OWNER_ID).get("internal"):
        assign_internal_id(OWNER_ID)
    return get_user(OWNER_ID)


def get_user(tg_id: int):
    ensure_storage()
    return STORE.get("users").get(str(int(tg_id)))


def update_user(tg_id: int, mutator):
    key = str(int(tg_id))
    def _m(users):
        users.setdefault(key, new_user_record(int(tg_id)))
        mutator(users[key])
        return users
    return STORE.update("users", _m)


def ensure_user(tg_id: int) -> dict:
    key = str(int(tg_id))
    def _m(users):
        if key not in users:
            users[key] = new_user_record(int(tg_id))
        return users
    STORE.update("users", _m)
    return get_user(tg_id)


def touch_user(tg_id: int):
    update_user(tg_id, lambda u: u.update({"last_seen": iso_utc(now_utc())}))


def _gen_internal(existing: set) -> str:
    while True:
        n = str(random.randint(300_000_000, 999_999_999))
        if n not in existing:
            existing.add(n)
            return n


def assign_internal_id(tg_id: int) -> str:
    """تولید شناسه اختصاصی تصادفی ۹ رقمی یکتا در کل دیتابیس (قابل تغییر توسط کاربر نیست)."""
    def _m(users):
        u = users[str(int(tg_id))]
        if u.get("internal"):
            return users
        existing = {x.get("internal") for x in users.values() if x.get("internal")}
        u["internal"] = _gen_internal(existing)
        return users
    STORE.update("users", _m)
    return get_user(tg_id)["internal"]


def find_user_by_internal(internal: str):
    users = STORE.get("users")
    for rec in users.values():
        if rec.get("internal") == str(internal):
            return rec
    return None

# ---------- فرم ثبت‌نام ----------

PROVINCES = [
    "آذربایجان شرقی", "آذربایجان غربی", "اردبیل", "اصفهان", "البرز", "ایلام",
    "بوشهر", "تهران", "چهارمحال و بختیاری", "خراسان جنوبی", "خراسان رضوی",
    "خراسان شمالی", "خوزستان", "زنجان", "سمنان", "سیستان و بلوچستان", "فارس",
    "قزوین", "قم", "کردستان", "کرمان", "کرمانشاه", "کهگیلویه و بویراحمد",
    "گلستان", "گیلان", "لرستان", "مازندران", "مرکزی", "هرمزگان", "همدان", "یزد",
]

NAME_RE = re.compile(r"^[\u0600-\u06FF\u200c A-Za-z]{2,30}$")

def valid_name(s: str) -> bool:
    return bool(NAME_RE.match(s.strip()))


def valid_age(s: str) -> bool:
    try:
        n = int(en_num(s).strip())
        return 10 <= n <= 99
    except Exception:
        return False


def start_registration(tg_id: int, kind: str = "reg"):
    """شروع فرم مرحله‌ای. kind: reg | edit (ویرایش پروفایل)"""
    def _m(u):
        u["form"] = {"kind": kind, "step": "name", "data": {}}
        return u
    update_user(tg_id, _m)


def set_form(tg_id: int, form):
    update_user(tg_id, lambda u: u.update({"form": form}))


def clear_form(tg_id: int):
    update_user(tg_id, lambda u: u.update({"form": None}))


def province_kb(page: int = 0):
    """صفحه انتخاب استان — هر استان یک دکمه واقعی اینلاین با callback اختصاصی (pr:<نام>)."""
    per = 12
    rows = []
    chunk = PROVINCES[page * per:(page + 1) * per]
    for i in range(0, len(chunk), 3):
        rows.append([InlineKeyboardButton(name, callback_data=f"pr:{name}")
                     for name in chunk[i:i + 3]])
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("قبلی", callback_data=f"pv:{page - 1}"))
    if (page + 1) * per < len(PROVINCES):
        nav.append(InlineKeyboardButton("بعدی", callback_data=f"pv:{page + 1}"))
    if nav:
        rows.append(nav)
    rows.append([ib("btn_back", "form_back"), ib("btn_cancel", "form_cancel")])
    return InlineKeyboardMarkup(rows)


def gender_kb():
    return imarkup([
        [("btn_next", "g:m", "پسر"), ("btn_next", "g:f", "دختر")],
        [("btn_back", "form_back"), ("btn_cancel", "form_cancel")],
    ])


def consent_kb():
    return imarkup([
        [("btn_confirm", "consent_ok", "تأیید و ادامه"), ("btn_reject", "consent_no", "رد کردن")],
    ])


def reconsent_kb():
    return imarkup([
        [("btn_confirm", "consent_retry", "مشاهده مجدد سیاست حریم خصوصی")],
    ])


def pref_gender_kb():
    return imarkup([
        [("btn_next", "pfg:male", "پسر"), ("btn_next", "pfg:female", "دختر"), ("btn_next", "pfg:any", "بدون فیلتر")],
        [("btn_back", "pf_back")],
    ])


def pref_age_kb():
    return imarkup([
        [("btn_next", "pfa:same", "هم‌سن"), ("btn_next", "pfa:older", "سن بالاتر"), ("btn_next", "pfa:any", "بدون فیلتر")],
        [("btn_back", "pf_back")],
    ])

REG_STEP_TEXTS = {
    "name": "📝 لطفاً <b>نام</b> خود را ارسال کنید (۲ تا ۳۰ نویسه، فقط حروف):",
    "gender": "🚻 جنسیت خود را انتخاب کنید:",
    "age": "🎂 سن خود را به عدد ارسال کنید (۱۰ تا ۹۹):",
    "province": "🗺 استان خود را انتخاب کنید:",
}


def reg_progress(u) -> str:
    d = u["form"]["data"] if u.get("form") else {}
    done = []
    if d.get("name"):
        done.append(f"نام: {d['name']}")
    if d.get("gender"):
        done.append("جنسیت: " + ("پسر" if d["gender"] == "male" else "دختر"))
    if d.get("age"):
        done.append(f"سن: {fa_num(d['age'])}")
    if d.get("province"):
        done.append(f"استان: {d['province']}")
    if not done:
        return ""
    return "☑️ ثبت‌شده:\n" + "\n".join("• " + x for x in done) + "\n\n"


def apply_registration(tg_id: int, data: dict):
    def _m(u):
        u.update({
            "name": data["name"], "gender": data["gender"],
            "age": int(en_num(str(data["age"]))), "province": data["province"],
            "registered": True, "form": None,
        })
        if u.get("last_profile_edit") is None:
            u["last_profile_edit"] = iso_utc(now_utc())
        return u
    update_user(tg_id, _m)
    assign_internal_id(tg_id)

# ---------- حریم خصوصی ----------

def accept_consent(tg_id: int):
    update_user(tg_id, lambda u: u.update({
        "consent": "accepted", "consent_at": iso_utc(now_utc()),
    }))


def decline_consent(tg_id: int):
    update_user(tg_id, lambda u: u.update({"consent": "declined"}))

# ---------- اطلاعات من ----------

def fmt_prefs(p) -> str:
    g = {"male": "پسر", "female": "دختر", "any": "بدون فیلتر"}.get(p.get("gender"), "بدون فیلتر")
    a = {"same": "هم‌سن", "older": "سن بالاتر", "any": "بدون فیلتر"}.get(p.get("age"), "بدون فیلتر")
    return g, a


def account_status_line(u) -> str:
    if is_banned(u):
        return "⛔ مسدود (دائمی)" if (u.get("ban") or {}).get("perm") else "⛔ مسدود موقت"
    if is_muted(u):
        return "🤫 در سکوت"
    return "🟢 فعال و بدون محدودیت"


def info_text(u) -> str:
    """اطلاعات کامل حساب — برای مالک هم بدون نیاز به ثبت‌نام کار می‌کند."""
    g_l, a_l = fmt_prefs(u.get("prefs", {}))
    blocked = STORE.get("blocks")["by"].get(str(u["tg"]), [])
    blocked_ids = []
    for t in blocked:
        rec = get_user(int(t)) if t.isdigit() else None
        blocked_ids.append(rec["internal"] if rec else "؟")
    created = jalali(parse_iso(u["created"]))
    owner = is_owner(u["tg"])
    gender_fa = "پسر" if u.get("gender") == "male" else "دختر" if u.get("gender") == "female" else "ثبت نشده"
    uname = ("@" + str(u.get("username")).lstrip("@")) if u.get("username") else "—"
    lines = [
        "<b>اطلاعات من</b>" + (" (حساب مالک ربات)" if owner else ""), "",
        f"نام نمایشی: <b>{esc(u.get('name') or '—')}</b>",
        f"نام کاربری تلگرام: <b>{esc(uname)}</b>",
        f"جنسیت: <b>{gender_fa}</b>",
        f"سن: <b>{fa_num(u.get('age') or 'ثبت نشده')}</b>",
        f"استان: <b>{esc(u.get('province') or 'ثبت نشده')}</b>",
        f"کد اختصاصی: <code>{u.get('internal') or '—'}</code> (دائمی و غیرقابل تغییر)",
        f"وضعیت ثبت‌نام: <b>{'کامل' if u.get('registered') else 'ناتمام'}</b>",
        f"وضعیت حساب: <b>{account_status_line(u)}</b>",
        f"تعداد چت‌ها: <b>{fa_num(u.get('chats', 0))}</b>",
        f"تعداد بلاک‌ها: <b>{fa_num(u.get('blocks_made', 0))}</b>",
        f"تعداد اخطارها: <b>{fa_num(u.get('warnings', 0))}</b>",
        f"عضویت از: {created}",
    ]
    if owner:
        oc = get_owner_code_record()
        if oc and oc.get("code"):
            lines.append(f"کد اختصاصی مالک (برای دوستان): <code>{oc['code']}</code> | ایجاد: {jalali(parse_iso(oc['created']))}")
        lines.append("مدیریت: مستثنا از اخطار/بن/سکوت و فیلتر فحاشی")
        lines.append("پنل مدیریت: دستور /panel")
    lines += ["", "<b>تنظیمات جست‌وجو</b>",
              f"فیلتر جنسیت: <b>{g_l}</b>",
              f"فیلتر سن: <b>{a_l}</b>"]
    if blocked_ids:
        lines.append("")
        lines.append(f"فهرست بلاک ({fa_num(len(blocked_ids))}): " + "، ".join(blocked_ids[:30]))
    return "\n".join(lines)


def info_kb(u) -> InlineKeyboardMarkup:
    rows = [
        [("btn_next", "pf_gender", "فیلتر جنسیت"), ("btn_next", "pf_age", "فیلتر سن")],
        [("btn_next", "pe_start", "تغییر مشخصات")],
        [("btn_back", "menu_home", "منوی اصلی")],
    ]
    return imarkup(rows)


# ---------- کد اختصاصی مالک (نمایش/لغو/بازتولید) ----------

def get_owner_code_record() -> dict:
    ensure_storage()
    rec = STORE.get("owner_code") or {}
    if not rec.get("code"):
        if OWNER_ID:
            code = _gen_owner_code()
            rec = {"code": code, "created": iso_utc(now_utc()), "revoked": []}
            STORE.update("owner_code", lambda d: rec)
    return rec


def _gen_owner_code() -> str:
    users = STORE.get("users")
    used = {u.get("internal") for u in users.values() if u.get("internal")}
    cur = (STORE.get("owner_code") or {}).get("code")
    if cur:
        used.add(cur)
    used.update((STORE.get("owner_code") or {}).get("revoked", []))
    while True:
        code = str(random.randint(300_000_000, 999_999_999))
        if code not in used:
            return code


def revoke_owner_code() -> dict:
    """لغو کد فعلی مالک؛ کد قدیمی فوراً نامعتبر و کد جدید صادر می‌شود."""
    rec = get_owner_code_record()
    old = rec.get("code")
    revoked = list(rec.get("revoked", []))
    if old:
        revoked.append(old)
    new_code = _gen_owner_code()
    new_rec = {"code": new_code, "created": iso_utc(now_utc()), "revoked": revoked}
    STORE.update("owner_code", lambda d: new_rec)
    audit("owner", "owner_code_revoked", details=f"old:{old} new:{new_code}")
    return new_rec


def set_owner_code(code: str) -> str:
    """ثبت دستی کد اختصاصی مالک (۹ رقم). کد قبلی به فهرست لغوشده‌ها می‌رود.
    خروجی: "" در موفقیت یا پیام خطا."""
    code = en_num((code or "").strip())
    ensure_owner_record()
    if not re.fullmatch(r"\d{9}", code):
        return "کد باید دقیقاً ۹ رقم باشد."
    oc = get_owner_code_record()
    if code == oc.get("code"):
        return "این کد همان کد فعلی است؛ کد دیگری ارسال کنید."
    for u in STORE.get("users").values():
        if u.get("internal") == code:
            return "این کد با کد اختصاصی یک کاربر یکسان است؛ کد دیگری انتخاب کنید."
    old = oc.get("code")
    revoked = list(oc.get("revoked", []))
    if old:
        revoked.append(old)
    new_rec = {"code": code, "created": iso_utc(now_utc()), "revoked": revoked}
    STORE.update("owner_code", lambda d: new_rec)
    audit("owner", "owner_code_manual_set", details=f"old:{old} new:{code}")
    return ""


def find_by_internal_or_owner_code(code: str):
    """یافتن کاربر با کد اختصاصی؛ کد مالک هم پشتیبانی می‌شود. کد لغوشده هرگز برنمی‌گردد."""
    user = find_user_by_internal(code)
    if user:
        return user, "user"
    oc = get_owner_code_record()
    if oc and oc.get("code") == code and code not in oc.get("revoked", []):
        if OWNER_ID:
            return get_user(OWNER_ID) or {"tg": OWNER_ID}, "owner"
    return None, None


def can_edit_profile(u) -> bool:
    if is_owner(u["tg"]):
        return True
    lpe = u.get("last_profile_edit")
    if not lpe:
        return True
    try:
        return now_utc() - parse_iso(lpe) >= timedelta(days=180)
    except Exception:
        return True


def next_edit_date(u):
    lpe = u.get("last_profile_edit")
    if not lpe:
        return None
    try:
        return parse_iso(lpe) + timedelta(days=180)
    except Exception:
        return None

# ---------- بلاک ----------

def add_block(by_tg: int, target_tg: int):
    """ثبت رابطه بلاک (پایدار و دوطرفه از نظر اتصال مجدد)."""
    key, tkey = str(int(by_tg)), str(int(target_tg))

    def _m(d):
        lst = d["by"].setdefault(key, [])
        if tkey not in lst:
            lst.append(tkey)
        d["entries"].append({
            "by": key, "target": tkey, "created": iso_utc(now_utc()), "active": True,
        })
        return d
    STORE.update("blocks", _m)
    update_user(by_tg, lambda u: u.update({"blocks_made": u.get("blocks_made", 0) + 1}))


def blocked_between(a: int, b: int) -> bool:
    d = STORE.get("blocks")
    ka, kb = str(int(a)), str(int(b))
    return kb in d["by"].get(ka, []) or ka in d["by"].get(kb, [])

# ---------- سوابق ارتباطات ----------

def add_relationship(uid: int, partner: int, conv_type: str, blocked: bool):
    key = str(int(uid))

    def _m(rel):
        lst = rel.setdefault(key, [])
        for item in lst:
            if item.get("p") == str(int(partner)):
                item["last"] = iso_utc(now_utc())
                item["blocked"] = bool(item.get("blocked") or blocked)
                return rel
        lst.append({
            "p": str(int(partner)), "type": conv_type,
            "last": iso_utc(now_utc()), "blocked": bool(blocked),
        })
        del lst[:-50]
        return rel
    STORE.update("relationships", _m)

# ---------- عضویت اجباری ----------

async def check_membership(bot, tg_id: int):
    """بررسی عضویت واقعی کاربر از طریق Telegram API. خروجی: (ok, missing_channels)"""
    conf = STORE.get("mandatory_channels")
    if not conf.get("enabled") or is_owner(tg_id):
        return True, []
    missing = []
    for ch in conf.get("channels", []):
        target = ch.get("target")
        if not target:
            continue
        try:
            member = await bot.get_chat_member(target, int(tg_id))
            status = getattr(member, "status", "")
            if status in ("member", "administrator", "creator"):
                continue
            if status == "restricted" and getattr(member, "is_member", False):
                continue
            missing.append(ch)
        except TelegramError as e:
            LOG.error("خطا در بررسی عضویت کانال %s: %s", ch.get("title"), e.__class__.__name__)
            missing.append(ch)
    return (len(missing) == 0), missing

# ============================================================
# 11) ثبت‌نامه‌های عمومی: Audit Log و Moderation Log
# ============================================================

def audit(actor: str, action: str, target: str = "", details: str = ""):
    ensure_storage()

    def _m(lst):
        lst.append({
            "time": iso_utc(now_utc()), "actor": actor,
            "action": action, "target": target, "details": details[:500],
        })
        del lst[:-10000]
        return lst
    STORE.update("audit", _m)


def modlog(by: str, action: str, target_uid: int = None, details: str = ""):
    ensure_storage()

    def _m(lst):
        lst.append({
            "time": iso_utc(now_utc()), "by": by, "action": action,
            "target": str(target_uid) if target_uid else "",
            "details": details[:500],
        })
        del lst[:-20000]
        return lst
    STORE.update("moderation_logs", _m)


def actor_name_of(tg_id) -> str:
    if tg_id is None:
        return "system"
    if is_owner(int(tg_id)):
        return "owner"
    return f"tg:{int(tg_id)}"
# ============================================================
# 12) مکالمه‌ها، صف انتظار، اتصال اتمیک و رله پیام
# ============================================================

def new_conv_id() -> str:
    return "c" + os.urandom(6).hex()


def get_conv(conv_id: str):
    return STORE.get("conversations").get(conv_id)


def new_message_record(conv, sender, kind="text", text="", file_id=None,
                       mime="", name="", src_msg_id=None, owner_msg=False) -> dict:
    return {
        "mid": "m" + os.urandom(6).hex(),
        "conv": conv["id"],
        "sender": str(sender["tg"]),
        "sender_internal": sender.get("internal"),
        "kind": kind,
        "text": text[:4000] if text else "",
        "file_id": file_id,
        "mime": mime,
        "name": name,
        "src_msg_id": src_msg_id,
        "created": iso_utc(now_utc()),
        "owner_msg": bool(owner_msg),
        "delivered": {},
        "deleted_for": [],
        "removed": False,
    }


def add_message(conv_id: str, rec: dict) -> str:
    def _m(d):
        d["messages"].append(rec)
        del d["messages"][:-5000]
        return d
    MSGS.update(conv_id, _m)
    return rec["mid"]


def msg_preview(rec) -> str:
    if rec.get("removed"):
        return "(پیام حذف‌شده)"
    kind = rec.get("kind", "text")
    if kind == "text":
        t = rec.get("text") or ""
        return t[:MESSAGE_PREVIEW_LEN] + ("…" if len(t) > MESSAGE_PREVIEW_LEN else "")
    return "[" + FORMAT_LABELS.get(kind, kind) + "]"


def msg_line(rec, show_deleted_label=True) -> str:
    """نمایش پیام در سوابق مجاز رسیدگی؛ حذف‌شده‌ها برچسب می‌گیرند."""
    deleted = rec.get("removed") or rec.get("deleted_for")
    body = msg_preview(rec)
    if deleted and show_deleted_label:
        body = "«حذف شده» " + body
    tm = jalali(parse_iso(rec["created"]))
    direction = "➡️" if not rec.get("sender_internal") else "👤"
    return f"{tm} | {body}"


CLOSE_TEXTS = {
    "next": "ℹ️ طرف مقابل مکالمه را ترک کرد و به جست‌وجوی مخاطب جدید پرداخت.",
    "end": "⚪ مکالمه پایان یافت.",
    "block": "⚪ مکالمه پایان یافت.",
    "report": "⛔ این مکالمه توسط سامانه پایان یافت.",
    "admin": "⛔ مکالمه توسط مدیریت پایان یافت.",
    "partner_left": "ℹ️ طرف مقابل ربات را ترک کرده است.",
    "protection": "🛡 این مکالمه به دلیل نقض قوانین امنیتی توسط سامانه محافظت پایان یافت.",
}


def create_conversation(a: int, b: int, ctype: str):
    """اتصال اتمیک دو کاربر با Transaction و قفل سراسری."""
    ensure_storage()
    with STORE.glock:
        users = STORE.get("users")
        ua, ub = users.get(str(a)), users.get(str(b))
        if not ua or not ub or ua.get("conv") or ub.get("conv"):
            return None
        conv_id = new_conv_id()
        conv = {
            "id": conv_id, "type": ctype,
            "participants": [str(a), str(b)],
            "created": iso_utc(now_utc()),
            "status": "active", "closed_at": None, "closed_reason": None,
            "has_open_report": False,
        }

        def _m(convs):
            convs[conv_id] = conv
            return convs
        STORE.update("conversations", _m)

        def _mu(u):
            u["conv"] = conv_id
            u["searching"] = False
            u["queue_since"] = None
            return u
        for t in (a, b):
            update_user(t, _mu)
        return conv_id


def is_busy(tg: int) -> bool:
    u = get_user(tg)
    return bool(u and u.get("conv"))


def compatibility(ua, ub) -> bool:
    """سازگاری دو کاربر: فیلتر جنسیت، فیلتر سن و جداسازی قطعی زیر ۱۸ / ۱۸+."""
    pa, pb = ua.get("prefs", {}), ub.get("prefs", {})
    ga = ua.get("gender")
    gb = ub.get("gender")
    want_a = pa.get("gender", "any")
    want_b = pb.get("gender", "any")
    if want_a in ("male", "female") and gb != want_a:
        return False
    if want_b in ("male", "female") and ga != want_b:
        return False
    # قانون امنیتی قطعی: زیر ۱۸ فقط با زیر ۱۸ و ۱۸+ فقط با ۱۸+
    under_a = (ua.get("age") or 99) < 18
    under_b = (ub.get("age") or 99) < 18
    if under_a != under_b:
        return False
    age_a, age_b = ua.get("age") or 0, ub.get("age") or 0
    fa = pa.get("age", "any")
    fb = pb.get("age", "any")
    if fa == "same" and abs(age_b - age_a) > 3:
        return False
    if fa == "older" and not (age_b > age_a):
        return False
    if fb == "same" and abs(age_a - age_b) > 3:
        return False
    if fb == "older" and not (age_a > age_b):
        return False
    # منع چت با دختران (سیستم محافظت): بررسی سمت سرور در لحظه اتصال
    if get_protection().get("girl_block_enabled", True):
        if girl_block_state(ua) != "none" and gb == "female":
            return False
        if girl_block_state(ub) != "none" and ga == "female":
            return False
    return True


def attempt_match(context: ContextTypes.DEFAULT_TYPE):
    """یافتن و اتصال یک زوج سازگار از صف انتظار (اتمیک). خروجی: conv_id یا None"""
    ensure_storage()
    with STORE.glock:
        users = STORE.get("users")
        waiting = [u for u in users.values()
                   if u.get("searching") and not u.get("conv") and not u.get("ban")
                   and not is_muted(u)]
        waiting.sort(key=lambda x: x.get("queue_since") or "")
        pair = None
        for i, ua in enumerate(waiting):
            if blocked_between(int(ua["tg"]), int(ua["tg"])):
                continue
            for ub in waiting[i + 1:]:
                if blocked_between(int(ua["tg"]), int(ub["tg"])):
                    continue
                if compatibility(ua, ub):
                    pair = (int(ua["tg"]), int(ub["tg"]))
                    break
            if pair:
                break
        if not pair:
            return None
        conv_id = create_conversation(pair[0], pair[1], "random")
        return conv_id


def start_search(tg: int) -> bool:
    update_user(tg, lambda u: u.update({"searching": True, "queue_since": iso_utc(now_utc())}))
    return True


def cancel_search(tg: int) -> bool:
    update_user(tg, lambda u: u.update({"searching": False, "queue_since": None}))
    return True


def close_conversation(conv_id: str, reason: str, by_tg=None):
    """
    پایان کنترل‌شده مکالمه (اتمیک): آزادسازی هر دو کاربر، به‌روزرسانی سوابق.
    خروجی: [(tg_id, متن اطلاع‌رسانی)] برای ارسال پس از تراکنش.
    """
    ensure_storage()
    notifications = []
    with STORE.glock:
        convs = STORE.get("conversations")
        conv = convs.get(conv_id)
        if not conv or conv.get("status") != "active":
            return notifications
        participants = [int(x) for x in conv.get("participants", [])]

        def _m(cs):
            c = cs[conv_id]
            c["status"] = "closed"
            c["closed_at"] = iso_utc(now_utc())
            c["closed_reason"] = reason
            if reason == "report":
                c["has_open_report"] = True
            return cs
        STORE.update("conversations", _m)

        blocked_pair = False
        if reason == "block" and by_tg is not None:
            other = participants[0] if by_tg == participants[1] else participants[1]
            add_block(int(by_tg), other)
            blocked_pair = True

        for t in participants:
            def _mu(u, t=t):
                u["conv"] = None
                u["searching"] = False
                u["queue_since"] = None
                u["chats"] = u.get("chats", 0) + 1
                return u
            update_user(t, _mu)
        if len(participants) == 2:
            add_relationship(participants[0], participants[1], conv.get("type", "random"), blocked_pair)
            add_relationship(participants[1], participants[0], conv.get("type", "random"), blocked_pair)
        reason_key = reason if reason in ("next", "end", "block", "report", "admin", "protection") else "end"
        text = CLOSE_TEXTS.get(reason_key, CLOSE_TEXTS["end"])
        for t in participants:
            if by_tg is not None and t == int(by_tg) and reason_key in ("next", "end", "block", "protection"):
                continue  # متخلف پیام تفصیلی مجازات را جداگانه می‌گیرد
            notifications.append((t, text))
    return notifications

# ============================================================
# 13) رله پیام (متن/رسانه) با کنترل کامل قبل از انتقال
# ============================================================

_RATE = {}
_RATE_NOTICE = {}
_CB_FLOOD = {}


def rate_ok(tg_id: int) -> bool:
    limit = STORE.get("settings").get("rate_limit_per_minute", 20)
    now = _time.time()
    dq = _RATE.setdefault(int(tg_id), [])
    while dq and now - dq[0] > 60:
        dq.pop(0)
    if len(dq) >= max(1, int(limit)):
        last = _RATE_NOTICE.get(int(tg_id), 0)
        if now - last > 60:
            _RATE_NOTICE[int(tg_id)] = now
            return False
        return False
    dq.append(now)
    return True


def callback_ok(tg_id: int) -> bool:
    now = _time.time()
    dq = _CB_FLOOD.setdefault(int(tg_id), [])
    while dq and now - dq[0] > 10:
        dq.pop(0)
    if len(dq) >= 15:
        return False
    dq.append(now)
    return True


async def relay_copy(bot, chat_id: int, from_chat_id: int, message_id: int):
    """کپی پیام با مدیریت خطاها و RetryAfter؛ خروجی message_id یا None."""
    for attempt in (1, 2):
        try:
            m = await bot.copy_message(chat_id=chat_id, from_chat_id=from_chat_id,
                                       message_id=message_id)
            return m.message_id
        except RetryAfter as e:
            await asyncio.sleep(float(e.retry_after) + 1)
        except Forbidden:
            return None
        except (BadRequest, TimedOut, TelegramError) as e:
            LOG.error("خطای کپی پیام (%s) تلاش %s", e.__class__.__name__, attempt)
            if attempt == 1:
                await asyncio.sleep(1)
    return None


async def send_text(bot, chat_id: int, text: str, reply_markup=None, html=False):
    """
    ارسال پیام؛ متن‌ها همیشه با ParseMode.HTML ارسال می‌شوند تا تگ‌های قالبی رندر شوند.
    اگر تلگرام HTML را نپذیرفت (تگ نامعتبر یا محتوای escape‌نشده)، نسخه بدون تگ
    جایگزین می‌شود تا هیچ تگ خامی به کاربر نمایش داده نشود.
    """
    parse = ParseMode.HTML
    try:
        return await bot.send_message(chat_id=chat_id, text=text,
                                      parse_mode=parse, reply_markup=reply_markup)
    except RetryAfter as e:
        await asyncio.sleep(float(e.retry_after) + 1)
        try:
            return await bot.send_message(chat_id=chat_id, text=text,
                                          parse_mode=parse, reply_markup=reply_markup)
        except TelegramError:
            return None
    except Forbidden:
        LOG.info("کاربر ربات را بلاک کرده: tg:%s", chat_id)
        return None
    except BadRequest:
        # فالبک: حذف تگ‌ها و ارسال متن ساده — تگ خام هرگز به کاربر نمی‌رسد
        try:
            return await bot.send_message(chat_id=chat_id, text=strip_tags(text),
                                          reply_markup=reply_markup)
        except TelegramError:
            return None
    except TelegramError as e:
        LOG.error("خطای ارسال پیام: %s", e.__class__.__name__)
        return None


async def try_delete(bot, chat_id: int, message_id: int) -> bool:
    try:
        await bot.delete_message(chat_id=chat_id, message_id=message_id)
        return True
    except TelegramError:
        return False


def profanity_active(settings) -> bool:
    if not settings.get("profanity_enabled", True):
        return False
    return in_active_window(settings.get("profanity_hours", []),
                            settings.get("profanity_weekdays"))


async def handle_conversation_message(update: Update, context: ContextTypes.DEFAULT_TYPE,
                                      user: dict):
    """مسیر کامل پیام داخل مکالمه ناشناس."""
    ensure_storage()
    msg = update.effective_message
    bot = context.bot
    sender_tg = int(user["tg"])
    conv_id = user["conv"]
    conv = get_conv(conv_id)
    if not conv or conv.get("status") != "active":
        update_user(sender_tg, lambda u: u.update({"conv": None}))
        await send_text(bot, sender_tg, "ℹ️ مکالمه فعال نیست. از منوی اصلی شروع کنید.", main_menu_kb())
        return

    partner_tg = next(int(p) for p in conv["participants"] if int(p) != sender_tg)
    text = (msg.text or "").strip()
    settings = STORE.get("settings")

    # --- نرخ ارسال ---
    if not rate_ok(sender_tg):
        await send_text(bot, sender_tg, "⏳ پیام‌های شما بیش از حد مجاز است؛ کمی آرام‌تر ارسال کنید.")
        return

    # --- دستورات متنی مالک («روشن»، «بن60»، «سکوت30»، «اخطار»، «حذف بن»، «گزارش») ---
    # در on_text و پیش از این‌جا از طریق try_owner_text_command روی مخاطب مکالمه
    # اجرا می‌شوند؛ پیام عادی مالک فقط در این‌جا رله می‌شود.

    # --- گزارش بدون دکمه: واژه «گزارش» یا /report (هرگز منتقل نمی‌شود) ---
    if text in ("گزارش", "/report"):
        await trigger_report(update, context, user, conv)
        return

    # --- حذف پیام شخصی با ریپلای «حذف» ---
    if text in ("حذف", "حذف پیام", "/del") and msg.reply_to_message:
        await handle_delete_request(update, context, user, conv, msg.reply_to_message.message_id)
        return

    # --- سیستم محافظت هوشمند کاربران (چت‌های دختر-پسر؛ مدیر مستثناست) ---
    # پیش از فیلتر عمومی اجرا می‌شود تا سطح دقیق تخلف و مجازات اختصاصی اعمال شود
    if not is_owner(sender_tg):
        partner_user = get_user(partner_tg)
        content = text or (msg.caption or "")
        pres = analyze_protection(user, partner_user, content,
                                  is_reply=(msg.reply_to_message is not None))
        if pres:
            await handle_protection_violation(update, context, user, conv,
                                              partner_user, pres[0], pres[1])
            return

    # --- ضد فحاشی (مدیر مستثناست) ---
    if not is_owner(sender_tg) and profanity_active(settings):
        content = text or (msg.caption or "")
        res = detect_profanity(content)
        if res:
            await handle_profanity_violation(update, context, user, res)
            return

    # --- فحاشی با فیلتر خاموش: پیام می‌رود اما دریافت‌کننده پیشنهاد تغییر چت می‌گیرد ---
    soft_profane = False
    if not is_owner(sender_tg) and not profanity_active(settings):
        content = text or (msg.caption or "")
        if detect_profanity(content):
            soft_profane = True

    # --- فرمت‌های مجاز و اطلاعات تماس ---
    ok, blocked = check_allowed(msg, settings)
    if not ok:
        notice = "🚫 ارسال این نوع محتوا در این ربات مجاز نیست:\n• " + "\n• ".join(blocked)
        await send_text(bot, sender_tg, notice)
        return

    # --- ذخیره و رله ---
    kinds = classify_message(msg)
    if msg.text and not kinds:
        kind = "text"
    else:
        kind = next(iter(kinds), "text") if kinds else "text"
        if kind == "unknown_file":
            kind = "file"
    doc = getattr(msg, "document", None)
    rec = new_message_record(conv, user, kind=kind, text=text or (msg.caption or ""),
                             file_id=(doc.file_id if doc else None),
                             mime=(doc.mime_type or "") if doc else "",
                             name=(doc.file_name or "") if doc else "",
                             src_msg_id=msg.message_id,
                             owner_msg=is_owner(sender_tg))
    delivered = await relay_copy(bot, partner_tg, sender_tg, msg.message_id)
    if delivered is None:
        await send_text(bot, sender_tg, "⚠️ ارسال پیام به طرف مقابل ناموفق بود (ممکن است ربات را بلاک کرده باشد).")
        return
    rec["delivered"] = {str(partner_tg): {"chat": partner_tg, "mid": delivered}}
    add_message(conv_id, rec)

    # --- هشدار لینک برای دریافت‌کننده (فقط لینک‌های غیرتلگرام؛ استثنای فرمت‌ها) ---
    # فقط وقتی فرمت «لینک وب» مجاز است هشدار معنا دارد؛ در حالت بسته بودن، خود پیام مسدود شده است.
    if settings.get("link_warning_enabled", True) and settings.get("formats", {}).get("web_link", True):
        contacts = detect_contacts(text or (msg.caption or ""))
        if "web_link" in contacts:
            await send_text(bot, partner_tg,
                            settings.get("link_warning_text") or LINK_WARNING_DEFAULT,
                            html=True)

    # --- فحاشی با فیلتر خاموش: پیشنهاد تغییر چت فقط برای دریافت‌کننده (خصوصی) ---
    if soft_profane:
        await send_text(bot, partner_tg,
                        "💬 <b>آیا مایل به تغییر چت خود هستید؟</b>",
                        change_chat_kb(), html=True)


async def handle_delete_request(update, context, user, conv, reply_mid: int):
    """حذف پیام از نمایش شخصی درخواست‌کننده + برچسب «حذف شده» در سوابق مجاز."""
    bot = context.bot
    uid = str(int(user["tg"]))
    target_rec = None

    def _m(d):
        nonlocal target_rec
        for rec in reversed(d["messages"]):
            if rec.get("conv") != conv["id"] or rec.get("removed"):
                continue
            dv = rec.get("delivered", {}).get(uid)
            if dv and dv.get("mid") == reply_mid:
                target_rec = rec
                break
            if rec.get("sender") == uid and rec.get("src_msg_id") == reply_mid:
                target_rec = rec
                break
        if target_rec is not None:
            if uid not in target_rec["deleted_for"]:
                target_rec["deleted_for"].append(uid)
        return d
    MSGS.mutate(conv["id"], _m)

    ok_tg = await try_delete(bot, int(user["tg"]), reply_mid)
    if target_rec is not None:
        await send_text(bot, int(user["tg"]), "🗑 پیام از نمایش شما حذف شد."
                        + ("" if ok_tg else " (حذف در تلگرام ممکن نشد ولی در سوابق برچسب خورد)"))
        audit(actor_name_of(user["tg"]), "user_delete_message", target=conv["id"])
    else:
        await send_text(bot, int(user["tg"]), "ℹ️ پیام مورد نظر برای حذف یافت نشد.")

# ============================================================
# 14) گزارش تخلف (بدون دکمه؛ بستن خودکار چت؛ ناشناس ماندن گزارش‌دهنده)
# ============================================================

async def trigger_report(update, context, user, conv):
    bot = context.bot
    reporter_tg = int(user["tg"])
    existing = [r for r in STORE.get("reports") if r.get("conv") == conv["id"]]
    if existing:
        await send_text(bot, reporter_tg,
                        "ℹ️ برای این مکالمه قبلاً گزارش ثبت شده است و امکان ثبت گزارش تکراری وجود ندارد.",
                        main_menu_kb())
        return
    participants = [int(p) for p in conv["participants"]]
    reported_tg = next(p for p in participants if p != reporter_tg)
    notifs = close_conversation(conv["id"], "report", reporter_tg)
    rid = "r" + os.urandom(5).hex()

    def _m(lst):
        lst.append({
            "rid": rid, "conv": conv["id"],
            "reporter": str(reporter_tg), "reported": str(reported_tg),
            "reporter_internal": user.get("internal"),
            "created": iso_utc(now_utc()),
            "reason": "", "status": "new", "outcome": None,
            "notes": [], "closed": None,
        })
        return lst
    STORE.update("reports", _m)
    update_user(reporter_tg, lambda u: u.update({
        "conv": None,
        "form": {"kind": "report_reason", "data": {"rid": rid}},
    }))
    for tg, t in notifs:
        await send_text(bot, tg, t, main_menu_kb())
    audit(actor_name_of(reporter_tg), "report_created", target=rid, details=f"conv:{conv['id']}")
    await send_text(bot, reporter_tg,
                    "🛡 مکالمه بسته شد و <b>گزارش شما ثبت گردید</b>.\n\n"
                    "دلیل گزارش را بنویسید (اختیاری):", report_reason_kb())


def report_reason_kb():
    return imarkup([
        [("btn_cancel", "rpt_skip", "ثبت بدون توضیح")],
    ])


def change_chat_kb():
    """دکمه‌های یک‌ردیفی بلاک | چت بعدی (پیشنهاد تغییر چت پس از دریافت پیام نامناسب)."""
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("بلاک ⛔", callback_data="chg:block"),
        InlineKeyboardButton("چت بعدی ⏭️", callback_data="chg:next"),
    ]])


def save_report_reason(rid: str, reason: str):
    def _m(lst):
        for r in lst:
            if r.get("rid") == rid:
                r["reason"] = reason[:500]
                return lst
        return lst
    STORE.update("reports", _m)


async def handle_profanity_violation(update, context, user, res):
    """واکنش به تخلف ضد فحاشی: عدم ارسال، اطلاع‌رسانی، اخطار و مجازات."""
    bot = context.bot
    sender_tg = int(user["tg"])
    matched, ver = res
    settings = STORE.get("settings")
    cap = int(settings.get("warning_cap", 3))
    wid = "w" + os.urandom(5).hex()
    count = 0
    punished = False

    def _m(lst):
        nonlocal count
        lst.append({
            "wid": wid, "uid": str(sender_tg),
            "reason": "استفاده از محتوای توهین‌آمیز",
            "matched": "،".join(matched)[:200],
            "source": "profanity", "by": "system",
            "created": iso_utc(now_utc()), "filter_version": ver,
        })
        return lst
    STORE.update("warnings", _m)

    def _mu(u):
        nonlocal count
        u["warnings"] = u.get("warnings", 0) + 1
        count = u["warnings"]
        return u
    update_user(sender_tg, _mu)

    if count >= cap:
        action = settings.get("profanity_action", "warn")
        minutes = int(settings.get("punishment_minutes", 60))
        if action == "mute":
            until = iso_utc(now_utc() + timedelta(minutes=minutes))
            update_user(sender_tg, lambda u: u.update({"mute_until": until}))
            punished = True
        elif action == "ban":
            apply_ban(sender_tg, minutes=minutes, by="system",
                      reason="نقض مکرر قوانین (محتوای توهین‌آمیز)")
            punished = True
        elif action == "perm":
            apply_ban(sender_tg, permanent=True, by="system",
                      reason="نقض مکرر قوانین (محتوای توهین‌آمیز)")
            punished = True
    modlog("system", "profanity_block", sender_tg,
           f"words:{','.join(matched)[:120]} ver:{ver} warning:{count}/{cap}")
    msg_lines = ["🚫 <b>پیام شما ارسال نشد.</b>",
                 "محتوای پیام شما نقض قوانین ربات است.",
                 f"⚠️ اخطار {fa_num(count)} از {fa_num(cap)} ثبت شد."]
    if punished:
        msg_lines.append("به دلیل رسیدن به سقف اخطار، مجازات تعیین‌شده اعمال شد.")
    await send_text(bot, sender_tg, "\n".join(msg_lines))

# ============================================================
# 15) چت ناشناس با دوست (درخواست و پذیرش)
# ============================================================

def create_friend_request(from_tg: int, to_tg: int):
    """ثبت درخواست چت دوستانه. خروجی: (code, fid)"""
    u_from, u_to = get_user(from_tg), get_user(to_tg)
    if not u_from or not u_to:
        return "not_found", None
    if u_to.get("ban") or u_from.get("ban"):
        return "banned", None
    if blocked_between(from_tg, to_tg):
        return "blocked", None
    if u_to.get("conv"):
        return "target_busy", None
    frs = STORE.get("friend_requests")
    for r in frs:
        if r.get("status") == "pending" and {r.get("from"), r.get("to")} == {str(from_tg), str(to_tg)}:
            return "dup_pending", None
    fid = "f" + os.urandom(5).hex()

    def _m(lst):
        lst.append({
            "fid": fid, "from": str(from_tg), "to": str(to_tg),
            "created": iso_utc(now_utc()), "status": "pending", "conv": None,
        })
        return lst
    STORE.update("friend_requests", _m)
    return "ok", fid


def friend_request_kb(fid: str):
    return imarkup([
        [("btn_confirm", f"frq:{fid}:acc", "پذیرش"), ("btn_reject", f"frq:{fid}:rej", "رد کردن")],
    ])


def set_friend_request(fid: str, status: str, conv_id=None):
    def _m(lst):
        for r in lst:
            if r.get("fid") == fid:
                r["status"] = status
                if conv_id:
                    r["conv"] = conv_id
        return lst
    STORE.update("friend_requests", _m)


async def accept_friend_request(update, context, fid: str):
    bot = context.bot
    rec = next((r for r in STORE.get("friend_requests") if r.get("fid") == fid), None)
    if not rec or rec.get("status") != "pending":
        await send_text(bot, update.effective_user.id, "ℹ️ این درخواست قبلاً پاسخ داده شده یا منقضی شده است.")
        return
    a, b = int(rec["from"]), int(rec["to"])
    ua, ub = get_user(a), get_user(b)
    if not ua or not ub or ua.get("ban") or ub.get("ban") or blocked_between(a, b):
        set_friend_request(fid, "rejected")
        await send_text(bot, update.effective_user.id, "امکان ایجاد مکالمه نیست.")
        return
    # سکوت/محدودیت فوق‌العاده/منع چت با دختران در سمت سرور برای هر دو طرف کنترل می‌شود
    for uid_, uu in ((a, ua), (b, ub)):
        if is_muted(uu):
            await send_text(bot, uid_, mute_notice(uu), notice_kb(uu))
            return
        rem = super_start_block_minutes(uu)
        if rem is not None:
            await send_text(bot, uid_, super_block_text(rem), notice_kb(uu))
            return
    if get_protection().get("girl_block_enabled", True):
        for uid_, uu, other in ((a, ua, ub), (b, ub, ua)):
            if girl_block_state(uu) != "none" and other.get("gender") == "female":
                await send_text(bot, uid_,
                                "🛡 شروع چت جدید با دختران برای حساب شما در حال حاضر مجاز نیست.")
                return
    if ua.get("conv") or ub.get("conv"):
        set_friend_request(fid, "rejected")
        await send_text(bot, update.effective_user.id, "ℹ️ یکی از طرفین در حال حاضر در مکالمه دیگری است.")
        return
    conv_id = create_conversation(a, b, "friend")
    if not conv_id:
        await send_text(bot, update.effective_user.id, "⚠️ ایجاد مکالمه ناموفق بود؛ بعداً تلاش کنید.")
        return
    mark_new_chat_started(a)
    mark_new_chat_started(b)
    set_friend_request(fid, "accepted", conv_id)
    intro = "<b>اتصال برقرار شد!</b>\n\nبا احترام گفت‌وگو کنید. برای پایان، «پایان مکالمه» را بزنید."
    await send_text(bot, a, intro, conv_kb(), html=True)
    await send_text(bot, b, intro, conv_kb(), html=True)
# ============================================================
# 16) بن، سکوت، اخطار و دستورات مدیریتی متنی
# ============================================================

def apply_ban(tg_id: int, minutes: int = None, permanent: bool = False,
              by: str = "owner", reason: str = "", case: str = None):
    if is_owner(int(tg_id)):
        return False  # مدیر اصلی هرگز بن نمی‌شود
    bid = "b" + os.urandom(5).hex()
    until = None if permanent else iso_utc(now_utc() + timedelta(minutes=minutes or 0))
    rec = {
        "bid": bid, "uid": str(int(tg_id)),
        "type": "perm" if permanent else "temp",
        "minutes": minutes, "created": iso_utc(now_utc()),
        "until": until, "reason": reason[:300], "by": by,
        "case": case, "active": True, "removed_at": None,
    }

    def _m(lst):
        lst.append(rec)
        return lst
    STORE.update("bans", _m)
    update_user(int(tg_id), lambda u: u.update({
        "ban": {"perm": permanent, "until": until, "reason": reason[:300], "bid": bid},
        "searching": False, "queue_since": None,
    }))
    modlog(by, "ban_perm" if permanent else f"ban_{minutes}m", tg_id, reason)
    return True


def apply_mute(tg_id: int, minutes: int, by: str = "owner", reason: str = "",
               case: str = None):
    if is_owner(int(tg_id)):
        return False
    bid = "b" + os.urandom(5).hex()
    until = iso_utc(now_utc() + timedelta(minutes=minutes))
    rec = {
        "bid": bid, "uid": str(int(tg_id)), "type": "mute",
        "minutes": minutes, "created": iso_utc(now_utc()),
        "until": until, "reason": reason[:300], "by": by,
        "case": case, "active": True, "removed_at": None,
    }

    def _m(lst):
        lst.append(rec)
        return lst
    STORE.update("bans", _m)
    update_user(int(tg_id), lambda u: u.update({"mute_until": until}))
    modlog(by, f"mute_{minutes}m", tg_id, reason)
    return True


def release_ban(tg_id: int, by: str = "owner", case: str = None):
    if is_owner(int(tg_id)):
        return False
    key = str(int(tg_id))

    def _m(lst):
        for b in lst:
            if (b.get("uid") == key and b.get("active")
                    and b.get("type") in ("temp", "perm")
                    and (case is None or b.get("case") == case)):
                b["active"] = False
                b["removed_at"] = iso_utc(now_utc())
        return lst
    STORE.update("bans", _m)
    # در لغو موردی، سایر بن‌های فعال همان کاربر حفظ می‌شوند
    keep_perm, keep_until = False, None
    for b in STORE.get("bans"):
        if b.get("uid") == key and b.get("active") and b.get("type") in ("temp", "perm"):
            if b.get("type") == "perm":
                keep_perm = True
            else:
                try:
                    dt = parse_iso(b["until"])
                    if dt > now_utc() and (keep_until is None or dt > keep_until):
                        keep_until = dt
                except Exception:
                    pass
    update_user(int(tg_id), lambda u: u.update({
        "ban": None if not (keep_perm or keep_until) else {
            "perm": keep_perm,
            "until": iso_utc(keep_until) if keep_until else None,
            "bid": None, "reason": "بن فعال دیگر پرونده‌ها حفظ شد",
        }}))
    modlog(by, "unban" + (f":{case}" if case else ""), tg_id)
    return True


def release_mute(tg_id: int, by: str = "owner", case: str = None):
    if is_owner(int(tg_id)):
        return False
    key = str(int(tg_id))

    def _m(lst):
        for b in lst:
            if (b.get("uid") == key and b.get("active") and b.get("type") == "mute"
                    and (case is None or b.get("case") == case)):
                b["active"] = False
                b["removed_at"] = iso_utc(now_utc())
        return lst
    STORE.update("bans", _m)
    # در لغو موردی، سایر سکوت‌های فعال حفظ می‌شوند
    keep_until = None
    for b in STORE.get("bans"):
        if b.get("uid") == key and b.get("active") and b.get("type") == "mute":
            try:
                dt = parse_iso(b["until"])
                if dt > now_utc() and (keep_until is None or dt > keep_until):
                    keep_until = dt
            except Exception:
                pass
    update_user(int(tg_id), lambda u: u.update(
        {"mute_until": iso_utc(keep_until) if keep_until else None}))
    modlog(by, "unmute" + (f":{case}" if case else ""), tg_id)
    return True


def is_banned(u) -> bool:
    if not u:
        return False
    b = u.get("ban")
    if not b:
        return False
    if b.get("perm"):
        return True
    try:
        if parse_iso(b["until"]) > now_utc():
            return True
    except Exception:
        return True
    update_user(u["tg"], lambda x: x.update({"ban": None}))
    return False


def is_muted(u) -> bool:
    mu = u.get("mute_until") if u else None
    if not mu:
        return False
    try:
        if parse_iso(mu) > now_utc():
            return True
    except Exception:
        return False
    update_user(u["tg"], lambda x: x.update({"mute_until": None}))
    return False


def add_admin_warning(tg_id: int, reason: str, by: str):
    if is_owner(int(tg_id)):
        return False
    wid = "w" + os.urandom(5).hex()

    def _m(lst):
        lst.append({
            "wid": wid, "uid": str(int(tg_id)), "reason": reason[:300],
            "source": "admin", "by": by,
            "created": iso_utc(now_utc()), "filter_version": None,
        })
        return lst
    STORE.update("warnings", _m)
    update_user(int(tg_id), lambda u: u.update({"warnings": u.get("warnings", 0) + 1}))
    modlog(by, "warn", tg_id, reason)
    return True

# ---------- دستورات متنی مالک (هرگز به‌عنوان پیام عادی ارسال نمی‌شوند) ----------

CMD_SILENCE = re.compile(r"^سکوت\s*([0-9۰-۹]{1,5})$")
CMD_BAN = re.compile(r"^بن\s*([0-9۰-۹]{1,5})$")
CMD_WARN = re.compile(r"^اخطار$")
CMD_UNSILENCE = re.compile(r"^حذف\s+سکوت$")
CMD_UNBAN = re.compile(r"^حذف\s+بن$")
CMD_REPORTS = re.compile(r"^گزارش$")


def parse_admin_command(text: str):
    """تشخیص دستور مدیریتی متنی. خروجی: (name, arg) یا None"""
    t = en_num(text.strip())
    for pat, name in ((CMD_SILENCE, "silence"), (CMD_BAN, "ban")):
        m = pat.match(t)
        if m:
            try:
                return name, int(m.group(1))
            except Exception:
                return None
    if CMD_WARN.match(t):
        return "warn", None
    if CMD_UNSILENCE.match(t):
        return "unsilence", None
    if CMD_UNBAN.match(t):
        return "unban", None
    if CMD_REPORTS.match(t):
        return "reports", None
    return None


def target_of_reports(uid: int):
    return [r for r in STORE.get("reports") if r.get("reported") == str(int(uid))]

# ============================================================
# 17) پشتیبانی (تیکت)
# ============================================================

def open_ticket(tg_id: int):
    """تیکت باز موجود را می‌دهد یا تیکت جدید می‌سازد."""
    key = str(int(tg_id))
    tickets = STORE.get("tickets")
    for t in tickets:
        if t.get("uid") == key and t.get("status") in ("new", "open"):
            return t
    tid = "t" + os.urandom(5).hex()
    u = get_user(tg_id)

    def _m(lst):
        lst.append({
            "tid": tid, "uid": key, "internal": u.get("internal") if u else None,
            "created": iso_utc(now_utc()), "updated": iso_utc(now_utc()),
            "status": "new",
        })
        return lst
    STORE.update("tickets", _m)
    update_user(tg_id, lambda x: x.update({"support_open": tid}))
    return STORE.get("tickets")[-1]


def add_ticket_message(tid: str, who: str, text: str):
    mid = "sm" + os.urandom(5).hex()

    def _m(lst):
        lst.append({
            "mid": mid, "tid": tid, "who": who,
            "text": text[:4000], "created": iso_utc(now_utc()),
        })
        del lst[:-20000]
        return lst
    STORE.update("support_messages", _m)
    STORE.update("tickets", lambda ts: [dict(t, updated=iso_utc(now_utc())) if t.get("tid") == tid else t for t in ts])
    return mid


def get_ticket(tid: str):
    return next((t for t in STORE.get("tickets") if t.get("tid") == tid), None)


def get_ticket_messages(tid: str):
    return [m for m in STORE.get("support_messages") if m.get("tid") == tid]


def set_ticket_status(tid: str, status: str):
    STORE.update("tickets", lambda ts: [dict(t, status=status) if t.get("tid") == tid else t for t in ts])
    if status == "closed":
        rec = get_ticket(tid)
        if rec:
            update_user(int(rec["uid"]), lambda x: x.update({"support_open": None}))


def ticket_status_fa(s) -> str:
    return {"new": "🆕 جدید", "open": "📬 در حال بررسی", "closed": "✅ بسته‌شده"}.get(s, s)

# ============================================================
# 18) وظایف زمان‌بندی‌شده پایدار (بازیابی از دیتابیس)
# ============================================================

def add_task(kind: str, run_at_utc: datetime, payload=None):
    tid = "task" + os.urandom(4).hex()

    def _m(lst):
        lst.append({
            "tid": tid, "kind": kind,
            "run_at": iso_utc(run_at_utc), "payload": payload or {},
            "done": False, "created": iso_utc(now_utc()),
        })
        return lst
    STORE.update("scheduled_tasks", _m)
    return tid


def pop_due_tasks() -> list:
    """وظایف رسیده را اتمیک برمی‌دارد (done=True)."""
    out = []

    def _m(lst):
        now = now_utc()
        for t in lst:
            if t.get("done"):
                continue
            try:
                due = parse_iso(t["run_at"])
            except Exception:
                t["done"] = True
                continue
            if due <= now:
                t["done"] = True
                out.append(t)
        return lst
    STORE.mutate("scheduled_tasks", _m)
    return out
# ============================================================
# 19) پنل مالک — ابزارهای مشترک
# ============================================================

def pager(items, page: int, per: int = PAGE_SIZE):
    total = len(items)
    pages = max(1, (total + per - 1) // per)
    page = max(0, min(page, pages - 1))
    return items[page * per:(page + 1) * per], page, pages


def nav_rows(prefix: str, page: int, pages: int, back_cd="pn") -> list:
    rows = []
    if pages > 1:
        rows.append([
            InlineKeyboardButton("⬅️ قبلی", callback_data=f"{prefix}:{max(0, page - 1)}"),
            InlineKeyboardButton(f"صفحه {fa_num(page + 1)}/{fa_num(pages)}", callback_data="noop"),
            InlineKeyboardButton("بعدی ➡️", callback_data=f"{prefix}:{min(pages - 1, page + 1)}"),
        ])
    rows.append([ib("btn_back", back_cd, "بازگشت")])
    return rows


OWNER_PANEL_TEXT = "<b>پنل مدیریت ربات</b>\n\nبخش مورد نظر را انتخاب کنید:"


def owner_panel_kb() -> InlineKeyboardMarkup:
    """رنگ‌بندی بر اساس اهمیت (سیستم دکمه رنگی رسمی تلگرام):
    primary (آبی) = عملیات اصلی روزمره | success (سبز) = امنیت/مشاهده
    danger (قرمز) = عملیات حساس و مخرب | بدون استایل = خنثی/پشتیبانی"""
    return imarkup([
        [("btn_next", "pn_dash", "داشبورد", "primary"), ("btn_next", "pn_users", "مدیریت کاربران", "primary")],
        [("btn_next", "pn_rpts", "گزارش‌ها", "success"), ("btn_next", "pn_bc", "اطلاع‌رسانی", "primary")],
        [("btn_next", "pn_bc_jobs", "⏰ ارسال‌های زمان‌بندی‌شده")],
        [("btn_next", "pn_set", "تنظیمات سیستمی"), ("btn_next", "pn_fmt", "مدیریت فرمت‌ها")],
        [("btn_next", "pn_prof", "ضد فحاشی", "success"), ("btn_next", "pn_ch", "عضویت اجباری")],
        [("btn_next", "pn_prot", "سیستم محافظت", "success"), ("btn_next", "pn_apls", "اعتراض‌ها", "success")],
        [("btn_next", "pn_adv", "تنظیمات پیشرفته", "primary"), ("btn_next", "pn_bot", "وضعیت ربات", "danger")],
        [("btn_next", "pn_supp", "پشتیبانی"), ("btn_next", "pn_oc", "چت‌های مدیر")],
        [("btn_next", "pn_logs", "گزارش عملیات"), ("btn_next", "pn_bk", "مدیریت بکاپ", "success")],
        [("btn_next", "pn_oguide", "راهنمای کامل مدیریت")],
        [("btn_next", "pn_me", "مشخصات من", "success")],
        [("btn_back", "menu_home", "منوی اصلی کاربری")],
    ])

# ============================================================
# 20) سیستم بکاپ و بازیابی (JSON روی Railway Volume)
# ============================================================

REQUIRED_BACKUP_FILES = ["users.json", "settings.json", "conversations.json",
                         "blocks.json", "reports.json", "bans.json", "tickets.json"]


def compute_counts() -> dict:
    users = STORE.get("users")
    convs = STORE.get("conversations")
    return {
        "users": len(users),
        "conversations": len(convs),
        "active_conversations": sum(1 for c in convs.values() if c.get("status") == "active"),
        "reports": len(STORE.get("reports")),
        "warnings": len(STORE.get("warnings")),
        "bans": len(STORE.get("bans")),
        "tickets": len(STORE.get("tickets")),
        "messages": sum(len(MSGS.get(c).get("messages", [])) for c in MSGS.list_convs()),
    }


def create_backup(kind: str = "manual") -> dict:
    """تهیه بکاپ کامل با نوشتن اتمیک + SHA-256 + ثبت تاریخچه."""
    ensure_storage()
    ts = now_utc()
    bid = "bk" + ts.strftime("%Y%m%d%H%M%S") + os.urandom(3).hex()
    fname = f"backup-{ts.strftime('%Y%m%d-%H%M%S')}-{bid}.json"
    path = os.path.join(STORE.root, "backups", fname)
    files = STORE.snapshot_files()
    files.update(MSGS.snapshot_messages())
    content = {
        "schema_version": SCHEMA_VERSION,
        "created_utc": iso_utc(ts),
        "created_tehran": jalali(ts),
        "kind": kind,
        "counts": compute_counts(),
        "files": files,
    }
    try:
        _atomic_write(path, json.dumps(content, ensure_ascii=False, separators=(",", ":")))
    except OSError as e:
        LOG.error("نوشتن بکاپ ناموفق: %s", e)
        raise
    size = os.path.getsize(path)
    sha = _sha256_of(path)
    rec = {
        "bid": bid, "file": fname, "kind": kind,
        "created_utc": content["created_utc"], "created_tehran": content["created_tehran"],
        "size": size, "sha256": sha, "counts": content["counts"],
        "valid": True, "file_deleted": False,
    }

    def _m(lst):
        lst.append(rec)
        del lst[:-500]
        return lst
    STORE.update("backup_history", _m)
    audit("owner" if kind != "auto" else "system", f"backup_{kind}", target=bid,
          details=f"size:{size}")
    return rec


def _sha256_of(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def backup_path(rec) -> str:
    return os.path.join(STORE.root, "rec" "backups" if False else "backups", rec["file"])


def verify_backup(rec) -> tuple:
    """بررسی سلامت بکاپ: وجود فایل، حجم، SHA-256 و اعتبارسنجی ساختار."""
    path = backup_path(rec)
    if not os.path.exists(path):
        return (False, "فایل بکاپ یافت نشد")
    try:
        size = os.path.getsize(path)
        sha = _sha256_of(path)
    except OSError as e:
        return (False, f"خواندن فایل ناموفق: {e}")
    if sha != rec.get("sha256"):
        return (False, "عدم تطابق SHA-256 — فایل دستکاری‌شده یا خراب است")
    ok, summary = validate_backup_file(path)
    if not ok:
        return (False, "ساختار نامعتبر: " + summary)
    return (True, summary)


def validate_backup_file(path: str):
    """اعتبارسنجی ساختار JSON، نسخه فایل و اطلاعات ضروری. خروجی: (ok, summary|خطا)"""
    try:
        if os.path.getsize(path) > MAX_BACKUP_UPLOAD_BYTES:
            return (False, "حجم فایل بیش از حد مجاز است")
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except Exception as e:
        return (False, f"فایل JSON معتبر نیست: {e.__class__.__name__}")
    if not isinstance(data, dict):
        return (False, "ساختار فایل نامعتبر است")
    if data.get("schema_version") != SCHEMA_VERSION:
        return (False, f"نسخه ساختار ناسازگار: {data.get('schema_version')}")
    files = data.get("files")
    if not isinstance(files, dict):
        return (False, "بخش فایل‌ها موجود نیست")
    for name in REQUIRED_BACKUP_FILES:
        if name not in files:
            return (False, f"فایل ضروری «{name}» در بکاپ نیست")
    counts = {}
    try:
        counts["users"] = len(files["users.json"])
        counts["conversations"] = len(files["conversations.json"])
        counts["reports"] = len(files.get("reports.json", []))
        msgs = 0
        for key, val in files.items():
            if key.startswith("messages/conv-"):
                if not isinstance(val, dict) or not isinstance(val.get("messages"), list):
                    return (False, f"ساختار پیام‌ها نامعتبر: {key}")
                msgs += len(val["messages"])
        counts["messages"] = msgs
        if not isinstance(files["settings.json"], dict):
            return (False, "تنظیمات نامعتبر است")
    except Exception as e:
        return (False, f"اعتبارسنجی داده ناموفق: {e.__class__.__name__}")
    return (True, counts)


def prune_backups():
    """حذف قدیمی‌ترین بکاپ‌های «خودکار» فراتر از سقف نگهداری (بکاپ دستی هرگز حذف نمی‌شود)."""
    settings = STORE.get("settings")
    if not settings.get("auto_backup_enabled", True):
        return
    keep = max(3, int(settings.get("backup_keep", 30)))
    hist = STORE.get("backup_history")
    autos = [r for r in hist if r.get("kind") == "auto" and not r.get("file_deleted")]
    autos.sort(key=lambda r: r.get("created_utc") or "")
    for rec in autos[:-keep]:
        try:
            p = backup_path(rec)
            if os.path.exists(p):
                os.remove(p)
            rec["file_deleted"] = True
            LOG.info("بکاپ خودکار قدیمی حذف شد: %s", rec["bid"])
        except OSError as e:
            LOG.error("حذف بکاپ قدیمی ناموفق: %s", e)
    STORE.update("backup_history", lambda lst: [dict(r) for r in hist])


async def send_backup_file(bot, chat_id: int, rec) -> bool:
    path = backup_path(rec)
    if not os.path.exists(path):
        return False
    caption = (f"بکاپ {rec['bid']}\n🗓 {rec.get('created_tehran')}\n"
               f"📦 حجم: {fa_num(rec['size'] // 1024)} کیلوبایت\n"
               f"SHA256: <code>{rec['sha256'][:16]}…</code>")
    try:
        with open(path, "rb") as f:
            await bot.send_document(chat_id=chat_id, document=f, filename=rec["file"],
                                    caption=caption, parse_mode=ParseMode.HTML)
        audit("owner", "backup_download", target=rec["bid"])
        return True
    except TelegramError as e:
        LOG.error("ارسال فایل بکاپ ناموفق: %s", e.__class__.__name__)
        return False


def stage_restore(path: str):
    """مرحله ۱ بازیابی: ذخیره امن فایل آپلودی در مسیر موقت و اعتبارسنجی."""
    tmp_dir = os.path.join(STORE.root, "tmp")
    os.makedirs(tmp_dir, exist_ok=True)
    staged = os.path.join(tmp_dir, "restore-staged.json")
    shutil.copy2(path, staged)
    ok, summary = validate_backup_file(staged)
    return (ok, staged, summary)


def perform_restore(staged_path: str) -> tuple:
    """
    اجرای کامل بازیابی با بازگشت امن:
    ۱) حالت نگهداری ۲) بکاپ پیش از بازیابی ۳) بررسی نسخه آزمایشی
    ۴) جایگزینی اتمیک ۵) بازسازی کش‌ها ۶) بررسی نتیجه.
    در هر شکست، دیتابیس قبلی حفظ می‌شود.
    """
    ensure_storage()
    ok, summary = validate_backup_file(staged_path)
    if not ok:
        return (False, "بازیابی رد شد: " + summary)
    try:
        with open(staged_path, "r", encoding="utf-8") as f:
            data = json.load(f)
        files = data["files"]
    except Exception as e:
        return (False, f"خواندن فایل ناموفق: {e.__class__.__name__}")

    # ۱) حالت نگهداری
    STORE.update("settings", lambda s: dict(s, maintenance=True))
    pre_restore_rec = None
    try:
        # ۲) بکاپ از وضعیت فعلی
        pre_restore_rec = create_backup(kind="pre_restore")
        # ۳) نسخه آزمایشی: بررسی همه داده‌های کلیدی
        test_users = files["users.json"]
        if not isinstance(test_users, dict):
            raise ValueError("users نامعتبر")
        for key, val in files.items():
            if key.startswith("messages/"):
                json.dumps(val, ensure_ascii=False)  # قابل سریال‌شدن بودن
        # ۴) جایگزینی اتمیک فایل به فایل
        for name, val in files.items():
            if name.startswith("messages/"):
                continue  # بعداً یکجا
            _atomic_write(os.path.join(STORE.root, name),
                          json.dumps(val, ensure_ascii=False, separators=(",", ":")))
        MSGS.replace_all(files, keep_missing=False)
        # ۵) بازسازی کش‌ها
        STORE.reload_all()
        # ۶) بررسی نتیجه واقعی
        now_counts = compute_counts()
        restored_users = len(STORE.get("users"))
        if restored_users != len(test_users):
            raise RuntimeError(f"تطابق تعداد کاربران پس از بازیابی برقرار نشد ({restored_users})")
        STORE.update("settings", lambda s: dict(s, maintenance=False))
        audit("owner", "restore_success", target=os.path.basename(staged_path),
              details=f"users:{restored_users}")
        return (True, {"users": restored_users, "counts": now_counts})
    except Exception as e:
        LOG.error("بازیابی ناموفق بود: %s", e)
        # بازگشت امن به نسخه قبلی
        rolled_back = False
        try:
            if pre_restore_rec is not None:
                pr_path = backup_path(pre_restore_rec)
                with open(pr_path, "r", encoding="utf-8") as f:
                    prev = json.load(f)
                for name, val in prev["files"].items():
                    if name.startswith("messages/"):
                        continue
                    _atomic_write(os.path.join(STORE.root, name),
                                  json.dumps(val, ensure_ascii=False, separators=(",", ":")))
                MSGS.replace_all(prev["files"], keep_missing=False)
                STORE.reload_all()
                rolled_back = True
        except Exception as e2:
            log_exc("بازگشت امن نیز ناموفق بود: %s", e2)
        STORE.update("settings", lambda s: dict(s, maintenance=False))
        audit("owner", "restore_failed", target=os.path.basename(staged_path),
              details=(f"rollback:{rolled_back} err:{e.__class__.__name__}"))
        return (False, f"بازیابی ناموفق بود؛ دیتابیس قبلی {'حفظ شد' if rolled_back else 'در وضعیت بکاپ پیش از بازیابی قرار دارد'}. خطا: {e.__class__.__name__}")
# ============================================================
# 21) پنل مالک — داشبورد، مدیریت کاربران، گزارش‌ها، اطلاع‌رسانی
# ============================================================

BOT_START_TS = None  # در main() مقداردهی می‌شود


def dashboard_text() -> str:
    ensure_storage()
    users = STORE.get("users")
    convs = STORE.get("conversations")
    settings = STORE.get("settings")
    now = now_utc()
    active_24h = sum(1 for u in users.values()
                     if _within(u.get("last_seen"), now, hours=24))
    banned = sum(1 for u in users.values() if is_banned(u))
    active_convs = sum(1 for c in convs.values() if c.get("status") == "active")
    open_reports = sum(1 for r in STORE.get("reports") if r.get("status") in ("new", "in_review"))
    warnings = len(STORE.get("warnings"))
    hist = STORE.get("backup_history")
    last_bk = hist[-1] if hist else None
    bot_state = "🟢 روشن" if settings.get("bot_enabled", True) else "🔴 خاموش"
    if settings.get("maintenance"):
        bot_state += " (حالت نگهداری)"
    uptime = "—"
    if BOT_START_TS:
        secs = int((_time.time() - BOT_START_TS))
        uptime = f"{fa_num(secs // 3600)} ساعت و {fa_num((secs % 3600) // 60)} دقیقه"
    return (
        "📊 <b>داشبورد (آمار واقعی دیتابیس)</b>\n\n"
        f"👥 کل کاربران: <b>{fa_num(len(users))}</b>\n"
        f"🟢 کاربران فعال (۲۴ ساعت اخیر): <b>{fa_num(active_24h)}</b>\n"
        f"⛔ بن‌شده: <b>{fa_num(banned)}</b>\n"
        f"💬 کل مکالمات: <b>{fa_num(len(convs))}</b>\n"
        f"🔗 مکالمات فعال: <b>{fa_num(active_convs)}</b>\n"
        f"🛡 گزارش‌های باز: <b>{fa_num(open_reports)}</b>\n"
        f"⚠️ کل اخطارها: <b>{fa_num(warnings)}</b>\n"
        f"⭕ وضعیت ربات: {bot_state}\n"
        f"⏱ زمان اجرا: {uptime}\n"
        f"💾 آخرین بکاپ موفق: <b>{last_bk['created_tehran'] if last_bk else '—'}</b>\n"
        f"امروز: {jalali(now)}"
    )


def _within(iso: str, now: datetime, hours: int = 24) -> bool:
    try:
        return now - parse_iso(iso) <= timedelta(hours=hours)
    except Exception:
        return False


def users_list_text(page: int):
    ensure_storage()
    users = list(STORE.get("users").values())
    users.sort(key=lambda u: u.get("created") or "", reverse=True)
    chunk, page, pages = pager(users, page, 10)
    lines = [f"👥 <b>مدیریت کاربران</b> ({fa_num(len(users))} کاربر)", ""]
    kb_rows = []
    for u in chunk:
        state = "⛔" if is_banned(u) else ("💬" if u.get("conv") else "🟢")
        lines.append(f"{state} <code>{u.get('internal') or '—'}</code> | {u.get('name') or 'بدون ثبت‌نام'}")
        kb_rows.append([InlineKeyboardButton(
            f"👤 {u.get('internal') or u['tg']}",
            callback_data=f"pn_u:{u['tg']}")])
    kb_rows.extend(nav_rows("pn_up", page, pages, back_cd="pn"))  # بازگشت به پنل اصلی
    return "\n".join(lines), InlineKeyboardMarkup(kb_rows)


def user_view_text(uid: int, back_cd: str = "pn_users"):
    u = get_user(uid)
    if not u:
        return "ℹ️ کاربر یافت نشد.", None
    rel = STORE.get("relationships").get(str(uid), [])
    rel_lines = []
    for item in rel[:20]:
        partner = get_user(int(item["p"])) if str(item.get("p", "")).isdigit() else None
        pid = partner.get("internal") or item["p"] if partner else item["p"]
        # فقط شناسه اختصاصی طرف مقابل و وضعیت بلاک نمایش داده می‌شود
        rel_lines.append(f"• {pid} | {'🚫 بلاک' if item.get('blocked') else '✅'} | {jalali(parse_iso(item['last']))}")
    bans_hist = [b for b in STORE.get("bans") if b.get("uid") == str(uid)][-10:]
    ban_lines = []
    for b in bans_hist:
        kind = {"temp": "موقت", "perm": "دائمی", "mute": "سکوت"}.get(b.get("type"), "?")
        act = "فعال" if b.get("active") else "پایان‌یافته"
        ban_lines.append(f"• {kind} | {b.get('reason') or '—'} | {jalali(parse_iso(b['created']))} | {act}")
    ban_state = "ندارد"
    if u.get("ban"):
        if u["ban"].get("perm"):
            ban_state = "دائمی"
        else:
            try:
                ban_state = "موقت تا " + jalali(parse_iso(u["ban"]["until"]))
            except Exception:
                ban_state = "موقت"
    txt = (
        f"👤 <b>کاربر {u.get('name') or 'بدون ثبت‌نام'}</b>\n\n"
        f"🆔 شناسه اختصاصی: <code>{u.get('internal') or '—'}</code>\n"
        f"🔢 شناسه تلگرام: <code>{u['tg']}</code>\n"
        f"🚻 جنسیت: {'پسر' if u.get('gender') == 'male' else 'دختر' if u.get('gender') == 'female' else '—'}\n"
        f"🎂 سن: {fa_num(u.get('age') or '—')}\n"
        f"🗺 استان: {u.get('province') or '—'}\n"
        f"📅 اولین ورود: {jalali(parse_iso(u['created']))}\n"
        f"💬 چت‌ها: {fa_num(u.get('chats', 0))} | 🚫 بلاک‌ها: {fa_num(u.get('blocks_made', 0))} | ⚠️ اخطارها: {fa_num(u.get('warnings', 0))}\n"
        f"🔒 رضایت حریم خصوصی: {'تأیید' if u.get('consent') == 'accepted' else 'رد' if u.get('consent') == 'declined' else 'بدون پاسخ'}\n"
        f"⛔ وضعیت بن: {ban_state}\n"
        f"🤫 سکوت: {jalali(parse_iso(u['mute_until'])) if u.get('mute_until') else 'ندارد'}\n\n"
        f"📜 <b>تاریخچه ارتباطات</b> (فقط شناسه طرف مقابل و وضعیت بلاک):\n"
        + ("\n".join(rel_lines) if rel_lines else "• موردی ثبت نشده") + "\n\n"
        f"🧾 <b>تاریخچه بن</b>:\n" + ("\n".join(ban_lines) if ban_lines else "• موردی ثبت نشده")
    )
    kb = imarkup([
        [("btn_next", f"pn_ua:{uid}:msg", " ارسال پیام", "primary"), ("btn_next", f"pn_ua:{uid}:edit", " تغییر مشخصات", "primary")],
        [("btn_next", f"pn_ua:{uid}:warn", " اخطار", "danger"), ("btn_next", f"pn_ua:{uid}:ban", "بن موقت", "danger")],
        [("btn_next", f"pn_ua:{uid}:perm", "بن دائم", "danger"), ("btn_next", f"pn_ua:{uid}:unban", " رفع بن", "success")],
        [("btn_next", f"pn_ua:{uid}:unmute", "رفع سکوت", "success")],
        [("btn_next", f"pn_sec:{uid}", "وضعیت امنیتی و مجازات‌ها", "primary")],
        [("btn_back", back_cd)],
    ])
    return txt, kb


def reports_list_text(page: int):
    reports = sorted(STORE.get("reports"), key=lambda r: r.get("created") or "", reverse=True)
    chunk, page, pages = pager(reports, page, 10)
    status_fa = {"new": "🆕 جدید", "in_review": "🔍 در حال بررسی", "reviewed": "✅ بررسی‌شده"}
    lines = [f"🛡 <b>گزارش‌ها</b> ({fa_num(len(reports))})", ""]
    kb_rows = []
    for r in chunk:
        lines.append(f"• {r['rid']} | {status_fa.get(r.get('status'), '?')} | {jalali(parse_iso(r['created']))}")
        kb_rows.append([InlineKeyboardButton(f" {r['rid']}", callback_data=f"pn_rv:{r['rid']}")])
    kb_rows.extend(nav_rows("pn_rp", page, pages, back_cd="pn"))
    return "\n".join(lines), InlineKeyboardMarkup(kb_rows)


def report_view_text(rid: str):
    r = next((x for x in STORE.get("reports") if x.get("rid") == rid), None)
    if not r:
        return "ℹ️ گزارش یافت نشد.", None
    rep_u = get_user(int(r["reporter"])) if str(r.get("reporter", "")).isdigit() else None
    repd_u = get_user(int(r["reported"])) if str(r.get("reported", "")).isdigit() else None
    status_fa = {"new": "🆕 جدید", "in_review": "🔍 در حال بررسی", "reviewed": "✅ بررسی‌شده"}
    notes = r.get("notes", [])
    note_lines = [f"• {jalali(parse_iso(n['time']))}: {n['text'][:100]}" for n in notes[-5:]]
    conv = get_conv(r.get("conv") or "")
    msgs_count = len(MSGS.get(r.get("conv") or "").get("messages", [])) if conv else 0
    txt = (
        f"🛡 <b>گزارش {r['rid']}</b>\n\n"
        f"🆔 مکالمه: <code>{r.get('conv')}</code> ({'فعال' if conv and conv.get('status') == 'active' else 'بسته'})\n"
        f"👤 گزارش‌دهنده: <code>{r.get('reporter_internal') or r.get('reporter')}</code>\n"
        f"🎯 کاربر گزارش‌شده: <code>{repd_u.get('internal') if repd_u else r.get('reported')}</code>\n"
        f"⏱ زمان: {jalali(parse_iso(r['created']))}\n"
        f"📌 وضعیت: {status_fa.get(r.get('status'), '?')}\n"
        f"📝 دلیل: {r.get('reason') or '(ننوشته)'}\n"
        f"💬 پیام‌های مرتبط: {fa_num(msgs_count)}\n"
        f"🗂 نتیجه: {r.get('outcome') or '—'}\n"
        + (("\n📝 <b>یادداشت‌ها:</b>\n" + "\n".join(note_lines)) if note_lines else "")
    )
    kb = imarkup([
        [("btn_next", f"pn_ra:{rid}:review", "شروع بررسی"), ("btn_next", f"pn_ra:{rid}:msgs", "مشاهده پیام‌ها")],
        [("btn_next", f"pn_ra:{rid}:msg_r", " پیام به گزارش‌دهنده"), ("btn_next", f"pn_ra:{rid}:msg_b", " پیام به گزارش‌شده")],
        [("btn_next", f"pn_ra:{rid}:warn", " اخطار به گزارش‌شده"), ("btn_next", f"pn_ra:{rid}:ban", "بن موقت")],
        [("btn_next", f"pn_ra:{rid}:perm", "بن دائم"), ("btn_next", f"pn_ra:{rid}:note", "یادداشت")],
        [("btn_next", f"pn_ra:{rid}:confirm", "تأیید تخلف"), ("btn_reject", f"pn_ra:{rid}:reject", "رد گزارش")],
        [("btn_back", "pn_rpts")],
    ])
    return txt, kb


def report_messages_text(rid: str, page: int):
    r = next((x for x in STORE.get("reports") if x.get("rid") == rid), None)
    conv = get_conv(r.get("conv") or "") if r else None
    if not r or not conv:
        return "ℹ️ مکالمه گزارش یافت نشد.", None
    recs = MSGS.get(conv["id"]).get("messages", [])
    chunk, page, pages = pager(recs, page, 8)
    lines = [f"💬 <b>پیام‌های مکالمه {conv['id']}</b>", ""]
    kb_rows = []
    for rec in chunk:
        sender = "؟"
        if str(rec.get("sender")) == str(r.get("reporter")):
            sender = "گزارش‌دهنده"
        elif str(rec.get("sender")) == str(r.get("reported")):
            sender = "گزارش‌شده"
        lines.append(f"[{sender}] {jalali(parse_iso(rec['created']))}\n{msg_line(rec)}")
        kb_rows.append([InlineKeyboardButton(" ارسال این پیام به من", callback_data=f"pn_rmsg:{rid}:{page}:{rec['mid']}")])
    kb_rows.extend(nav_rows(f"pn_rm:{rid}", page, pages, back_cd=f"pn_rv:{rid}"))
    audit("owner", "report_message_access", target=rid, details=f"page:{page}")
    return "\n".join(lines), InlineKeyboardMarkup(kb_rows)


async def send_report_message_to_owner(context, rid: str, mid: str) -> bool:
    r = next((x for x in STORE.get("reports") if x.get("rid") == rid), None)
    if not r:
        return False
    conv_id = r.get("conv") or ""
    rec = next((m for m in MSGS.get(conv_id).get("messages", []) if m.get("mid") == mid), None)
    if not rec:
        return False
    audit("owner", "report_message_access_single", target=rid, details=mid)
    sender_tg = int(rec.get("sender") or 0)
    delivered = rec.get("delivered", {})
    for src in [sender_tg] + [dv.get("chat") for dv in delivered.values()]:
        try:
            await context.bot.copy_message(chat_id=OWNER_ID, from_chat_id=src,
                                           message_id=rec.get("src_msg_id"))
            return True
        except TelegramError:
            continue
    body = "«حذف شده» " if (rec.get("removed") or rec.get("deleted_for")) else ""
    await send_text(context.bot, OWNER_ID, f"محتوای پیام ({rec.get('kind')}):\n{body}{msg_preview(rec)}")
    return True


def broadcast_confirm_kb(pin: bool = False, react: bool = False):
    """دکمه‌های تأیید ارسال همگانی — سنجاق و واکنش روی پیام فعال/غیرفعال می‌شوند."""
    pin_txt = "📌 سنجاق: روشن" if pin else "📌 سنجاق: خاموش"
    react_txt = "👍 واکنش: روشن" if react else "👍 واکنش: خاموش"
    return imarkup([
        [("btn_next", "pn_bc_pin", pin_txt), ("btn_next", "pn_bc_react", react_txt)],
        [("btn_next", "pn_bc_sched", "⏰ ارسال زمان‌بندی‌شده / تکرارشونده")],
        [("btn_confirm", "pn_bc_go", "ارسال به همه"), ("btn_reject", "pn_bc_no", "انصراف")],
    ])


def broadcast_jobs_list_text() -> str:
    """فهرست ارسال‌های همگانی زمان‌بندی‌شده/تکرارشونده (زنده از دیتابیس)."""
    jobs = [b for b in STORE.get("broadcast_jobs") if isinstance(b, dict)
            and not b.get("cancelled") and not b.get("finished")]
    if not jobs:
        return ("⏰ <b>ارسال همگانی زمان‌بندی‌شده</b>\n\n"
                "هیچ ارسال زمان‌بندی‌شده‌ای فعال نیست.\n\n"
                "برای ساخت ارسال جدید، از «اطلاع‌رسانی» متن پیام را آماده کنید و سپس "
                "دکمه «ارسال زمان‌بندی‌شده» را بزنید.")
    lines = ["⏰ <b>ارسال‌های همگانی زمان‌بندی‌شده</b>", ""]
    for j in jobs:
        run = parse_iso(j["next_run"]) if j.get("next_run") else None
        run_fa = jalali(run) if run else "—"
        if j.get("repeat_hours"):
            mode = f"تکرار هر {fa_num(j['repeat_hours'])} ساعت"
            if j.get("repeat_count"):
                mode += f" ({fa_num(j.get('sent_count', 0))}/{fa_num(j['repeat_count'])})"
        else:
            mode = "یک‌بار"
        pin_s = "📌" if j.get("pin") else ""
        react_s = "👍" if j.get("react") else ""
        preview = (j.get("text") or "").replace("\n", " ")[:40]
        lines.append(f"• <code>{j['jid']}</code> — {mode} {pin_s}{react_s}")
        lines.append(f"  ▸ ارسال بعدی: {run_fa}")
        lines.append(f"  ▸ متن: {esc(preview)}…")
        lines.append("")
    lines.append("برای لغو هر مورد، دکمه حذف کنار آن را بزنید.")
    return "\n".join(lines)


def broadcast_jobs_kb() -> InlineKeyboardMarkup:
    jobs = [b for b in STORE.get("broadcast_jobs") if isinstance(b, dict)
            and not b.get("cancelled") and not b.get("finished")]
    rows = []
    for j in jobs:
        label = "تکرار" if j.get("repeat_hours") else "یک‌بار"
        rows.append([InlineKeyboardButton(f"🗑 حذف {label} ({j['jid'][-6:]})",
                                          callback_data=f"pn_bj_del:{j['jid']}")])
    rows.append([ib("btn_back", "pn_bc_jobs")])
    return InlineKeyboardMarkup(rows)


def add_broadcast_job(text: str, delay_minutes: int, repeat_hours: int = 0,
                      repeat_count: int = 0, pin: bool = False, react: bool = False) -> str:
    """ثبت ارسال همگانی زمان‌بندی‌شده؛ repeat_hours>0 یعنی تکرارشونده (۰=یک‌بار).
    repeat_count=0 یعنی بی‌نهایت تکرار. ماندگار در دیتابیس و مقاوم به Restart."""
    jid = "bj" + os.urandom(4).hex()
    next_run = now_utc() + timedelta(minutes=max(0, int(delay_minutes)))

    def _m(lst):
        lst.append({
            "jid": jid, "text": text,
            "delay_minutes": int(delay_minutes),
            "repeat_hours": int(repeat_hours),       # 0 = یک‌بار
            "repeat_count": int(repeat_count),        # 0 = بی‌نهایت
            "sent_count": 0,
            "pin": bool(pin), "react": bool(react),
            "next_run": iso_utc(next_run),
            "created": iso_utc(now_utc()),
            "cancelled": False, "finished": False, "last_result": None,
        })
        return lst
    STORE.update("broadcast_jobs", _m)
    audit("owner", "broadcast_job_created", target=jid,
          details=f"delay:{delay_minutes}m repeat:{repeat_hours}h count:{repeat_count} pin:{pin} react:{react}")
    return jid


def cancel_broadcast_job(jid: str) -> bool:
    def _m(lst):
        for j in lst:
            if j.get("jid") == jid and not j.get("finished"):
                j["cancelled"] = True
        return lst
    res = STORE.update("broadcast_jobs", _m)
    ok = any(j.get("jid") == jid and j.get("cancelled") for j in res)
    if ok:
        audit("owner", "broadcast_job_cancelled", target=jid)
    return ok


def due_broadcast_jobs() -> list:
    """ارسال‌های زمان‌بندی‌شده‌ای که زمانشان رسیده (بدون تغییر وضعیت)."""
    now = now_utc()
    out = []
    for j in STORE.get("broadcast_jobs"):
        if not isinstance(j, dict) or j.get("cancelled") or j.get("finished"):
            continue
        try:
            if parse_iso(j["next_run"]) <= now:
                out.append(j)
        except Exception:
            continue
    return out


def advance_broadcast_job(jid: str, sent: int, failed: int):
    """پس از هر ارسال: شمارنده به‌روز، ارسال بعدی محاسبه یا کار پایان می‌یابد."""
    def _m(lst):
        for j in lst:
            if j.get("jid") != jid or j.get("cancelled") or j.get("finished"):
                continue
            j["sent_count"] = int(j.get("sent_count", 0)) + 1
            j["last_result"] = f"sent:{sent} failed:{failed} at:{iso_utc(now_utc())}"
            rh = int(j.get("repeat_hours", 0) or 0)
            rc = int(j.get("repeat_count", 0) or 0)
            if rh <= 0 or (rc > 0 and j["sent_count"] >= rc):
                j["finished"] = True
                j["next_run"] = None
            else:
                j["next_run"] = iso_utc(now_utc() + timedelta(hours=rh))
            return lst
        return lst
    STORE.update("broadcast_jobs", _m)


async def do_broadcast(context, text: str, pin: bool = False, react: bool = False):
    """ارسال همگانی با حفظ فرمت‌های تلگرام (Bold/Italic/...).
    pin=True → نمونه پیام در چت هر کاربر سنجاق می‌شود.
    react=True → واکنش رسمی تلگرام 👍 روی پیام برای هر کاربر ثبت می‌شود."""
    users = STORE.get("users")
    targets = [int(t) for t, u in users.items()
               if u.get("consent") == "accepted" and u.get("registered") and not is_owner(int(t))]
    sent, failed, pinned, reacted = 0, 0, 0, 0
    delivered = []  # (tg, message_id) برای سنجاق/واکنش در چت خود کاربر
    for tg in targets:
        m = await send_text(context.bot, tg, f"📣 <b>پیام مدیریت</b>\n\n{text}", html=True)
        if m:
            sent += 1
            delivered.append((tg, m.message_id))
        else:
            failed += 1
        await asyncio.sleep(0.06)
    # سنجاق و واکنش روی «نمونه پیام در چت خود هر کاربر» — بعد از ارسال موفق
    if pin:
        for tg, mid in delivered:
            try:
                await context.bot.pin_chat_message(chat_id=tg, message_id=mid,
                                                   disable_notification=True)
                pinned += 1
            except TelegramError:
                pass
            await asyncio.sleep(0.05)
    if react:
        for tg, mid in delivered:
            try:
                await context.bot.set_message_reaction(chat_id=tg, message_id=mid,
                                                       reaction="👍")
                reacted += 1
            except TelegramError:
                pass
            await asyncio.sleep(0.05)
    audit("owner", "broadcast",
          details=f"sent:{sent} failed:{failed} pin:{pinned} react:{reacted}")
    return sent, failed
# ============================================================
# 22) پنل مالک — تنظیمات، فرمت‌ها، ضد فحاشی، عضویت اجباری،
#     پشتیبانی، وضعیت ربات، ظاهر دکمه‌ها، لاگ‌ها، چت‌های مدیر
# ============================================================

def settings_text() -> str:
    s = STORE.get("settings")
    cap = s.get("warning_cap", 3)
    action_fa = {"warn": "فقط اخطار", "mute": "سکوت", "ban": "بن موقت", "perm": "بن دائم"}.get(s.get("profanity_action"), "؟")
    hours = s.get("profanity_hours") or ["همیشه فعال"]
    return (
        "⚙️ <b>تنظیمات سیستمی</b>\n\n"
        f"⚠️ سقف اخطار: <b>{fa_num(cap)}</b>\n"
        f"🧹 نوع مجازات ضد فحاشی: <b>{action_fa}</b>\n"
        f"⏳ مدت مجازات: <b>{fa_num(s.get('punishment_minutes', 60))}</b> دقیقه\n"
        f"🚦 ساعات فعالیت فیلتر: <b>{fa_num('، '.join(hours))}</b>\n"
        f"⏱ سقف نرخ پیام: <b>{fa_num(s.get('rate_limit_per_minute', 20))}</b>/دقیقه\n"
        f"🕒 نگهداری پیام‌ها: <b>{fa_num(s.get('retention_hours', 72))}</b> ساعت\n"
        f"⏰ صف انتظار: <b>{fa_num(s.get('queue_timeout_minutes', 30))}</b> دقیقه | درخواست دوست: <b>{fa_num(s.get('request_timeout_minutes', 10))}</b> دقیقه\n"
        f"👤 مشخصات پروفایل مالک: {s.get('owner_name') or '—'}\n\n"
        "برای تغییر هر مورد، دکمه مربوطه را بزنید:"
    )


def settings_kb() -> InlineKeyboardMarkup:
    return imarkup([
        [("btn_next", "pn_sa:cap", "سقف اخطار"), ("btn_next", "pn_sa:action", "نوع مجازات")],
        [("btn_next", "pn_sa:minutes", "مدت مجازات"), ("btn_next", "pn_sa:rate", "نرخ پیام")],
        [("btn_next", "pn_sa:retention", "نگهداری پیام"), ("btn_next", "pn_sa:qtimeout", "صف انتظار")],
        [("btn_next", "pn_sa:rtimeout", "درخواست دوست"), ("btn_next", "pn_sa:oname", "پروفایل مالک")],
        [("btn_next", "pn_sa:auto_bk", "بکاپ خودکار"), ("btn_next", "pn_sa:bk_keep", "تعداد بکاپ")],
        [("btn_back", "pn")],
    ])


def formats_text() -> str:
    s = STORE.get("settings")
    formats = s.get("formats", {})
    rows = []
    for i, k in enumerate(FORMAT_KEYS):
        st = "✅" if formats.get(k, True) else "⛔"
        rows.append(f"{fa_num(i + 1)}. {FORMAT_LABELS[k]}: {st}")
    unk = "✅" if s.get("allow_unknown_files") else "⛔"
    rows.append(f"—. فایل‌های نوع ناشناخته: {unk}")
    lnk = formats.get("web_link", True)
    rows.append("")
    rows.append(f"🔗 فرمت دامنه (www / http / https و دامنه ساده): {'✅ مجاز' if lnk else '⛔ ممنوع'}")
    warn = "🟢 روشن" if s.get("link_warning_enabled", True) else "🔴 خاموش"
    rows.append(f"⚠️ هشدار لینک برای دریافت‌کننده: {warn}")
    rows.append(f"📝 متن هشدار: {s.get('link_warning_text') or LINK_WARNING_DEFAULT}")
    return ("🗂 <b>مدیریت فرمت‌های مجاز</b>\n\n"
            "✅ مجاز | ⛔ ممنوع — تغییرات بلافاصله و بدون Restart اعمال می‌شود:\n\n"
            + "\n".join(rows) +
            "\n\nℹ️ تشخیص فایل بر اساس ساختار و MIME انجام می‌شود؛ نه صرفاً نام فایل.\n"
            "ℹ️ «لینک وب» شامل www، http، https و دامنه‌های ساده (مثل example.com) است؛ "
            "بستن آن ارسال همه لینک‌های غیرتلگرام را مسدود می‌کند و هشدار لینک دیگر نمایش داده نمی‌شود.")


def formats_kb() -> InlineKeyboardMarkup:
    s = STORE.get("settings")
    formats = s.get("formats", {})
    rows = []
    for i in range(0, len(FORMAT_KEYS), 2):
        pair = []
        for k in FORMAT_KEYS[i:i + 2]:
            st = "✅" if formats.get(k, True) else "⛔"
            pair.append(InlineKeyboardButton(f"{st} {FORMAT_LABELS[k]}", callback_data=f"pn_fa:{k}"))
        rows.append(pair)
    unk = "✅" if s.get("allow_unknown_files") else "⛔"
    rows.append([InlineKeyboardButton(f"{unk} فایل ناشناخته", callback_data="pn_fa:allow_unknown")])
    warn = "🟢 هشدار لینک: روشن" if s.get("link_warning_enabled", True) else "🔴 هشدار لینک: خاموش"
    rows.append([InlineKeyboardButton(warn, callback_data="pn_fa:link_warn")])
    rows.append([InlineKeyboardButton("📝 ویرایش متن هشدار لینک", callback_data="pn_fa:link_warn_text")])
    rows.append([ib("btn_back", "pn")])
    return InlineKeyboardMarkup(rows)


def profanity_text() -> str:
    s = STORE.get("settings")
    cfg = STORE.get("profanity_words")
    days = s.get("profanity_weekdays", [0, 1, 2, 3, 4, 5, 6])
    day_str = "، ".join(WEEKDAY_LABELS[d] for d in sorted(days)) or "—"
    return (
        "🧹 <b>سیستم ضد فحاشی</b>\n\n"
        f"وضعیت: {'🟢 روشن' if s.get('profanity_enabled', True) else '🔴 خاموش'}\n"
        f"سقف اخطار: <b>{fa_num(s.get('warning_cap', 3))}</b>\n"
        f"بازه‌های زمانی: <b>{fa_num('، '.join(s.get('profanity_hours') or ['همیشه']))}</b>\n"
        f"روزهای هفته: <b>{day_str}</b>\n"
        f"واژه‌های ممنوع سفارشی: <b>{fa_num(len(cfg.get('custom_blocked', [])))}</b>\n"
        f"واژه‌های مجاز (whitelist): <b>{fa_num(len(cfg.get('custom_whitelist', [])))}</b>\n"
        f"نسخه فیلتر: <b>{PROFANITY_VERSION}</b>\n\n"
        "ℹ️ خاموش بودن فحاشی، کنترل فرمت‌های ممنوع و امنیت پایه را غیرفعال نمی‌کند."
    )


def profanity_kb() -> InlineKeyboardMarkup:
    s = STORE.get("settings")
    cfg = STORE.get("profanity_words")
    st = "🔴 خاموش کردن" if s.get("profanity_enabled", True) else "🟢 روشن کردن"
    rows = [[InlineKeyboardButton(st, callback_data="pn_pa:toggle")]]
    rows.append([InlineKeyboardButton(" افزودن واژه ممنوع", callback_data="pn_pa:wadd"),
                 InlineKeyboardButton(" افزودن مجاز", callback_data="pn_pa:wladd")])
    rows.append([InlineKeyboardButton(" واژه‌های ممنوع", callback_data="pn_pa:words"),
                 InlineKeyboardButton(" واژه‌های مجاز", callback_data="pn_pa:wlist")])
    rows.append([InlineKeyboardButton("⏰ بازه‌های زمانی", callback_data="pn_pa:hours"),
                 InlineKeyboardButton(" روزهای هفته", callback_data="pn_pa:days")])
    rows.append([ib("btn_back", "pn")])
    return InlineKeyboardMarkup(rows)


def profanity_words_text(which: str, page: int):
    cfg = STORE.get("profanity_words")
    items = cfg.get("custom_blocked" if which == "b" else "custom_whitelist", [])
    chunk, page, pages = pager(items, page, 10)
    title = "واژه‌های ممنوع سفارشی" if which == "b" else "واژه‌های مجاز سفارشی"
    lines = [f"📜 <b>{title}</b> ({fa_num(len(items))})", ""]
    kb_rows = []
    for i, w in enumerate(chunk):
        gidx = page * 10 + i
        lines.append(f"{fa_num(gidx + 1)}. {w}")
        kb_rows.append([InlineKeyboardButton(f" حذف «{w[:18]}»", callback_data=f"pn_pw:{which}:{gidx}")])
    kb_rows.extend(nav_rows(f"pn_pwp:{which}", page, pages, back_cd="pn_prof"))
    return "\n".join(lines), InlineKeyboardMarkup(kb_rows)


def profanity_days_kb() -> InlineKeyboardMarkup:
    s = STORE.get("settings")
    days = set(s.get("profanity_weekdays", []))
    rows = []
    for i in range(0, 7, 2):
        pair = []
        for d in WEEKDAY_LABELS[i:i + 2]:
            idx = WEEKDAY_LABELS.index(d)
            st = "✅" if idx in days else "⛔"
            pair.append(InlineKeyboardButton(f"{st} {d}", callback_data=f"pn_pd:{idx}"))
        rows.append(pair)
    rows.append([ib("btn_back", "pn_prof")])
    return InlineKeyboardMarkup(rows)


def profanity_hours_text() -> str:
    s = STORE.get("settings")
    hours = s.get("profanity_hours", [])
    lines = ["⏰ <b>بازه‌های فعالیت فیلتر فحاشی (ساعت تهران)</b>", ""]
    for i, h in enumerate(hours):
        lines.append(f"{fa_num(i + 1)}. {fa_num(h)}")
    lines.append("")
    lines.append("فرمت افزودن بازه: «22:00-06:00» — بدون بازه یعنی همیشه فعال.")
    kb_rows = []
    for i in range(len(hours)):
        kb_rows.append([InlineKeyboardButton(f" حذف بازه {fa_num(i + 1)}", callback_data=f"pn_ph:{i}")])
    kb_rows.append([ib("btn_next", "pn_pa:hadd", "افزودن بازه"), ib("btn_back", "pn_prof")])
    return "\n".join(lines), InlineKeyboardMarkup(kb_rows)

# ---------- عضویت اجباری ----------

def channels_text() -> str:
    conf = STORE.get("mandatory_channels")
    chs = conf.get("channels", [])
    lines = [f"📢 <b>عضویت اجباری</b> — وضعیت: {'🟢 فعال' if conf.get('enabled') else '🔴 غیرفعال'}", ""]
    for i, ch in enumerate(chs):
        lines.append(f"{fa_num(i + 1)}. {ch.get('title')} | <code>{ch.get('target')}</code>")
    if not chs:
        lines.append("• موردی ثبت نشده")
    return "\n".join(lines)


def channels_kb() -> InlineKeyboardMarkup:
    conf = STORE.get("mandatory_channels")
    chs = conf.get("channels", [])
    st = "🔴 غیرفعال‌سازی" if conf.get("enabled") else "🟢 فعال‌سازی"
    rows = [[InlineKeyboardButton(st, callback_data="pn_ca:toggle"),
             InlineKeyboardButton(" افزودن کانال/گروه", callback_data="pn_ca:add")]]
    for i, ch in enumerate(chs):
        rows.append([InlineKeyboardButton(f" حذف «{ch.get('title')[:16]}»", callback_data=f"pn_cr:{i}")])
    rows.append([ib("btn_back", "pn")])
    return InlineKeyboardMarkup(rows)

# ---------- پشتیبانی ----------

def tickets_list_text(page: int):
    tickets = sorted(STORE.get("tickets"), key=lambda t: t.get("updated") or "", reverse=True)
    chunk, page, pages = pager(tickets, page, 10)
    lines = [f"🟡 <b>درخواست‌های پشتیبانی</b> ({fa_num(len(tickets))})", ""]
    kb_rows = []
    for t in chunk:
        lines.append(f"• {t['tid']} | {ticket_status_fa(t.get('status'))} | {jalali(parse_iso(t.get('updated') or t['created']))}")
        kb_rows.append([InlineKeyboardButton(f" {t['tid']}", callback_data=f"pn_tv:{t['tid']}")])
    kb_rows.extend(nav_rows("pn_tp", page, pages, back_cd="pn"))
    return "\n".join(lines), InlineKeyboardMarkup(kb_rows)


def ticket_view_text(tid: str):
    t = get_ticket(tid)
    if not t:
        return "ℹ️ تیکت یافت نشد.", None
    u = get_user(int(t["uid"]))
    msgs = get_ticket_messages(tid)
    lines = [f"🎫 <b>تیکت {tid}</b>",
             f"👤 کاربر: <code>{u.get('internal') if u else '—'}</code> | وضعیت: {ticket_status_fa(t.get('status'))}", ""]
    for m in msgs[-15:]:
        who = "👤 کاربر" if m.get("who") == "user" else "🛡 مدیریت"
        lines.append(f"{who} | {jalali(parse_iso(m['created']))}")
        lines.append(m["text"][:300])
        lines.append("")
    kb = imarkup([
        [("btn_next", f"pn_ta:{tid}:reply", " پاسخ"), ("btn_next", f"pn_ta:{tid}:open", "در حال بررسی")],
        [("btn_reject", f"pn_ta:{tid}:close", "بستن درخواست")],
        [("btn_back", "pn_supp")],
    ])
    return "\n".join(lines), kb

# ---------- وضعیت ربات ----------

def bot_status_text() -> str:
    s = STORE.get("settings")
    on = s.get("sched_on", {})
    off = s.get("sched_off", {})
    return (
        "⭕ <b>مدیریت وضعیت ربات</b>\n\n"
        f"وضعیت فعلی: {'🟢 روشن' if s.get('bot_enabled', True) else '🔴 خاموش'}\n"
        f"{'🛧 حالت نگهداری فعال است\n' if s.get('maintenance') else ''}"
        f"⏰ خاموشی زمان‌بندی‌شده: {'روزانه ساعت ' + fa_num(off.get('time')) if off.get('enabled') else 'غیرفعال'}\n"
        f"⏰ روشن‌شدن زمان‌بندی‌شده: {'روزانه ساعت ' + fa_num(on.get('time')) if on.get('enabled') else 'غیرفعال'}\n\n"
        "زمان‌بندی‌ها در دیتابیس ذخیره می‌شوند و پس از Restart بازیابی می‌گردند."
    )


def bot_status_kb() -> InlineKeyboardMarkup:
    s = STORE.get("settings")
    on_state = s.get("bot_enabled", True)
    rows = [
        [("btn_confirm", "pn_ba:on", "روشن کردن فوری") if not on_state else ("btn_reject", "pn_ba:off", "خاموش کردن فوری")],
        [("btn_next", "pn_ba:sched_on", "⏰ روشن شدن زمان‌بندی"), ("btn_next", "pn_ba:sched_off", "⏰ خاموش شدن زمان‌بندی")],
        [("btn_next", "pn_ba:sched_clear", "حذف زمان‌بندی‌ها")],
        [("btn_back", "pn")],
    ]
    return imarkup(rows)

# ---------- ظاهر و رنگ دکمه‌ها ----------

def owner_chat_history_text(conv_id: str, page: int):
    conv = get_conv(conv_id)
    if not conv or str(OWNER_ID) not in conv.get("participants", []):
        return "ℹ️ مکالمه یافت نشد.", None
    recs = MSGS.get(conv_id).get("messages", [])
    chunk, page, pages = pager(recs, page, 6)
    partner = next((int(p) for p in conv["participants"] if int(p) != OWNER_ID), 0)
    pu = get_user(partner)
    lines = [f"💬 <b>تاریخچه مکالمه {conv_id}</b>",
             f"👤 طرف مقابل: <code>{pu.get('internal') if pu else partner}</code> | وضعیت: {'فعال' if conv.get('status') == 'active' else 'بسته'}", ""]
    kb_rows = []
    for rec in chunk:
        who = "🛡 مدیر" if str(rec.get("sender")) == str(OWNER_ID) else "👤 کاربر"
        lines.append(f"[{who}] {jalali(parse_iso(rec['created']))}\n{msg_line(rec)}")
        kb_rows.append([InlineKeyboardButton(f" حذف پیام {rec['mid'][-4:]}", callback_data=f"pn_od:{conv_id}:{page}:{rec['mid']}")])
    kb_rows.append([InlineKeyboardButton(" حذف کامل این تاریخچه", callback_data=f"pn_odf:{conv_id}")])
    kb_rows.extend(nav_rows(f"pn_oh:{conv_id}", page, pages, back_cd="pn_oc"))
    return "\n".join(lines), InlineKeyboardMarkup(kb_rows)


async def delete_owner_messages(context, records: list):
    """حذف مرحله‌ای پیام‌های مدیر از سرور و نمای طرف مقابل؛ پیام‌های کاربران حذف نمی‌شود."""
    bot = context.bot
    removed, tg_ok, tg_fail = 0, 0, 0
    for rec in records:
        conv_id = rec.get("conv")
        rec_removed = {"ok": False}

        def _m(d, rec=rec, rec_removed=rec_removed):
            for r in d["messages"]:
                if r.get("mid") == rec["mid"]:
                    r["removed"] = True
                    r["text"] = ""
                    r["file_id"] = None
                    rec_removed["ok"] = True
                    break
            return d
        MSGS.mutate(conv_id, _m)
        if rec_removed["ok"]:
            removed += 1
        dv = rec.get("delivered", {})
        for uid, dv_info in dv.items():
            if await try_delete(bot, int(dv_info.get("chat", 0)), dv_info.get("mid", 0)):
                tg_ok += 1
            else:
                tg_fail += 1
        await asyncio.sleep(0.05)
    return removed, tg_ok, tg_fail


async def del_all_owner_messages(context):
    """«del all / حذف همه»: حذف تمام پیام‌های مدیر در تمام گفت‌وگوهای ناشناس
    از سرور و از نمای طرف مقابل. فقط پیام‌های خودِ مدیر حذف می‌شوند."""
    records = []
    for conv_id in MSGS.list_convs():
        for rec in MSGS.get(conv_id).get("messages", []):
            if str(rec.get("sender")) == str(OWNER_ID) and not rec.get("removed"):
                records.append(rec)
    removed, tg_ok, tg_fail = await delete_owner_messages(context, records)
    audit("owner", "owner_del_all", details=f"removed:{removed} tg_ok:{tg_ok} tg_fail:{tg_fail}")
    modlog("owner", "del_all_owner_messages", OWNER_ID, f"removed:{removed}")
    return removed, tg_ok, tg_fail

# ---------- مدیریت بکاپ (پنل) ----------

def backups_text() -> str:
    hist = STORE.get("backup_history")
    last = hist[-1] if hist else None
    s = STORE.get("settings")
    auto = "🟢 روشن" if s.get("auto_backup_enabled", False) else "🔴 خاموش (پیش‌فرض نسخه ۲.۳.۰)"
    return (
        "💾 <b>مدیریت بکاپ و بازیابی</b>\n\n"
        f"بکاپ خودکار: <b>{auto}</b>\n"
        f"تعداد بکاپ‌های ثبت‌شده: <b>{fa_num(len(hist))}</b>\n"
        f"آخرین بکاپ: <b>{last['created_tehran'] if last else '—'}</b>"
        + (f" (نوع: {last['kind']}, حجم: {fa_num(last['size'] // 1024)} کیلوبایت)" if last else "") + "\n\n"
        "ایجاد بکاپ جدید | 🔵 دریافت آخرین بکاپ | 📁 بکاپ‌های قبلی | 🔄 بررسی سلامت | 📤 آپلود و بازیابی"
    )


def backups_kb() -> InlineKeyboardMarkup:
    return imarkup([
        [("btn_confirm", "pn_ba2:create", "ایجاد بکاپ جدید")],
        [("btn_next", "pn_ba2:get", "دریافت آخرین بکاپ"), ("btn_next", "pn_ba2:list", "بکاپ‌های قبلی")],
        [("btn_next", "pn_ba2:check", "بررسی سلامت بکاپ")],
        [("btn_next", "pn_ba2:restore", "آپلود بکاپ و بازیابی")],
        [("btn_back", "pn")],
    ])


def backups_list_text(page: int):
    hist = sorted(STORE.get("backup_history"), key=lambda b: b.get("created_utc") or "", reverse=True)
    chunk, page, pages = pager(hist, page, 5)
    lines = [f"📁 <b>بکاپ‌های قبلی</b> ({fa_num(len(hist))})", ""]
    kb_rows = []
    for b in chunk:
        state = "✅" if b.get("valid") and not b.get("file_deleted") else "⛔/حذف‌شده"
        lines.append(f"• {b['bid']} | {b.get('created_tehran')} | {state} | {b.get('kind')}")
        if not b.get("file_deleted"):
            kb_rows.append([InlineKeyboardButton(f"⬇ دریافت {b['bid'][-8:]}", callback_data=f"pn_bf:{b['bid']}")])
    kb_rows.extend(nav_rows("pn_bl", page, pages, back_cd="pn_bk"))
    return "\n".join(lines), InlineKeyboardMarkup(kb_rows)


def backup_check_text() -> str:
    hist = sorted(STORE.get("backup_history"), key=lambda b: b.get("created_utc") or "", reverse=True)[:5]
    lines = ["🔄 <b>بررسی سلامت ۵ بکاپ اخیر</b>", ""]
    if not hist:
        lines.append("• بکاپی ثبت نشده است")
    for b in hist:
        if b.get("file_deleted"):
            lines.append(f"• {b['bid']}: فایل حذف شده")
            continue
        ok, info = verify_backup(b)
        STORE.update("backup_history", lambda lst: [
            dict(x, valid=ok) if x.get("bid") == b["bid"] else x for x in lst])
        lines.append(f"• {b['bid']}: {'✅ سالم' if ok else '⛔ ناسالم — ' + str(info)[:60]}")
    return "\n".join(lines)
# ============================================================
# 23) مسیریابی پیام‌ها و دستورات
# ============================================================

async def membership_gate(update, context, user) -> bool:
    """کنترل عضویت اجباری با بررسی واقعی از Telegram API."""
    ok, missing = await check_membership(context.bot, user["tg"])
    if ok:
        return True
    conf = STORE.get("mandatory_channels")
    rows = []
    for ch in missing:
        url = ch.get("invite_link")
        if not url and str(ch.get("target", "")).startswith("@"):
            url = "https://t.me/" + str(ch["target"]).lstrip("@")
        if url:
            rows.append([InlineKeyboardButton(f"عضویت در {ch.get('title')}", url=url)])
    rows.append([("btn_next", "mcheck", "بررسی مجدد عضویت")])
    await send_text(context.bot, user["tg"],
                    "📢 برای استفاده از امکانات چت، ابتدا در کانال‌/گروه‌های زیر عضو شوید:",
                    imarkup(rows))
    return False


async def try_match_and_notify(context, tg_id: int, conv_id=None):
    """پس از ورود به صف، تلاش برای اتصال و اطلاع‌رسانی."""
    if not conv_id:
        conv_id = attempt_match(context)
    if not conv_id:
        await send_text(context.bot, tg_id, start_search_text(), imarkup([[("btn_reject", "qcancel", "لغو جست‌وجو")]]))
        return
    conv = get_conv(conv_id)
    intro = "<b>اتصال برقرار شد!</b>\n\nبا احترام گفت‌وگو کنید."
    for p in conv["participants"]:
        await send_text(context.bot, int(p), intro, conv_kb(), html=True)


async def start_chat_flow(update, context, user):
    tg = int(user["tg"])
    if is_owner(tg):
        user = ensure_owner_record()  # مالک معاف از ثبت‌نام
    if not user.get("registered"):
        await send_text(context.bot, tg, "ℹ️ برای شروع چت ابتدا ثبت‌نام را کامل کنید: /start")
        return
    if is_banned(user):
        await send_text(context.bot, tg, ban_notice(user))
        return
    if is_muted(user):
        await send_text(context.bot, tg, mute_notice(user), notice_kb(user))
        return
    rem = super_start_block_minutes(user)
    if rem is not None:
        await send_text(context.bot, tg, super_block_text(rem), notice_kb(user))
        return
    if user.get("conv"):
        await send_text(context.bot, tg, "ℹ️ شما در حال حاضر در یک مکالمه هستید.")
        return
    if user.get("searching"):
        await send_text(context.bot, tg, "ℹ️ شما در صف انتظار هستید.", imarkup([[("btn_reject", "qcancel", "لغو جست‌وجو")]]))
        return
    if not await membership_gate(update, context, user):
        return
    start_search(tg)
    mark_new_chat_started(tg)
    await try_match_and_notify(context, tg)


def _capture_username(update, tg: int):
    """ثبت نام کاربری تلگرام (برای نمایش در اطلاعات حساب)."""
    uname = getattr(getattr(update, "effective_user", None), "username", None)
    if uname:
        update_user(tg, lambda u: u.update({"username": str(uname).lstrip("@")}))


async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    tg = update.effective_user.id
    ensure_user(tg)
    touch_user(tg)
    _capture_username(update, tg)
    user = get_user(tg)
    settings = STORE.get("settings")

    if is_owner(tg):
        # /start همیشه صفحه اصلی را نشان می‌دهد؛ پنل فقط با دستور/دکمه اختصاصی باز می‌شود
        await send_text(context.bot, tg, MAIN_HINT, main_menu_kb())
        await send_text(context.bot, tg, "پنل مدیریت:",
                        imarkup([[("btn_next", "pn", "پنل مدیریت")]]))
        return
    if not settings.get("bot_enabled", True):
        await send_text(context.bot, tg, "⚠️ ربات در حال حاضر خاموش است. بعداً مراجعه کنید.")
        return
    if settings.get("maintenance"):
        await send_text(context.bot, tg, "ربات در حال نگهداری است؛ چند دقیقه دیگر مراجعه کنید.")
        return
    if is_banned(user):
        await send_text(context.bot, tg, ban_notice(user), notice_kb(user))
        return
    if user.get("consent") is None:
        await send_text(context.bot, tg, PRIVACY_TEXT, consent_kb())
        return
    if user.get("consent") == "declined":
        await send_text(context.bot, tg,
                        "⛔ شما سیاست حریم خصوصی را رد کرده‌اید و دسترسی به امکانات ربات ندارید.",
                        reconsent_kb())
        return
    if not user.get("registered"):
        # ادامه ثبت‌نام نیمه‌کاره از همان مرحله؛ شروع مجدد ناخواسته انجام نمی‌شود
        if not user.get("form"):
            start_registration(tg)
            user = get_user(tg)
        step = user["form"].get("step", "name")
        await send_text(context.bot, tg,
                        ("ادامه ثبت‌نام:\n\n" if user["form"].get("data") else "ثبت‌نام آغاز شد:\n\n")
                        + reg_progress(user) + REG_STEP_TEXTS.get(step, ""),
                        imarkup([[("btn_cancel", "form_cancel")]]))
        return
    clear_form(tg)
    await send_text(context.bot, tg, MAIN_HINT, main_menu_kb())
    ok, _missing = await check_membership(context.bot, tg)
    if not ok:
        await membership_gate(update, context, user)


async def cmd_info(update: Update, context: ContextTypes.DEFAULT_TYPE):
    tg = update.effective_user.id
    ensure_user(tg)
    touch_user(tg)
    _capture_username(update, tg)
    user = get_user(tg)
    if not is_owner(tg):
        settings = STORE.get("settings")
        if not settings.get("bot_enabled", True) or settings.get("maintenance"):
            await send_text(context.bot, tg, "⚠️ ربات در حال حاضر غیرفعال است.")
            return
        if is_banned(user):
            await send_text(context.bot, tg, ban_notice(user))
            return
        if user.get("consent") != "accepted":
            await send_text(context.bot, tg, "ℹ️ ابتدا سیاست حریم خصوصی را با /start تأیید کنید.")
            return
        if not user.get("registered"):
            await send_text(context.bot, tg, "ℹ️ ابتدا ثبت‌نام را کامل کنید: /start")
            return
    else:
        # مالک: اطلاعات کامل حساب بدون نیاز به ثبت‌نام
        if not user.get("internal"):
            assign_internal_id(tg)
            user = get_user(tg)
    cmd = next((c for c in get_commands() if c["name"] == "/info"), None)
    if cmd and not cmd.get("enabled", True) and not is_owner(tg):
        await send_text(context.bot, tg, "ℹ️ این دستور توسط مدیریت غیرفعال شده است.")
        return
    await send_text(context.bot, tg, info_text(user), info_kb(user))


async def cmd_supp(update: Update, context: ContextTypes.DEFAULT_TYPE):
    tg = update.effective_user.id
    ensure_user(tg)
    touch_user(tg)
    _capture_username(update, tg)
    user = get_user(tg)
    if is_banned(user):
        await send_text(context.bot, tg, ban_notice(user), notice_kb(user))
        return
    # جلوگیری از دور زدن محدودیت با پشتیبانی عادی؛ مسیر مستقل اعتراض باز می‌ماند
    if not is_owner(tg) and protection_restriction_active(user):
        await send_text(context.bot, tg,
                        "🛡 حساب شما دارای محدودیت فعال سامانه محافظت است و پشتیبانی عادی "
                        "برای دور زدن آن استفاده نمی‌شود.\n"
                        "برای همان پرونده از دکمه «ثبت اعتراض» استفاده کنید (فقط یک بار).",
                        notice_kb(user))
        return
    settings = STORE.get("settings")
    if not settings.get("bot_enabled", True) and not is_owner(tg):
        await send_text(context.bot, tg, "⚠️ ربات در حال حاضر خاموش است.")
        return
    t = open_ticket(tg)
    set_form(tg, {"kind": "support", "data": {"tid": t["tid"]}})
    await send_text(context.bot, tg,
                    "<b>پشتیبانی</b>\n\nپیام خود را ارسال کنید؛ پیام‌های شما فقط برای مدیریت ربات ارسال می‌شود.\n"
                    "برای پایان گفت‌وگو دکمه زیر را بزنید:",
                    imarkup([[("btn_reject", "sup_end", "پایان گفت‌وگو")]]))


async def cmd_guide(update: Update, context: ContextTypes.DEFAULT_TYPE):
    tg = update.effective_user.id
    ensure_user(tg)
    touch_user(tg)
    _capture_username(update, tg)
    user = get_user(tg)
    if not is_owner(tg):
        settings = STORE.get("settings")
        if is_banned(user):
            await send_text(context.bot, tg, ban_notice(user))
            return
        if not settings.get("bot_enabled", True) or settings.get("maintenance"):
            await send_text(context.bot, tg, "⚠️ ربات در حال حاضر غیرفعال است.")
            return
    cmd = next((c for c in get_commands() if c["name"] == "/guide"), None)
    if cmd and not cmd.get("enabled", True) and not is_owner(tg):
        await send_text(context.bot, tg, "ℹ️ این دستور توسط مدیریت غیرفعال شده است.")
        return
    set_form(tg, {"kind": "guide_search", "data": {}})
    await send_text(context.bot, tg, guide_main_text(is_owner(tg)), guide_main_kb(is_owner(tg)))


async def cmd_report(update: Update, context: ContextTypes.DEFAULT_TYPE):
    tg = update.effective_user.id
    ensure_user(tg)
    touch_user(tg)
    user = get_user(tg)
    if user.get("conv"):
        conv = get_conv(user["conv"])
        if conv and conv.get("status") == "active":
            await trigger_report(update, context, user, conv)
            return
    await send_text(context.bot, tg,
                    "ℹ️ برای ثبت گزارش، در حین مکالمه واژه «گزارش» یا دستور /report را ارسال کنید.")


async def cmd_panel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    tg = update.effective_user.id
    if not is_owner(tg):
        return
    ensure_user(tg)
    await send_text(context.bot, tg, OWNER_PANEL_TEXT, owner_panel_kb(), html=True)

# ---------- روتر متن ----------

OWNER_STATE_KINDS = ("panel_broadcast", "panel_user_msg", "panel_admin_reply",
                     "panel_user_warn", "panel_user_ban", "panel_user_edit",
                     "panel_search", "panel_cap", "panel_minutes", "panel_rate",
                     "panel_retention", "panel_qtimeout", "panel_rtimeout",
                     "panel_oname", "panel_obio", "panel_hours_add", "panel_wadd",
                     "panel_wladd", "panel_ch_add", "panel_ch_link", "panel_sched_on",
                     "panel_sched_off", "panel_bk_restore", "panel_rpt_note",
                     "panel_rpt_umsg", "panel_btn_text", "panel_cmd_edit",
                     # ارسال همگانی زمان‌بندی‌شده/تکرارشونده
                     "panel_bc_sched",
                     # ویرایش متن هشدار لینک (مدیریت فرمت‌ها)
                     "panel_link_warn_text",
                     # سیستم محافظت — تنظیمات عددی و عملیات امنیتی کاربر
                     "panel_prot_num", "panel_sec_num", "panel_sec_reason",
                     "panel_sec_custom",
                     # کد اختصاصی مالک — تغییر دستی
                     "panel_oc_set")


async def on_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    tg = update.effective_user.id
    ensure_user(tg)
    touch_user(tg)
    _capture_username(update, tg)
    user = get_user(tg)
    settings = STORE.get("settings")
    text = (update.effective_message.text or "").strip()

    # حالت‌های پنل مالک
    if user.get("form") and user["form"].get("kind", "").startswith("panel_"):
        if not is_owner(tg):
            clear_form(tg)
            return
        # دکمه‌های منوی اصلی/چت هرگز ورودی پنل حساب نمی‌شوند؛ زدن آن‌ها فرم پنل را
        # می‌بندد و عملکرد اصلی دکمه اجرا می‌شود (رفع باگ «شروع چت ناشناس» برای مالک).
        btn_key_panel = resolve_button_key(text)
        if btn_key_panel:
            clear_form(tg)
            user = get_user(tg)
        else:
            await handle_owner_state(update, context, user, text)
            return

    # دستورات متنی مالک (بن/سکوت/اخطار/حذف بن/حذف سکوت/گزارش/روشن) —
    # پیش از همه فرم‌ها تا هرگز به‌عنوان ورودی فرم یا پیام عادی تفسیر نشود
    if await try_owner_text_command(update, context):
        return

    if not is_owner(tg):
        if is_banned(user):
            await send_text(context.bot, tg, ban_notice(user))
            return
        if not settings.get("bot_enabled", True):
            await send_text(context.bot, tg, "⚠️ ربات در حال حاضر خاموش است.")
            return
        if settings.get("maintenance"):
            await send_text(context.bot, tg, "ربات در حال نگهداری است.")
            return

        # دکمه‌های منو (متن سفارشی‌شده مالک هم تشخیص داده می‌شود) هرگز به‌عنوان
        # ورودی فرم‌های کاربر (گزارش/اعتراض/پشتیبانی/راهنما) تفسیر نمی‌شوند؛
        # زدن دکمه فرم را می‌بندد و عملکرد اصلی اجرا می‌شود (رفع باگ شروع چت ناشناس).
        menu_key_user = resolve_button_key(text)
        if menu_key_user:
            clear_form(tg)
            user = get_user(tg)

    # فرم گزارش: دلیل
    if user.get("form") and user["form"].get("kind") == "report_reason":
        rid = user["form"]["data"].get("rid")
        save_report_reason(rid, text)
        clear_form(tg)
        await send_text(context.bot, tg, "گزارش شما با دلیل ثبت شد. به بررسی آن رسیدگی خواهد شد.", main_menu_kb())
        return

    # فرم اعتراض: متن توضیحات (سیستم محافظت)
    if user.get("form") and user["form"].get("kind") == "appeal_text":
        if text in CANCEL_KB_TEXTS:
            clear_form(tg)
            await send_text(context.bot, tg, "❌ ثبت اعتراض لغو شد.", main_menu_kb())
            return
        case = user["form"]["data"].get("case")
        form = user["form"]
        form["kind"] = "appeal_photo"
        form.setdefault("data", {})["text"] = text[:1000]
        set_form(tg, form)
        await send_text(context.bot, tg,
                        "✅ توضیحات ثبت شد. در صورت تمایل <b>تصویر پیوست</b> را ارسال کنید (اختیاری)، "
                        "یا بدون تصویر ادامه دهید:",
                        imarkup([
                            [("btn_next", f"apl_confirm:{case}", "ادامه بدون تصویر")],
                            [("btn_cancel", "apl_cancel")],
                        ]))
        return

    # جست‌وجوی راهنما
    if user.get("form") and user["form"].get("kind") == "guide_search":
        if text in CANCEL_KB_TEXTS:
            clear_form(tg)
            await send_text(context.bot, tg, MAIN_HINT, main_menu_kb())
            return
        # دکمه‌های منو هرگز «جست‌وجوی راهنما» حساب نمی‌شوند؛ کاربر با زدن دکمه منو
        # از حالت جستجو خارج می‌شود و عملکرد اصلی دکمه اجرا می‌گردد (رفع باگ شروع چت).
        btn_key_menu = resolve_button_key(text)
        if btn_key_menu:
            clear_form(tg)
            user = get_user(tg)
        else:
            results, suggestions = search_guide(text, is_owner(tg))
            clear_form(tg)
            txt, kb = guide_search_result_text(results, suggestions, text)
            set_form(tg, {"kind": "guide_search", "data": {}})
            await send_text(context.bot, tg, txt, kb)
            return

    # گفت‌وگو با پشتیبانی
    if user.get("form") and user["form"].get("kind") == "support":
        tid = user["form"]["data"].get("tid")
        if get_ticket(tid) and get_ticket(tid).get("status") != "closed":
            # حفظ فرمت‌های تلگرام کاربر (Bold/Italic/...) در ارسال به پشتیبانی
            _em = getattr(update, "effective_message", None)
            msg_html = (getattr(_em, "text_html", None) if _em is not None else None) or esc(text)
            add_ticket_message(tid, "user", text)
            if OWNER_ID:
                await send_text(context.bot, OWNER_ID,
                                "🛡 <b>پیام کاربر (پشتیبانی)</b>\n\n" + msg_html, html=True)
            await send_text(context.bot, tg, "پیام شما ثبت شد و در اسرع وقت پاسخ داده می‌شود.")
        else:
            clear_form(tg)
            await send_text(context.bot, tg, "ℹ️ این درخواست بسته شده است. برای گفت‌وگوی جدید «پشتیبانی» را ارسال کنید.", main_menu_kb())
        return

    # فرم ثبت‌نام/ویرایش
    if user.get("form") and user["form"].get("kind") in ("reg", "edit"):
        await handle_registration_text(update, context, user, text)
        return

    # دکمه‌های منو با متن قابل تغییر مالک → تشخیص با کلید (تغییر نام عملکرد را نمی‌شکند)
    btn_key = resolve_button_key(text)

    # واژه پشتیبانی (خارج از مکالمه فعال؛ داخل چت به‌عنوان پیام عادی ارسال می‌شود)
    if (text == "پشتیبانی" or text.lower() == "پشتیبانی") and not (btn_key == "conv_next"):
        if not (user.get("conv") and get_conv(user["conv"]) and get_conv(user["conv"]).get("status") == "active"):
            await cmd_supp(update, context)
            return

    if btn_key == "menu_chat":
        await start_chat_flow(update, context, user)
        return
    if btn_key == "menu_info":
        if not user.get("registered") and not is_owner(tg):
            await send_text(context.bot, tg, "ℹ️ ابتدا ثبت‌نام را کامل کنید: /start")
            return
        if is_owner(tg) and not user.get("internal"):
            assign_internal_id(tg)
            user = get_user(tg)
        await send_text(context.bot, tg, info_text(user), info_kb(user))
        return
    if btn_key == "menu_guide":
        await cmd_guide(update, context)
        return

    # مکالمه فعال
    if user.get("conv"):
        conv = get_conv(user["conv"])
        if conv and conv.get("status") == "active":
            if btn_key == "conv_next":
                notifs = close_conversation(conv["id"], "next", tg)
                for pt, t in notifs:
                    await send_text(context.bot, pt, t, main_menu_kb())
                # سکوت و محدودیت فوق‌العاده در سمت سرور بررسی می‌شود، نه فقط با مخفی‌کردن دکمه
                fresh = get_user(tg)
                if is_muted(fresh):
                    await send_text(context.bot, tg, mute_notice(fresh), notice_kb(fresh))
                    return
                rem = super_start_block_minutes(fresh)
                if rem is not None:
                    await send_text(context.bot, tg, super_block_text(rem), notice_kb(fresh))
                    return
                start_search(tg)
                mark_new_chat_started(tg)
                await try_match_and_notify(context, tg)
                return
            if btn_key == "conv_block":
                notifs = close_conversation(conv["id"], "block", tg)
                for pt, t in notifs:
                    await send_text(context.bot, pt, t, main_menu_kb())
                clear_form(tg)
                await send_text(context.bot, tg, "کاربر بلاک شد و دیگر به شما متصل نخواهد شد.", main_menu_kb())
                return
            if btn_key == "conv_end":
                notifs = close_conversation(conv["id"], "end", tg)
                for pt, t in notifs:
                    await send_text(context.bot, pt, t, main_menu_kb())
                clear_form(tg)
                await send_text(context.bot, tg, CLOSE_TEXTS["end"], main_menu_kb())
                return
            await handle_conversation_message(update, context, user)
            return
        update_user(tg, lambda u: u.update({"conv": None}))

    # چت با دوست: کد اختصاصی ۹ رقمی (کاربر یا کد اختصاصی مالک)
    digits = en_num(text).strip()
    if digits.isdigit() and len(digits) == 9:
        await handle_friend_id(update, context, user, digits)
        return

    await send_text(context.bot, tg, MAIN_HINT, main_menu_kb())


async def handle_friend_id(update, context, user, digits: str):
    bot = context.bot
    tg = int(user["tg"])
    if is_owner(tg):
        user = ensure_owner_record()  # مالک معاف از ثبت‌نام
    if not user.get("registered"):
        await send_text(bot, tg, "ℹ️ ابتدا ثبت‌نام را کامل کنید: /start")
        return
    me = get_user(tg)
    if me.get("internal") == digits:
        await send_text(bot, tg, "ℹ️ این شناسه اختصاصی خود شما است.")
        return
    if is_muted(me):
        await send_text(bot, tg, mute_notice(me), notice_kb(me))
        return
    rem = super_start_block_minutes(me)
    if rem is not None:
        await send_text(bot, tg, super_block_text(rem), notice_kb(me))
        return
    if not await membership_gate(update, context, me):
        return
    target, tkind = find_by_internal_or_owner_code(digits)
    if not target:
        await send_text(bot, tg, "ℹ️ کاربری با این کد یافت نشد.")
        return
    target_tg = int(target["tg"])
    code, fid = create_friend_request(tg, target_tg)
    if code == "banned" or code == "blocked":
        await send_text(bot, tg, "امکان ایجاد مکالمه با این کاربر نیست.")
        return
    if code == "target_busy":
        await send_text(bot, tg, "ℹ️ کاربر مورد نظر در حال حاضر در مکالمه دیگری است.")
        return
    if code == "dup_pending":
        await send_text(bot, tg, "ℹ️ درخواست قبلی شما هنوز در انتظار پاسخ است.")
        return
    if code != "ok" or not fid:
        await send_text(bot, tg, "⚠️ ثبت درخواست ناموفق بود؛ دوباره تلاش کنید.")
        return
    await send_text(bot, target_tg,
                    "<b>درخواست چت ناشناس دارید.</b>\n\nکاربری می‌خواهد با شما گفت‌وگو کند:",
                    friend_request_kb(fid))
    await send_text(bot, tg, "درخواست شما ارسال شد؛ پس از پذیرش، مکالمه ایجاد می‌شود.")


async def handle_registration_text(update, context, user, text: str):
    tg = int(user["tg"])
    form = user["form"]
    data = form.setdefault("data", {})
    step = form.get("step")
    if text == "❌ لغو":
        clear_form(tg)
        await send_text(context.bot, tg, "❌ عملیات لغو شد.", main_menu_kb())
        return
    if text in ("🔙 بازگشت", "بازگشت"):
        order = ["name", "gender", "age", "province"]
        idx = order.index(step) if step in order else 0
        prev = order[max(0, idx - 1)]
        form["step"] = prev
        set_form(tg, form)
        await send_reg_step(context.bot, tg, get_user(tg))
        return
    if step == "name":
        if not valid_name(text):
            await send_text(context.bot, tg, "⚠️ نام نامعتبر است. فقط حروف، ۲ تا ۳۰ نویسه:")
            return
        data["name"] = text.strip()
        form["step"] = "gender"
        set_form(tg, form)
        await send_text(context.bot, tg, reg_progress(get_user(tg)) + REG_STEP_TEXTS["gender"], gender_kb(), html=True)
        return
    if step == "age":
        if not valid_age(text):
            await send_text(context.bot, tg, "⚠️ سن نامعتبر است. عددی بین ۱۰ تا ۹۹ ارسال کنید:")
            return
        data["age"] = int(en_num(text).strip())
        form["step"] = "province"
        set_form(tg, form)
        await send_text(context.bot, tg, reg_progress(get_user(tg)) + REG_STEP_TEXTS["province"], province_kb(), html=True)
        return
    await send_text(context.bot, tg, "ℹ️ لطفاً از دکمه‌های موجود استفاده کنید.")


def send_reg_step_sync_text(u):
    step = u["form"]["step"] if u.get("form") else "name"
    return reg_progress(u) + REG_STEP_TEXTS.get(step, REG_STEP_TEXTS["name"])


async def send_reg_step(bot, tg, u):
    step = u["form"]["step"] if u.get("form") else "name"
    kb = main_menu_kb() if step == "name" else (gender_kb() if step == "gender" else province_kb())
    if step == "gender" or step == "province":
        await send_text(bot, tg, send_reg_step_sync_text(u), kb, html=True)
    else:
        await send_text(bot, tg, send_reg_step_sync_text(u),
                        imarkup([[("btn_cancel", "form_cancel")]]), html=True)

# ---------- روتر رسانه ----------

async def on_media(update: Update, context: ContextTypes.DEFAULT_TYPE):
    tg = update.effective_user.id
    ensure_user(tg)
    touch_user(tg)
    user = get_user(tg)
    settings = STORE.get("settings")
    msg = update.effective_message

    if user.get("form") and user["form"].get("kind") == "panel_bk_restore":
        if not is_owner(tg):
            clear_form(tg)
            return
        await handle_backup_upload(update, context, user)
        return

    # تصویر پیوست اعتراض (سیستم محافظت)
    if user.get("form") and user["form"].get("kind") == "appeal_photo":
        case = user["form"]["data"].get("case")
        msg = update.effective_message
        file_id = None
        if getattr(msg, "photo", None):
            file_id = msg.photo[-1].file_id
        elif getattr(msg, "document", None) and (msg.document.mime_type or "").startswith("image/"):
            file_id = msg.document.file_id
        if not file_id:
            await send_text(context.bot, tg,
                            "⚠️ فقط تصویر پذیرفته می‌شود؛ دوباره ارسال کنید یا «ادامه بدون تصویر» را بزنید.",
                            imarkup([[("btn_next", f"apl_confirm:{case}", "ادامه بدون تصویر")]]))
            return
        form = user["form"]
        form.setdefault("data", {})["photo_id"] = file_id
        set_form(tg, form)
        d = form["data"]
        await send_text(context.bot, tg,
                        "📋 <b>پیش‌نمایش اعتراض</b>\n\n"
                        f"توضیحات: {esc(d.get('text') or '—')}\n"
                        "تصویر پیوست: دارد\n\nبرای ارسال نهایی، دکمه سبز را بزنید.",
                        imarkup([
                            [("btn_appeal", f"apl_send:{case}", "ثبت و ارسال اعتراض")],
                            [("btn_cancel", "apl_cancel")],
                        ]))
        return

    if not is_owner(tg):
        if is_banned(user):
            await send_text(context.bot, tg, ban_notice(user))
            return
        if not settings.get("bot_enabled", True):
            await send_text(context.bot, tg, "⚠️ ربات در حال حاضر خاموش است.")
            return
        if settings.get("maintenance"):
            await send_text(context.bot, tg, "ربات در حال نگهداری است.")
            return

    if user.get("conv"):
        conv = get_conv(user["conv"])
        if conv and conv.get("status") == "active":
            await handle_conversation_message(update, context, user)
            return
        update_user(tg, lambda u: u.update({"conv": None}))

    await send_text(context.bot, tg, "ℹ️ در این بخش امکان ارسال فایل نیست.")
# ============================================================
# 24) پردازش حالت‌های ورودی پنل مالک
# ============================================================

async def exec_admin_command(context, cmd: str, arg, target_uid: int) -> bool:
    """اجرای دستورات متنی مالک؛ هرگز به‌عنوان پیام عادی ارسال نمی‌شوند."""
    bot = context.bot
    if is_owner(int(target_uid)):
        await send_text(bot, OWNER_ID, "ℹ️ اعمال این دستور روی حساب مدیر مجاز نیست.")
        return True
    if cmd == "silence":
        if apply_mute(int(target_uid), arg, by="owner"):
            await send_text(bot, int(target_uid), f"حساب شما به مدت {fa_num(arg)} دقیقه در سکوت قرار گرفت.")
            await send_text(bot, OWNER_ID, f"سکوت {fa_num(arg)} دقیقه‌ای اعمال شد.")
            return True
    elif cmd == "ban":
        if apply_ban(int(target_uid), minutes=arg, by="owner"):
            await send_text(bot, int(target_uid), f"حساب شما به مدت {fa_num(arg)} دقیقه مسدود شد.")
            await send_text(bot, OWNER_ID, f"بن {fa_num(arg)} دقیقه‌ای اعمال شد.")
            return True
    elif cmd == "warn":
        if add_admin_warning(int(target_uid), "اخطار مدیریتی", "owner"):
            await send_text(bot, int(target_uid), "⚠️ به حساب شما اخطار داده شد.")
            await send_text(bot, OWNER_ID, "اخطار ثبت شد.")
            return True
    elif cmd == "unsilence":
        release_mute(int(target_uid), by="owner")
        await send_text(bot, int(target_uid), "سکوت شما برداشته شد.")
        await send_text(bot, OWNER_ID, "سکوت حذف شد.")
        return True
    elif cmd == "unban":
        release_ban(int(target_uid), by="owner")
        await send_text(bot, int(target_uid), "♻️ مسدودی حساب شما برداشته شد.")
        await send_text(bot, OWNER_ID, "بن حذف شد.")
        return True
    elif cmd == "reports":
        reps = target_of_reports(int(target_uid))
        if reps:
            lines = [f"🛡 گزارش‌های مربوط به کاربر: {fa_num(len(reps))}"]
            for r in reps[-10:]:
                lines.append(f"• {r['rid']} | {r.get('status')} | {jalali(parse_iso(r['created']))}")
            await send_text(bot, OWNER_ID, "\n".join(lines))
        else:
            await send_text(bot, OWNER_ID, "ℹ️ گزارشی برای این کاربر ثبت نشده است.")
        return True
    return False


def _resolve_owner_command_target(update, context):
    """هدف دستور متنی مالک: اولویت با ریپلای به پیام کاربر، سپس مخاطب مکالمه فعال.
    خروجی: tg_id کاربر هدف یا None."""
    msg = getattr(update, "effective_message", None)
    rmsg = getattr(msg, "reply_to_message", None) if msg is not None else None
    ruser = getattr(rmsg, "from_user", None) if rmsg is not None else None
    if ruser is not None:
        rid = int(getattr(ruser, "id", 0) or 0)
        bot_id = int(getattr(context.bot, "id", 0) or 0)
        if rid and rid != OWNER_ID and rid != bot_id and get_user(rid):
            return rid
    u = get_user(update.effective_user.id)
    if u and u.get("conv"):
        conv = get_conv(u["conv"])
        if conv and conv.get("status") == "active":
            for p in conv.get("participants", []):
                if int(p) != int(u["tg"]):
                    return int(p)
    return None


async def try_owner_text_command(update, context) -> bool:
    """دستورات متنی مالک: بن/سکوت/اخطار/حذف بن/حذف سکوت/گزارش/روشن.
    هدف: ریپلای به پیام کاربر یا مخاطب فعلی در مکالمه. True یعنی مدیریت شد و
    این متن هرگز به‌عنوان پیام عادی/ورودی فرم تفسیر نمی‌شود."""
    if not update.effective_user or not is_owner(update.effective_user.id):
        return False
    msg = getattr(update, "effective_message", None)
    text = (msg.text or "").strip() if msg is not None else ""
    if not text:
        return False

    # دستور «روشن» — آشکارسازی مدیر برای مخاطب مکالمه فعال
    if text == "روشن":
        target = _resolve_owner_command_target(update, context)
        if not target:
            await send_text(context.bot, OWNER_ID,
                            "ℹ️ دستور «روشن» فقط در مکالمه فعال کار می‌کند.")
            return True
        await send_text(context.bot, target, "🏆 <b>کاربر مورد نظر ادمین است. 💯</b>", html=True)
        audit("owner", "reveal_admin_command", details="دستور «روشن» (دستور متنی مالک)")
        return True

    parsed = parse_admin_command(text)
    if not parsed:
        return False
    name, arg = parsed
    target = _resolve_owner_command_target(update, context)
    if not target:
        await send_text(context.bot, OWNER_ID,
                        "⚠️ هدف دستور مشخص نیست. روی پیام کاربر ریپلای کنید یا در مکالمه فعال آن را بفرستید.")
        return True
    ok = await exec_admin_command(context, name, arg, target)
    if ok:
        audit("owner", f"text_command_{name}", target=str(target), details=f"arg:{arg}")
    return True  # دستور شناسایی شد؛ حتی اگر اجرا نشد، پیام عادی حساب نمی‌شود


async def handle_owner_state(update, context, user, text: str):
    tg = int(user["tg"])
    form = user.get("form") or {}
    kind = form.get("kind")
    data = form.get("data", {})
    bot = context.bot
    # حفظ فرمت‌های تلگرام (Bold/Italic/Code/...) در پیام‌های مالک:
    # text_html موجودیت‌های خام تلگرام را به HTML تبدیل می‌کند.
    _em = getattr(update, "effective_message", None)
    text_html = (getattr(_em, "text_html", None) if _em is not None else None) or esc(text)

    def done(msg, kb=None):
        clear_form(tg)
        return send_text(bot, tg, msg, kb, html=True)

    if kind == "panel_broadcast":
        form["data"] = {"text": text_html, "pin": bool(form.get("data", {}).get("pin")),
                        "react": bool(form.get("data", {}).get("react"))}
        set_form(tg, form)
        pin = form["data"]["pin"]
        react = form["data"]["react"]
        await send_text(bot, tg,
                        "📣 <b>پیش‌نمایش پیام همگانی:</b>\n\n" + text +
                        f"\n\n📌 سنجاق: {'روشن' if pin else 'خاموش'} | "
                        f"👍 واکنش: {'روشن' if react else 'خاموش'}",
                        broadcast_confirm_kb(pin, react), html=True)
        return
    if kind == "panel_link_warn_text":
        new_text = LINK_WARNING_DEFAULT if text.strip() == "پیش‌فرض" else text[:1500]
        STORE.update("settings", lambda x: dict(x, link_warning_text=new_text))
        audit("owner", "link_warning_text_updated", details=f"len:{len(new_text)}")
        await done("✅ متن هشدار لینک ذخیره شد.", imarkup([[("btn_back", "pn_fmt")]]))
        return
    if kind == "panel_bc_sched":
        d = form.get("data", {})
        text_b = d.get("text")
        if not text_b:
            await done("ℹ️ متن پیام یافت نشد؛ از ابتدا اقدام کنید.", owner_panel_kb())
            return
        parts = [p for p in re.split(r"[/\\]", en_num(text).strip()) if p != ""]
        if not (1 <= len(parts) <= 3) or not all(p.isdigit() for p in parts):
            await send_text(bot, tg,
                            "⚠️ قالب درست: «30» (دقیقه تأخیر) | «30/6» (تأخیر/ساعت تکرار) | "
                            "«30/6/5» (تأخیر/ساعت تکرار/دفعات)",
                            imarkup([[("btn_cancel", "pn_bc_sched_no")]]), html=True)
            return
        delay = max(0, min(int(parts[0]), 525600))          # حداکثر یک سال
        repeat_h = max(0, min(int(parts[1]), 8760)) if len(parts) >= 2 else 0
        repeat_n = max(0, min(int(parts[2]), 1000)) if len(parts) >= 3 else 0
        if delay == 0 and repeat_h == 0:
            await send_text(bot, tg, "⚠️ تأخیر صفر فقط با تکرار معتبر است؛ مثال: «0/6» یعنی هر ۶ ساعت.",
                            imarkup([[("btn_cancel", "pn_bc_sched_no")]]), html=True)
            return
        jid = add_broadcast_job(text_b, delay, repeat_h, repeat_n,
                                pin=bool(d.get("pin")), react=bool(d.get("react")))
        run_fa = jalali(now_utc() + timedelta(minutes=delay))
        if repeat_h:
            rep_txt = f"تکرار هر {fa_num(repeat_h)} ساعت" + (f"، {fa_num(repeat_n)} بار" if repeat_n else "، بی‌نهایت")
        else:
            rep_txt = "یک‌بار"
        await done(f"⏰ ارسال زمان‌بندی‌شده ثبت شد.\n\n"
                   f"کد: <code>{jid}</code>\n"
                   f"ارسال بعدی: {run_fa}\n"
                   f"{rep_txt}\n"
                   f"📌 سنجاق: {'روشن' if d.get('pin') else 'خاموش'} | "
                   f"👍 واکنش: {'روشن' if d.get('react') else 'خاموش'}\n\n"
                   "فهرست و لغو: پنل ← اطلاع‌رسانی ← ارسال‌های زمان‌بندی‌شده.",
                   owner_panel_kb())
        return
    if kind == "panel_user_msg":
        uid = data.get("uid")
        cmd = parse_admin_command(text)
        if cmd:
            await exec_admin_command(context, cmd[0], cmd[1], uid)
            return
        u = get_user(int(uid))
        if u:
            ok = await send_text(bot, int(u["tg"]), "📨 <b>پیام از مدیریت</b>\n\n" + text_html, html=True)
            await send_text(bot, tg, "✅ پیام ارسال شد." if ok else "⚠️ ارسال ناموفق بود.")
            audit("owner", "admin_message_user", target=str(uid))
        else:
            await done("ℹ️ کاربر یافت نشد.")
        return
    if kind == "panel_admin_reply":
        tid = data.get("tid")
        t = get_ticket(tid)
        if not t:
            await done("ℹ️ تیکت یافت نشد.")
            return
        cmd = parse_admin_command(text)
        if cmd:
            await exec_admin_command(context, cmd[0], cmd[1], int(t["uid"]))
            return
        add_ticket_message(tid, "admin", text)
        await send_text(bot, int(t["uid"]), "🛡 <b>پاسخ پشتیبانی</b>\n\n" + text_html, html=True)
        await send_text(bot, tg, "پاسخ ارسال و در تاریخچه ثبت شد.")
        return
    if kind == "panel_user_warn":
        uid = data.get("uid")
        if add_admin_warning(int(uid), text, "owner"):
            u = get_user(int(uid))
            if u:
                await send_text(bot, int(u["tg"]), f"⚠️ به حساب شما اخطار داده شد.\nدلیل: {text}")
            await done("اخطار ثبت شد.")
        else:
            await done("ℹ️ امکان اخطار به این کاربر نیست.")
        return
    if kind == "panel_user_ban":
        uid = data.get("uid")
        try:
            minutes = max(1, int(en_num(text).strip()))
        except Exception:
            await send_text(bot, tg, "⚠️ عدد دقیقه نامعتبر است:")
            return
        if apply_ban(int(uid), minutes=minutes, by="owner", reason="بن مدیریتی"):
            u = get_user(int(uid))
            if u:
                await send_text(bot, int(u["tg"]), f"حساب شما به مدت {fa_num(minutes)} دقیقه مسدود شد.")
            await done(f"بن {fa_num(minutes)} دقیقه‌ای اعمال شد.")
        else:
            await done("ℹ️ امکان بن این کاربر نیست.")
        return
    if kind == "panel_user_edit":
        uid, field = data.get("uid"), data.get("field")
        ok = False
        if field == "name" and valid_name(text):
            update_user(int(uid), lambda u: u.update({"name": text.strip()}))
            ok = True
        elif field == "gender" and text in ("پسر", "دختر"):
            update_user(int(uid), lambda u: u.update({"gender": "male" if text == "پسر" else "female"}))
            ok = True
        elif field == "age" and valid_age(text):
            update_user(int(uid), lambda u: u.update({"age": int(en_num(text).strip())}))
            ok = True
        elif field == "province" and text in PROVINCES:
            update_user(int(uid), lambda u: u.update({"province": text}))
            ok = True
        if ok:
            modlog("owner", "edit_profile", uid, f"field:{field}")
            await done("مشخصات تغییر کرد.")
        else:
            await send_text(bot, tg, "⚠️ مقدار نامعتبر است؛ دوباره ارسال کنید یا لغو کنید:")
        return
    if kind == "panel_search":
        results = []
        users = STORE.get("users")
        q = en_num(text).strip()
        for rec in users.values():
            if q == str(rec.get("internal")) or q == str(rec.get("tg")) or (q and q in (rec.get("name") or "")):
                results.append(rec)
        clear_form(tg)
        if not results:
            await send_text(bot, tg, "ℹ️ نتیجه‌ای یافت نشد.", owner_panel_kb())
            return
        lines = [f"🔍 نتایج ({fa_num(len(results[:10]))}):"]
        rows = []
        for rec in results[:10]:
            lines.append(f"• <code>{rec.get('internal')}</code> | {rec.get('name') or '—'}")
            rows.append([InlineKeyboardButton(f"👤 {rec.get('internal')}", callback_data=f"pn_u:{rec['tg']}")])
        rows.append([ib("btn_back", "pn_users")])
        await send_text(bot, tg, "\n".join(lines), InlineKeyboardMarkup(rows), html=True)
        return
    if kind in ("panel_cap", "panel_minutes", "panel_rate", "panel_retention",
                "panel_qtimeout", "panel_rtimeout"):
        try:
            val = int(en_num(text).strip())
        except Exception:
            await send_text(bot, tg, "⚠️ عدد نامعتبر است:")
            return
        keymap = {"panel_cap": ("warning_cap", 1, 100), "panel_minutes": ("punishment_minutes", 1, 100000),
                  "panel_rate": ("rate_limit_per_minute", 1, 1000), "panel_retention": ("retention_hours", 1, 720),
                  "panel_qtimeout": ("queue_timeout_minutes", 1, 1440), "panel_rtimeout": ("request_timeout_minutes", 1, 1440)}
        key, lo, hi = keymap[kind]
        if not (lo <= val <= hi):
            await send_text(bot, tg, f"⚠️ مقدار باید بین {fa_num(lo)} و {fa_num(hi)} باشد:")
            return
        STORE.update("settings", lambda s: dict(s, **{key: val}))
        await done(f"تنظیم «{key}» روی {fa_num(val)} ذخیره شد.")
        return
    if kind == "panel_oname":
        STORE.update("settings", lambda s: dict(s, owner_name=text[:40]))
        await done("نام پروفایل مالک ذخیره شد.")
        return
    if kind == "panel_obio":
        STORE.update("settings", lambda s: dict(s, owner_bio=text[:200]))
        await done("توضیحات پروفایل مالک ذخیره شد.")
        return
    if kind == "panel_hours_add":
        if not valid_interval(text):
            await send_text(bot, tg, "⚠️ بازه نامعتبر است. نمونه صحیح: «22:00-06:00»:")
            return
        iv = norm_hhmm(text.split("-")[0]) + "-" + norm_hhmm(text.split("-")[1])
        STORE.update("settings", lambda s: dict(s, profanity_hours=(s.get("profanity_hours") or []) + [iv]))
        await done(f"بازه {fa_num(iv)} افزوده شد.")
        return
    if kind == "panel_wadd":
        w = normalize_text(text)
        if not w or " " in w and len(w) > 60:
            await send_text(bot, tg, "⚠️ واژه نامعتبر است:")
            return
        STORE.update("profanity_words", lambda c: dict(c, custom_blocked=c.get("custom_blocked", []) + [w]))
        await done(f"واژه «{w}» به فهرست ممنوع افزوده شد.")
        return
    if kind == "panel_wladd":
        w = normalize_text(text)
        if not w:
            await send_text(bot, tg, "⚠️ واژه نامعتبر است:")
            return
        STORE.update("profanity_words", lambda c: dict(c, custom_whitelist=c.get("custom_whitelist", []) + [w]))
        await done(f"واژه «{w}» به فهرست مجاز افزوده شد.")
        return
    if kind == "panel_ch_add":
        target = text.strip()
        if not (target.startswith("@") or target.lstrip("-").isdigit()):
            await send_text(bot, tg, "⚠️ شناسه نامعتبر است؛ @username یا شناسه عددی ارسال کنید:")
            return
        try:
            chat = await bot.get_chat(target)
            title = chat.title or target
        except TelegramError as e:
            await send_text(bot, tg, f"⚠️ کانال یافت نشد ({e.__class__.__name__}). ربات باید عضو کانال باشد.")
            return
        conf = STORE.get("mandatory_channels")
        idx = len(conf.get("channels", []))
        STORE.update("mandatory_channels", lambda c: dict(c, channels=c.get("channels", []) + [
            {"target": target, "title": title, "invite_link": ""}]))
        set_form(tg, {"kind": "panel_ch_link", "data": {"idx": idx}})
        await send_text(bot, tg, f"«{title}» ثبت شد.\n\nلینک دعوت را ارسال کنید یا «لغو» بزنید (برای کانال عمومی لازم نیست):")
        return
    if kind == "panel_ch_link":
        idx = int(data.get("idx", 0))
        if text in ("لغو", "لغو", "-"):
            await done("ثبت کانال کامل شد.")
            return
        if not text.startswith(("http://", "https://", "t.me/", "https://t.me/")):
            await send_text(bot, tg, "⚠️ لینک نامعتبر است؛ دوباره ارسال کنید یا «لغو» بزنید:")
            return
        def _upd(c):
            chs = c.get("channels", [])
            if idx < len(chs):
                chs[idx]["invite_link"] = text.strip()
            return c
        STORE.update("mandatory_channels", _upd)
        await done("لینک دعوت ذخیره شد.")
        return
    if kind in ("panel_sched_on", "panel_sched_off"):
        if not valid_hhmm(text):
            await send_text(bot, tg, "⚠️ ساعت نامعتبر است. نمونه: «08:30»:")
            return
        key = "sched_on" if kind == "panel_sched_on" else "sched_off"
        def _set(s):
            d = dict(s.get(key) or {})
            d["enabled"] = True
            d["time"] = norm_hhmm(text)
            return dict(s, **{key: d})
        STORE.update("settings", _set)
        await done(f"زمان‌بندی ذخیره شد (ساعت {fa_num(norm_hhmm(text))} به وقت تهران).")
        return
    if kind == "panel_rpt_note":
        rid = data.get("rid")

        def _m(lst):
            for r in lst:
                if r.get("rid") == rid:
                    r.setdefault("notes", []).append({"time": iso_utc(now_utc()), "text": text[:400]})
            return lst
        STORE.update("reports", _m)
        audit("owner", "report_note", target=rid)
        await done("یادداشت مدیریتی ثبت شد.")
        return
    if kind == "panel_rpt_umsg":
        rid, who = data.get("rid"), data.get("who")
        r = next((x for x in STORE.get("reports") if x.get("rid") == rid), None)
        if not r:
            await done("ℹ️ گزارش یافت نشد.")
            return
        uid = int(r["reporter"] if who == "r" else r["reported"])
        ok = await send_text(bot, uid, "🛡 <b>پیام مدیریت درباره گزارش ثبت‌شده</b>\n\n" + text, html=True)
        audit("owner", "report_party_message", target=rid, details=f"to:{who} ok:{ok}")
        await done("✅ پیام ارسال شد." if ok else "⚠️ ارسال ناموفق بود.")
        return
    if kind == "panel_bk_restore":
        await send_text(bot, tg, "فایل بکاپ (JSON) را ارسال کنید یا لغو کنید.",
                        imarkup([[("btn_cancel", "pn_bk")]]))
        return
    if kind == "panel_oc_set":
        # تغییر دستی کد اختصاصی مالک (پچ ۲.۴.۰ — بخش ۱۱)
        err = set_owner_code(text)
        if err:
            await send_text(bot, tg, f"⚠️ {esc(err)}\nکد را دوباره ارسال کنید یا لغو کنید:")
            return
        await done("✅ کد اختصاصی مالک تغییر کرد؛ کد قبلی فوراً غیرقابل استفاده است.\n\n"
                   + (owner_code_text()[0]))
        return
    if kind == "panel_btn_text":
        key = data.get("key")
        if key not in STYLE_KEYS:
            await done("ℹ️ دکمه یافت نشد.")
            return
        val = text.strip()
        if not val or len(val) > 40 or has_decorative_emoji(val):
            await send_text(bot, tg, "⚠️ متن نامعتبر است (بدون ایموجی تزئینی، حداکثر ۴۰ نویسه). دوباره ارسال کنید یا لغو کنید:")
            return
        draft_set_text(key, val)
        await done(f"متن در پیش‌نویس ذخیره شد: «{esc(val)}»\nبرای اعمال، «پیش‌نمایش و ذخیره» را بزنید.")
        return
    if kind == "panel_cmd_edit":
        name = data.get("name")
        field = data.get("field")
        limits = {"title": 60, "desc": 300, "usage": 200, "example": 60}
        val = text.strip()
        if not val or len(val) > limits.get(field, 100):
            await send_text(bot, tg, f"⚠️ مقدار نامعتبر است (حداکثر {fa_num(limits.get(field, 100))} نویسه). دوباره ارسال کنید یا لغو کنید:")
            return
        if save_commands_meta(name, {field: val}):
            audit("owner", "command_meta_changed", target=name, details=f"field:{field}")
            await done("عنوان و توضیحات در راهنما به‌روزرسانی شد؛ عملکرد واقعی دستور تغییری نکرده است.")
        else:
            await done("ℹ️ این دستور سیستمی/امنیتی است و قابل تغییر نیست.")
        return
    # ---------- سیستم محافظت — تنظیمات عددی ----------
    if kind == "panel_prot_num":
        field, key = data.get("field"), data.get("key")
        try:
            num = int(en_num(text).strip())
        except Exception:
            await send_text(bot, tg, "⚠️ عدد نامعتبر است؛ دوباره ارسال کنید یا لغو کنید:")
            return
        if field == "mute_minutes" and not (1 <= num <= 60 * 24 * 30):
            await send_text(bot, tg, "⚠️ مقدار باید بین ۱ و ۴۳۲۰۰ دقیقه باشد:")
            return
        if field == "stage_ban_hours" and not (0 <= num <= 24 * 365):
            await send_text(bot, tg, "⚠️ مقدار باید بین ۰ و ۸۷۶۰ ساعت باشد:")
            return
        if field in ("stage_super_minutes",) and not (0 <= num <= 60 * 24 * 365):
            await send_text(bot, tg, "⚠️ مقدار نامعتبر است:")
            return
        if field == "escalation_threshold" and not (1 <= num <= 50):
            await send_text(bot, tg, "⚠️ مقدار باید بین ۱ و ۵۰ باشد:")
            return
        if field == "girl_block_stage4_hours" and not (0 <= num <= 24 * 365):
            await send_text(bot, tg, "⚠️ مقدار باید بین ۰ و ۸۷۶۰ ساعت باشد (۰ = دائمی):")
            return
        if field == "girl_block_stage5_hours" and not (0 <= num <= 24 * 365):
            await send_text(bot, tg, "⚠️ مقدار باید بین ۰ و ۸۷۶۰ ساعت باشد (۰ = دائمی):")
            return

        def _set(p):
            if key is None:
                p[field] = num
            else:
                p.setdefault(field, {})[key] = num
        set_protection(_set)
        modlog("owner", "protection_setting", details=f"{field}:{key or '-'}={num}")
        await done(f"✔ تنظیم شد: {field}" + (f" [{key}]" if key else "") + f" = {fa_num(num)}")
        return
    # ---------- عملیات امنیتی عددی روی کاربر ----------
    if kind == "panel_sec_num":
        uid = int(data.get("uid"))
        op = data.get("op")
        try:
            num = int(en_num(text).strip())
        except Exception:
            await send_text(bot, tg, "⚠️ عدد نامعتبر است؛ دوباره ارسال کنید:")
            return
        u2 = get_user(uid)
        if not u2 or is_owner(uid):
            await done("ℹ️ عملیات روی این کاربر مجاز نیست.")
            return
        if op == "mute_add":
            cur = mute_remaining_minutes(u2)
            if not cur:
                apply_mute(uid, num, by="owner", reason="تمدید سکوت از پنل")
            else:
                update_user(uid, lambda x: x.update({
                    "mute_until": iso_utc(parse_iso(x["mute_until"]) + timedelta(minutes=num))}))
            await send_text(bot, uid, f"⏳ سکوت شما {fa_num(num)} دقیقه تمدید شد.")
            modlog("owner", f"mute_extend_{num}m", uid)
            await done(f"✔ سکوت {fa_num(num)} دقیقه تمدید شد.")
            return
        if op == "mute_reduce":
            cur = mute_remaining_minutes(u2)
            if not cur:
                await done("ℹ️ سکوت فعالی وجود ندارد.")
                return
            new_until = now_utc() + timedelta(minutes=max(0, cur - num))
            if cur - num <= 0:
                release_mute(uid, by="owner")
                await send_text(bot, uid, "سکوت شما برداشته شد.")
                modlog("owner", "mute_reduce_remove", uid)
                await done("✔ سکوت کامل برداشته شد.")
            else:
                update_user(uid, lambda x: x.update({"mute_until": iso_utc(new_until)}))
                modlog("owner", f"mute_reduce_{num}m", uid)
                await done(f"✔ سکوت {fa_num(num)} دقیقه کاهش یافت.")
            return
        if op == "ban_change":
            if num < 1:
                await send_text(bot, tg, "⚠️ مدت بن باید حداقل ۱ دقیقه باشد:")
                return
            release_ban(uid, by="owner")
            apply_ban(uid, minutes=num, by="owner", reason="تغییر مدت بن از پنل")
            await send_text(bot, uid, f"⛔ مدت مسدودی حساب شما به {fa_num(num)} دقیقه تغییر کرد.")
            modlog("owner", f"ban_changed_{num}m", uid)
            await done(f"✔ مدت بن به {fa_num(num)} دقیقه تغییر کرد.")
            return
        if op == "girl_set":
            apply_girl_block(uid, hours=num, by="owner")
            await send_text(bot, uid, "🚻 شروع چت جدید شما با دختران توسط مدیریت محدود شد.")
            await done("✔ منع چت با دختران تنظیم شد." + (" (دائمی)" if num == 0 else f" ({fa_num(num)} ساعت)"))
            return
        await done("ℹ️ عملیات نامشخص.")
        return
    # ---------- پاک‌کردن سابقه تخلفات با ثبت دلیل ----------
    if kind == "panel_sec_reason":
        uid = int(data.get("uid"))
        viol = [v for v in STORE.get("violations")
                if v.get("uid") == str(uid) and not v.get("revoked")]
        for v in viol:
            revoke_violation(v["vid"], "owner", f"پاک‌کردن سابقه: {text[:200]}")
        modlog("owner", "violations_cleared", uid, f"count:{len(viol)} reason:{text[:120]}")
        audit("owner", "violations_cleared", target=str(uid), details=text[:200])
        await done(f"✔ سابقه {fa_num(len(viol))} تخلف با ثبت دلیل پاک شد و مجازات‌های مرتبط اصلاح گردید.")
        return
    # ---------- مجازات اختصاصی ----------
    if kind == "panel_sec_custom":
        uid = int(data.get("uid"))
        t2 = en_num(text).strip().replace(" ", "")
        m = re.match(r"^(سکوت|بن|فوق‌العاده|دختر)[:：](\d+)(ساعت)?$", t2)
        if not m:
            await send_text(bot, tg, "⚠️ قالب درست: «سکوت:۳۰» | «بن:۲۴ساعت» | «فوق‌العاده:۱۲۰» | «دختر:۱۶۸»")
            return
        kind_p, amount, unit = m.group(1), int(m.group(2)), m.group(3)
        u2 = get_user(uid)
        if not u2 or is_owner(uid):
            await done("ℹ️ عملیات روی این کاربر مجاز نیست.")
            return
        if kind_p == "سکوت":
            apply_mute(uid, amount, by="owner", reason="مجازات اختصاصی")
            await send_text(bot, uid, f"⏳ سکوت {fa_num(amount)} دقیقه‌ای برای حساب شما اعمال شد.")
            await done(f"✔ سکوت {fa_num(amount)} دقیقه اعمال شد.")
        elif kind_p == "بن":
            hours = amount if unit else 0
            if hours:
                apply_ban(uid, minutes=hours * 60, by="owner", reason="مجازات اختصاصی")
            else:
                apply_ban(uid, minutes=amount, by="owner", reason="مجازات اختصاصی")
            await send_text(bot, uid, "⛔ حساب شما مسدود شد.")
            await done("✔ بن اعمال شد.")
        elif kind_p == "فوق‌العاده":
            apply_super_limit(uid, amount, by="owner")
            await done(f"✔ محدودیت فوق‌العاده {fa_num(amount)} دقیقه‌ای اعمال شد.")
        elif kind_p == "دختر":
            apply_girl_block(uid, hours=amount, by="owner")
            await done("✔ منع چت با دختران اعمال شد." + (" (دائمی)" if amount == 0 else f" ({fa_num(amount)} ساعت)"))
        return
    await done("ℹ️ حالت نامشخص؛ لغو شد.")


async def handle_backup_upload(update, context, user):
    tg = int(user["tg"])
    bot = context.bot
    msg = update.effective_message
    doc = msg.document
    if not doc:
        await send_text(bot, tg, "⚠️ فقط فایل JSON بکاپ پذیرفته می‌شود.")
        return
    name = doc.file_name or ""
    mime = (doc.mime_type or "").lower()
    if not (name.lower().endswith(".json") or "json" in mime):
        await send_text(bot, tg, "⚠️ نوع فایل باید JSON باشد.")
        return
    if (doc.file_size or 0) > MAX_BACKUP_UPLOAD_BYTES:
        await send_text(bot, tg, "⚠️ حجم فایل بیش از حد مجاز است.")
        return
    try:
        os.makedirs(os.path.join(STORE.root, "tmp"), exist_ok=True)
        up_path = os.path.join(STORE.root, "tmp", f"upload-{int(_time.time())}.json")
        f = await doc.get_file()
        await f.download_to_drive(up_path)
        ok, staged, summary = stage_restore(up_path)
        try:
            os.remove(up_path)
        except OSError:
            pass
    except TelegramError as e:
        LOG.error("دانلود بکاپ ناموفق: %s", e.__class__.__name__)
        await send_text(bot, tg, "⚠️ دریافت فایل ناموفق بود.")
        return
    except OSError as e:
        LOG.error("ذخیره فایل موقت ناموفق: %s", e)
        await send_text(bot, tg, "⚠️ ذخیره فایل موقت ناموفق بود.")
        return
    if not ok:
        audit("owner", "backup_upload_rejected", details=str(summary)[:200])
        clear_form(tg)
        await send_text(bot, tg, "⛔ فایل بکاپ رد شد:\n" + str(summary))
        return
    set_form(tg, {"kind": "panel_bk_restore", "data": {"staged": staged}})
    counts = summary if isinstance(summary, dict) else {}
    lines = ["✅ فایل بکاپ معتبر است؛ خلاصه اطلاعات:", ""]
    for k, v in counts.items():
        lines.append(f"• {k}: {fa_num(v)}")
    lines.append("")
    lines.append("⚠️ با تأیید نهایی، اطلاعات فعلی با محتوای این بکاپ جایگزین می‌شود.")
    await send_text(bot, tg, "\n".join(lines),
                    imarkup([[("btn_confirm", "pn_brs_go", "تأیید نهایی بازیابی"),
                              ("btn_reject", "pn_brs_no", "انصراف")]]))
# ============================================================
# 25) روتر Callback (کل دکمه‌های اینلاین + پنل)
# ============================================================

def modlog_text(page: int):
    logs = sorted(STORE.get("moderation_logs"), key=lambda a: a.get("time") or "", reverse=True)
    chunk, page, pages = pager(logs, page, 10)
    lines = [f"🧾 <b>عملیات مدیریتی</b> — {fa_num(len(logs))} رکورد", ""]
    for a in chunk:
        lines.append(f"• {jalali(parse_iso(a['time']))} | {a.get('by')} | {a.get('action')}"
                     + (f" | کاربر {a.get('target')}" if a.get("target") else ""))
    return "\n".join(lines), InlineKeyboardMarkup(nav_rows("pn_mg", page, pages, back_cd="pn_logs"))


async def _edit(q, text, kb=None):
    try:
        await q.edit_message_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except BadRequest as e:
        if "not modified" in str(e).lower():
            return
        try:
            await q.message.reply_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
        except TelegramError:
            pass


def _pn_prompt(kind, data, text, kb=None):
    return {"kind": kind, "data": data}, text, kb


async def on_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    data = q.data or ""
    tg = update.effective_user.id
    ensure_user(tg)
    touch_user(tg)
    user = get_user(tg)
    bot = context.bot
    settings = STORE.get("settings")

    if data.startswith("pn") and not is_owner(tg):
        await q.answer("⛔ فقط مالک", show_alert=True)
        return
    if not callback_ok(tg):
        await q.answer("⏳ کمی آرام‌تر", show_alert=True)
        return
    await q.answer()

    # ---------- پیشنهاد تغییر چت (فحاشی با فیلتر خاموش) ----------
    if data in ("chg:block", "chg:next"):
        fresh = get_user(tg)
        conv_id_u = fresh.get("conv") if fresh else None
        conv_u = get_conv(conv_id_u) if conv_id_u else None
        if not (conv_u and conv_u.get("status") == "active"):
            await _edit(q, "ℹ️ این مکالمه دیگر فعال نیست.", main_menu_kb())
            return
        if data == "chg:block":
            notifs = close_conversation(conv_u["id"], "block", tg)
            for pt, t in notifs:
                await send_text(bot, pt, t, main_menu_kb())
            clear_form(tg)
            await _edit(q, "⛔ کاربر بلاک شد و دیگر به شما متصل نخواهد شد.", main_menu_kb())
        else:
            notifs = close_conversation(conv_u["id"], "next", tg)
            for pt, t in notifs:
                await send_text(bot, pt, t, main_menu_kb())
            # سکوت و محدودیت فوق‌العاده سمت سرور کنترل می‌شود
            f2 = get_user(tg)
            if is_muted(f2):
                await _edit(q, mute_notice(f2), notice_kb(f2))
                return
            rem = super_start_block_minutes(f2)
            if rem is not None:
                await _edit(q, super_block_text(rem), notice_kb(f2))
                return
            start_search(tg)
            mark_new_chat_started(tg)
            await _edit(q, "⏭️ در حال جست‌وجوی چت جدید…", main_menu_kb())
            await try_match_and_notify(context, tg)
        audit(actor_name_of(tg), f"change_chat_{ 'block' if data == 'chg:block' else 'next' }",
              target=conv_u["id"])
        return

    # ---------- حریم خصوصی و ثبت‌نام ----------
    if data == "consent_ok":
        accept_consent(tg)
        start_registration(tg)
        u = get_user(tg)
        await send_text(bot, tg, "سیاست پذیرفته شد.\n\n" + send_reg_step_sync_text(u),
                        imarkup([[("btn_cancel", "form_cancel")]]))
        return
    if data == "consent_no":
        decline_consent(tg)
        await _edit(q, "⛔ شما سیاست حریم خصوصی را رد کردید؛ دسترسی به امکانات ربات ندارید.",
                    reconsent_kb())
        return
    if data == "consent_retry":
        await _edit(q, PRIVACY_TEXT, consent_kb())
        return
    if data in ("g:m", "g:f"):
        form = user.get("form") or {"kind": "reg", "data": {}}
        form.setdefault("data", {})["gender"] = "male" if data == "g:m" else "female"
        form["step"] = "age"
        set_form(tg, form)
        await _edit(q, reg_progress(get_user(tg)) + REG_STEP_TEXTS["age"])
        return
    if data.startswith("pr:"):
        # انتخاب استان در ثبت‌نام — تکمیل نهایی فرم (منبع واحد: registered=True پایدار)
        form = user.get("form")
        if not form or form.get("kind") not in ("reg", "edit"):
            await _edit(q, "ℹ️ فرم ثبت‌نام فعالی وجود ندارد. با /start شروع کنید.")
            return
        province = data.split(":", 1)[1]
        if province not in PROVINCES:
            await _edit(q, "⚠️ استان نامعتبر است؛ دوباره انتخاب کنید.", province_kb())
            return
        form.setdefault("data", {})["province"] = province
        set_form(tg, form)
        apply_registration(tg, form["data"])
        clear_form(tg)
        await _edit(q, "ثبت‌نام با موفقیت کامل شد و دائمی ذخیره شد.\n\nکد اختصاصی شما از «اطلاعات من» قابل مشاهده است.")
        await send_text(bot, tg, MAIN_HINT, main_menu_kb())
        return
    if data.startswith("pv:"):
        page = int(data.split(":")[1])
        await _edit(q, reg_progress(user) + REG_STEP_TEXTS["province"], province_kb(page))
        return
    if data == "form_back":
        form = user.get("form")
        if form and form.get("kind") in ("reg", "edit"):
            order = ["name", "gender", "age", "province"]
            idx = order.index(form.get("step", "name"))
            form["step"] = order[max(0, idx - 1)]
            set_form(tg, form)
            u = get_user(tg)
            step = form["step"]
            if step == "name":
                await _edit(q, send_reg_step_sync_text(u))
            elif step == "gender":
                await _edit(q, send_reg_step_sync_text(u), gender_kb())
            else:
                await _edit(q, send_reg_step_sync_text(u), province_kb())
        return
    if data == "form_cancel":
        clear_form(tg)
        await send_text(bot, tg, "عملیات لغو شد.", main_menu_kb())
        return
    if data == "menu_home":
        clear_form(tg)
        await send_text(bot, tg, MAIN_HINT, main_menu_kb())
        if is_owner(tg):
            await send_text(bot, tg, "پنل مدیریت:", imarkup([[("btn_next", "pn", "پنل مدیریت")]]))
        return
    if data.startswith("pfg:"):
        val = data.split(":")[1]
        update_user(tg, lambda u: u["prefs"].update({"gender": val}))
        await _edit(q, info_text(get_user(tg)), info_kb(get_user(tg)))
        return
    if data.startswith("pfa:"):
        val = data.split(":")[1]
        update_user(tg, lambda u: u["prefs"].update({"age": val}))
        await _edit(q, info_text(get_user(tg)), info_kb(get_user(tg)))
        return
    if data == "pf_gender":
        await _edit(q, "🎚 فیلتر جنسیت را انتخاب کنید:", pref_gender_kb())
        return
    if data == "pf_age":
        await _edit(q, "🎯 فیلتر سن را انتخاب کنید:", pref_age_kb())
        return
    if data == "pf_back":
        await _edit(q, info_text(get_user(tg)), info_kb(get_user(tg)))
        return
    if data == "pe_start":
        u = get_user(tg)
        if can_edit_profile(u):
            start_registration(tg, kind="edit")
            nu = get_user(tg)
            await send_text(bot, tg, "✏️ ویرایش مشخصات (هر ۶ ماه یک بار)\n\n" + send_reg_step_sync_text(nu),
                            imarkup([[("btn_cancel", "form_cancel")]]), html=True)
        else:
            nxt = next_edit_date(u)
            await q.answer("تغییر مشخصات هر ۶ ماه یک بار امکان‌پذیر است", show_alert=True)
            if nxt:
                await send_text(bot, tg, f"ℹ️ تاریخ مجاز تغییر بعدی: {jalali(nxt)}")
        return
    if data == "qcancel":
        cancel_search(tg)
        await send_text(bot, tg, "🔴 جست‌وجو لغو شد.", main_menu_kb())
        return
    if data.startswith("frq:"):
        parts = data.split(":")
        fid, act = parts[1], parts[2]
        rec = next((r for r in STORE.get("friend_requests") if r.get("fid") == fid), None)
        if not rec or rec.get("status") != "pending":
            await _edit(q, "ℹ️ این درخواست دیگر معتبر نیست.")
            return
        if act == "acc":
            await accept_friend_request(update, context, fid)
            await _edit(q, "درخواست پذیرفته شد؛ مکالمه ایجاد شد.")
        else:
            set_friend_request(fid, "rejected")
            await _edit(q, "ℹ️ درخواست رد شد.")
            await send_text(bot, int(rec["from"]), "ℹ️ درخواست چت شما رد شد.")
        return
    if data == "rpt_skip":
        form = user.get("form") or {}
        rid = form.get("data", {}).get("rid")
        if rid:
            save_report_reason(rid, "")
        clear_form(tg)
        await send_text(bot, tg, "✅ گزارش ثبت شد. به بررسی آن رسیدگی خواهد شد.", main_menu_kb())
        return
    if data == "sup_end":
        clear_form(tg)
        await send_text(bot, tg, "✅ گفت‌وگوی پشتیبانی پایان یافت؛ درخواست شما برای مدیریت باقی می‌ماند.", main_menu_kb())
        return
    if data == "mcheck":
        u = get_user(tg)
        await start_chat_flow(update, context, u)
        return
    if data == "noop":
        return

    # ---------- اعتراض به مجازات (سیستم محافظت) ----------
    if data.startswith("apl_start:"):
        case = data.split(":", 1)[1]
        v = next((x for x in STORE.get("violations") if x.get("case") == case), None)
        if not v or str(v.get("uid")) != str(tg) or v.get("appeal") or v.get("revoked"):
            await send_text(bot, tg, "ℹ️ این پرونده قابل اعتراض نیست (قبلاً اعتراض ثبت شده یا اصلاح شده است).")
            return
        av = appealable_violation(tg)
        if not av or av.get("case") != case:
            await send_text(bot, tg, "ℹ️ مجازات فعالِ قابل اعتراض برای این پرونده وجود ندارد.")
            return
        set_form(tg, {"kind": "appeal_text", "data": {"case": case}})
        await send_text(bot, tg,
                        "✉️ <b>ثبت اعتراض</b>\n\nتوضیحات خود را بنویسید (چرا این تصمیم اشتباه است؟).\n"
                        "هر پرونده فقط یک بار قابل اعتراض است؛ پس از ارسال، رسید دریافت می‌کنید.",
                        imarkup([[("btn_cancel", "apl_cancel")]]))
        return
    if data == "apl_cancel":
        clear_form(tg)
        try:
            await _edit(q, "❌ ثبت اعتراض لغو شد.")
        except Exception:
            pass
        return
    if data.startswith("apl_confirm:") or data == "apl_skipphoto":
        case = (data.split(":", 1)[1] if ":" in data else
                (user.get("form") or {}).get("data", {}).get("case"))
        form = user.get("form") or {}
        if form.get("kind") != "appeal_photo" or form.get("data", {}).get("case") != case:
            await _edit(q, "ℹ️ فرم اعتراض یافت نشد؛ از دکمه «ثبت اعتراض» دوباره شروع کنید.")
            return
        d = form.get("data", {})
        txt2 = ("📋 <b>پیش‌نمایش اعتراض</b>\n\n"
                f"توضیحات: {esc(d.get('text') or '—')}\n"
                f"تصویر پیوست: {'دارد' if d.get('photo_id') else 'ندارد'}\n\n"
                "برای ارسال نهایی، دکمه سبز را بزنید.")
        await _edit(q, txt2, imarkup([
            [("btn_appeal", f"apl_send:{case}", "ثبت و ارسال اعتراض")],
            [("btn_cancel", "apl_cancel")],
        ]))
        return
    if data.startswith("apl_send:"):
        case = data.split(":", 1)[1]
        form = user.get("form") or {}
        if form.get("kind") != "appeal_photo" or form.get("data", {}).get("case") != case:
            await _edit(q, "ℹ️ فرم اعتراض منقضی شده است؛ دوباره شروع کنید.")
            return
        v = next((x for x in STORE.get("violations") if x.get("case") == case), None)
        if not v or str(v.get("uid")) != str(tg) or v.get("appeal") or v.get("revoked"):
            clear_form(tg)
            await _edit(q, "ℹ️ امکان ثبت اعتراض برای این پرونده وجود نیست.")
            return
        d = form.get("data", {})
        ok_ap = register_appeal(case, d.get("text", ""), d.get("photo_id"))
        clear_form(tg)
        if not ok_ap:
            await _edit(q, "ℹ️ ثبت اعتراض ناموفق بود (احتمالاً قبلاً ثبت شده است).")
            return
        prot = get_protection()
        if prot.get("appeal_mode") == "auto_approve":
            decide_appeal(v["vid"], "approved", "system:auto_appeal", "پذیرش خودکار طبق تنظیمات")
            await _edit(q, "✅ اعتراض شما ثبت و طبق تنظیمات، <b>پذیرفته و مجازات مرتبط لغو شد</b>.",
                        imarkup([[("btn_back", "menu_home")]]))
        elif prot.get("appeal_mode") == "auto_reject":
            decide_appeal(v["vid"], "rejected", "system:auto_appeal", "رد خودکار طبق تنظیمات")
            await _edit(q, "✅ اعتراض شما ثبت شد؛ طبق تنظیمات بررسی، <b>رد شد</b>.",
                        imarkup([[("btn_back", "menu_home")]]))
        else:
            await _edit(q,
                        "✅ <b>اعتراض شما ثبت و ارسال شد.</b>\n\n"
                        f"🧾 شماره رسید پرونده: <code>{case}</code>\n"
                        "نتیجه رسیدگی از همین ربات اعلام می‌شود.\n"
                        "ℹ️ ارسال اعتراض به معنی رفع خودکار مجازات نیست.",
                        imarkup([[("btn_back", "menu_home")]]))
        audit(actor_name_of(tg), "appeal_submitted", target=case)
        return

    # ---------- پنل مالک ----------
    if data == "pn":
        await _edit(q, OWNER_PANEL_TEXT, owner_panel_kb())
        return
    # ---------- راهنمای کامل مدیریت ربات ----------
    if data == "pn_oguide":
        await _edit(q, "📖 <b>راهنمای کامل مدیریت ربات</b>\n\n"
                       "دسته مورد نظر را انتخاب کنید؛ وضعیت فعال/غیرفعال از تنظیمات زنده خوانده می‌شود.",
                    owner_guide_kb())
        return
    if data.startswith("ogc:"):
        if not is_owner(tg):
            await q.answer("⛔ فقط مالک", show_alert=True)
            return
        cat = data.split(":", 1)[1]
        if cat not in OWNER_GUIDE_CATS:
            await _edit(q, "ℹ️ دسته نامعتبر است.", owner_guide_kb())
            return
        await _edit(q, owner_guide_text(cat), imarkup([[("btn_back", "pn_oguide")]]))
        return
    # ---------- سیستم محافظت ----------
    if data == "pn_prot":
        await _edit(q, protection_view_text(), protection_view_kb())
        return
    if data == "pn_prot_tgl":
        cur = get_protection().get("enabled", True)
        set_protection(lambda p: p.update({"enabled": not cur}))
        modlog("owner", "protection_toggle", details=f"enabled={not cur}")
        await _edit(q, protection_view_text(), protection_view_kb())
        return
    if data.startswith("pn_prot_lvl:"):
        n = data.split(":")[1]
        cur = get_protection().get("level_enabled", {}).get(n, True)
        set_protection(lambda p: p.setdefault("level_enabled", {}).update({n: not cur}))
        modlog("owner", "protection_level_toggle", details=f"level:{n} -> {not cur}")
        await _edit(q, protection_view_text(), protection_view_kb())
        return
    if data.startswith("pn_prot_mute:"):
        n = data.split(":")[1]
        set_form(tg, {"kind": "panel_prot_num", "data": {"field": "mute_minutes", "key": n}})
        await send_text(bot, tg, f"مدت سکوت سطح {fa_num(n)} به دقیقه را ارسال کنید:", imarkup([[("btn_cancel", "pn_cancel")]]))
        return
    if data.startswith("pn_prot_stage:"):
        st = data.split(":")[1]
        set_form(tg, {"kind": "panel_prot_num", "data": {"field": "stage_ban_hours", "key": st}})
        await send_text(bot, tg, f"مدت بن مرحله {fa_num(st)} به ساعت را ارسال کنید:", imarkup([[("btn_cancel", "pn_cancel")]]))
        return
    if data.startswith("pn_prot_sup:"):
        st = data.split(":")[1]
        set_form(tg, {"kind": "panel_prot_num", "data": {"field": "stage_super_minutes", "key": st}})
        await send_text(bot, tg, f"مدت محدودیت فوق‌العاده مرحله {fa_num(st)} به دقیقه را ارسال کنید:", imarkup([[("btn_cancel", "pn_cancel")]]))
        return
    if data == "pn_prot_girl":
        cur = get_protection().get("girl_block_enabled", True)
        set_protection(lambda p: p.update({"girl_block_enabled": not cur}))
        modlog("owner", "protection_girl_toggle", details=f"enabled={not cur}")
        await _edit(q, protection_view_text(), protection_view_kb())
        return
    if data in ("pn_prot_girlh4", "pn_prot_girlh5"):
        fld = "girl_block_stage4_hours" if data.endswith("4") else "girl_block_stage5_hours"
        set_form(tg, {"kind": "panel_prot_num", "data": {"field": fld, "key": None}})
        await send_text(bot, tg, "مدت منع چت با دختران به ساعت را ارسال کنید (۰ = دائمی):",
                        imarkup([[("btn_cancel", "pn_cancel")]]))
        return
    if data == "pn_prot_thr":
        set_form(tg, {"kind": "panel_prot_num", "data": {"field": "escalation_threshold", "key": None}})
        await send_text(bot, tg, "تعداد تخلفات تأییدشده لازم برای ارتقای یک مرحله را ارسال کنید:",
                        imarkup([[("btn_cancel", "pn_cancel")]]))
        return
    if data == "pn_prot_apl":
        order = ["manual", "auto_approve", "auto_reject"]
        cur = get_protection().get("appeal_mode", "manual")
        nxt = order[(order.index(cur) + 1) % len(order)] if cur in order else "manual"
        set_protection(lambda p: p.update({"appeal_mode": nxt}))
        modlog("owner", "protection_appeal_mode", details=nxt)
        await _edit(q, protection_view_text(), protection_view_kb())
        return
    if data == "pn_prot_reset":
        set_protection(lambda p: p.clear() or p.update(dict(DEFAULT_PROTECTION)))
        modlog("owner", "protection_reset_defaults")
        await _edit(q, "♻️ تنظیمات سیستم محافظت به پیش‌فرض بازگشت.\n\n" + protection_view_text(),
                    protection_view_kb())
        return
    # ---------- اعتراض‌ها ----------
    if data == "pn_apls" or data.startswith("pn_aplp:"):
        page = int(data.split(":")[1]) if ":" in data else 0
        txt2, kb2 = appeals_list_text(page)
        await _edit(q, txt2, kb2)
        return
    if data.startswith("pn_apv:"):
        vid = data.split(":", 1)[1]
        txt2, kb2 = appeal_view_text(vid)
        await _edit(q, txt2, kb2)
        return
    if data.startswith("pn_apimg:"):
        vid = data.split(":", 1)[1]
        v = next((x for x in STORE.get("violations") if x.get("vid") == vid), None)
        if not v or not (v.get("appeal") or {}).get("photo_id"):
            await send_text(bot, tg, "ℹ️ تصویری برای این پرونده ثبت نشده است.")
            return
        try:
            await bot.send_photo(chat_id=tg, photo=v["appeal"]["photo_id"],
                                 caption=f"🖼 تصویر پیوست اعتراض {v['case']}")
        except TelegramError:
            await send_text(bot, tg, "⚠️ ارسال تصویر ناموفق بود.")
        return
    if data.startswith("pn_apdec:"):
        _, vid, decision = data.split(":")
        if decision not in ("approved", "rejected", "hold"):
            return
        v = next((x for x in STORE.get("violations") if x.get("vid") == vid), None)
        note_txt = {"approved": "اعتراض تأیید شد؛ مجازات مرتبط لغو گردید.",
                    "rejected": "اعتراض بررسی و رد شد.",
                    "hold": "اعتراض برای بررسی بیشتر نگه داشته شد."}
        decide_appeal(vid, decision, "owner")
        if v and decision == "approved":
            await send_text(bot, int(v["uid"]),
                            "✅ <b>اعتراض شما تأیید شد.</b>\nمجازات‌های مرتبط با پرونده شما لغو گردید.",
                            main_menu_kb())
        elif v:
            await send_text(bot, int(v["uid"]), f"⚖ نتیجه اعتراض شما: {note_txt[decision]}")
        txt2, kb2 = appeal_view_text(vid)
        await _edit(q, txt2, kb2)
        return
    # ---------- وضعیت امنیتی و مجازات‌های کاربر ----------
    if data.startswith("pn_sec:"):
        uid = int(data.split(":")[1])
        txt2, _kb = security_view_text(uid)
        await _edit(q, txt2, security_view_kb(uid))
        return
    if data.startswith("pn_sx:"):
        _, uid_s, op = data.split(":", 2)
        uid = int(uid_s)
        if op == "unmute":
            release_mute(uid, by="owner")
            await send_text(bot, uid, "سکوت شما برداشته شد.")
            await _edit(q, "✔ سکوت رفع شد.")
        elif op == "unban":
            release_ban(uid, by="owner")
            await send_text(bot, uid, "♻️ مسدودی حساب شما برداشته شد.")
            await _edit(q, "✔ بن رفع شد.")
        elif op == "clearsuper":
            release_super_limit(uid, by="owner")
            await _edit(q, "✔ محدودیت فوق‌العاده لغو شد.")
        elif op == "girl_remove":
            release_girl_block(uid, by="owner")
            await _edit(q, "✔ منع چت با دختران لغو شد.")
        elif op == "mute_add":
            set_form(tg, {"kind": "panel_sec_num", "data": {"uid": uid, "op": "mute_add"}})
            await send_text(bot, tg, "دقیقه‌های افزودنی سکوت را ارسال کنید:", imarkup([[("btn_cancel", "pn_cancel")]]))
        elif op == "mute_reduce":
            set_form(tg, {"kind": "panel_sec_num", "data": {"uid": uid, "op": "mute_reduce"}})
            await send_text(bot, tg, "دقیقه‌های کاهنده سکوت را ارسال کنید:", imarkup([[("btn_cancel", "pn_cancel")]]))
        elif op == "ban_change":
            set_form(tg, {"kind": "panel_sec_num", "data": {"uid": uid, "op": "ban_change"}})
            await send_text(bot, tg, "مدت جدید بن به دقیقه را ارسال کنید (برای بن دائمی، مدت جدید موقت جایگزین می‌شود):",
                            imarkup([[("btn_cancel", "pn_cancel")]]))
        elif op == "girl_set":
            set_form(tg, {"kind": "panel_sec_num", "data": {"uid": uid, "op": "girl_set"}})
            await send_text(bot, tg, "مدت منع چت با دختران به ساعت را ارسال کنید (۰ = دائمی):",
                            imarkup([[("btn_cancel", "pn_cancel")]]))
        elif op == "custom":
            set_form(tg, {"kind": "panel_sec_custom", "data": {"uid": uid}})
            await send_text(bot, tg, "مجازات اختصاصی — یکی را ارسال کنید:\n«سکوت:۳۰» | «بن:۲۴ساعت» | «فوق‌العاده:۱۲۰» (دقیقه) | «دختر:۱۶۸» (ساعت، ۰=دائمی)",
                            imarkup([[("btn_cancel", "pn_cancel")]]))
        elif op == "warndel":
            warns = [w for w in STORE.get("warnings") if w.get("uid") == uid_s][-6:]
            if not warns:
                await _edit(q, "ℹ️ اخطاری برای حذف وجود ندارد.")
                return
            rows2 = [[InlineKeyboardButton(f"حذف: {w['reason'][:28]} ({jalali(parse_iso(w['created']))})",
                                           callback_data=f"pn_sxwd:{uid}:{w['wid']}")] for w in reversed(warns)]
            rows2.append([("btn_back", f"pn_sec:{uid}")])
            await _edit(q, "کدام اخطار حذف شود؟", imarkup(rows2))
            return
        elif op == "revoke":
            viol = [v for v in STORE.get("violations")
                    if v.get("uid") == uid_s and not v.get("revoked")][-6:]
            if not viol:
                await _edit(q, "ℹ️ تخلف تأییدشده‌ای برای لغو وجود ندارد.")
                return
            rows2 = [[InlineKeyboardButton(f"لغو {v['case']} — سطح {fa_num(v.get('level', 0))}",
                                           callback_data=f"pn_sxrv:{uid}:{v['vid']}")] for v in reversed(viol)]
            rows2.append([("btn_back", f"pn_sec:{uid}")])
            await _edit(q, "کدام تخلف لغو شود؟ (تشخیص اشتباه — دیگر در مرحله‌بندی شمرده نمی‌شود)", imarkup(rows2))
            return
        elif op == "clearviol":
            set_form(tg, {"kind": "panel_sec_reason", "data": {"uid": uid}})
            await send_text(bot, tg, "دلیل مدیریتی پاک‌کردن سابقه تخلفات را بنویسید:",
                            imarkup([[("btn_cancel", "pn_cancel")]]))
            return
        txt2, _kb = security_view_text(uid)
        try:
            await _edit(q, txt2, security_view_kb(uid))
        except Exception:
            pass
        return
    if data.startswith("pn_sxwd:"):
        _, uid_s, wid = data.split(":")
        uid = int(uid_s)

        def _wd(lst):
            for w in lst:
                if w.get("wid") == wid:
                    w["deleted"] = True
                    w["deleted_by"] = "owner"
                    w["deleted_at"] = iso_utc(now_utc())
            return lst
        STORE.update("warnings", _wd)
        update_user(uid, lambda x: x.update({"warnings": max(0, x.get("warnings", 0) - 1)}))
        modlog("owner", "warning_deleted", uid, wid)
        txt2, _kb = security_view_text(uid)
        await _edit(q, "✔ اخطار حذف شد.\n\n" + txt2, security_view_kb(uid))
        return
    if data.startswith("pn_sxrv:"):
        _, uid_s, vid = data.split(":")
        revoke_violation(vid, "owner", "اصلاح مدیریتی از پنل")
        uid = int(uid_s)
        u2 = get_user(uid)
        if u2:
            await send_text(bot, uid, "♻️ یکی از تخلف‌های ثبت‌شده در پرونده شما پس از بررسی مدیریت لغو شد.")
        txt2, _kb = security_view_text(uid)
        await _edit(q, "✔ تخلف لغو و مجازات‌های همان پرونده اصلاح شد.\n\n" + txt2, security_view_kb(uid))
        return
    if data == "pn_dash":
        await _edit(q, dashboard_text(), imarkup([[("btn_back", "pn")]]))
        return
    if data == "pn_me":
        # مشخصات خودِ مالک — بدون نیاز به ثبت‌نام؛ ویرایش از مسیر همان پنل کاربر
        ensure_owner_record()
        txt, kb = user_view_text(OWNER_ID, back_cd="pn")
        await _edit(q, txt, kb)
        return
    if data == "pn_users" or data.startswith("pn_up:"):
        page = int(data.split(":")[1]) if ":" in data else 0
        txt, kb = users_list_text(page)
        await _edit(q, txt, kb)
        return
    if data == "pn_us":
        set_form(tg, {"kind": "panel_search", "data": {}})
        await send_text(bot, tg, "عبارت جست‌وجو را ارسال کنید (شناسه اختصاصی، شناسه تلگرام یا نام):")
        return
    if data.startswith("pn_u:"):
        uid = int(data.split(":")[1])
        txt, kb = user_view_text(uid)
        await _edit(q, txt, kb)
        return
    if data.startswith("pn_ua:"):
        _, uid_s, act = data.split(":")
        uid = int(uid_s)
        if act == "msg":
            set_form(tg, {"kind": "panel_user_msg", "data": {"uid": uid}})
            await send_text(bot, tg,
                            "✉️ متن پیام برای کاربر:\n\n"
                            "دستورات مدیریتی: «سکوت{دقیقه}»، «بن{دقیقه}»، «اخطار»، «حذف سکوت»، «حذف بن»، «گزارش»",
                            imarkup([[("btn_cancel", "pn_cancel")]]))
        elif act == "edit":
            kb = imarkup([
                [("btn_next", f"pn_ue:{uid}:name", "نام"), ("btn_next", f"pn_ue:{uid}:gender", "جنسیت")],
                [("btn_next", f"pn_ue:{uid}:age", "سن"), ("btn_next", f"pn_ue:{uid}:province", "استان")],
                [("btn_back", f"pn_u:{uid}")],
            ])
            await _edit(q, "✏️ کدام مشخصه را تغییر می‌دهید؟", kb)
        elif act == "warn":
            set_form(tg, {"kind": "panel_user_warn", "data": {"uid": uid}})
            await send_text(bot, tg, " دلیل اخطار را بنویسید:", imarkup([[("btn_cancel", "pn_cancel")]]))
        elif act == "ban":
            set_form(tg, {"kind": "panel_user_ban", "data": {"uid": uid}})
            await send_text(bot, tg, " مدت بن به دقیقه را ارسال کنید:", imarkup([[("btn_cancel", "pn_cancel")]]))
        elif act == "perm":
            if apply_ban(uid, permanent=True, by="owner", reason="بن دائمی مدیریتی"):
                u2 = get_user(uid)
                if u2:
                    await send_text(bot, uid, "حساب شما به‌صورت دائمی مسدود شد.")
                await _edit(q, "بن دائمی اعمال شد.")
            else:
                await _edit(q, "ℹ️ امکان بن این کاربر نیست.")
        elif act == "unban":
            release_ban(uid, by="owner")
            u2 = get_user(uid)
            if u2:
                await send_text(bot, uid, "♻️ مسدودی حساب شما برداشته شد.")
            await _edit(q, "بن رفع شد.")
        elif act == "unmute":
            release_mute(uid, by="owner")
            u2 = get_user(uid)
            if u2:
                await send_text(bot, uid, "سکوت شما برداشته شد.")
            await _edit(q, "سکوت رفع شد.")
        return
    if data.startswith("pn_ue:"):
        _, uid_s, field = data.split(":")
        prompts = {"name": "نام جدید:", "gender": "جنسیت جدید (پسر/دختر):",
                   "age": "سن جدید (عدد):", "province": "استان جدید:"}
        set_form(tg, {"kind": "panel_user_edit", "data": {"uid": int(uid_s), "field": field}})
        await send_text(bot, tg, prompts[field], imarkup([[("btn_cancel", "pn_cancel")]]))
        return
    if data == "pn_rpts" or data.startswith("pn_rp:"):
        page = int(data.split(":")[1]) if ":" in data else 0
        txt, kb = reports_list_text(page)
        await _edit(q, txt, kb)
        return
    if data.startswith("pn_rv:"):
        rid = data.split(":")[1]
        txt, kb = report_view_text(rid)
        await _edit(q, txt, kb)
        return
    if data.startswith("pn_ra:"):
        _, rid, act = data.split(":")
        r = next((x for x in STORE.get("reports") if x.get("rid") == rid), None)
        if not r:
            await _edit(q, "ℹ️ گزارش یافت نشد.")
            return
        if act == "review":
            STORE.update("reports", lambda lst: [dict(x, status="in_review") if x.get("rid") == rid else x for x in lst])
            txt, kb = report_view_text(rid)
            await _edit(q, txt, kb)
        elif act == "msgs":
            txt, kb = report_messages_text(rid, 0)
            await _edit(q, txt, kb)
        elif act == "msg_r":
            set_form(tg, {"kind": "panel_rpt_umsg", "data": {"rid": rid, "who": "r"}})
            await send_text(bot, tg, " متن پیام به گزارش‌دهنده:", imarkup([[("btn_cancel", "pn_cancel")]]))
        elif act == "msg_b":
            set_form(tg, {"kind": "panel_rpt_umsg", "data": {"rid": rid, "who": "b"}})
            await send_text(bot, tg, " متن پیام به کاربر گزارش‌شده:", imarkup([[("btn_cancel", "pn_cancel")]]))
        elif act == "warn":
            uid = int(r["reported"])
            if add_admin_warning(uid, "اخطار ناشی از بررسی گزارش", "owner"):
                await send_text(bot, uid, "⚠️ به حساب شما اخطار داده شد.")
                await _edit(q, "اخطار ثبت شد.")
            else:
                await _edit(q, "ℹ️ امکان اخطار نیست.")
        elif act == "ban":
            set_form(tg, {"kind": "panel_user_ban", "data": {"uid": int(r["reported"])}})
            await send_text(bot, tg, " مدت بن به دقیقه:", imarkup([[("btn_cancel", "pn_cancel")]]))
        elif act == "perm":
            if apply_ban(int(r["reported"]), permanent=True, by="owner", reason="تأیید گزارش"):
                await send_text(bot, int(r["reported"]), "حساب شما به‌صورت دائمی مسدود شد.")
                await _edit(q, "بن دائمی اعمال شد.")
            else:
                await _edit(q, "ℹ️ امکان بن نیست.")
        elif act == "note":
            set_form(tg, {"kind": "panel_rpt_note", "data": {"rid": rid}})
            await send_text(bot, tg, " یادداشت مدیریتی:", imarkup([[("btn_cancel", "pn_cancel")]]))
        elif act in ("confirm", "reject"):
            outcome = "confirmed" if act == "confirm" else "rejected"
            def _m(lst):
                for x in lst:
                    if x.get("rid") == rid:
                        x["status"] = "reviewed"
                        x["outcome"] = outcome
                        x["closed"] = iso_utc(now_utc())
                return lst
            STORE.update("reports", _m)
            conv_id = r.get("conv")
            if conv_id:
                STORE.update("conversations", lambda cs: dict(cs, **{conv_id: dict(cs[conv_id], has_open_report=False)}) if conv_id in cs else cs)
            audit("owner", f"report_{outcome}", target=rid)
            modlog("owner", f"report_{outcome}", int(r.get("reported") or 0))
            txt, kb = report_view_text(rid)
            await _edit(q, txt, kb)
        return
    if data.startswith("pn_rm:"):
        parts = data.split(":")
        rid, page = parts[1], int(parts[2])
        txt, kb = report_messages_text(rid, page)
        await _edit(q, txt, kb)
        return
    if data.startswith("pn_rmsg:"):
        parts = data.split(":")
        ok = await send_report_message_to_owner(context, parts[1], parts[3])
        await q.answer("ارسال شد ✅" if ok else "یافت نشد ⚠️", show_alert=not ok)
        return
    if data == "pn_bc":
        set_form(tg, {"kind": "panel_broadcast", "data": {}})
        await send_text(bot, tg, " متن پیام همگانی را ارسال کنید (فرمت‌های تلگرام حفظ می‌شود):", imarkup([[("btn_cancel", "pn_cancel")]]))
        return
    if data == "pn_bc_pin":
        form = user.get("form") or {}
        d = dict(form.get("data") or {})
        d["pin"] = not d.get("pin", False)
        form["data"] = d
        set_form(tg, form)
        await _edit(q, "📌 وضعیت سنجاق به‌روز شد.", broadcast_confirm_kb(d.get("pin"), d.get("react")))
        await send_text(bot, tg, f"📣 <b>پیش‌نمایش پیام همگانی:</b>\n\n{esc(d.get('text') or '')}"
                        f"\n\n📌 سنجاق: {'روشن' if d.get('pin') else 'خاموش'} | "
                        f"👍 واکنش: {'روشن' if d.get('react') else 'خاموش'}",
                        broadcast_confirm_kb(d.get("pin"), d.get("react")), html=True)
        return
    if data == "pn_bc_react":
        form = user.get("form") or {}
        d = dict(form.get("data") or {})
        d["react"] = not d.get("react", False)
        form["data"] = d
        set_form(tg, form)
        await _edit(q, "👍 وضعیت واکنش به‌روز شد.", broadcast_confirm_kb(d.get("pin"), d.get("react")))
        await send_text(bot, tg, f"📣 <b>پیش‌نمایش پیام همگانی:</b>\n\n{esc(d.get('text') or '')}"
                        f"\n\n📌 سنجاق: {'روشن' if d.get('pin') else 'خاموش'} | "
                        f"👍 واکنش: {'روشن' if d.get('react') else 'خاموش'}",
                        broadcast_confirm_kb(d.get("pin"), d.get("react")), html=True)
        return
    if data == "pn_bc_sched":
        form = user.get("form") or {}
        if not form.get("data", {}).get("text"):
            await send_text(bot, tg, "ℹ️ ابتدا متن پیام همگانی را ارسال کنید.", owner_panel_kb())
            return
        set_form(tg, {"kind": "panel_bc_sched", "data": dict(form["data"])})
        await send_text(bot, tg,
                        "⏰ <b>ارسال زمان‌بندی‌شده همگانی</b>\n\n"
                        "یکی از قالب‌ها را ارسال کنید:\n"
                        "• <b>تأخیر</b> — مثال: «30» (ارسال ۳۰ دقیقه بعد)\n"
                        "• <b>تأخیر + تکرار</b> — مثال: «30/6» (اولین ارسال ۳۰ دقیقه بعد، سپس هر ۶ ساعت)\n"
                        "• <b>تأخیر/تکرار/دفعات</b> — مثال: «30/6/5» (هر ۶ ساعت، ۵ بار)\n\n"
                        "اعداد فارسی/انگلیسی؛ تکرار=۰ یعنی بدون تکرار. سنجاق/واکنش از وضعیت فعلی حفظ می‌شود.",
                        imarkup([[("btn_cancel", "pn_bc_sched_no")]]), html=True)
        return
    if data == "pn_bc_sched_no":
        form = user.get("form") or {}
        if form.get("kind") == "panel_bc_sched" and form.get("data", {}).get("text"):
            set_form(tg, {"kind": "panel_broadcast", "data": dict(form["data"])})
            d = form["data"]
            await send_text(bot, tg, f"📣 <b>پیش‌نمایش پیام همگانی:</b>\n\n{esc(d.get('text') or '')}"
                            f"\n\n📌 سنجاق: {'روشن' if d.get('pin') else 'خاموش'} | "
                            f"👍 واکنش: {'روشن' if d.get('react') else 'خاموش'}",
                            broadcast_confirm_kb(d.get("pin"), d.get("react")), html=True)
        else:
            clear_form(tg)
            await send_text(bot, tg, "ℹ️ لغو شد.", owner_panel_kb())
        return
    if data == "pn_bc_jobs":
        await _edit(q, broadcast_jobs_list_text(), broadcast_jobs_kb())
        return
    if data.startswith("pn_bj_del:"):
        jid = data.split(":")[1]
        ok = cancel_broadcast_job(jid)
        await _edit(q, "✅ ارسال زمان‌بندی‌شده لغو شد." if ok else "ℹ️ یافت نشد یا قبلاً تمام شده است.",
                    broadcast_jobs_kb() if ok else broadcast_jobs_kb())
        return
    if data == "pn_bc_go":
        form = user.get("form") or {}
        text_b = form.get("data", {}).get("text")
        pin_b = bool(form.get("data", {}).get("pin"))
        react_b = bool(form.get("data", {}).get("react"))
        clear_form(tg)
        if not text_b:
            await send_text(bot, tg, "ℹ️ متن پیام یافت نشد.")
            return
        await send_text(bot, tg, "⏳ در حال ارسال...")
        sent, failed = await do_broadcast(context, text_b, pin=pin_b, react=react_b)
        await send_text(bot, tg, f"✅ اطلاع‌رسانی کامل شد.\nموفق: {fa_num(sent)} | ناموفق: {fa_num(failed)}", owner_panel_kb())
        return
    if data == "pn_bc_no":
        clear_form(tg)
        await _edit(q, "ℹ️ اطلاع‌رسانی لغو شد.")
        return
    if data == "pn_cancel":
        clear_form(tg)
        await send_text(bot, tg, "ℹ️ لغو شد.", owner_panel_kb())
        return
    if data == "pn_set":
        await _edit(q, settings_text(), settings_kb())
        return
    if data.startswith("pn_sa:"):
        key = data.split(":")[1]
        if key == "action":
            order = ["warn", "mute", "ban", "perm"]
            s = STORE.get("settings")
            cur = order.index(s.get("profanity_action", "warn"))
            STORE.update("settings", lambda x: dict(x, profanity_action=order[(cur + 1) % 4]))
            await _edit(q, settings_text(), settings_kb())
        elif key == "auto_bk":
            s = STORE.get("settings")
            STORE.update("settings", lambda x: dict(x, auto_backup_enabled=not s.get("auto_backup_enabled", True)))
            await _edit(q, settings_text(), settings_kb())
        elif key == "bk_keep":
            s = STORE.get("settings")
            vals = [10, 20, 30, 50, 100]
            cur = vals.index(s.get("backup_keep", 30)) if s.get("backup_keep", 30) in vals else 2
            STORE.update("settings", lambda x: dict(x, backup_keep=vals[(cur + 1) % len(vals)]))
            await _edit(q, settings_text(), settings_kb())
        else:
            prompts = {"cap": ("panel_cap", "سقف اخطار جدید (عدد):"),
                       "minutes": ("panel_minutes", "مدت مجازات (دقیقه):"),
                       "rate": ("panel_rate", "سقف پیام در دقیقه:"),
                       "retention": ("panel_retention", "ساعت نگهداری پیام‌ها (۱ تا ۷۲۰):"),
                       "qtimeout": ("panel_qtimeout", "انقضای صف انتظار (دقیقه):"),
                       "rtimeout": ("panel_rtimeout", "انقضای درخواست دوست (دقیقه):"),
                       "oname": ("panel_oname", "نام پروفایل مالک:"),
                       "obio": ("panel_obio", "توضیحات پروفایل مالک:")}
            if key in prompts:
                set_form(tg, {"kind": prompts[key][0], "data": {}})
                await send_text(bot, tg, prompts[key][1], imarkup([[("btn_cancel", "pn_cancel")]]))
        return
    if data == "pn_fmt" or data.startswith("pn_fp:"):
        await _edit(q, formats_text(), formats_kb())
        return
    if data.startswith("pn_fa:"):
        key = data.split(":")[1]
        if key == "allow_unknown":
            s = STORE.get("settings")
            STORE.update("settings", lambda x: dict(x, allow_unknown_files=not s.get("allow_unknown_files", False)))
        elif key == "link_warn":
            # باز/بسته کردن هشدار لینک برای دریافت‌کننده (استثنای لینک‌ها)
            s = STORE.get("settings")
            STORE.update("settings", lambda x: dict(x, link_warning_enabled=not s.get("link_warning_enabled", True)))
        elif key == "link_warn_text":
            # ویرایش متن هشدار لینک
            set_form(tg, {"kind": "panel_link_warn_text", "data": {}})
            s = STORE.get("settings")
            await send_text(bot, tg,
                            "📝 <b>متن هشدار لینک</b>\n\nمتن فعلی:\n"
                            + (s.get("link_warning_text") or LINK_WARNING_DEFAULT) +
                            "\n\nمتن جدید را ارسال کنید (تگ‌های HTML مجاز است) یا «پیش‌فرض» را بفرستید:",
                            imarkup([[("btn_cancel", "pn_cancel")]]), html=True)
            return
        else:
            s = STORE.get("settings")
            cur = s.get("formats", {}).get(key, True)
            def _m(x):
                fm = dict(x.get("formats", {}))
                fm[key] = not cur
                return dict(x, formats=fm)
            STORE.update("settings", _m)
        await _edit(q, formats_text(), formats_kb())
        return
    if data == "pn_prof":
        await _edit(q, profanity_text(), profanity_kb())
        return
    if data.startswith("pn_pa:"):
        act = data.split(":")[1]
        if act == "toggle":
            s = STORE.get("settings")
            STORE.update("settings", lambda x: dict(x, profanity_enabled=not s.get("profanity_enabled", True)))
            await _edit(q, profanity_text(), profanity_kb())
        elif act == "wadd":
            set_form(tg, {"kind": "panel_wadd", "data": {}})
            await send_text(bot, tg, " واژه یا عبارت ممنوع را ارسال کنید:", imarkup([[("btn_cancel", "pn_cancel")]]))
        elif act == "wladd":
            set_form(tg, {"kind": "panel_wladd", "data": {}})
            await send_text(bot, tg, " واژه مجاز (whitelist) را ارسال کنید:", imarkup([[("btn_cancel", "pn_cancel")]]))
        elif act == "words":
            txt, kb = profanity_words_text("b", 0)
            await _edit(q, txt, kb)
        elif act == "wlist":
            txt, kb = profanity_words_text("w", 0)
            await _edit(q, txt, kb)
        elif act == "hours":
            txt, kb = profanity_hours_text()
            await _edit(q, txt, kb)
        elif act == "hadd":
            set_form(tg, {"kind": "panel_hours_add", "data": {}})
            await send_text(bot, tg, "⏰ بازه زمانی را ارسال کنید (نمونه: 22:00-06:00):", imarkup([[("btn_cancel", "pn_cancel")]]))
        elif act == "days":
            await _edit(q, "📅 روزهای فعال فیلتر:", profanity_days_kb())
        return
    if data.startswith("pn_pwp:"):
        _, which, page = data.split(":")
        txt, kb = profanity_words_text(which, int(page))
        await _edit(q, txt, kb)
        return
    if data.startswith("pn_pw:"):
        _, which, idx = data.split(":")
        idx = int(idx)
        key = "custom_blocked" if which == "b" else "custom_whitelist"
        def _m(c):
            lst = list(c.get(key, []))
            if 0 <= idx < len(lst):
                lst.pop(idx)
            return dict(c, **{key: lst})
        STORE.update("profanity_words", _m)
        txt, kb = profanity_words_text(which, 0)
        await _edit(q, txt, kb)
        return
    if data.startswith("pn_pd:"):
        d = int(data.split(":")[1])
        def _m(x):
            days = list(x.get("profanity_weekdays", []))
            days = [x2 for x2 in days if x2 != d] if d in days else sorted(days + [d])
            return dict(x, profanity_weekdays=days)
        STORE.update("settings", _m)
        await _edit(q, "📅 روزهای فعال فیلتر:", profanity_days_kb())
        return
    if data.startswith("pn_ph:"):
        idx = int(data.split(":")[1])
        def _m(x):
            hours = list(x.get("profanity_hours", []))
            if 0 <= idx < len(hours):
                hours.pop(idx)
            return dict(x, profanity_hours=hours)
        STORE.update("settings", _m)
        txt, kb = profanity_hours_text()
        await _edit(q, txt, kb)
        return
    if data == "pn_ch":
        await _edit(q, channels_text(), channels_kb())
        return
    if data.startswith("pn_ca:"):
        act = data.split(":")[1]
        if act == "toggle":
            conf = STORE.get("mandatory_channels")
            STORE.update("mandatory_channels", lambda c: dict(c, enabled=not conf.get("enabled", False)))
            await _edit(q, channels_text(), channels_kb())
        elif act == "add":
            set_form(tg, {"kind": "panel_ch_add", "data": {}})
            await send_text(bot, tg, "➕ @username یا شناسه عددی کانال/گروه را ارسال کنید (ربات باید عضو باشد):",
                            imarkup([[("btn_cancel", "pn_cancel")]]))
        return
    if data.startswith("pn_cr:"):
        idx = int(data.split(":")[1])
        def _m(c):
            chs = list(c.get("channels", []))
            if 0 <= idx < len(chs):
                removed = chs.pop(idx)
                audit("owner", "mandatory_channel_removed", details=removed.get("target", ""))
            return dict(c, channels=chs)
        STORE.update("mandatory_channels", _m)
        await _edit(q, channels_text(), channels_kb())
        return
    if data == "pn_supp" or data.startswith("pn_tp:"):
        page = int(data.split(":")[1]) if ":" in data else 0
        txt, kb = tickets_list_text(page)
        await _edit(q, txt, kb)
        return
    if data.startswith("pn_tv:"):
        tid = data.split(":")[1]
        txt, kb = ticket_view_text(tid)
        await _edit(q, txt, kb)
        return
    if data.startswith("pn_ta:"):
        _, tid, act = data.split(":")
        if act == "reply":
            set_form(tg, {"kind": "panel_admin_reply", "data": {"tid": tid}})
            await send_text(bot, tg,
                            "✉️ پاسخ به کاربر:\n\nدستورات مدیریتی: «سکوت{دقیقه}»، «بن{دقیقه}»، «اخطار»، «حذف سکوت»، «حذف بن»، «گزارش»",
                            imarkup([[("btn_cancel", "pn_cancel")]]))
        elif act == "open":
            set_ticket_status(tid, "open")
            txt, kb = ticket_view_text(tid)
            await _edit(q, txt, kb)
        elif act == "close":
            set_ticket_status(tid, "closed")
            txt, kb = ticket_view_text(tid)
            await _edit(q, txt, kb)
        return
    if data == "pn_bot":
        await _edit(q, bot_status_text(), bot_status_kb())
        return
    if data.startswith("pn_ba:"):
        act = data.split(":")[1]
        if act == "on":
            STORE.update("settings", lambda x: dict(x, bot_enabled=True, maintenance=False))
            audit("owner", "bot_on")
            await _edit(q, bot_status_text(), bot_status_kb())
        elif act == "off":
            STORE.update("settings", lambda x: dict(x, bot_enabled=False))
            audit("owner", "bot_off")
            await _edit(q, bot_status_text(), bot_status_kb())
        elif act in ("sched_on", "sched_off"):
            set_form(tg, {"kind": f"panel_{act}", "data": {}})
            await send_text(bot, tg, "⏰ ساعت روزانه را ارسال کنید (نمونه: 08:30) — به وقت تهران:",
                            imarkup([[("btn_cancel", "pn_cancel")]]))
        elif act == "sched_clear":
            def _m(x):
                on = dict(x.get("sched_on") or {}, enabled=False)
                off = dict(x.get("sched_off") or {}, enabled=False)
                return dict(x, sched_on=on, sched_off=off)
            STORE.update("settings", _m)
            audit("owner", "schedule_cleared")
            await _edit(q, bot_status_text(), bot_status_kb())
        return
    # ---------- تنظیمات پیشرفته: مدیریت دکمه‌ها ----------
    if data == "pn_adv":
        await _edit(q, "🧩 <b>تنظیمات پیشرفته</b>\n\nمدیریت کامل دکمه‌ها و دستورات از همین بخش؛ بدون ویرایش کد.", adv_main_kb())
        return
    if data == "pn_btn":
        await _edit(q, btn_manager_text(), btn_manager_kb())
        return
    if data.startswith("pn_bv:"):
        key = data.split(":")[1]
        await _edit(q, btn_detail_text(key), btn_detail_kb(key))
        return
    if data.startswith("pn_bcolor:"):
        key = data.split(":")[1]
        await _edit(q, btn_detail_text(key) + "\n\nرنگ رسمی جدید را انتخاب کنید:", btn_color_kb(key))
        return
    if data.startswith("pn_bcset:"):
        parts = data.split(":")
        key, style = parts[1], parts[2] if len(parts) > 2 else ""
        if style not in VALID_STYLES:
            style = ""
        draft_set_style(key, style)
        await _edit(q, btn_detail_text(key) + "\n\nرنگ جدید در پیش‌نویس ذخیره شد؛ با «پیش‌نمایش و ذخیره» اعمال می‌شود.", btn_detail_kb(key))
        return
    if data.startswith("pn_btext:"):
        key = data.split(":")[1]
        set_form(tg, {"kind": "panel_btn_text", "data": {"key": key}})
        await send_text(bot, tg, f"متن جدید دکمه «{d_text(get_draft(), key)}» را ارسال کنید (بدون ایموجی):",
                        imarkup([[("btn_cancel", "pn_cancel")]]))
        return
    if data.startswith("pn_ben:"):
        key = data.split(":")[1]
        new_state = not d_enabled(get_draft(), key)
        draft_set_enabled(key, new_state)
        await _edit(q, btn_detail_text(key), btn_detail_kb(key))
        return
    if data.startswith("pn_bm:"):
        parts = data.split(":")
        key, direction = parts[1], parts[2]
        draft = get_draft()
        for kb_name in ("main_menu", "conv"):
            rows = d_layout(draft, kb_name)
            for i, row in enumerate(rows):
                if key in row:
                    j = row.index(key)
                    k = j - 1 if direction == "up" else j + 1
                    if 0 <= k < len(row):
                        row[j], row[k] = row[k], row[j]
                        draft_set_rows(kb_name, rows)
                        await _edit(q, layout_table_text(get_draft(), kb_name), layout_editor_kb(kb_name))
                        return
        await _edit(q, "ℹ️ این دکمه جابه‌جایی ندارد.", btn_detail_kb(key))
        return
    if data.startswith("pn_bmrow:"):
        key = data.split(":")[1]
        await _edit(q, f"انتقال «{d_text(get_draft(), key)}» به کدام ردیف؟", btn_move_rows_kb(key))
        return
    if data.startswith("pn_bmto:"):
        parts = data.split(":")
        key, kb_name, target = parts[1], parts[2], parts[3]
        if target == "first":
            # «ردیف اول» به‌معنای ردیف جدید در صدر کیبورد است (نه ادغام در ردیف ۱)
            if move_button_in_layout(kb_name, key, "first"):
                audit("owner", "button_moved", target=key, details=f"{kb_name}:first")
            await _edit(q, layout_table_text(get_draft(), kb_name), layout_editor_kb(kb_name))
            return
        draft = get_draft()
        rows = d_layout(draft, kb_name)
        # ۱) ابتدا ایندکس ردیف مبدا و مقصد با شماره‌گذاری «قبل از حذف» محاسبه می‌شود؛
        #    حذف ردیف خالی بعد از جابه‌جایی ایندکس مقصد را جابه‌جا نمی‌کند (رفع باگ
        #    «انتقال به ردیف اول وقتی دکمه تک‌عضو ردیفی پایین‌تر است کار نمی‌کند»).
        src_rows = [i for i, row in enumerate(rows) if key in row]
        ti = None
        if target != "new":
            ti = int(target)
        # ۲) حذف دکمه از ردیف فعلی
        for i in src_rows:
            rows[i] = [k for k in rows[i] if k != key]
        # ۳) اعمال مقصد با ایندکس پایدار: اگر ردیف مبدا خالی شد و قبل از مقصد بود،
        #    ایندکس مقصد یک واحد کم می‌شود تا همان ردیف دیداری قبلی هدف بماند.
        empty_src = [i for i in src_rows if not rows[i]]
        if ti is not None and empty_src:
            drop_before = sum(1 for i in empty_src if i < ti)
            ti = max(0, ti - drop_before)
        rows = [r for r in rows if r]
        if target == "new":
            rows.append([key])
        else:
            while ti >= len(rows):
                rows.append([])
            rows[ti].append(key)
        draft_set_rows(kb_name, rows)
        await _edit(q, layout_table_text(get_draft(), kb_name), layout_editor_kb(kb_name))
        return
    if data.startswith("pn_layout:"):
        kb_name = data.split(":")[1]
        await _edit(q, layout_table_text(get_draft(), kb_name), layout_editor_kb(kb_name))
        return
    if data.startswith("pn_ladd:"):
        parts = data.split(":")
        await _edit(q, "کدام دکمه به این ردیف اضافه شود؟", layout_add_kb(parts[1], int(parts[2])))
        return
    if data.startswith("pn_laddto:"):
        parts = data.split(":")
        kb_name, i, key = parts[1], int(parts[2]), parts[3]
        if key not in kb_allowed_keys(kb_name):
            await _edit(q, "ℹ️ این دکمه به این کیبورد تعلق ندارد؛ دکمه‌های هر کیبورد جدا می‌مانند.",
                        layout_editor_kb(kb_name))
            return
        draft = get_draft()
        rows = d_layout(draft, kb_name)
        if 0 <= i < len(rows):
            rows[i].append(key)
            draft_set_rows(kb_name, rows)
        await _edit(q, layout_table_text(get_draft(), kb_name), layout_editor_kb(kb_name))
        return
    if data.startswith("pn_lremove:"):
        parts = data.split(":")
        await _edit(q, "کدام دکمه حذف شود؟", layout_remove_kb(parts[1], int(parts[2])))
        return
    if data.startswith("pn_ldel:"):
        parts = data.split(":")
        kb_name, i, key = parts[1], int(parts[2]), parts[3]
        draft = get_draft()
        rows = d_layout(draft, kb_name)
        if 0 <= i < len(rows) and key in rows[i]:
            rows[i] = [k for k in rows[i] if k != key]
            draft_set_rows(kb_name, rows)
        await _edit(q, layout_table_text(get_draft(), kb_name), layout_editor_kb(kb_name))
        return
    if data.startswith("pn_lreset:"):
        kb_name = data.split(":")[1]
        draft = get_draft() or {"texts": {}, "styles": {}, "disabled": [], "layouts": {}}
        draft.get("layouts", {}).pop(kb_name, None)
        draft.pop("pair_sel", None)
        set_draft(draft)
        await _edit(q, layout_table_text(get_draft(), kb_name), layout_editor_kb(kb_name))
        return
    # ---------- جابه‌جایی دکمه‌ها و ردیف‌ها ----------
    if data.startswith("pn_lmv:"):
        _, kb_name, row_i_s = data.split(":")
        await _edit(q, "◀▶ داخل ردیف جابه‌جا می‌کند؛ ▲▼ دکمه را به ردیف قبل/بعد منتقل می‌کند.\n\n"
                    + layout_table_text(get_draft(), kb_name),
                    layout_move_kb(kb_name, int(row_i_s)))
        return
    if data.startswith("pn_bmv:"):
        _, kb_name, row_i_s, key, direction = data.split(":")
        if direction in ("l", "r", "u", "d"):
            layout_move_button(kb_name, int(row_i_s), key, direction)
            audit("owner", "layout_button_moved", details=f"{kb_name}:{key}:{direction}")
        await _edit(q, layout_table_text(get_draft(), kb_name),
                    layout_move_kb(kb_name, int(row_i_s)))
        return
    if data.startswith("pn_lrowmv:"):
        _, kb_name, row_i_s, direction = data.split(":")
        if direction in ("up", "down"):
            layout_move_row(kb_name, int(row_i_s), direction)
            audit("owner", "layout_row_moved", details=f"{kb_name}:row{row_i_s}:{direction}")
        await _edit(q, layout_table_text(get_draft(), kb_name), layout_editor_kb(kb_name))
        return
    if data.startswith("pn_breset:"):
        key = data.split(":")[1]
        draft_reset_button(key)
        await _edit(q, btn_detail_text(key), btn_detail_kb(key))
        return
    if data == "pn_breset_all_go":
        clear_draft()
        reset_style(None)
        audit("owner", "buttons_reset_all")
        await _edit(q, btn_manager_text(), btn_manager_kb())
        return
    if data == "pn_bprev":
        draft = get_draft()
        await send_text(bot, tg, btn_preview_text())
        await send_text(bot, tg, "پیش‌نمایش منوی اصلی:", build_preview_reply_kb(draft, "main_menu"))
        await send_text(bot, tg, "پیش‌نمایش کیبورد مکالمه:", build_preview_reply_kb(draft, "conv"))
        await _edit(q, "آیا ذخیره می‌کنید؟ (پیش‌نمایش‌ها در دو پیام قبلی ارسال شد)", btn_preview_confirm_kb())
        return
    if data == "pn_bsave":
        saved = draft_apply_save()
        await sync_bot_commands(bot)
        await _edit(q,
                    f"تغییرات ذخیره شد (متن: {fa_num(saved['texts'])}، رنگ: {fa_num(saved['styles'])}، "
                    f"فعال بودن: {fa_num(saved['disabled'])}، چیدمان: {fa_num(saved['layouts'])}).\n\n"
                    "از این پس کیبوردهای جدید کاربران با چیدمان جدید ساخته می‌شوند.",
                    btn_manager_kb())
        return
    if data == "pn_bcancel":
        clear_draft()
        audit("owner", "buttons_draft_cancelled")
        await _edit(q, "تغییرات لغو شد و پیش‌نویس پاک‌سازی شد.", btn_manager_kb())
        return

    # ---------- مدیریت دستورات ----------
    if data == "pn_cmd":
        await _edit(q, cmd_manager_text(), cmd_manager_kb())
        return
    if data.startswith("pn_cv:"):
        name = data.split(":", 1)[1]
        await _edit(q, cmd_detail_text(name), cmd_detail_kb(name))
        return
    if data.startswith("pn_ce:"):
        parts = data.split(":")
        name, field = parts[1], parts[2]
        prompts = {"title": "عنوان نمایشی جدید:", "desc": "توضیحات جدید:",
                   "usage": "نحوه استفاده جدید:", "example": "نمونه استفاده جدید:"}
        set_form(tg, {"kind": "panel_cmd_edit", "data": {"name": name, "field": field}})
        await send_text(bot, tg, prompts.get(field, "مقدار جدید:"), imarkup([[("btn_cancel", "pn_cancel")]]))
        return
    if data.startswith("pn_ct:"):
        name = data.split(":", 1)[1]
        cmd = next((c for c in get_commands() if c["name"] == name), None)
        if cmd:
            set_command_enabled(name, not cmd.get("enabled", True))
            await sync_bot_commands(bot)
            audit("owner", "command_toggled", target=name)
        await _edit(q, cmd_detail_text(name), cmd_detail_kb(name))
        return
    if data.startswith("pn_cord:"):
        parts = data.split(":")
        if shift_command_order(parts[1], parts[2]):
            audit("owner", "command_reordered", target=parts[1])
        await _edit(q, cmd_detail_text(parts[1]), cmd_detail_kb(parts[1]))
        return

    # ---------- کد اختصاصی مالک ----------
    if data == "pn_ocd":
        txt, kb = owner_code_text()
        await _edit(q, txt, kb)
        return
    if data == "pn_ocd_revoke":
        await _edit(q, "⚠️ کد فعلی لغو و کد جدید تولید شود؟ کد قبلی فوراً غیرقابل استفاده می‌شود.",
                    imarkup([[("btn_confirm", "pn_ocd_go", "تأیید لغو و تولید کد جدید"),
                              ("btn_reject", "pn_ocd", "انصراف")]]))
        return
    if data == "pn_ocd_go":
        rec = revoke_owner_code()
        txt, kb = owner_code_text()
        await _edit(q, "کد قبلی لغو شد و کد جدید صادر شد:\n\n" + txt, kb)
        return
    if data == "pn_ocd_set":
        set_form(tg, {"kind": "panel_oc_set", "data": {}})
        await send_text(bot, tg,
                        "🔑 کد اختصاصی دلخواه ۹ رقمی خود را ارسال کنید "
                        "(کد فعلی فوراً لغو می‌شود؛ عدد فارسی هم پذیرفته است):",
                        imarkup([[("btn_cancel", "pn_cancel")]]))
        return

    # ---------- راهنما (کاربران و مالک) ----------
    if data == "gd_home":
        await _edit(q, guide_main_text(is_owner(tg)), guide_main_kb(is_owner(tg)))
        return
    if data == "gd_topics":
        await _edit(q, "موضوعات راهنما را انتخاب کنید:", guide_topic_kb(is_owner(tg)))
        return
    if data.startswith("gd_topic:"):
        title = data.split(":", 1)[1]
        topic = guide_topic_by_title(title)
        if not topic or (topic["access"] == "owner" and not is_owner(tg)):
            await _edit(q, "ℹ️ این موضوع فقط برای مالک قابل مشاهده است.")
            return
        await _edit(q, f"<b>{esc(topic['title'])}</b>\n\n" + topic["body"], guide_topic_view(topic))
        return
    if data.startswith("gd_cat:"):
        cat = data.split(":", 1)[1]
        txt, kb = guide_category_text(cat, is_owner(tg))
        await _edit(q, txt, kb)
        return
    if data.startswith("gd_cmd:"):
        name = data.split(":", 1)[1]
        cmd = next((c for c in get_commands() if c["name"] == name), None)
        if not cmd or (cmd.get("secret") and not is_owner(tg)):
            await _edit(q, "ℹ️ این دستور فقط برای مالک قابل مشاهده است.")
            return
        await _edit(q, guide_command_text(cmd), imarkup([[("btn_back", "gd_home")]]))
        return

    if data == "pn_logs":
        txt, kb = logs_text(0)
        await _edit(q, txt, kb)
        return
    if data.startswith("pn_lg:"):
        txt, kb = logs_text(int(data.split(":")[1]))
        await _edit(q, txt, kb)
        return
    if data.startswith("pn_mg:"):
        txt, kb = modlog_text(int(data.split(":")[1]))
        await _edit(q, txt, kb)
        return
    if data == "pn_mlogs":
        txt, kb = modlog_text(0)
        await _edit(q, txt, kb)
        return
    if data == "pn_oc" or data.startswith("pn_op:"):
        page = int(data.split(":")[1]) if ":" in data else 0
        txt, kb = owner_chats_text(page)
        await _edit(q, txt, kb)
        return
    if data.startswith("pn_ov:"):
        parts = data.split(":")
        txt, kb = owner_chat_history_text(parts[1], int(parts[2]))
        await _edit(q, txt, kb)
        return
    if data.startswith("pn_oh:"):
        parts = data.split(":")
        txt, kb = owner_chat_history_text(parts[1], int(parts[2]))
        await _edit(q, txt, kb)
        return
    if data.startswith("pn_od:"):
        parts = data.split(":")
        conv_id, page, mid = parts[1], int(parts[2]), parts[3]
        rec = next((m for m in MSGS.get(conv_id).get("messages", []) if m.get("mid") == mid), None)
        removed_n = 0
        if rec and not rec.get("removed"):
            def _m(d):
                for r in d["messages"]:
                    if r.get("mid") == mid:
                        r["removed"] = True
                        r["text"] = ""
                        r["file_id"] = None
                        break
                return d
            MSGS.mutate(conv_id, _m)
            removed_n = 1
            for dv in rec.get("delivered", {}).values():
                await try_delete(bot, int(dv.get("chat", 0)), dv.get("mid", 0))
            if str(rec.get("sender")) == str(OWNER_ID) and rec.get("src_msg_id"):
                await try_delete(bot, OWNER_ID, rec["src_msg_id"])
            audit("owner", "owner_chat_message_deleted", target=conv_id, details=mid)
        txt, kb = owner_chat_history_text(conv_id, page)
        await _edit(q, txt, kb)
        return
    if data.startswith("pn_odf:"):
        conv_id = data.split(":")[1]
        await _edit(q, f"⚠️ حذف کامل تاریخچه مکالمه «{conv_id}»؟\n\nپیام‌های مدیر از نمای طرف مقابل هم حذف می‌شوند؛ پیام‌های کاربر فقط از سرور.",
                    imarkup([[("btn_confirm", f"pn_odf_go:{conv_id}", "تأیید حذف"),
                              ("btn_reject", "pn_oc", "انصراف")]]))
        return
    if data.startswith("pn_odf_go:"):
        conv_id = data.split(":")[1]
        conv = get_conv(conv_id)
        if not conv or str(OWNER_ID) not in conv.get("participants", []):
            await _edit(q, "ℹ️ مکالمه یافت نشد.")
            return
        records = [m for m in MSGS.get(conv_id).get("messages", []) if not m.get("removed")]
        removed, tg_ok, tg_fail = await delete_owner_messages(context, records)
        audit("owner", "owner_chat_history_deleted", target=conv_id,
              details=f"removed:{removed} tg_ok:{tg_ok} tg_fail:{tg_fail}")
        await send_text(bot, tg, f"تاریخچه مکالمه حذف شد.\nپیام‌های مدیر: {fa_num(removed)} | حذف تلگرام: {fa_num(tg_ok)} موفق، {fa_num(tg_fail)} ناموفق")
        return
    if data == "pn_delall":
        await _edit(q,
                    "⚠️ <b>عملیات «حذف همه» (del all)</b>\n\nتمام پیام‌هایی که شما (مدیر اصلی) در تمام گفت‌وگوهای ناشناس ارسال کرده‌اید، "
                    "از سرور و از نمای طرف مقابل حذف می‌شود.\nپیام‌های کاربران مقابل حذف نمی‌شود.",
                    imarkup([[("btn_confirm", "pn_delall_go", "تأیید نهایی حذف همه"),
                              ("btn_reject", "pn_oc", "انصراف")]]))
        return
    if data == "pn_delall_go":
        await send_text(bot, tg, "⏳ در حال حذف مرحله‌ای پیام‌ها...")
        removed, tg_ok, tg_fail = await del_all_owner_messages(context)
        await send_text(bot, tg,
                        f"✅ عملیات «حذف همه» کامل شد.\nپیام‌های حذف‌شده از سرور: {fa_num(removed)}\n"
                        f"حذف از نمای طرف مقابل: {fa_num(tg_ok)} موفق، {fa_num(tg_fail)} ناموفق",
                        owner_panel_kb())
        return
    if data == "pn_bk":
        await _edit(q, backups_text(), backups_kb())
        return
    if data.startswith("pn_ba2:"):
        act = data.split(":")[1]
        if act == "create":
            rec = create_backup("manual")
            await send_text(bot, tg,
                            f"🟢 بکاپ جدید ساخته شد.\n🆔 {rec['bid']}\n🗓 {rec['created_tehran']}\n📦 {fa_num(rec['size'] // 1024)} کیلوبایت",
                            backups_kb())
        elif act == "get":
            hist = sorted(STORE.get("backup_history"), key=lambda b: b.get("created_utc") or "")
            last = hist[-1] if hist else None
            if not last or last.get("file_deleted"):
                await send_text(bot, tg, "ℹ️ بکاپ قابل ارسال وجود ندارد.", backups_kb())
            else:
                ok = await send_backup_file(context.bot, tg, last)
                if not ok:
                    await send_text(bot, tg, "⚠️ ارسال فایل ناموفق بود.", backups_kb())
        elif act == "list":
            txt, kb = backups_list_text(0)
            await _edit(q, txt, kb)
        elif act == "check":
            await send_text(bot, tg, backup_check_text(), backups_kb())
        elif act == "restore":
            set_form(tg, {"kind": "panel_bk_restore", "data": {}})
            await send_text(bot, tg,
                            "📤 فایل بکاپ JSON را ارسال کنید.\n\n⚠️ پیش از بازیابی، از دیتابیس فعلی بکاپ خودکار گرفته می‌شود و تأیید نهایی از شما پرسیده می‌شود.",
                            imarkup([[("btn_cancel", "pn_cancel")]]))
        return
    if data.startswith("pn_bl:"):
        txt, kb = backups_list_text(int(data.split(":")[1]))
        await _edit(q, txt, kb)
        return
    if data.startswith("pn_bf:"):
        bid = data.split(":")[1]
        rec = next((b for b in STORE.get("backup_history") if b.get("bid") == bid), None)
        if not rec or rec.get("file_deleted"):
            await q.answer("فایل یافت نشد", show_alert=True)
            return
        ok = await send_backup_file(context.bot, tg, rec)
        if not ok:
            await send_text(bot, tg, "⚠️ ارسال فایل ناموفق بود.")
        return
    if data == "pn_brs_go":
        form = user.get("form") or {}
        staged = form.get("data", {}).get("staged")
        clear_form(tg)
        if not staged or not os.path.exists(staged):
            await send_text(bot, tg, "ℹ️ فایل بازیابی یافت نشد؛ دوباره آپلود کنید.", backups_kb())
            return
        await send_text(bot, tg, "⏳ بازیابی در حال اجراست؛ ربات در حالت نگهداری قرار گرفت...")
        ok, result = perform_restore(staged)
        try:
            os.remove(staged)
        except OSError:
            pass
        if ok:
            counts = result.get("counts", {})
            lines = ["✅ <b>بازیابی با موفقیت انجام شد.</b>", ""]
            for k, v in counts.items():
                lines.append(f"• {k}: {fa_num(v)}")
            await send_text(bot, tg, "\n".join(lines), owner_panel_kb())
        else:
            await send_text(bot, tg, "⛔ " + str(result), backups_kb())
        return
    if data == "pn_brs_no":
        form = user.get("form") or {}
        staged = form.get("data", {}).get("staged")
        clear_form(tg)
        if staged and os.path.exists(staged):
            try:
                os.remove(staged)
            except OSError:
                pass
        await send_text(bot, tg, "ℹ️ بازیابی لغو شد و فایل موقت پاک‌سازی شد.", backups_kb())
        return
    await _edit(q, "ℹ️ دستور نامشخص.")
# ============================================================
# 28) راهنمای هوشمند و دستورات + کد اختصاصی مالک
# ============================================================

GUIDE_CATEGORIES_ORDER = ["general", "profile", "chat", "security", "owner", "usermgmt", "system"]


def guide_main_text(is_owner: bool) -> str:
    return (
        "📖 <b>دستورات</b>\n\n"
        "برای جست‌وجو، عبارت مورد نظر را همین‌جا ارسال کنید (مثال: «گزارش»، «کد اختصاصی»، «ثبت‌نام»، «چت»).\n\n"
        "دسته‌های دستورات را با دکمه‌های زیر ببینید."
    )


def guide_main_kb(is_owner: bool) -> InlineKeyboardMarkup:
    cmds = get_commands()
    if not is_owner:
        cmds = [c for c in cmds if not c.get("secret") and c.get("enabled", True)]
    rows = []
    cats = []
    for c in cmds:
        if c["category"] not in cats:
            cats.append(c["category"])
    for cat in cats:
        count = sum(1 for c in cmds if c["category"] == cat)
        rows.append([("btn_next", f"gd_cat:{cat}", f"{CATEGORY_LABELS.get(cat, cat)} ({fa_num(count)})")])
    rows.append([("btn_next", "gd_topics", "موضوعات راهنما")])
    rows.append([("btn_back", "menu_home", "منوی اصلی")])
    return imarkup(rows)


def guide_category_text(cat: str, is_owner: bool):
    cmds = get_commands()
    if not is_owner:
        cmds = [c for c in cmds if not c.get("secret") and c.get("enabled", True)]
    items = [c for c in cmds if c["category"] == cat]
    if not items:
        return "ℹ️ موردی در این دسته نمایش داده نمی‌شود.", None
    lines = [f"📚 <b>{CATEGORY_LABELS.get(cat, cat)}</b>", ""]
    kb_rows = []
    for c in items:
        state = "" if c.get("enabled", True) else " (غیرفعال)"
        lines.append(f"• <code>{c['name']}</code> — {c['title']}{state}")
        kb_rows.append([InlineKeyboardButton(f"ℹ {c['name']}", callback_data=f"gd_cmd:{c['name']}")])
    kb_rows.append([ib("btn_back", "gd_home")])
    return "\n".join(lines), InlineKeyboardMarkup(kb_rows)


def guide_command_text(cmd: dict) -> str:
    state = "فعال" if cmd.get("enabled", True) else "غیرفعال"
    return (
        f"<b>دستور {cmd['name']}</b>\n\n"
        f"عنوان نمایشی: {esc(cmd.get('title') or '')}\n"
        f"کاربرد: {esc(cmd.get('desc') or '')}\n"
        f"نحوه استفاده: {esc(cmd.get('usage') or '')}\n"
        f"نمونه: <code>{esc(cmd.get('example') or '')}</code>\n"
        f"دسته: {CATEGORY_LABELS.get(cmd.get('category'), '—')}\n"
        f"سطح دسترسی: {'فقط مالک' if cmd.get('secret') else 'کاربران'}\n"
        f"وضعیت: {state}"
    )


def guide_topic_text(topic: dict) -> str:
    return esc(topic["body"]).replace("\u200c", "\u200c")


def guide_topic_kb(is_owner: bool) -> InlineKeyboardMarkup:
    rows = []
    visible = [t for t in GUIDE_TOPICS if t["access"] == "user" or is_owner]
    for t in visible[:12]:
        marker = " (فقط مالک)" if t["access"] == "owner" else ""
        rows.append([("btn_next", f"gd_topic:{t['title']}", t["title"][:32] + marker)])
    rows.append([("btn_back", "gd_home")])
    return imarkup(rows)


def guide_topic_view(topic) -> InlineKeyboardMarkup:
    return imarkup([[("btn_back", "gd_topics")]])


def guide_search_result_text(results, suggestions, query: str) -> str:
    lines = [f"🔍 نتیجه جست‌وجوی «{esc(query)}»", ""]
    kb_rows = []
    if results:
        for t in results[:4]:
            lines.append(f"• <b>{t['title']}</b>")
            lines.append(t["body"][:400])
            lines.append("")
            kb_rows.append([("btn_next", f"gd_topic:{t['title']}", t["title"][:32])])
    elif suggestions:
        lines.append("نتیجه دقیقی پیدا نشد؛ این موضوعات نزدیک‌ترین‌اند:")
        kb_rows = [[("btn_next", f"gd_topic:{t['title']}", t["title"][:32])] for t in suggestions[:3]]
    else:
        lines.append("موردی پیدا نشد. از دکمه «موضوعات راهنما» فهرست کامل را ببینید.")
    kb_rows.append([("btn_back", "gd_home")])
    return "\n".join(lines), imarkup(kb_rows)

# ---------- پنل کد اختصاصی مالک ----------

def owner_code_text() -> str:
    oc = get_owner_code_record()
    lines = [
        "🔑 <b>کد اختصاصی مالک</b>", "",
        f"کد فعلی: <code>{oc.get('code') or '—'}</code>",
        f"زمان ایجاد: {jalali(parse_iso(oc['created']))}",
        f"تعداد کدهای لغوشده: {fa_num(len(oc.get('revoked', [])))}",
        "",
        "کاربران با ارسال این کد می‌توانند درخواست چت دوستانه با شما ثبت کنند.",
        "با لغو کد، کد قبلی فوراً غیرقابل استفاده می‌شود و کد جدید صادر می‌گردد.",
        "با «تغییر دستی کد» می‌توانید کد دلخواه ۹ رقمی خود را ثبت کنید.",
    ]
    kb = imarkup([
        [("btn_next", "pn_ocd_set", "تغییر دستی کد", "primary"),
         ("btn_reject", "pn_ocd_revoke", "لغو و تولید کد جدید", "danger")],
        [("btn_back", "pn_adv")],
    ])
    return "\n".join(lines), kb
# ============================================================
# 28.5) پنل مالک — سیستم محافظت، اعتراض‌ها، وضعیت امنیتی کاربر،
#       راهنمای کامل مدیریت ربات (نسخه ۲.۱.۰)
# ============================================================

PROT_LEVEL_FA = {
    1: "سطح ۱ — توهین جنسیتی",
    2: "سطح ۲ — توهین شدید جنسیتی و فحاشی رکیک",
    3: "سطح ۳ — آزار جنسی کلامی (تخلف بسیار شدید)",
}

# نمونه‌های آموزشی سانسورشده برای راهنمای پنل (بدون عبارت صریح)
PROT_LEVEL_EXAMPLES = {
    1: "تحقیر یک نفر به دلیل جنسیت؛ نسبت دادن صفت تحقیرآمیز جنسیتی؛ توهین گروهی به دختران یا پسران.",
    2: "ترکیب توهین جنسیتی با فحاشی شدید؛ تکرار توهین‌های جنسیتی در یک گفت‌وگو.",
    3: "درخواست جنسی صریح از مخاطب؛ درخواست تصویر/ویدئوی مستهجن؛ ترکیب آزار جنسی با توهین و فحاشی.",
}

APPEAL_MODE_FA = {"manual": "بررسی دستی توسط مالک",
                  "auto_approve": "پذیرش خودکار (لغو خودکار مجازات)",
                  "auto_reject": "رد خودکار"}

OWNER_GUIDE_CATS = ("general", "chat", "owner", "security")
OWNER_GUIDE_CAT_FA = {
    "general": "دستورات عمومی",
    "chat": "دستورات چت",
    "owner": "دستورات مالک",
    "security": "دستورات و تنظیمات امنیتی",
}


def _cmd_enabled_by_name(name: str) -> bool:
    cmd = next((c for c in get_commands() if c["name"] == name), None)
    return bool(cmd and cmd.get("enabled", True))


def build_owner_guide() -> list:
    """راهنمای کامل مدیریت — فقط دستورات واقعی نسخه فعلی ربات.
    خروجی: [{"cat", "name", "desc", "example", "result", "access", "secret",
              "active": bool}]"""
    prot = get_protection()
    s = STORE.get("settings")
    return [
        # ---------- دستورات عمومی ----------
        {"cat": "general", "name": "/start — شروع ربات",
         "desc": "نمایش منوی اصلی، ادامه ثبت‌نام نیمه‌کاره و دریافت اعلان‌های محدودیت.",
         "example": "/start", "result": "منوی اصلی با دکمه‌های قابل تنظیم نمایش داده می‌شود.",
         "access": "همه کاربران", "secret": False, "active": True},
        {"cat": "general", "name": "اطلاعات من (/info)",
         "desc": "مشاهده اطلاعات حساب: کد اختصاصی ۹ رقمی، مشخصات، فیلترها و آمار.",
         "example": "/info یا دکمه «اطلاعات من»",
         "result": "صفحه اطلاعات حساب با دکمه ویرایش مشخصات باز می‌شود.",
         "access": "همه کاربران ثبت‌نام‌شده", "secret": False,
         "active": _cmd_enabled_by_name("/info")},
        {"cat": "general", "name": "ویرایش نام و مشخصات",
         "desc": "تغییر نام، جنسیت، سن و استان از صفحه «اطلاعات من»؛ هر ۶ ماه یک بار.",
         "example": "اطلاعات من ← تغییر مشخصات ← نام ← «علی»",
         "result": "نام حساب فوراً به‌روز می‌شود و تاریخ ویرایش بعدی ثبت می‌شود.",
         "access": "همه کاربران ثبت‌نام‌شده", "secret": False,
         "active": True},
        {"cat": "general", "name": "مشاهده کد اختصاصی",
         "desc": "کد اختصاصی دائمی ۹ رقمی در صفحه اطلاعات حساب نمایش داده می‌شود.",
         "example": "/info → «شناسه اختصاصی»",
         "result": "کد ۹ رقمی برای چت دوستانه در دسترس است.",
         "access": "همه کاربران", "secret": False, "active": True},
        {"cat": "general", "name": "راهنمای ربات (/guide)",
         "desc": "راهنمای جست‌وجویی و فهرست موضوعات؛ موضوعات مالک فقط برای مالک نمایش داده می‌شود.",
         "example": "/guide یا دکمه «دستورات»",
         "result": "فهرست موضوعات + کادر جست‌وجو باز می‌شود.",
         "access": "همه کاربران", "secret": False,
         "active": _cmd_enabled_by_name("/guide")},
        # ---------- دستورات چت ----------
        {"cat": "chat", "name": "شروع چت ناشناس",
         "desc": "ورود به صف انتظار و اتصال خودکار به مخاطب سازگار.",
         "example": "دکمه «شروع چت ناشناس»",
         "result": "ورود به صف و اتصال پس از پیدا شدن مخاطب.",
         "access": "همه کاربران ثبت‌نام‌شده", "secret": False,
         "active": bool(s.get("bot_enabled", True)) and not bool(s.get("maintenance"))},
        {"cat": "chat", "name": "چت بعدی",
         "desc": "پایان مکالمه فعلی و جست‌وجوی مخاطب جدید (تحت کنترل سکوت/محدودیت فوق‌العاده).",
         "example": "دکمه «چت بعدی» در حین چت",
         "result": "چت فعلی بسته و صف جست‌وجوی جدید آغاز می‌شود؛ با سکوت فعال فقط پیام باقی‌مانده نمایش داده می‌شود.",
         "access": "کاربر در حین چت", "secret": False, "active": True},
        {"cat": "chat", "name": "خروج از چت",
         "desc": "پایان مکالمه با «پایان مکالمه» یا قطع دائمی با «بلاک».",
         "example": "دکمه «پایان مکالمه»",
         "result": "مکالمه بسته و هر دو طرف آزاد می‌شوند.",
         "access": "کاربر در حین چت", "secret": False, "active": True},
        {"cat": "chat", "name": "گزارش کاربر",
         "desc": "بستن فوری چت و ثبت گزارش ناشناس؛ هر مکالمه یک گزارش.",
         "example": "نوشتن «گزارش» در حین چت یا /report",
         "result": "مکالمه بسته، گزارش با وضعیت «جدید» ثبت و دلیل پرسیده می‌شود.",
         "access": "کاربر در حین چت", "secret": False, "active": True},
        {"cat": "chat", "name": "استفاده از پشتیبانی",
         "desc": "گفت‌وگوی مستقیم با مدیریت؛ هنگام مجازات فعال سامانه محافظت مسدود است (مسیر مستقل: اعتراض).",
         "example": "نوشتن «پشتیبانی» یا /support",
         "result": "تیکت پشتیبانی باز و پیام‌ها برای مدیریت ارسال می‌شود.",
         "access": "همه کاربران", "secret": False, "active": True},
        {"cat": "chat", "name": "چت دوستانه با کد",
         "desc": "ارسال کد اختصاصی ۹ رقمی دوست؛ پس از پذیرش او، مکالمه دوستانه ساخته می‌شود.",
         "example": "ارسال «978163038»",
         "result": "درخواست برای دوست ارسال و پس از پذیرش، اتصال برقرار می‌شود.",
         "access": "همه کاربران ثبت‌نام‌شده", "secret": False, "active": True},
        {"cat": "chat", "name": "ثبت اعتراض (مسیر مستقل)",
         "desc": "اعتراض به مجازات سامانه محافظت؛ فقط یک بار برای هر پرونده، با توضیح + تصویر اختیاری.",
         "example": "دکمه سبز «ثبت اعتراض» روی پیام مجازات",
         "result": "اعتراض به بخش اعتراض‌های پنل مالک می‌رود؛ رسید نمایش داده می‌شود؛ رفع خودکار مجازات نیست.",
         "access": "کاربر دارای مجازات قابل اعتراض", "secret": False,
         "active": bool(prot.get("enabled", True))},
        # ---------- دستورات مالک ----------
        {"cat": "owner", "name": "دستورات متنی ساده (سکوت، بن، اخطار)",
         "desc": "دستورات مدیریتی متنی در سه زمینه: «ارسال پیام به کاربر» در پرونده کاربر، «پاسخ به تیکت» پشتیبانی "
                 "و «داخل مکالمه» روی مخاطب فعلی مالک (بدون منتقل شدن به او). "
                 "«سکوت{دقیقه}» و «بن{دقیقه}» (عدد فارسی/انگلیسی، حداکثر ۵ رقم)، «اخطار»، «حذف سکوت»، «حذف بن» "
                 "(فاصله بین دو کلمه الزامی) و «گزارش» (فهرست گزارش‌های همان کاربر).",
         "example": "داخل مکالمه ← «بن60» یا پرونده کاربر ← ارسال پیام ← «سکوت 30»",
         "result": "دستور مستقیم اجرا می‌شود، هرگز به‌عنوان پیام عادی ارسال نمی‌گردد و رسید نتیجه برای مالک می‌آید؛ "
                   "روی حساب خود مالک مجاز نیست.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "مجازات اختصاصی با دونقطه",
         "desc": "قالب «نوع:عدد[ساعت]» در وضعیت امنیتی کاربر: «سکوت:۳۰» (دقیقه)، «بن:۲۴ساعت» یا «بن:۱۲۰» (دقیقه)، "
                 "«فوق‌العاده:۱۲۰» (دقیقه) و «دختر:۱۶۸» (ساعت؛ ۰ = دائمی).",
         "example": "وضعیت امنیتی ← مجازات اختصاصی ← «بن:۲۴ساعت»",
         "result": "مجازات با واحد درست اعمال و رویداد آن ثبت می‌شود.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "/panel — ورود به پنل مدیریت",
         "desc": "باز کردن پنل کامل مدیریت ربات.",
         "example": "/panel", "result": "منوی پنل مدیریت نمایش داده می‌شود.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "داشبورد",
         "desc": "آمار زنده دیتابیس: کاربران، مکالمات فعال، گزارش‌های باز و وضعیت ربات.",
         "example": "پنل ← داشبورد", "result": "آمار واقعی با تاریخ شمسی نمایش داده می‌شود.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "مشاهده اطلاعات کاربران",
         "desc": "فهرست کاربران با صفحه‌بندی و ورود به صفحه هر کاربر.",
         "example": "پنل ← مدیریت کاربران ← انتخاب کاربر",
         "result": "مشخصات کامل، تاریخچه ارتباطات و وضعیت امنیتی نمایش داده می‌شود.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "جست‌وجوی کاربر",
         "desc": "جست‌وجو با شناسه اختصاصی، شناسه تلگرام یا نام.",
         "example": "پنل ← جست‌وجوی کاربر ← «978163038»",
         "result": "پرونده کاربر باز می‌شود.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "مدیریت وضعیت حساب",
         "desc": "تغییر نام/جنسیت/سن/استان کاربر از پنل.",
         "example": "پرونده کاربر ← تغییر مشخصات ← سن ← «۲۲»",
         "result": "مقدار جدید ذخیره و در رویدادهای مدیریتی ثبت می‌شود.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "بن موقت و دائم",
         "desc": "مسدودسازی کامل حساب؛ دستور متنی یا دکمه‌های پرونده کاربر.",
         "example": "در زمینه پیام به کاربر: «بن۶۰» یا دکمه «بن دائم»",
         "result": "کاربر از همه امکانات چت مسدود و زمان پایان به او اعلام می‌شود.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "رفع بن",
         "desc": "برداشتن مسدودی موقت یا دائم.",
         "example": "«حذف بن» یا دکمه «رفع بن»",
         "result": "بن فعال خنثی و کاربر مطلع می‌شود.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "سکوت کاربر",
         "desc": "محدودیت کامل شروع گفت‌وگوی جدید: بدون شروع چت، چت بعدی و صف انتظار؛ بررسی سمت سرور و ماندگار در /data.",
         "example": "«سکوت۳۰» یا دکمه‌های سکوت در وضعیت امنیتی",
         "result": "سکوت تا پایان زمان اعمال می‌شود؛ زمان باقی‌مانده به کاربر نمایش داده می‌شود.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "رفع سکوت و تمدید/کاهش",
         "desc": "برداشتن سکوت یا تغییر زمان آن از صفحه «وضعیت امنیتی و مجازات‌ها».",
         "example": "وضعیت امنیتی ← تمدید سکوت ← «۱۵»",
         "result": "زمان سکوت به‌روز یا حذف می‌شود؛ رویداد ثبت می‌شود.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "محدودیت چت (فوق‌العاده)",
         "desc": "۱ چت جدید در هر بازه ۶۰ دقیقه‌ای؛ مستقل از سکوت و بن؛ قابل مشاهده، تمدید، کاهش و لغو.",
         "example": "وضعیت امنیتی ← لغو محدودیت فوق‌العاده",
         "result": "شروع چت جدید تا پایان بازه کنترل می‌شود.",
         "access": "فقط مالک", "secret": True,
         "active": bool(prot.get("enabled", True))},
        {"cat": "owner", "name": "مدیریت اخطارها",
         "desc": "ثبت اخطار («اخطار» یا دکمه) و حذف اخطار از وضعیت امنیتی کاربر.",
         "example": "«اخطار» در زمینه پیام به کاربر",
         "result": "اخطار ثبت و شمارنده کاربر افزایش می‌یابد؛ حذف از وضعیت امنیتی ممکن است.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "مدیریت محدودیت جنسیتی",
         "desc": "منع چت با دختران: فعال/غیرفعال‌سازی و تغییر مدت (تا دائمی) برای هر کاربر.",
         "example": "وضعیت امنیتی ← منع چت با دختران ← «۱۶۸» ساعت",
         "result": "اتصال کاربر به دختران تا پایان مدت (یا دائمی) بسته می‌شود؛ هر زمان قابل لغو.",
         "access": "فقط مالک", "secret": True,
         "active": bool(prot.get("girl_block_enabled", True))},
        {"cat": "owner", "name": "مشاهده گزارش‌ها",
         "desc": "فهرست گزارش‌ها با وضعیت، یادداشت و مشاهده پیام‌های مرتبط با ثبت دسترسی.",
         "example": "پنل ← گزارش‌ها ← انتخاب گزارش",
         "result": "جزئیات گزارش و تاریخچه رسیدگی نمایش داده می‌شود.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "بررسی اعتراض‌ها",
         "desc": "فهرست اعتراض‌های سامانه محافظت: تأیید (لغو خودکار مجازات)، رد یا نگه‌داشتن.",
         "example": "پنل ← اعتراض‌ها ← پرونده ← تأیید",
         "result": "در صورت تأیید، همه مجازات‌های همان پرونده خودکار لغو می‌شود.",
         "access": "فقط مالک", "secret": True,
         "active": bool(prot.get("enabled", True))},
        {"cat": "owner", "name": "مدیریت کد اختصاصی مالک",
         "desc": "مشاهده، لغو و تولید کد اختصاصی مالک در تنظیمات پیشرفته.",
         "example": "پنل ← تنظیمات پیشرفته ← کد اختصاصی مالک",
         "result": "کد قبلی فوراً باطل و کد جدید ساخته می‌شود.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "مدیریت تنظیمات دکمه‌ها",
         "desc": "تغییر متن، رنگ، فعال بودن و بازنشانی هر دکمه.",
         "example": "پنل ← تنظیمات پیشرفته ← مدیریت دکمه‌ها",
         "result": "تغییرات پس از پیش‌نمایش و ذخیره، روی کیبورد کاربران اعمال می‌شود.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "مدیریت رنگ و چیدمان",
         "desc": "ویرایشگر ردیف‌ها: افزودن/حذف، ادغام، تقسیم، انتقال دو دکمه به یک ردیف، جابه‌جایی چهارجهته و جابه‌جایی ردیف.",
         "example": "پنل ← تنظیمات پیشرفته ← چیدمان منوی اصلی ← «دو دکمه به این ردیف»",
         "result": "چیدمان جدید پس از ذخیره در /data ماندگار می‌شود؛ Callback دکمه‌ها دست‌نخورده می‌ماند.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "مدیریت نسخه‌های پشتیبان",
         "desc": "ایجاد دستی، دریافت فایل، بررسی سلامت SHA-256، آپلود و بازیابی امن؛ بکاپ خودکار از نسخه ۲.۳.۰ پیش‌فرض خاموش است (برای صرفه‌جویی در حجم) و از تنظیمات سیستمی قابل روشن‌کردن است.",
         "example": "پنل ← مدیریت بکاپ ← ایجاد بکاپ",
         "result": "بکاپ کامل فایل‌های /data ساخته و تاریخچه ثبت می‌شود.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "ارسال همگانی پیشرفته (زمان‌بندی، سنجاق، واکنش)",
         "desc": "اطلاع‌رسانی به همه کاربران با سه قابلیت: «⏰ ارسال زمان‌بندی‌شده» با قالب «30/6/5» "
                 "(دقیقه تأخیر/ساعت تکرار/دفعات؛ مثل هر ۶ ساعت یک‌بار)، سنجاق پیام 📌 در چت هر کاربر و "
                 "واکنش رسمی تلگرام 👍 روی پیام. فرمت‌های Bold/Italic تلگرام حفظ می‌شوند. "
                 "فهرست و لغو ارسال‌های زمان‌بندی‌شده: پنل ← ارسال‌های زمان‌بندی‌شده.",
         "example": "پنل ← اطلاع‌رسانی ← متن ← «⏰ ارسال زمان‌بندی‌شده» ← «30/6»",
         "result": "پیام در زمان مقرر و در صورت تکرار، دوره‌ای ارسال می‌شود؛ مقاوم به Restart.",
         "access": "فقط مالک", "secret": True, "active": True},
        {"cat": "owner", "name": "گزارش فعالیت‌های مدیریتی",
         "desc": "رویدادنگاری همه عملیات مدیریتی (بن، سکوت، اعتراض، مجازات‌ها و...).",
         "example": "پنل ← گزارش عملیات",
         "result": "لاگ مدیریتی با تاریخ و عامل عملیات نمایش داده می‌شود.",
         "access": "فقط مالک", "secret": True, "active": True},
        # ---------- دستورات و تنظیمات امنیتی ----------
        {"cat": "security", "name": "فیلتر فحاشی",
         "desc": "تشخیص محتوای توهین‌آمیز فارسی/انگلیسی با whitelist، ساعات و روزهای فعال و اقدام (اخطار/سکوت/بن).",
         "example": "پنل ← ضد فحاشی ← افزودن واژه",
         "result": "پیام متخلف ارسال نمی‌شود و اخطار ثبت می‌شود.",
         "access": "تنظیم: فقط مالک — اجرا: همه چت‌ها", "secret": True,
         "active": bool(s.get("profanity_enabled", True))},
        {"cat": "security", "name": "مقابله با توهین جنسی و جنسیتی",
         "desc": "سیستم محافظت هوشمند کاربران در چت‌های دختر-پسر؛ تشخیص مفهومی با کاهش تشخیص اشتباه (نقل‌قول/توضیح/whitelist).",
         "example": "پنل ← سیستم محافظت ← روشن/خاموش",
         "result": "پیام متخلف ارسال نمی‌شود، چت بسته و مجازات سطح مربوطه اعمال می‌شود.",
         "access": "تنظیم: فقط مالک — اجرا: چت دختر-پسر", "secret": True,
         "active": bool(prot.get("enabled", True))},
        {"cat": "security", "name": "سطح‌بندی تخلفات",
         "desc": "سه سطح: توهین جنسیتی / توهین شدید + فحاشی رکیک / آزار جنسی کلامی؛ مجازات‌های پیش‌فرض ۱۷، ۴۳ و ۵۰ دقیقه سکوت.",
         "example": f"سطح ۱: {PROT_LEVEL_EXAMPLES[1]}",
         "result": "سطح تخلف، مدت سکوت و ثبت سابقه را تعیین می‌کند.",
         "access": "تنظیم: فقط مالک", "secret": True,
         "active": bool(prot.get("enabled", True))},
        {"cat": "security", "name": "محدودیت‌های زمانی",
         "desc": "ساعات و روزهای فعالیت فیلتر فحاشی + زمان‌دار بودن همه مجازات‌ها (سکوت/بن/فوق‌العاده).",
         "example": "پنل ← ضد فحاشی ← ساعات فعالیت ← «22:00-06:00»",
         "result": "فیلتر فقط در بازه تعیین‌شده فعال است.",
         "access": "تنظیم: فقط مالک", "secret": True,
         "active": bool(s.get("profanity_hours"))},
        {"cat": "security", "name": "تنظیم مدت مجازات",
         "desc": "مدت سکوت هر سطح محافظت، مدت بن مراحل تکرار، محدودیت فوق‌العاده هر مرحله و مجازات عمومی ضد فحاشی.",
         "example": "پنل ← سیستم محافظت ← سکوت سطح ۲ ← «۴۳»",
         "result": "مجازات‌های بعدی با مدت جدید اعمال می‌شود.",
         "access": "فقط مالک", "secret": True,
         "active": bool(prot.get("enabled", True))},
        {"cat": "security", "name": "تنظیم سیاست نگهداری پیام‌ها",
         "desc": "مدت نگهداری پیام‌های کاربران عادی (پیش‌فرض ۷۲ ساعت) و حذف خودکار؛ مکالمات دارای گزارش باز مستثنا هستند.",
         "example": "پنل ← تنظیمات سیستمی ← نگهداری پیام ← «۷۲»",
         "result": "پیام‌های قدیمی‌تر از سیاست، خودکار و دائمی حذف می‌شوند.",
         "access": "فقط مالک", "secret": True, "active": True},
    ]


def owner_guide_text(cat: str) -> str:
    prot = get_protection()
    items = [e for e in build_owner_guide() if e["cat"] == cat]
    lines = [f"📖 <b>{OWNER_GUIDE_CAT_FA[cat]}</b>", ""]
    act_n = sum(1 for e in items if e["active"])
    lines.append(f"فعال: {fa_num(act_n)} از {fa_num(len(items))} — وضعیت از تنظیمات زنده ربات خوانده می‌شود.")
    lines.append("")
    for e in items:
        state = "✅ فعال" if e["active"] else "⛔ غیرفعال"
        secret = " | 🔒 محرمانه (فقط مالک)" if e.get("secret") else ""
        lines.append(f"• <b>{e['name']}</b> — {state}{secret}")
        lines.append(f"  {e['desc']}")
        lines.append(f"  ▸ مثال: {e['example']}")
        lines.append(f"  ▸ نتیجه: {e['result']}")
        lines.append(f"  ▸ دسترسی: {e['access']}")
        lines.append("")
    lines.append("ℹ️ دستوری که در این فهرست نیست، در نسخه فعلی ربات وجود ندارد و فعال معرفی نشده است.")
    if cat == "security":
        lines.append("")
        lines.append(f"نمونه‌های آموزشی سطح‌ها (سانسورشده):")
        for lv in (1, 2, 3):
            if prot.get("level_enabled", {}).get(str(lv), True):
                lines.append(f"• {PROT_LEVEL_FA[lv]}: {PROT_LEVEL_EXAMPLES[lv]}")
            else:
                lines.append(f"• {PROT_LEVEL_FA[lv]}: ⛔ این سطح خاموش است")
    return "\n".join(lines)


def owner_guide_kb() -> InlineKeyboardMarkup:
    rows = [[("btn_next", f"ogc:{c}", OWNER_GUIDE_CAT_FA[c])]
            for c in OWNER_GUIDE_CATS]
    rows.append([("btn_back", "pn")])
    return imarkup(rows)


def protection_view_text() -> str:
    prot = get_protection()
    mm = prot.get("mute_minutes", {})
    sb = prot.get("stage_ban_hours", {})
    ss = prot.get("stage_super_minutes", {})
    thr = prot.get("escalation_threshold", 1)
    g4 = prot.get("girl_block_stage4_hours", 168)
    g5 = prot.get("girl_block_stage5_hours", 0)
    lvl_fa = {n: ("✅" if prot.get("level_enabled", {}).get(str(n), True) else "⛔") for n in (1, 2, 3)}
    lines = [
        "🛡 <b>تنظیمات سیستم محافظت هوشمند کاربران</b>", "",
        f"وضعیت کلی: {'🟢 روشن' if prot.get('enabled', True) else '🔴 خاموش'}",
        f"سطح‌ها: {lvl_fa[1]} سطح ۱ | {lvl_fa[2]} سطح ۲ | {lvl_fa[3]} سطح ۳",
        "",
        f"🤫 سکوت پیش‌فرض: سطح ۱: {fa_num(mm.get('1', 17))} دقیقه | سطح ۲: {fa_num(mm.get('2', 43))} دقیقه | سطح ۳: {fa_num(mm.get('3', 50))} دقیقه",
        "",
        "<b>مجازات مرحله‌ای تکرار سطح ۳:</b>",
    ]
    for st in range(1, 6):
        ban_h = sb.get(str(st), 6 * st)
        sup_m = ss.get(str(st), 5)
        sup_s = f"{fa_num(sup_m // 60)} ساعت" if sup_m >= 60 else f"{fa_num(sup_m)} دقیقه"
        lines.append(f"• مرحله {fa_num(st)}: بن {fa_num(ban_h)} ساعت + فوق‌العاده {sup_s}")
    lines.append(f"• مرحله ۴+: منع چت با دختران: {fa_num(g4) if g4 else 'دائمی'} ساعت (مرحله ۴) / {'دائمی' if not g5 else fa_num(g5) + ' ساعت'} (مرحله ۵)")
    lines.append("")
    lines.append(f"🔢 ارتقای مرحله: هر {fa_num(thr)} تخلف تأییدشده سطح ۳")
    lines.append(f"🚻 منع چت با دختران: {'🟢 فعال' if prot.get('girl_block_enabled', True) else '🔴 غیرفعال'}")
    lines.append(f"⚖ نحوه بررسی اعتراض: {APPEAL_MODE_FA.get(prot.get('appeal_mode', 'manual'), '—')}")
    lines.append("")
    lines.append(f"⏱ محدودیت فوق‌العاده: در هر بازه {fa_num(WINDOW_MINUTES_SUPER)} دقیقه‌ای فقط یک چت جدید")
    return "\n".join(lines)


def protection_view_kb() -> InlineKeyboardMarkup:
    prot = get_protection()
    on_off = "خاموش کردن" if prot.get("enabled", True) else "روشن کردن"
    rows = [
        [("btn_next", "pn_prot_tgl", on_off)],
    ]
    for n in (1, 2, 3):
        mark = "✅" if prot.get("level_enabled", {}).get(str(n), True) else "⛔"
        rows.append([("btn_next", f"pn_prot_lvl:{n}", f"{mark} سطح {fa_num(n)}"),
                     ("btn_next", f"pn_prot_mute:{n}", f"سکوت سطح {fa_num(n)}")])
    for st in range(1, 6):
        rows.append([("btn_next", f"pn_prot_stage:{st}", f"بن مرحله {fa_num(st)}"),
                     ("btn_next", f"pn_prot_sup:{st}", f"فوق‌العاده مرحله {fa_num(st)}")])
    girl = "غیرفعال کردن منع دختران" if prot.get("girl_block_enabled", True) else "فعال کردن منع دختران"
    rows.append([("btn_next", "pn_prot_girl", girl)])
    rows.append([("btn_next", "pn_prot_girlh4", "مدت منع مرحله ۴"),
                 ("btn_next", "pn_prot_girlh5", "مدت منع مرحله ۵")])
    rows.append([("btn_next", "pn_prot_thr", "تعداد تخلف برای ارتقا"),
                 ("btn_next", "pn_prot_apl", "نحوه بررسی اعتراض")])
    rows.append([("btn_next", "pn_prot_reset", "بازگردانی پیش‌فرض‌ها")])
    rows.append([("btn_back", "pn")])
    return imarkup(rows)


def appeals_list_text(page: int):
    items = [v for v in STORE.get("violations") if isinstance(v.get("appeal"), dict)]
    items.sort(key=lambda v: v["appeal"].get("created") or "", reverse=True)
    chunk, page, pages = pager(items, page, 8)
    st_fa = {"pending": "🟡 در انتظار", "approved": "✅ تأییدشده",
             "rejected": "⛔ ردشده", "hold": "🔍 نگه‌داشته"}
    lines = [f"⚖ <b>اعتراض‌های سامانه محافظت</b> ({fa_num(len(items))})", ""]
    kb_rows = []
    for v in chunk:
        lines.append(f"• <code>{v['case']}</code> | {st_fa.get(v['appeal'].get('status'), '?')} | سطح {fa_num(v.get('level', 0))} | {jalali(parse_iso(v['created']))}")
        kb_rows.append([InlineKeyboardButton(f"⚖ {v['case']}", callback_data=f"pn_apv:{v['vid']}")])
    if not items:
        lines.append("• موردی ثبت نشده است.")
    kb_rows.extend(nav_rows("pn_aplp", page, pages, back_cd="pn"))
    return "\n".join(lines), InlineKeyboardMarkup(kb_rows)


def appeal_view_text(vid: str):
    v = next((x for x in STORE.get("violations") if x.get("vid") == vid), None)
    if not v:
        return "ℹ️ پرونده یافت نشد.", None
    ap = v.get("appeal") or {}
    uid = int(v["uid"])
    u = get_user(uid)
    st_fa = {"pending": "🟡 در انتظار رسیدگی", "approved": "✅ تأییدشده",
             "rejected": "⛔ ردشده", "hold": "🔍 نگه‌داشته برای بررسی بیشتر"}
    pun = []
    if v.get("mute_minutes"):
        pun.append(f"سکوت {fa_num(v['mute_minutes'])} دقیقه")
    if v.get("ban_hours"):
        pun.append(f"بن {fa_num(v['ban_hours'])} ساعت")
    if v.get("stage"):
        pun.append(f"مرحله {fa_num(v['stage'])} مجازات مرحله‌ای")
    txt = (
        f"⚖ <b>اعتراض پرونده {v['case']}</b>\n\n"
        f"👤 شناسه کاربر: <code>{u.get('internal') or '—'}</code> (تلگرام: <code>{uid}</code>)\n"
        f"🛡 نوع مجازات: {'؛ '.join(pun) or '—'} (سطح {fa_num(v.get('level', 0))})\n"
        f"⏱ زمان اعمال مجازات: {jalali(parse_iso(v['created']))}\n"
        f"📅 تاریخ ارسال اعتراض: {jalali(parse_iso(ap.get('created'))) if ap.get('created') else '—'}\n"
        f"📌 وضعیت رسیدگی: {st_fa.get(ap.get('status'), '—')}\n"
        f"🖼 تصویر پیوست: {'دارد' if ap.get('photo_id') else 'ندارد'}\n\n"
        f"📝 <b>توضیحات کاربر:</b>\n{esc(ap.get('text') or '—')}\n"
    )
    if ap.get("note"):
        txt += f"\n🗒 یادداشت مدیریت: {esc(ap['note'])}\n"
    if v.get("revoked"):
        txt += f"\n♻️ این پرونده لغو شده است ({v.get('revoke_reason') or '—'})\n"
    kb_rows = []
    if ap.get("photo_id"):
        kb_rows.append([InlineKeyboardButton("🖼 مشاهده تصویر پیوست", callback_data=f"pn_apimg:{vid}")])
    if ap.get("status") == "pending":
        kb_rows.append([("btn_confirm", f"pn_apdec:{vid}:approved", "تأیید و لغو مجازات"),
                        ("btn_reject", f"pn_apdec:{vid}:rejected", "رد اعتراض")])
        kb_rows.append([("btn_next", f"pn_apdec:{vid}:hold", "نگه‌داشتن برای بررسی بیشتر")])
    kb_rows.append([("btn_back", "pn_apls")])
    return txt, imarkup(kb_rows)


def security_view_text(uid: int):
    u = get_user(uid)
    if not u:
        return "ℹ️ کاربر یافت نشد.", None
    viol = [v for v in STORE.get("violations") if v.get("uid") == str(uid)]
    confirmed = [v for v in viol if not v.get("revoked")]
    last = confirmed[-1] if confirmed else None
    mute_rem = mute_remaining_minutes(u)
    mute_hist = [b for b in STORE.get("bans") if b.get("uid") == str(uid) and b.get("type") == "mute"]
    ban_hist = [b for b in STORE.get("bans") if b.get("uid") == str(uid) and b.get("type") in ("temp", "perm")]
    warn_hist = [w for w in STORE.get("warnings")
                 if w.get("uid") == str(uid) and not w.get("deleted")]
    sup_active = super_limit_active(u)
    sup_rem = super_start_block_minutes(u)
    gb = girl_block_state(u)
    appeals = [v for v in viol if isinstance(v.get("appeal"), dict)]
    ban_state = "ندارد"
    if u.get("ban"):
        if u["ban"].get("perm"):
            ban_state = "⛔ دائمی"
        else:
            try:
                ban_state = "موقت تا " + jalali(parse_iso(u["ban"]["until"]))
            except Exception:
                ban_state = "موقت"
    lines = [
        f"🛡 <b>وضعیت امنیتی و مجازات‌ها — کاربر {u.get('name') or uid}</b>", "",
        f"🆔 شناسه: <code>{u.get('internal') or '—'}</code> | تلگرام: <code>{uid}</code>",
        f"✅ تخلفات تأییدشده: {fa_num(len(confirmed))} (کل ثبت‌شده: {fa_num(len(viol))})",
    ]
    if last:
        lines.append(f"⭕ آخرین تخلف: سطح {fa_num(last.get('level', 0))} | {jalali(parse_iso(last['created']))}")
    else:
        lines.append("⭕ آخرین تخلف: —")
    lines.append(f"🤫 سکوت: {'فعال — ' + fa_num(mute_rem) + ' دقیقه باقی‌مانده' if mute_rem else 'ندارد'} | سابقه سکوت: {fa_num(len(mute_hist))} مورد")
    lines.append(f"⛔ بن: {ban_state} | سابقه بن: {fa_num(len(ban_hist))} مورد")
    lines.append(f"⚠️ اخطارها: {fa_num(u.get('warnings', 0))} (رکوردها: {fa_num(len(warn_hist))})")
    if sup_active:
        sup_until = jalali(parse_iso(u.get("super_until"))) if u.get("super_until") else "—"
        lines.append(f"⏱ محدودیت فوق‌العاده: فعال تا {sup_until}"
                     + (f" | شروع چت جدید تا {fa_num(sup_rem)} دقیقه بسته" if sup_rem is not None else ""))
    else:
        lines.append("⏱ محدودیت فوق‌العاده: ندارد")
    gb_fa = {"none": "ندارد", "timed": "زمان‌دار — فعال", "perm": "دائمی — فعال"}
    gb_line = f"🚻 منع چت با دختران: {gb_fa[gb]}"
    if gb == "timed" and u.get("girl_block_until"):
        try:
            gb_line += f" تا {jalali(parse_iso(u['girl_block_until']))}"
        except Exception:
            pass
    lines.append(gb_line)
    lines.append(f"⚖ اعتراض‌ها: {fa_num(len(appeals))} مورد" +
                 (f" (آخرین: {appeals[-1]['appeal'].get('status', '—')})" if appeals else ""))
    st = "ثبت‌نام‌شده" if u.get("registered") else "ثبت‌نام‌نشده"
    if u.get("ban"):
        st += " | بن فعال"
    if mute_rem:
        st += " | سکوت فعال"
    lines.append(f"📋 وضعیت فعلی حساب: {st}")
    if confirmed:
        lines.append("\n<b>تخلفات ثبت‌شده:</b>")
        for v in confirmed[-5:]:
            rev = " (لغوشده)" if v.get("revoked") else ""
            ap = " | اعتراض: " + v["appeal"]["status"] if isinstance(v.get("appeal"), dict) else ""
            lines.append(f"• <code>{v['case']}</code> | سطح {fa_num(v.get('level', 0))} | {jalali(parse_iso(v['created']))}{rev}{ap}")
    return "\n".join(lines), None


def security_view_kb(uid: int) -> InlineKeyboardMarkup:
    u = get_user(uid)
    kb_rows = [
        [("btn_next", f"pn_sx:{uid}:unmute", "رفع سکوت"),
         ("btn_next", f"pn_sx:{uid}:unban", "رفع بن")],
        [("btn_next", f"pn_sx:{uid}:mute_add", "تمدید سکوت"),
         ("btn_next", f"pn_sx:{uid}:mute_reduce", "کاهش سکوت")],
        [("btn_next", f"pn_sx:{uid}:ban_change", "تغییر مدت بن"),
         ("btn_next", f"pn_sx:{uid}:custom", "مجازات اختصاصی")],
        [("btn_next", f"pn_sx:{uid}:girl_set", "منع چت با دختران"),
         ("btn_next", f"pn_sx:{uid}:girl_remove", "لغو منع دختران")],
        [("btn_next", f"pn_sx:{uid}:clearsuper", "لغو فوق‌العاده"),
         ("btn_next", f"pn_sx:{uid}:warndel", "حذف اخطار")],
        [("btn_next", f"pn_sx:{uid}:revoke", "لغو یک تخلف"),
         ("btn_next", f"pn_sx:{uid}:clearviol", "پاک‌کردن سابقه تخلفات")],
    ]
    kb_rows.append([("btn_back", f"pn_u:{uid}")])
    return imarkup(kb_rows)

# ============================================================
# 29) تنظیمات پیشرفته — مدیریت دکمه‌ها (پیش‌نمایش/چیدمان/ذخیره) و مدیریت دستورات
# ============================================================

def get_draft() -> dict:
    cfg = get_button_config()
    d = cfg.get("draft")
    return d if isinstance(d, dict) else None


def set_draft(d):
    def _m(cfg):
        cfg["draft"] = d
        return cfg
    STORE.update("button_styles", _m)


def clear_draft():
    set_draft(None)


def dval(draft, field, key, default):
    if draft and field in draft and key in draft[field]:
        return draft[field][key]
    cfg = get_button_config()
    return cfg[field].get(key, default)


def d_enabled(draft, key) -> bool:
    if draft and "disabled" in draft:
        return key not in draft["disabled"]
    return is_enabled(key)


def d_text(draft, key) -> str:
    return dval(draft, "texts", key, "") or STYLE_KEYS[key][0]


def d_style(draft, key) -> str:
    v = dval(draft, "styles", key, None)
    if v is None:
        v = STYLE_KEYS[key][1]
    return v


def d_layout(draft, kb_name):
    """چیدمان دیدِ پیش‌نویس — همیشه فقط دکمه‌های همان کیبورد (فیلتر محدوده)."""
    if draft and kb_name in (draft.get("layouts") or {}):
        rows = draft["layouts"][kb_name]
    else:
        rows = [list(r) for r in get_layout(kb_name)]
    allowed = kb_allowed_keys(kb_name)
    return [[k for k in row if k in allowed] for row in rows]


def draft_set_text(key: str, text: str):
    d = get_draft() or {"texts": {}, "styles": {}, "disabled": [], "layouts": {}}
    d.setdefault("texts", {})[key] = text.strip()
    set_draft(d)


def draft_set_style(key: str, style: str):
    d = get_draft() or {"texts": {}, "styles": {}, "disabled": [], "layouts": {}}
    d.setdefault("styles", {})[key] = style
    set_draft(d)


def draft_set_enabled(key: str, enabled: bool):
    d = get_draft() or {"texts": {}, "styles": {}, "disabled": [], "layouts": {}}
    dis = d.setdefault("disabled", [])
    if enabled:
        d["disabled"] = [k for k in dis if k != key]
    else:
        if key not in dis:
            dis.append(key)
    set_draft(d)


def draft_set_rows(kb_name: str, rows):
    d = get_draft() or {"texts": {}, "styles": {}, "disabled": [], "layouts": {}}
    d.setdefault("layouts", {})[kb_name] = rows
    set_draft(d)


def draft_has_changes() -> bool:
    d = get_draft()
    if not d:
        return False
    return bool(d.get("texts") or d.get("styles") or d.get("disabled") or d.get("layouts"))


def draft_reset_button(key: str):
    """بازگرداندن تنظیمات فقط همین دکمه به حالت اولیه (در پیش‌نویس)."""
    d = get_draft()
    if not d:
        return
    d.get("texts", {}).pop(key, None)
    d.get("styles", {}).pop(key, None)
    d["disabled"] = [k for k in (d.get("disabled") or []) if k != key]
    # چیدمان سراسری است؛ دکمه در چیدمان می‌ماند و فقط تنظیمات آن بازنشانی می‌شود
    set_draft(d)


def draft_apply_save() -> dict:
    """اعمال پیش‌نویس به پیکربندی پایدار (پس از تأیید مالک).
    وضعیت «فعال» هم ذخیره می‌شود — دکمه‌ای که در پیش‌نویس فعال شده،
    از فهرست غیرفعال‌های پایدار هم حذف می‌شود (رفع باگ فعال‌نشدن دکمه)."""
    d = get_draft() or {}
    saved = {"texts": 0, "styles": 0, "disabled": 0, "layouts": 0}
    if not d:
        return saved
    for key, text in (d.get("texts") or {}).items():
        if set_text(key, text):
            saved["texts"] += 1
    for key, style in (d.get("styles") or {}).items():
        if set_style(key, style):
            saved["styles"] += 1
    draft_disabled = set(d.get("disabled") or [])
    for key in STYLE_KEYS:
        should_disable = key in draft_disabled
        if set_enabled(key, not should_disable):
            if should_disable:
                saved["disabled"] += 1
    for kb_name, rows in (d.get("layouts") or {}).items():
        if set_layout(kb_name, rows):
            saved["layouts"] += 1
    clear_draft()
    audit("owner", "buttons_saved", details=str(saved))
    return saved


def build_preview_reply_kb(draft, kb_name) -> ReplyKeyboardMarkup:
    rows_out = []
    for row in d_layout(draft, kb_name):
        r = []
        for key in row:
            if d_enabled(draft, key):
                style = d_style(draft, key)
                kw = {"style": style} if style else {}
                r.append(KeyboardButton(d_text(draft, key), **kw))
        if r:
            rows_out.append(r)
    return ReplyKeyboardMarkup(rows_out, resize_keyboard=True, one_time_keyboard=False)


def layout_table_text(draft, kb_name: str) -> str:
    rows = d_layout(draft, kb_name)
    kb_title = "منوی اصلی" if kb_name == "main_menu" else "کیبورد مکالمه"
    lines = [f"🧩 <b>چیدمان {kb_title}</b>", ""]
    for i, row in enumerate(rows):
        names = []
        for key in row:
            mark = "" if d_enabled(draft, key) else " (غیرفعال)"
            names.append(d_text(draft, key) + mark)
        lines.append(f"ردیف {fa_num(i + 1)}: {' | '.join(names) if names else '(خالی)'}")
    lines.append("")
    lines.append("دکمه‌های پنل مدیریتی (اینلاین): چیدمان ثابت است و فقط متن و رنگ قابل تغییر است؛")
    lines.append("دکمه‌های URL و دکمه‌های سیستمی پنل از محدودیت‌های Telegram Bot API پیروی می‌کنند.")
    return "\n".join(lines)

# ---------- نمای پنل‌ها ----------

def adv_main_kb() -> InlineKeyboardMarkup:
    return imarkup([
        [("btn_next", "pn_btn", "مدیریت دکمه‌ها"), ("btn_next", "pn_cmd", "مدیریت دستورات")],
        [("btn_next", "pn_ocd", "کد اختصاصی مالک")],
        [("btn_back", "pn")],
    ])


def btn_manager_text() -> str:
    draft = get_draft()
    changed = "🟡 پیش‌نویس تغییرات ذخیره‌نشده دارد" if draft_has_changes() else "سبز تغییر ذخیره‌نشده‌ای وجود ندارد"
    reply_btns = [k for k, v in STYLE_KEYS.items() if v[2] == "reply"]
    inline_btns = [k for k, v in STYLE_KEYS.items() if v[2] == "inline"]
    lines = [
        "🎛 <b>مدیریت دکمه‌ها</b>", "",
        f"وضعیت: {changed}", "",
        "برای هر دکمه: تغییر نام، رنگ رسمی، جابه‌جایی ردیف، فعال/غیرفعال و بازنشانی.", "",
        "<b>دکمه‌های کیبورد (Reply):</b>",
    ]
    for key in reply_btns:
        mark = " (غیرفعال)" if not d_enabled(draft, key) else ""
        style_s = style_label(d_style(draft, key))
        lines.append(f"• «{d_text(draft, key)}»{mark} — رنگ: {style_s}")
    lines.append("")
    lines.append("<b>دکمه‌های اینلاین (فرم‌ها و تأییدها):</b>")
    for key in inline_btns:
        lines.append(f"• «{d_text(draft, key)}» — رنگ: {style_label(d_style(draft, key))}")
    lines.append("")
    lines.append("ℹ️ استایل رسمی تلگرام فقط primary/success/danger/پیش‌فرض است؛ رنگ دلخواه HEX توسط Bot API پشتیبانی نمی‌شود.")
    return "\n".join(lines)


def btn_manager_kb() -> InlineKeyboardMarkup:
    rows = [
        [("btn_next", "pn_layout:main_menu", "چیدمان منوی اصلی", "primary"),
         ("btn_next", "pn_layout:conv", "چیدمان کیبورد چت", "primary")],
    ]
    for key in [k for k, v in STYLE_KEYS.items() if v[2] == "reply"]:
        rows.append([("btn_next", f"pn_bv:{key}", f"«{d_text(get_draft(), key)}»")])
    rows.append([("btn_next", "pn_bprev", "پیش‌نمایش و ذخیره", "success")])
    rows.append([("btn_next", "pn_breset_all_go", "بازگرداندن کل چیدمان به پیش‌فرض", "danger")])
    rows.append([("btn_back", "pn_adv")])
    return imarkup(rows)


def btn_detail_text(key: str) -> str:
    draft = get_draft()
    kind_fa = "کیبورد Reply" if STYLE_KEYS[key][2] == "reply" else "دکمه اینلاین"
    movable = STYLE_KEYS[key][3]
    lines = [
        f"🔘 <b>دکمه «{d_text(draft, key)}»</b>", "",
        f"کلید سیستمی: <code>{key}</code> (برای Callbackها — تغییر نمی‌کند)",
        f"نوع: {kind_fa}",
        f"متن نمایشی: «{d_text(draft, key)}»",
        f"رنگ (استایل رسمی): {style_label(d_style(draft, key))}",
        f"وضعیت: {'فعال' if d_enabled(draft, key) else 'غیرفعال'}",
    ]
    if STYLE_KEYS[key][2] == "reply":
        for kb_name, rows in (("main_menu", d_layout(draft, "main_menu")), ("conv", d_layout(draft, "conv"))):
            for i, row in enumerate(rows):
                if key in row:
                    lines.append(f"جایگاه: {('منوی اصلی' if kb_name == 'main_menu' else 'کیبورد چت')} — ردیف {fa_num(i + 1)}, جایگاه {fa_num(row.index(key) + 1)}")
    if key.startswith("btn_"):
        lines.append("")
        lines.append("ℹ️ دکمه‌های اینلاین فقط متن و رنگ قابل تغییر دارند؛ جابه‌جایی ندارند (محدودیت API).")
    elif not movable:
        lines.append("")
        lines.append("ℹ️ این دکمه جابه‌جایی ندارد.")
    return "\n".join(lines)


def btn_detail_kb(key: str) -> InlineKeyboardMarkup:
    rows = [
        [("btn_next", f"pn_btext:{key}", "تغییر نام/متن", "primary")],
        [("btn_next", f"pn_bcolor:{key}", "تغییر رنگ", "primary")],
        [("btn_next", f"pn_ben:{key}",
          "غیرفعال کردن" if d_enabled(get_draft(), key) else "فعال کردن",
          "danger" if d_enabled(get_draft(), key) else "success")],
    ]
    if STYLE_KEYS[key][2] == "reply":
        rows.append([("btn_next", f"pn_bm:{key}:up", "جابه‌جایی به عقب"),
                     ("btn_next", f"pn_bm:{key}:down", "جابه‌جایی به جلو")])
        rows.append([("btn_next", f"pn_bmrow:{key}", "انتقال به ردیف دیگر", "primary")])
    rows.append([("btn_next", f"pn_breset:{key}", "بازگرداندن این دکمه به حالت اولیه", "danger")])
    rows.append([("btn_back", "pn_btn")])
    return imarkup(rows)


def btn_color_kb(key: str) -> InlineKeyboardMarkup:
    draft = get_draft()
    cur = d_style(draft, key)
    rows = []
    row = []
    for s in VALID_STYLES:
        mark = " ✔" if s == cur else ""
        row.append(InlineKeyboardButton(style_label(s) + mark, callback_data=f"pn_bcset:{key}:{s}"))
    rows.append(row)
    rows.append([ib("btn_back", f"pn_bv:{key}")])
    return InlineKeyboardMarkup(rows)


def btn_move_rows_kb(key: str) -> InlineKeyboardMarkup:
    draft = get_draft()
    kb_name = "main_menu" if key in [k for r in d_layout(draft, "main_menu") for k in r] else "conv"
    rows = d_layout(draft, kb_name)
    kb_rows = [[InlineKeyboardButton("⬆️ به ردیف اول (ردیف جدید)",
                                     callback_data=f"pn_bmto:{key}:{kb_name}:first")]]
    for i, row in enumerate(rows):
        names = " | ".join(d_text(draft, k) for k in row) or "(خالی)"
        kb_rows.append([InlineKeyboardButton(f"انتقال به ردیف {fa_num(i + 1)} ({names[:24]})",
                                             callback_data=f"pn_bmto:{key}:{kb_name}:{i}")])
    kb_rows.append([InlineKeyboardButton("ایجاد ردیف جدید", callback_data=f"pn_bmto:{key}:{kb_name}:new")])
    kb_rows.append([ib("btn_back", f"pn_bv:{key}")])
    return InlineKeyboardMarkup(kb_rows)


def layout_editor_kb(kb_name: str) -> InlineKeyboardMarkup:
    """ویرایشگر ساده چیدمان: برای هر ردیف فقط افزودن/حذف/جابه‌جایی دکمه‌ها + جابه‌جایی ردیف."""
    draft = get_draft()
    rows = d_layout(draft, kb_name)
    kb_rows = []
    for i, row in enumerate(rows):
        # جابه‌جایی ردیف
        r = []
        if len(rows) > 1 and i > 0:
            r.append(InlineKeyboardButton(f"▲ بالا بردن ردیف {fa_num(i + 1)}",
                                          callback_data=f"pn_lrowmv:{kb_name}:{i}:up"))
        if len(rows) > 1 and i < len(rows) - 1:
            r.append(InlineKeyboardButton(f"▼ پایین بردن ردیف {fa_num(i + 1)}",
                                          callback_data=f"pn_lrowmv:{kb_name}:{i}:down"))
        if r:
            kb_rows.append(r)
        r2 = [InlineKeyboardButton(f"➕ افزودن به ردیف {fa_num(i + 1)}",
                                   callback_data=f"pn_ladd:{kb_name}:{i}")]
        if row:
            r2.append(InlineKeyboardButton(f"➖ حذف از ردیف {fa_num(i + 1)}",
                                           callback_data=f"pn_lremove:{kb_name}:{i}"))
            r2.append(InlineKeyboardButton(f"⇄ جابه‌جایی دکمه‌های ردیف {fa_num(i + 1)}",
                                           callback_data=f"pn_lmv:{kb_name}:{i}"))
        kb_rows.append(r2)
    kb_rows.append([InlineKeyboardButton("چیدمان پیش‌فرض این کیبورد",
                                         callback_data=f"pn_lreset:{kb_name}", style="danger")])
    kb_rows.append([ib("btn_next", "pn_bprev", "پیش‌نمایش و ذخیره", "success"),
                    ib("btn_back", "pn_btn")])
    return InlineKeyboardMarkup(kb_rows)


def layout_add_kb(kb_name: str, row_i: int) -> InlineKeyboardMarkup:
    draft = get_draft()
    rows = d_layout(draft, kb_name)
    existing = [k for r in rows for k in r]
    # فقط دکمه‌های همین کیبورد پیشنهاد می‌شوند (منوی اصلی ≠ کیبورد چت)
    candidates = [k for k in kb_allowed_keys(kb_name) if k not in existing]
    kb_rows = []
    for key in candidates:
        kb_rows.append([InlineKeyboardButton(f"«{d_text(draft, key)}»",
                                             callback_data=f"pn_laddto:{kb_name}:{row_i}:{key}")])
    if not candidates:
        kb_rows.append([InlineKeyboardButton("دکمه‌ای برای افزودن وجود ندارد", callback_data="noop")])
    kb_rows.append([ib("btn_back", f"pn_layout:{kb_name}")])
    return InlineKeyboardMarkup(kb_rows)


def layout_remove_kb(kb_name: str, row_i: int) -> InlineKeyboardMarkup:
    draft = get_draft()
    rows = d_layout(draft, kb_name)
    row = rows[row_i] if 0 <= row_i < len(rows) else []
    kb_rows = []
    for key in row:
        kb_rows.append([InlineKeyboardButton(f"حذف «{d_text(draft, key)}»",
                                             callback_data=f"pn_ldel:{kb_name}:{row_i}:{key}")])
    if not kb_rows:
        kb_rows.append([InlineKeyboardButton("(ردیف خالی است)", callback_data="noop")])
    kb_rows.append([ib("btn_back", f"pn_layout:{kb_name}")])
    return InlineKeyboardMarkup(kb_rows)


# ---------- ابزارهای پیشرفته چیدمان (نسخه ۲.۱.۰) ----------

def move_button_in_layout(kb_name: str, key: str, direction: str) -> bool:
    """جابه‌جایی دکمه در پیش‌نویس چیدمان (سازگار با سیستم پیش‌نویس پنل).
    direction: "first" (ردیف جدید در صدر) | "up" | "down"
    ایندکس ردیف‌های میانی پایدار می‌ماند؛ ردیف خالی مبدا در ذخیره نهایی حذف می‌شود."""
    rows = d_layout(get_draft(), kb_name)
    pos = None
    for ri, row in enumerate(rows):
        if key in row:
            pos = (ri, row.index(key))
            break
    if pos is None:
        return False
    ri, ci = pos
    if direction == "first":
        rows[ri] = [k for k in rows[ri] if k != key]
        rows.insert(0, [key])
    elif direction == "up" and ri > 0:
        rows[ri].pop(ci)
        rows[ri - 1].append(key)
    elif direction == "down" and ri < len(rows) - 1:
        rows[ri].pop(ci)
        rows[ri + 1].append(key)
    else:
        return False
    draft_set_rows(kb_name, rows)
    return True


def layout_move_button(kb_name: str, row_i: int, key: str, direction: str) -> bool:
    """جابه‌جایی یک دکمه: چپ/راست داخل ردیف، بالا/پایین بین ردیف‌ها.
    فقط ترتیب تغییر می‌کند؛ Callback دکمه دست‌نخورده می‌ماند."""
    draft = get_draft()
    rows = d_layout(draft, kb_name)
    if not (0 <= row_i < len(rows)):
        return False
    if direction in ("l", "r"):
        row = rows[row_i]
        if key not in row:
            return False
        j = row.index(key)
        nj = j - 1 if direction == "l" else j + 1
        if not (0 <= nj < len(row)):
            return False
        row[j], row[nj] = row[nj], row[j]
    else:
        src = row_i if key in rows[row_i] else next(
            (i for i, r in enumerate(rows) if key in r), None)
        if src is None:
            return False
        dst = src - 1 if direction == "u" else src + 1
        if dst < 0:
            return False
        if dst >= len(rows):
            rows.append([])
        if key not in rows[dst]:
            rows[dst].append(key)
        rows[src] = [k for k in rows[src] if k != key]
        # ردیف‌های خالی حذف نمی‌شوند: ایندکس ردیف‌ها برای کنترل‌های پنل پایدار می‌ماند؛
        # ردیف خالی در get_layout/d_layout به‌صورت خودکار فیلتر و در ذخیره نهایی حذف می‌شود.
    draft_set_rows(kb_name, rows)
    return True


def layout_move_row(kb_name: str, row_i: int, direction: str) -> bool:
    draft = get_draft()
    rows = d_layout(draft, kb_name)
    if not (0 <= row_i < len(rows)):
        return False
    dst = row_i - 1 if direction == "up" else row_i + 1
    if not (0 <= dst < len(rows)):
        return False
    rows[row_i], rows[dst] = rows[dst], rows[row_i]
    draft_set_rows(kb_name, rows)
    return True


def layout_move_kb(kb_name: str, row_i: int) -> InlineKeyboardMarkup:
    """کنترل چهارجهته جابه‌جایی دکمه‌های یک ردیف (چپ/راست/بالا/پایین)."""
    draft = get_draft()
    rows = d_layout(draft, kb_name)
    row = rows[row_i] if 0 <= row_i < len(rows) else []
    kb_rows = []
    for key in row:
        kb_rows.append([
            InlineKeyboardButton(f"«{d_text(draft, key)}»", callback_data="noop"),
            InlineKeyboardButton("◀", callback_data=f"pn_bmv:{kb_name}:{row_i}:{key}:l"),
            InlineKeyboardButton("▶", callback_data=f"pn_bmv:{kb_name}:{row_i}:{key}:r"),
            InlineKeyboardButton("▲", callback_data=f"pn_bmv:{kb_name}:{row_i}:{key}:u"),
            InlineKeyboardButton("▼", callback_data=f"pn_bmv:{kb_name}:{row_i}:{key}:d"),
        ])
    if not kb_rows:
        kb_rows.append([InlineKeyboardButton("(ردیف خالی است)", callback_data="noop")])
    kb_rows.append([ib("btn_back", f"pn_layout:{kb_name}")])
    return InlineKeyboardMarkup(kb_rows)


def btn_preview_text() -> str:
    return ("👁 <b>پیش‌نمایش چیدمان نهایی</b>\n\n"
            "دو پیام زیر، کیبوردهای واقعی (Reply) با متن/رنگ/چیدمان جدید هستند.\n"
            "پس از ذخیره، کیبوردهای جدید کاربران با همین شکل ساخته می‌شوند؛ "
            "پیام‌های قدیمی در صورت امکان با ویرایش به‌روز می‌شوند و در غیر این صورت فقط "
            "کیبوردهای جدید اعمال می‌شود (بدون خطای اضافی).")


def btn_preview_confirm_kb() -> InlineKeyboardMarkup:
    return imarkup([
        [("btn_confirm", "pn_bsave", " ذخیره نهایی تغییرات"), ("btn_reject", "pn_bcancel", "لغو تغییرات")],
        [("btn_back", "pn_btn")],
    ])

# ---------- مدیریت دستورات ----------

def cmd_manager_text() -> str:
    cmds = get_commands()
    lines = ["🧭 <b>مدیریت دستورات</b>", "",
             "تغییر عنوان/توضیح/نمونه و ترتیب فقط در «راهنما» اعمال می‌شود؛ عملکرد واقعی دستورها ثابت است.",
             "دستورهای سیستمی و امنیتی (/start، /report، /panel و دستورهای محرمانه) قابل بازنویسی نیستند.", ""]
    for cat in GUIDE_CATEGORIES_ORDER:
        items = [c for c in cmds if c["category"] == cat]
        if not items:
            continue
        lines.append(f"<b>{CATEGORY_LABELS[cat]}</b>")
        for c in items:
            state = "" if c.get("enabled", True) else " (غیرفعال)"
            ch = " | قابل تغییر" if c.get("changeable") else " | سیستمی"
            secret = " | محرمانه مالک" if c.get("secret") else ""
            lines.append(f"• <code>{c['name']}</code> — {c['title']}{state}{ch}{secret}")
        lines.append("")
    return "\n".join(lines)


def cmd_manager_kb() -> InlineKeyboardMarkup:
    cmds = get_commands()
    kb_rows = []
    for c in cmds:
        label = f"{c['name']} — {c['title']}" + ("" if c.get("enabled", True) else " (غیرفعال)")
        kb_rows.append([InlineKeyboardButton(label[:44], callback_data=f"pn_cv:{c['name']}")])
    kb_rows.append([ib("btn_back", "pn_adv")])
    return InlineKeyboardMarkup(kb_rows)


def cmd_detail_text(name: str) -> str:
    cmd = next((c for c in get_commands() if c["name"] == name), None)
    if not cmd:
        return "ℹ️ دستور یافت نشد."
    return guide_command_text(cmd)


def cmd_detail_kb(name: str) -> InlineKeyboardMarkup:
    cmd = next((c for c in get_commands() if c["name"] == name), None)
    if not cmd:
        return imarkup([[("btn_back", "pn_cmd")]])
    kb_rows = []
    if cmd.get("changeable"):
        kb_rows.append([("btn_next", f"pn_ce:{name}:title", "تغییر عنوان"),
                        ("btn_next", f"pn_ce:{name}:desc", "تغییر توضیحات")])
        kb_rows.append([("btn_next", f"pn_ce:{name}:usage", "تغییر نحوه استفاده"),
                        ("btn_next", f"pn_ce:{name}:example", "تغییر نمونه")])
        kb_rows.append([("btn_next", f"pn_ct:{name}", "غیرفعال کردن" if cmd.get("enabled", True) else "فعال کردن")])
        kb_rows.append([("btn_next", f"pn_cord:{name}:up", "ترتیب به عقب"),
                        ("btn_next", f"pn_cord:{name}:down", "ترتیب به جلو")])
    else:
        kb_rows.append([("btn_next", "noop", "سیستمی — بدون امکان تغییر")])
    kb_rows.append([("btn_back", "pn_cmd")])
    return imarkup(kb_rows)


def set_command_enabled(name: str, enabled: bool) -> bool:
    cmd = next((c for c in COMMANDS_DEFAULT if c["name"] == name), None)
    if cmd is None or not cmd.get("changeable"):
        return False
    return save_commands_meta(name, {"enabled": bool(enabled)})


def shift_command_order(name: str, direction: str) -> bool:
    cmd = next((c for c in COMMANDS_DEFAULT if c["name"] == name), None)
    if cmd is None or not cmd.get("changeable"):
        return False
    cmds = get_commands()
    idx = next((i for i, c in enumerate(cmds) if c["name"] == name), None)
    if idx is None:
        return False
    swap = idx - 1 if direction == "up" else idx + 1
    if not (0 <= swap < len(cmds)):
        return False
    cmds[idx], cmds[swap] = cmds[swap], cmds[idx]
    # ترتیب همه دستورها ذخیره می‌شود تا ترکیب پیش‌فرض و ذخیره‌شده ناسازگار نشود
    for i, c in enumerate(cmds):
        save_commands_meta(c["name"], {"order": (i + 1) * 10})
    return True


async def sync_bot_commands(bot):
    """به‌روزرسانی منوی دستورات تلگرام بر اساس رجیستری (فقط دستورهای فعال عمومی)."""
    from telegram import BotCommand, BotCommandScopeChat
    public = [c for c in get_commands()
              if c.get("enabled", True) and not c.get("secret") and str(c["name"]).startswith("/")]
    try:
        await bot.set_my_commands([BotCommand(c["name"].lstrip("/"), c.get("title") or c["name"]) for c in public])
        if OWNER_ID:
            owner_cmds = [c for c in get_commands()
                          if c.get("enabled", True) and not c.get("secret") and str(c["name"]).startswith("/")]
            await bot.set_my_commands(
                [BotCommand(c["name"].lstrip("/"), c.get("title") or c["name"]) for c in owner_cmds]
                + [BotCommand("panel", "پنل مدیریت")],
                scope=BotCommandScopeChat(chat_id=OWNER_ID))
        return True
    except TelegramError as e:
        LOG.error("به‌روزرسانی منوی دستورات ناموفق: %s", e.__class__.__name__)
        return False
# ============================================================
# 26) جلوگیری از پردازش Update تکراری + نگهبان زمان‌بندی پایدار
# ============================================================

_LAST_UPDATE_ID = -1
_RECENT_IDS = set()


def load_update_watermark():
    global _LAST_UPDATE_ID
    ensure_storage()
    d = STORE.get("processed_updates")
    try:
        _LAST_UPDATE_ID = int(d.get("last", -1))
    except Exception:
        _LAST_UPDATE_ID = -1


def flush_update_watermark():
    ensure_storage()
    lid = _LAST_UPDATE_ID

    def _m(d):
        d["last"] = max(int(d.get("last", -1)), lid)
        return d
    STORE.mutate("processed_updates", _m)


async def dedupe_update(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Update تکراری (پس از Restart/Redeploy) فقط یک‌بار پردازش می‌شود."""
    global _LAST_UPDATE_ID
    uid = update.update_id
    if uid is None:
        return
    if uid in _RECENT_IDS or uid <= _LAST_UPDATE_ID:
        raise ApplicationHandlerStop
    _RECENT_IDS.add(uid)
    if len(_RECENT_IDS) > 20000:
        _RECENT_IDS.clear()
    if uid > _LAST_UPDATE_ID:
        _LAST_UPDATE_ID = uid


async def on_error(update: object, context: ContextTypes.DEFAULT_TYPE):
    log_exc("خطای پردازش آپدیت: %s", context.error.__class__.__name__)


def cleanup_old_messages(settings, now_utc_dt: datetime):
    """پاک‌سازی خودکار پیام‌ها بر اساس سیاست نگهداری (۷۲ ساعت)؛
    استثناها: پیام‌های مدیر اصلی (دائمی) و مکالمه‌های دارای گزارش باز."""
    retention = int(settings.get("retention_hours", 72))
    open_convs = {r.get("conv") for r in STORE.get("reports")
                  if r.get("status") in ("new", "in_review")}
    cutoff = now_utc_dt - timedelta(hours=retention)
    removed = 0
    for conv_id in MSGS.list_convs():
        def _mmsg(d, conv_id=conv_id):
            nonlocal removed
            keep = []
            for rec in d.get("messages", []):
                if rec.get("owner_msg") or conv_id in open_convs:
                    keep.append(rec)
                    continue
                try:
                    if parse_iso(rec["created"]) >= cutoff:
                        keep.append(rec)
                    else:
                        removed += 1
                except Exception:
                    continue
            d["messages"] = keep
            return d
        MSGS.mutate(conv_id, _mmsg)
    return removed


async def sweeper(app: Application):
    """حلقه پایدار زمان‌بندی: همه وضعیت‌ها از دیتابیس خوانده می‌شوند و پس از Restart بازیابی می‌گردند."""
    tick = 0
    while True:
        try:
            tick += 1
            # ۱) وظایف زمان‌بندی‌شده ذخیره‌شده در دیتابیس
            for t in pop_due_tasks():
                kind = t.get("kind")
                payload = t.get("payload") or {}
                if kind == "bot_on":
                    STORE.update("settings", lambda x: dict(x, bot_enabled=True, maintenance=False))
                    await send_text(app.bot, OWNER_ID, "🟢 ربات طبق زمان‌بندی روشن شد.")
                elif kind == "bot_off":
                    STORE.update("settings", lambda x: dict(x, bot_enabled=False))
                    await send_text(app.bot, OWNER_ID, "🔴 ربات طبق زمان‌بندی خاموش شد.")
                elif kind == "unban" and str(payload.get("uid", "")).isdigit():
                    release_ban(int(payload["uid"]), by="scheduler")
                elif kind == "unmute" and str(payload.get("uid", "")).isdigit():
                    release_mute(int(payload["uid"]), by="scheduler")

            # ۱.۵) ارسال‌های همگانی زمان‌بندی‌شده/تکرارشونده (ماندگار در دیتابیس)
            for bj in due_broadcast_jobs():
                sent, failed = await do_broadcast(
                    app, bj["text"], pin=bj.get("pin"), react=bj.get("react"))
                advance_broadcast_job(bj["jid"], sent, failed)

            # ۲) روشن/خاموش شدن روزانه زمان‌بندی‌شده (ساعت تهران)
            s = STORE.get("settings")
            hm = te_hm()
            for key, want in (("sched_off", False), ("sched_on", True)):
                d = s.get(key) or {}
                if d.get("enabled") and d.get("time") == hm:
                    fire_key = te_date_key() + hm
                    fired = (s.get("sched_last_fired") or {}).get(key)
                    if fired != fire_key:
                        def _m(x, key=key, want=want, fire_key=fire_key):
                            lf = dict(x.get("sched_last_fired") or {})
                            lf[key] = fire_key
                            return dict(x, bot_enabled=want, sched_last_fired=lf)
                        STORE.update("settings", _m)
                        await send_text(app.bot, OWNER_ID,
                                        "🟢 ربات طبق زمان‌بندی روشن شد." if want else "🔴 ربات طبق زمان‌بندی خاموش شد.")
                        s = STORE.get("settings")

            # ۳) بازیابی مکالمات/صف پس از Restart و تلاش اتصال
            conv_id = attempt_match(None)
            if conv_id:
                conv = get_conv(conv_id)
                intro = "🎉 <b>اتصال برقرار شد!</b>\n\nبا احترام گفت‌وگو کنید."
                for p in conv["participants"]:
                    await send_text(app.bot, int(p), intro, conv_kb(), html=True)

            # ۴) انقضای صف انتظار
            qto = int(s.get("queue_timeout_minutes", 30))
            users = STORE.get("users")
            now = now_utc()
            for u in users.values():
                if u.get("searching") and u.get("queue_since"):
                    try:
                        if now - parse_iso(u["queue_since"]) > timedelta(minutes=qto):
                            cancel_search(int(u["tg"]))
                            await send_text(app.bot, int(u["tg"]),
                                            "ℹ️ زمان انتظار به پایان رسید؛ جست‌وجو لغو شد. دوباره تلاش کنید.", main_menu_kb())
                    except Exception:
                        cancel_search(int(u["tg"]))

            # ۵) انقضای درخواست‌های دوست
            rto = int(s.get("request_timeout_minutes", 10))
            expired = []
            def _fr(lst):
                for r in lst:
                    if r.get("status") == "pending":
                        try:
                            if now - parse_iso(r["created"]) > timedelta(minutes=rto):
                                r["status"] = "expired"
                                expired.append(r)
                        except Exception:
                            r["status"] = "expired"
                            expired.append(r)
                return lst
            STORE.mutate("friend_requests", _fr)
            for r in expired:
                await send_text(app.bot, int(r["from"]),
                                "ℹ️ درخواست چت شما پاسخ داده نشد و منقضی شد.")

            if tick % 4 == 0:
                # ۶) پاک‌سازی خودکار پیام‌ها بر اساس سیاست نگهداری (۷۲ ساعت؛ استثنا: مدیر و گزارش باز)
                cleanup_old_messages(s, now)

                # ۷) پایان خودکار بن‌ها و سکوت‌های منقضی‌شده
                for u in STORE.get("users").values():
                    if u.get("ban") and not u["ban"].get("perm"):
                        try:
                            if parse_iso(u["ban"]["until"]) <= now:
                                release_ban(int(u["tg"]), by="scheduler")
                        except Exception:
                            pass
                    if u.get("mute_until"):
                        try:
                            if parse_iso(u["mute_until"]) <= now:
                                release_mute(int(u["tg"]), by="scheduler")
                        except Exception:
                            pass

                # ۸) بکاپ خودکار زمان‌بندی‌شده
                s2 = STORE.get("settings")
                if s2.get("auto_backup_enabled", True):
                    last = s2.get("last_auto_backup")
                    interval = max(1, int(s2.get("backup_interval_hours", 24)))
                    due = False
                    if not last:
                        due = True
                    else:
                        try:
                            due = (now - parse_iso(last)) >= timedelta(hours=interval)
                        except Exception:
                            due = True
                    if due:
                        create_backup("auto")
                        STORE.update("settings", lambda x: dict(x, last_auto_backup=iso_utc(now_utc())))
                        prune_backups()

            # ۹) ثبت نشانگر آپدیت‌ها (ضد تکرار پس از Restart)
            flush_update_watermark()
        except Exception:
            log_exc("خطا در حلقه نگهبان")
        await asyncio.sleep(15)

# ============================================================
# 27) اجرا (Long Polling دائمی روی Railway)
# ============================================================

def _check_single_instance():
    """جلوگیری از اجرای هم‌زمان چند نمونه ربات (قفل فایل)."""
    lock_path = os.path.join(DATA_DIR, "bot.lock")
    try:
        fd = os.open(lock_path, os.O_CREAT | os.O_RDWR)
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        return fd
    except (OSError, BlockingIOError):
        LOG.critical("یک نمونه دیگر از ربات در حال اجراست؛ اجرای نمونه دوم متوقف شد.")
        raise SystemExit(3)


def _migrate_storage():
    """مهاجرت نرم ساختار داده برای نسخه ۲.۲.۰ — هیچ داده‌ای حذف یا Reset نمی‌شود:
    فقط فیلدهای جدید کاربران مقدار اولیه می‌گیرند (کلیدهای فایل جدید مثل
    «protection» و «violations» به‌طور خودکار با مقدار پیش‌فرض ساخته می‌شوند).
    از این نسخه، بکاپ خودکار برای نصب‌های موجود هم خاموش می‌شود (کاهش مصرف حجم دیسک)."""
    ensure_storage()

    def _um(users):
        for u in users.values():
            for f in ("super_until", "super_last_chat", "super_case",
                      "girl_block_until", "girl_block_case"):
                u.setdefault(f, None)
        return users
    STORE.update("users", _um)
    # خاموش‌کردن بکاپ خودکار برای نصب‌های موجود (یک‌بار در مهاجرت نسخه؛ قابل روشن‌کردن از پنل)
    STORE.update("settings", lambda x: dict(x, auto_backup_enabled=False))
    LOG.info("مهاجرت ساختار داده نسخه %s انجام شد (بدون تغییر داده‌های موجود)", BOT_VERSION)


def _maybe_backup_before_update():
    """طبق قانون آپدیت‌ها: پیش از اعمال نسخه جدید، از کل فایل‌های /data بکاپ گرفته می‌شود.
    هیچ داده‌ای Reset نمی‌شود؛ تغییر ساختار فقط با مهاجرت خودکار انجام می‌شود."""
    ensure_storage()
    s = STORE.get("settings")
    if s.get("bot_version") != BOT_VERSION:
        try:
            rec = create_backup("pre_update")
            STORE.update("settings", lambda x: dict(x, bot_version=BOT_VERSION))
            LOG.info("بکاپ پیش از به‌روزرسانی ساخته شد: %s", rec["bid"])
        except Exception as e:
            LOG.error("بکاپ پیش از به‌روزرسانی ناموفق بود: %s", e.__class__.__name__)


async def _post_init(app: Application):
    global BOT_START_TS
    BOT_START_TS = _time.time()
    # منوی دستورات تلگرام از رجیستری (عنوان‌ها از پنل مالک قابل تغییر است)
    await sync_bot_commands(app.bot)
    app.bot_data["sweeper_task"] = asyncio.get_running_loop().create_task(sweeper(app))
    LOG.info("ربات با Long Polling اجرا شد (نسخه ربات %s، ساختار داده %s)", BOT_VERSION, SCHEMA_VERSION)


async def _post_stop(app: Application):
    task = app.bot_data.get("sweeper_task")
    if task:
        task.cancel()
        try:
            await task
        except (asyncio.CancelledError, Exception):
            pass
    try:
        flush_update_watermark()
    except Exception:
        pass
    LOG.info("ربات به‌صورت ایمن متوقف شد.")


def main():
    global BOT_START_TS
    if not BOT_TOKEN_ENV:
        LOG.critical("متغیر محیطی BOT_TOKEN تنظیم نشده است.")
        raise SystemExit(1)
    if not OWNER_ID:
        LOG.warning("متغیر محیطی OWNER_ID تنظیم نشده است؛ پنل مدیریت غیرفعال خواهد بود.")
    _check_single_instance()
    init_storage(DATA_DIR)
    _maybe_backup_before_update()   # بکاپ خودکار داده‌ها هنگام آپدیت نسخه — بدون Reset
    _migrate_storage()
    load_update_watermark()
    audit("system", "bot_start", details=f"bot:{BOT_VERSION} schema:{SCHEMA_VERSION}")

    app = Application.builder().token(BOT_TOKEN_ENV).concurrent_updates(False).build()

    app.add_handler(TypeHandler(Update, dedupe_update), group=-1)
    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("info", cmd_info))
    app.add_handler(CommandHandler("guide", cmd_guide))
    app.add_handler(CommandHandler("support", cmd_supp))
    app.add_handler(CommandHandler("supp", cmd_supp))
    app.add_handler(CommandHandler("report", cmd_report))
    app.add_handler(CommandHandler("panel", cmd_panel))
    app.add_handler(CallbackQueryHandler(on_callback))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND & filters.ChatType.PRIVATE, on_text))
    app.add_handler(MessageHandler(~filters.TEXT & filters.ChatType.PRIVATE, on_media))
    app.add_error_handler(on_error)

    app.post_init = _post_init
    app.post_stop = _post_stop
    LOG.info("شروع ربات چت ناشناس | DATA_DIR=%s | OWNER_ID=%s", DATA_DIR, "تنظیم‌شده" if OWNER_ID else "خیر")
    app.run_polling(poll_interval=1.0, timeout=30,
                    allowed_updates=Update.ALL_TYPES, drop_pending_updates=False)


if __name__ == "__main__":
    main()
