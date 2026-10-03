# -*- coding: utf-8 -*-
"""
Virtual Number Shop - Telegram Bot
====================================================================
বাটন, মেনু নেভিগেশন ও স্ট্যাকচারের পাশাপাশি এখন Purchase (Buy one pcs / Bulk Buy)
এবং Admin File Upload (stock যুক্ত করা) এর real logic যুক্ত করা হয়েছে।
✅ ডেটা এখন আর শুধু in-memory (RAM) তে থাকে না — সব ডেটা (users/products/
orders/deposits/sms_log/bot_settings) অটোমেটিক ডিস্কে JSON ফাইলে (DB_FILE_PATH,
ডিফল্ট: bot_data.json) সেভ হয় এবং bot চালু হওয়ার সময় সেখান থেকে লোড হয়ে যায়,
তাই bot restart হলেও ডেটা হারায় না (দেখুন: save_db() / load_db())। Railway তে
এটা সত্যিকারের persistent রাখতে হলে DB_FILE_PATH একটা attached Volume এর
path এ সেট করে দিন, নাহলে নতুন ডিপ্লয়ে ফাইল রিসেট হয়ে যেতে পারে।
যেখানে আসল Payment gateway বসবে সেখানে এখনও # TODO: ... কমেন্ট দিয়ে চিহ্নিত
করা আছে।

Library: pyTelegramBotAPI (telebot)
    pip install pyTelegramBotAPI flask openpyxl

Environment variables (Railway এ / .env এ সেট করবেন):
    BOT_TOKEN     -> BotFather থেকে পাওয়া টোকেন
    ADMIN_ID      -> আপনার টেলিগ্রাম User ID (একাধিক হলে কমা দিয়ে আলাদা করুন)
    RAILWAY_URL   -> Railway তে ডিপ্লয় করা অ্যাপের পাবলিক URL (webhook এর জন্য)
    PORT          -> Railway যে পোর্ট দেয় (ডিফল্ট 8080)
    DB_FILE_PATH  -> persistent DB JSON ফাইলের path (ডিফল্ট: স্ক্রিপ্টের পাশে bot_data.json)

Run mode:
    - RAILWAY_URL সেট থাকলে -> Webhook mode (Flask + Railway)
    - RAILWAY_URL না থাকলে -> Polling mode (লোকাল টেস্টিং এর জন্য)
"""

import os
import requests
import io
import json
import re
import html as _html
import threading
import time
import uuid
import datetime
import copy
import gzip

import telebot
from telebot import types

# ---------------------------------------------------------------------------
# ENV / CONFIG
# ---------------------------------------------------------------------------
BOT_TOKEN = os.environ.get("BOT_TOKEN", "PUT_YOUR_BOT_TOKEN_HERE")
ADMIN_IDS = [
    int(x.strip())
    for x in os.environ.get("ADMIN_ID", "6053411200").split(",")
    if x.strip().isdigit()
]
RAILWAY_URL = os.environ.get("RAILWAY_URL", "")   # e.g. https://your-app.up.railway.app
PORT = int(os.environ.get("PORT", 8080))
REFERRAL_BONUS = 10   # TODO: real bonus amount (এডমিন Bot Settings থেকে সেট করার আগে placeholder)

bot = telebot.TeleBot(BOT_TOKEN, parse_mode="HTML")

# বটের আসল username নিজে থেকে (dynamically) নিয়ে নেওয়া হচ্ছে, যাতে রেফারেল লিংকে
# ভুল/হার্ডকোড করা username (যেমন "vertual_shop_bot" / "virtualshop") না বসে।
try:
    BOT_USERNAME = bot.get_me().username
except Exception:
    BOT_USERNAME = os.environ.get("BOT_USERNAME", "your_bot_username")  # fallback

# ---------------------------------------------------------------------------
# IN-MEMORY "DATABASE" (এখন অটোমেটিক ডিস্কে JSON ফাইলে persist হয়, দেখুন save_db()/
# load_db()/start_persistent_db() — নিচের দিকে "PERSISTENT DATABASE" সেকশনে)
# ---------------------------------------------------------------------------
users = {}      # user_id -> {full_name, username, balance, total_purchased, today_spent, today_deposit, referrals, earned}
products = {}   # WhatsApp/Telegram প্রোডাক্ট সরানো হয়েছে (পরে নতুন প্রোডাক্ট যুক্ত হবে)
orders = {}     # order_id -> order data
deposits = {}   # deposit_id -> {id, user_id, method, amount, trx_id, status, date}
_deposit_id_counter = [1000]   # পরবর্তী deposit id বানানোর কাউন্টার (in-memory)
# 🔒 একই Deposit যেন দুইজন Admin (বা একজন Admin ডাবল-ক্লিক করে) প্রায় একই সময়ে
# Approve/Reject করলে দুইবার ব্যালেন্স যোগ না হয়ে যায় (race condition), সেজন্য
# "status pending কিনা চেক করা -> approved/rejected এ সেট করা -> ব্যালেন্স যোগ করা"
# পুরো অংশটুকু সবসময় এই লক দিয়ে atomic রাখা হয় (ম্যানুয়াল Approve/Reject এবং
# SMS auto-approve/auto-reject — দুই জায়গাতেই)।
_deposit_lock = threading.Lock()
# 🔒 দুইজন ইউজার প্রায় একই সময়ে একই প্রোডাক্ট কিনতে গেলে (বিশেষত স্টক ১টা থাকা
# অবস্থায়), "স্টক আছে কিনা চেক করা -> pop করে item বের করা -> balance কাটা ->
# order সেভ করা" পুরো অংশটুকু atomic রাখতে এই লক ব্যবহার হয় (Buy one pcs ও
# Bulk Buy দুই জায়গাতেই), যাতে stock check আর pop এর মাঝে race condition
# (IndexError crash বা ভুল স্টক গণনা) না হয়।
_stock_lock = threading.Lock()
sms_log = []    # SMS Forwarder থেকে আসা প্রতিটা পার্স-করা পেমেন্ট SMS/নোটিফিকেশন
_sms_id_counter = [0]          # পরবর্তী sms log id বানানোর কাউন্টার (in-memory)


def _next_deposit_id():
    _deposit_id_counter[0] += 1
    return _deposit_id_counter[0]


def _next_sms_id():
    _sms_id_counter[0] += 1
    return _sms_id_counter[0]


# এই মেথডগুলোর ডিপোজিট সবসময় ম্যানুয়ালি Admin রিভিউ করে Approve/Reject করা হবে
# (bKash/Nagad/Rocket/Binance -> TrxID যাচাই করে Admin নিজে Approve করবে)।
# bot_settings["deposit_methods"] এ এর বাইরে যেকোনো মেথড থাকলে সেটা সাথে সাথে
# (কোনো Admin রিভিউ ছাড়াই) অটো-অ্যাপ্রুভ হয়ে যাবে।
DEPOSIT_MANUAL_METHODS = ["bKash", "Nagad", "Rocket", "Binance"]

# এই কয়টা মেথডেই SMS/নোটিফিকেশন Forwarder App থেকে আসা মেসেজের সাথে মিলিয়ে অটো-অ্যাপ্রুভ
# করা হয়। bKash/Nagad/Rocket -> TrxID + Amount; Binance -> Binance Username + USDT Amount
# (ইউজারের সাবমিট করা username ও USDT amount নোটিফিকেশনের সাথে হুবহু মিললে তবেই)।
# না মিললে deposit pending থাকে এবং Admin ম্যানুয়ালি Approve/Reject করতে পারে।
SMS_AUTO_APPROVE_METHODS = ["bKash", "Nagad", "Rocket", "Binance"]

# ---------------------------------------------------------------------------
# BOT SETTINGS (runtime-editable, Admin Panel -> ⚙️ Bot Settings থেকে বদলানো যায়,
# প্রতিটা পরিবর্তনের পর save_db() কল হয়ে ডিস্কে persist হয়ে যায়)
# ---------------------------------------------------------------------------
bot_settings = {
    "referral_bonus": REFERRAL_BONUS,   # প্রতি রেফারেলে বোনাস (BDT)
    "min_deposit": 0,                   # 0 মানে কোনো সীমা সেট করা নেই
    "max_deposit": 0,                   # 0 মানে কোনো সীমা সেট করা নেই
    "maintenance_mode": False,          # True হলে সাধারণ ইউজাররা বট ব্যবহার করতে পারবে না
    "deposit_methods": ["bKash", "Nagad", "Rocket", "Binance"],  # কমা-আলাদা তালিকা, Admin থেকে এডিট হয়
    "deposit_numbers": {                # প্রতিটা মেথডের পেমেন্ট নাম্বার/অ্যাড্রেস (Admin প্যানেল থেকে সেট হবে)
        "bKash": "",
        "Nagad": "",
        "Rocket": "",
        "Binance": "",
    },
    "usd_rate": 0,                       # 1 USD = কত BDT (Admin Panel থেকে সেট হবে; 0 মানে সেট করা নেই)
    "support_username": "",              # 🆘 Support বাটনের "24/7 live chat" এর জন্য (@ ছাড়া বা সহ, দুটোই চলবে)
    "method_videos": [],                 # ⚙️ Method বাটনে দেখানো টিউটোরিয়াল ভিডিওর তালিকা: [{"title": ..., "link": ...}, ...]
    "catalog": {},                       # 🧩 প্রোডাক্ট ON/OFF ও rename ওভাররাইড (দেখুন: PRODUCT CATALOG)
    "premium_emoji": {},                 # 💎 নরমাল emoji -> Premium custom emoji ID ম্যাপ (দেখুন: PREMIUM EMOJI সেকশন)
    "premium_emoji_enabled": True,       # False হলে Premium emoji বন্ধ, নরমাল emoji দেখাবে
    "force_join_channels": [],           # 🔐 Force Join চ্যানেল/গ্রুপের তালিকা: [{"name": ..., "link": ..., "chat_id": ...}, ...]
}

# 💾 DB Import এ "ঠিক আগের অবস্থায় ফেরত" নিশ্চিত করতে ডিফল্ট সেটিংসের একটা কপি রাখা হয়
# (restore এর সময় আগে ডিফল্টে রিসেট, তারপর ব্যাকআপের সেটিংস বসে — যাতে বর্তমানের কোনো বাড়তি
# সেটিং/ম্যাপ ব্যাকআপের সাথে মিশে না যায়)।
_BOT_SETTINGS_DEFAULTS = copy.deepcopy(bot_settings)

# navigation state per user, e.g. {"menu": "buy_mail"}
user_state = {}


def get_user(message_or_call):
    """Ensure user exists in temp store and return the user dict."""
    u = message_or_call.from_user
    uid = u.id
    if uid not in users:
        users[uid] = {
            "full_name": (u.first_name or "") + ((" " + u.last_name) if u.last_name else ""),
            "username": f"@{u.username}" if u.username else "N/A",
            "balance": 0,
            "total_purchased": 0,
            "today_spent": 0,
            "today_deposit": 0,
            "referrals": 0,
            "earned": 0,
            "referred_by": None,   # কে রেফার করেছে (user_id), একবারই সেট হবে
            "kb_version": KEYBOARD_VERSION,   # কীবোর্ড লেআউট ভার্সন (পুরোনো কীবোর্ড অটো রিফ্রেশের জন্য)
        }
    return users[uid]


def is_admin(user_id):
    return user_id in ADMIN_IDS


def maintenance_block(ctx):
    """Maintenance mode চালু থাকলে non-admin ইউজারদের ব্লক করে True রিটার্ন করে।
    ctx একটি message অথবা callback হতে পারে।"""
    uid = ctx.from_user.id
    if bot_settings["maintenance_mode"] and not is_admin(uid):
        chat_id = ctx.chat.id if hasattr(ctx, "chat") else ctx.message.chat.id
        bot.send_message(
            chat_id,
            "🛠️ <b>Bot Update চলতেছে</b>\n\n"
            "সাময়িক অসুবিধার জন্য দুঃখিত। একটু পরে আবার চেষ্টা করুন।",
        )
        return True
    return False


# ---------------------------------------------------------------------------
# FORCE JOIN (Admin Panel -> 🔐 Force Join থেকে এডমিন চ্যানেল/গ্রুপ যুক্ত করবে,
# ইউজার প্রথমবার /start দিলে সেগুলোতে জয়েন করতে বলা হবে, জয়েন না করা পর্যন্ত
# বট ব্যবহার করতে পারবে না)
# ---------------------------------------------------------------------------
def get_force_join_channels():
    return bot_settings.get("force_join_channels", [])


def check_user_joined_all(user_id):
    """সব ফোর্স-জয়েন চ্যানেল/গ্রুপে ইউজার জয়েন করেছে কিনা লাইভ চেক করে (Telegram API
    দিয়ে)। বট নিজে ঐ চ্যানেল/গ্রুপে Admin হিসেবে না থাকলে get_chat_member এরর দিতে
    পারে — নিরাপত্তার জন্য সেক্ষেত্রে not-joined (False) ধরে নেওয়া হয়।"""
    channels = get_force_join_channels()
    if not channels:
        return True
    for ch in channels:
        cid = ch.get("chat_id")
        if not cid:
            continue
        try:
            member = bot.get_chat_member(cid, user_id)
            if member.status in ("left", "kicked"):
                return False
        except Exception:
            return False
    return True


def force_join_prompt_inline():
    """ইউজারকে দেখানো জয়েন বাটন গুলো + ✅ Join Check বাটন।"""
    kb = types.InlineKeyboardMarkup(row_width=1)
    for ch in get_force_join_channels():
        title = ch.get("name") or "Channel"
        link = ch.get("link")
        if link:
            kb.add(types.InlineKeyboardButton(f"📣 {title}", url=link))
    kb.add(types.InlineKeyboardButton("🚪 Join Check", callback_data="check_join"))
    return kb


def send_force_join_prompt(chat_id):
    bot.send_message(
        chat_id,
        "🔐 <b>বট ব্যবহার করার আগে জয়েন করুন</b>\n\n"
        "নিচের চ্যানেল/গ্রুপ(গুলো)-তে জয়েন করুন, তারপর 👇 ✅ Join Check বাটনে ক্লিক করুন।",
        reply_markup=force_join_prompt_inline(),
    )


def require_force_join(ctx):
    """Force Join গেট। ইউজার এখনও সব চ্যানেল/গ্রুপে জয়েন না করে থাকলে জয়েন
    প্রম্পট পাঠিয়ে True (blocked) রিটার্ন করে; জয়েন থাকলে/এডমিন হলে/কোনো ফোর্স
    জয়েন চ্যানেল সেট করা না থাকলে False (not blocked) রিটার্ন করে। ctx একটি
    message অথবা callback হতে পারে।"""
    uid = ctx.from_user.id
    if is_admin(uid):
        return False
    if not get_force_join_channels():
        return False

    u = users.get(uid)
    if u and u.get("force_join_passed"):
        return False

    chat_id = ctx.chat.id if hasattr(ctx, "chat") else ctx.message.chat.id
    if check_user_joined_all(uid):
        if u:
            u["force_join_passed"] = True
            save_db()
        return False

    user_state[uid] = {"menu": "force_join_wait"}
    send_force_join_prompt(chat_id)
    return True


def force_join_admin_inline():
    """Admin Panel -> 🔐 Force Join সাব-মেনু: বর্তমানে যুক্ত চ্যানেল/গ্রুপ
    (Remove বাটনসহ) + নতুন যুক্ত করার বাটন।"""
    kb = types.InlineKeyboardMarkup(row_width=1)
    channels = get_force_join_channels()
    if not channels:
        kb.add(types.InlineKeyboardButton("🕳️ কোনো চ্যানেল/গ্রুপ যুক্ত নেই", callback_data="fj_noop"))
    else:
        for i, ch in enumerate(channels):
            title = ch.get("name") or "Channel"
            kb.add(types.InlineKeyboardButton(f"🗑️ Remove: {title}", callback_data=f"fj_remove_{i}"))
    kb.add(types.InlineKeyboardButton("➕ Add Channel/Group", callback_data="fj_add"))
    kb.add(types.InlineKeyboardButton("⬅️ Back", callback_data="fj_back"))
    return kb


def method_video_admin_inline():
    """⚙️ Method এর টিউটোরিয়াল ভিডিও বাটন ম্যানেজ করার সাব-মেনু: বর্তমান
    ভিডিও বাটনগুলো (Remove সহ) + নতুন যুক্ত করার বাটন।"""
    kb = types.InlineKeyboardMarkup(row_width=1)
    videos = bot_settings.get("method_videos") or []
    if not videos:
        kb.add(types.InlineKeyboardButton("📭 কোনো ভিডিও বাটন যুক্ত নেই", callback_data="mv_noop"))
    else:
        for i, v in enumerate(videos):
            kb.add(types.InlineKeyboardButton(f"✂️ Remove: {v['title']}", callback_data=f"mv_remove_{i}"))
    kb.add(types.InlineKeyboardButton("🎬 Add New Video", callback_data="mv_add"))
    kb.add(types.InlineKeyboardButton("⬅️ Back", callback_data="mv_back"))
    return kb


def fmt_amount(value):
    """সব জায়গায় একই ফরম্যাটে টাকা দেখানোর জন্য: 100৳ ($0.91)
    bot_settings["usd_rate"] (1 USD = কত BDT) অনুযায়ী ডলার হিসাব করা হয়;
    রেট সেট করা না থাকলে (0) BDT ভ্যালুটাই ডলার হিসেবে দেখানো হয়।"""
    rate = bot_settings.get("usd_rate") or 0
    usd = (value / rate) if rate > 0 else value
    return f"{value}৳ (${usd:.2f})"


def safe_edit_or_send(chat_id, msg_id, text, reply_markup=None):
    """একটামাত্র মেসেজ এডিট করে ধাপে ধাপে ফ্লো দেখানোর জন্য কমন হেল্পার
    (যেমন Deposit ফ্লো)। msg_id থাকলে সেই মেসেজটা এডিট করার চেষ্টা করে;
    এডিট ফেইল করলে (৪৮ ঘণ্টা পার হয়ে গেছে / মেসেজ ডিলিট হয়ে গেছে ইত্যাদি)
    fallback হিসেবে নতুন মেসেজ পাঠায়। সবসময় (edit হোক বা নতুন পাঠানো হোক)
    বর্তমান "অ্যাংকর" মেসেজের message_id রিটার্ন করে, যাতে পরের ধাপেও সেটাই
    এডিট করা যায়।"""
    if msg_id:
        try:
            bot.edit_message_text(
                text,
                chat_id=chat_id,
                message_id=msg_id,
                reply_markup=reply_markup,
            )
            return msg_id
        except Exception:
            pass
    sent = bot.send_message(chat_id, text, reply_markup=reply_markup)
    return sent.message_id


# ---------------------------------------------------------------------------
# KEYBOARDS (Reply / Main menu)
# ---------------------------------------------------------------------------
class StyledKeyboardButton(types.KeyboardButton):
    """রঙিন রিপ্লাই-কীবোর্ড বাটন (Bot API 9.4 `style`): "success" = সবুজ, "primary" = নীল,
    "danger" = লাল। পুরোনো ক্লায়েন্টে রঙ না দেখালেও বাটন স্বাভাবিকভাবে কাজ করে।"""

    def __init__(self, text, style=None, **kwargs):
        super().__init__(text, **kwargs)
        self.style = style

    def to_dict(self):
        d = super().to_dict()
        if isinstance(d, dict) and self.style:
            d["style"] = self.style
        return d


# সব Inline বাটন ডিফল্টভাবে নীল ("primary")। অন্য রঙ: "success" (সবুজ) / "danger" (লাল);
# None দিলে ডিফল্ট রঙ (রঙ বন্ধ)। কোনো বাটনে আলাদা style সেট করা থাকলে সেটাই থাকবে।
INLINE_BUTTON_STYLE = "primary"

_orig_inline_button_to_dict = types.InlineKeyboardButton.to_dict


def _inline_button_to_dict_styled(self):
    d = _orig_inline_button_to_dict(self)
    style = d.get("style") if isinstance(d, dict) else None
    style = style or getattr(self, "style", None) or INLINE_BUTTON_STYLE
    if isinstance(d, dict) and style:
        d["style"] = style
    return d


types.InlineKeyboardButton.to_dict = _inline_button_to_dict_styled


def main_menu_keyboard(user_id):
    kb = types.ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    # উপরের ৪টা বাটন সবুজ, Support ও Method নীল
    kb.add(
        StyledKeyboardButton("🛒 Buy", style="success"),
        StyledKeyboardButton("💳 Deposit", style="success"),
    )
    kb.add(
        StyledKeyboardButton("🎁 Referral", style="success"),
        StyledKeyboardButton("👤 Profile", style="success"),
    )
    kb.add(
        StyledKeyboardButton("🆘 Support", style="primary"),
        StyledKeyboardButton("⚙️ Method", style="primary"),
    )
    if is_admin(user_id):
        kb.add(types.KeyboardButton("👮 Admin Panel"))
    return kb


def back_to_main_keyboard():
    kb = types.ReplyKeyboardMarkup(resize_keyboard=True)
    kb.add(types.KeyboardButton("🏠 Back to Menu"))
    return kb


def back_only_keyboard():
    """শুধু Back বাটনসহ কীবোর্ড — Bulk Buy quantity ইনপুট ধাপে ব্যবহার হয়,
    এখান থেকে Back করলে buy মেনুতে (main menu তে নয়) ফিরে যায়।"""
    kb = types.ReplyKeyboardMarkup(resize_keyboard=True)
    kb.add(types.KeyboardButton("⬅️ Back"))
    return kb


# ---------------------------------------------------------------------------
# KEYBOARDS (Inline)
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
# 🧩 PRODUCT CATALOG: Buy মেনুর ক্যাটাগরি/প্রোডাক্ট। Admin Panel -> 🧩 Products থেকে
# প্রতিটার ON/OFF ও নাম (rename) বদলানো যায়; বদল bot_settings["catalog"] এ সেভ হয়।
# ---------------------------------------------------------------------------
CATALOG = {
    "proxy":     {"name": "Proxy",     "parent": None},
    "vpn":       {"name": "VPN",       "parent": None},
    "mail":      {"name": "Mail",      "parent": None},
    "px9":       {"name": "9Proxy",     "parent": "proxy"},
    "pxowl":     {"name": "Owl Proxy",  "parent": "proxy"},
    "pxcli":     {"name": "Cli Proxy",  "parent": "proxy"},
    "pxabc":     {"name": "Abc Proxy",  "parent": "proxy"},
    "px711":     {"name": "711Proxy",   "parent": "proxy"},
    "hotmail":   {"name": "Hotmail",    "parent": "mail"},
    "outlook":   {"name": "Outlook",    "parent": "mail"},
    "outlookfr": {"name": "Outlook.fr", "parent": "mail"},
    "vpn3":      {"name": "3days VPN",  "parent": "vpn"},
    "vpn7":      {"name": "7days VPN",  "parent": "vpn"},
    "vpn14":     {"name": "14days VPN", "parent": "vpn"},
    "vpn30":     {"name": "30Days VPN", "parent": "vpn"},
}

# VPN প্যাকেজ (3/7/14/30 days) এর প্রতিটার ভেতরে ১০টা করে বাটন। Admin Panel -> 🧩 Products
# থেকে প্রতিটার নাম বদলানো ও ON/OFF করা যায় (প্যাকেজের পাশের 📂 বাটনে চাপলে ১০টা দেখাবে)।
VPN_SUB_COUNT = 10
VPN_GROUPS = ("vpn3", "vpn7", "vpn14", "vpn30")
# 🌐 Proxy: 9Proxy / Owl / Cli / 711Proxy / Abc Proxy এর প্রতিটার ভেতরে ৪টা করে বাটন
PROXY_SUB_COUNT = 4
PROXY_GROUPS = ("px9", "pxowl", "pxcli", "px711", "pxabc")
GROUP_PARENTS = ("vpn", "proxy")   # যাদের ভেতরের বাটনগুলো আরেক ধাপ সাব-মেনুতে খোলে
for _grp in ("vpn3", "vpn7", "vpn14", "vpn30"):
    for _n in range(1, VPN_SUB_COUNT + 1):
        CATALOG[f"{_grp}_{_n}"] = {"name": f"Option {_n}", "parent": _grp}
for _grp in PROXY_GROUPS:
    for _n in range(1, PROXY_SUB_COUNT + 1):
        CATALOG[f"{_grp}_{_n}"] = {"name": f"Option {_n}", "parent": _grp}


# 💎 প্রতিটা প্রোডাক্ট/ক্যাটাগরি বাটনের নিজস্ব UNIQUE নরমাল emoji — বটের আর কোনো বাটন/মেনুতে এই
# emoji গুলো ব্যবহার হয় না, তাই Admin প্রতিটা বাটনের জন্য আলাদা Premium emoji সেট করতে পারবে
# (ম্যাপিং: নরমাল emoji -> Premium emoji, দেখুন PREMIUM EMOJI সেকশন / /emoji কমান্ড)।
# emoji শুধু বাটনের লেবেলে বসে — প্রোডাক্টের নাম (rename), অর্ডার, ডেটাবেস বা মেসেজে নয়।
CATALOG_BTN_EMOJI = {
    "proxy": "🧿",
    "vpn": "🔮",
    "mail": "💼",
    "px9": "🍀",
    "pxowl": "🦉",
    "pxcli": "🐙",
    "pxabc": "🍎",
    "px711": "🍊",
    "hotmail": "🔥",
    "outlook": "🌊",
    "outlookfr": "🥐",
    "vpn3": "🥝",
    "vpn7": "🍇",
    "vpn14": "🍓",
    "vpn30": "🍋",
    "vpn3_1": "🍌",
    "vpn3_2": "🍉",
    "vpn3_3": "🍒",
    "vpn3_4": "🍑",
    "vpn3_5": "🍍",
    "vpn3_6": "🥭",
    "vpn3_7": "🍐",
    "vpn3_8": "🍈",
    "vpn3_9": "🥥",
    "vpn3_10": "🍅",
    "vpn7_1": "🥑",
    "vpn7_2": "🌽",
    "vpn7_3": "🥕",
    "vpn7_4": "🥦",
    "vpn7_5": "🍄",
    "vpn7_6": "🌰",
    "vpn7_7": "🍞",
    "vpn7_8": "🧀",
    "vpn7_9": "🍔",
    "vpn7_10": "🍕",
    "vpn14_1": "🌮",
    "vpn14_2": "🍩",
    "vpn14_3": "🍪",
    "vpn14_4": "🍫",
    "vpn14_5": "🍿",
    "vpn14_6": "🍬",
    "vpn14_7": "🍭",
    "vpn14_8": "🍦",
    "vpn14_9": "🍰",
    "vpn14_10": "🥧",
    "vpn30_1": "🍯",
    "vpn30_2": "🥜",
    "vpn30_3": "🥨",
    "vpn30_4": "🥞",
    "vpn30_5": "🧇",
    "vpn30_6": "🥓",
    "vpn30_7": "🥩",
    "vpn30_8": "🍗",
    "vpn30_9": "🍖",
    "vpn30_10": "🌭",
    "px9_1": "🍟",
    "px9_2": "🥪",
    "px9_3": "🌯",
    "px9_4": "🥙",
    "pxowl_1": "🧆",
    "pxowl_2": "🥚",
    "pxowl_3": "🍳",
    "pxowl_4": "🥘",
    "pxcli_1": "🍲",
    "pxcli_2": "🥗",
    "pxcli_3": "🍱",
    "pxcli_4": "🍣",
    "px711_1": "🍤",
    "px711_2": "🍙",
    "px711_3": "🍚",
    "px711_4": "🍘",
    "pxabc_1": "🍥",
    "pxabc_2": "🥮",
    "pxabc_3": "🍢",
    "pxabc_4": "🍡",
}


def _btn_emoji(key):
    return CATALOG_BTN_EMOJI.get(key, "")


def _prod_btn_label(key, text=None):
    """প্রোডাক্ট বাটনের লেবেল: '<unique emoji> <নাম>' (emoji না থাকলে শুধু নাম)"""
    t = catalog_name(key) if text is None else text
    e = _btn_emoji(key)
    return f"{e} {t}" if e else t


def catalog_name(key):
    ov = (bot_settings.get("catalog") or {}).get(key, {})
    return ov.get("name") or CATALOG[key]["name"]


def catalog_on(key):
    """নিজে ON আছে কিনা (প্যারেন্ট ক্যাটাগরি OFF থাকলে সেটাও ধরা হয়)"""
    ov = (bot_settings.get("catalog") or {}).get(key, {})
    if not ov.get("enabled", True):
        return False
    parent = CATALOG[key]["parent"]
    return catalog_on(parent) if parent else True


def catalog_children(key):
    return [k for k, v in CATALOG.items() if v["parent"] == key]


def catalog_visible(key):
    """ON আছে এবং (ক্যাটাগরি হলে) অন্তত একটা সাব-প্রোডাক্ট ON আছে"""
    if key not in CATALOG or not catalog_on(key):
        return False
    kids = catalog_children(key)
    return (not kids) or any(catalog_on(k) for k in kids)


def _prod_name(key):
    """প্রোডাক্টের দেখানোর নাম: catalog এ থাকলে (rename সহ) সেটা, নাহলে products এর নাম"""
    if key in CATALOG:
        return catalog_name(key)
    return (products.get(key) or {}).get("name", key)


def _is_vpn_sub(key):
    """VPN প্যাকেজের (3days/7days/14days/30Days) ভেতরের ১০টা বাটনের একটা কিনা"""
    return key in CATALOG and CATALOG[key]["parent"] in VPN_GROUPS


def _is_proxy_sub(key):
    """Proxy প্যাকেজের (Owl/9Proxy/711Proxy/Abc) ভেতরের ৪টা বাটনের একটা কিনা"""
    return key in CATALOG and CATALOG[key]["parent"] in PROXY_GROUPS


def _is_group_sub(key):
    return _is_vpn_sub(key) or _is_proxy_sub(key)


def _stock_kind(key):
    return "vpn" if _is_vpn_sub(key) else "proxy" if _is_proxy_sub(key) else "mail"


def _is_stock_key(key):
    """যেসব প্রোডাক্টের নাম/দাম/স্টক আছে এবং কেনা যায় (Mail + VPN সাব-বাটন + Proxy সাব-বাটন)"""
    return key in CATALOG and (CATALOG[key]["parent"] == "mail" or _is_group_sub(key))


def _ensure_mail_products():
    """Mail ও VPN সাব-বাটনগুলোর জন্য products এ price/stock এন্ট্রি নিশ্চিত করে।"""
    for k in catalog_children("mail") + [x for g in VPN_GROUPS + PROXY_GROUPS for x in catalog_children(g)]:
        p = products.setdefault(k, {"name": CATALOG[k]["name"], "price": 0, "stock": 0, "description": "", "stock_list": []})
        p.setdefault("stock_list", [])
        p.setdefault("price", 0)
        p.setdefault("description", "")
        p["name"] = catalog_name(k)          # rename হলে এখানেও মিলে যায়
        p["stock"] = len(p["stock_list"])


def _order_account_text(order):
    num = str(order.get("number", "N/A"))
    extra = str(order.get("otp_link", "") or "")
    if extra and extra != "N/A" and not extra.startswith("📎") and order.get("qty", 1) == 1:
        return f"{num}|{extra}"
    return num


def _cat_btn(key, prefix):
    return types.InlineKeyboardButton(_prod_btn_label(key), callback_data=f"{prefix}{key}")


# Telegram এ inline বাটনের প্রস্থ মেসেজ বাবলের প্রস্থের সাথে বাঁধা। তাই বাবলকে সর্বোচ্চ প্রস্থে
# নিতে মেসেজের শেষে অদৃশ্য ক্যারেক্টারের (Hangul filler, ১ ক্যারেক্টার ≈ ১ অক্ষর-প্রস্থ) একটা লাইন
# যোগ করা হয়। লাইনটা স্ক্রিনের প্রস্থের চেয়ে লম্বা, তাই বাবল সর্বোচ্চ প্রস্থ পর্যন্ত চওড়া হয়।
# বাটন আরও চওড়া/সরু করতে BUY_PAD_CHARS বদলান (খুব বেশি দিলে নিচে ফাঁকা লাইন বেড়ে যায়)।
BUY_PAD_CHARS = 30
PROXY_PAD_CHARS = 40       # Proxy মেনুর বাটন-প্রস্থ (বাড়ালে বাটন আরও চওড়া)
VPN_PAD_CHARS = 40         # VPN মেনুর (প্যাকেজ তালিকা) বাটন-প্রস্থ
VPN_SUB_PAD_CHARS = 60     # প্রতিটা VPN প্যাকেজের ভেতরের ১০টা বাটনের মেনুর প্রস্থ
PROXY_SUB_PAD_CHARS = 60   # প্রতিটা Proxy প্যাকেজের ভেতরের ৪টা বাটনের মেনুর প্রস্থ
BUY_MAIN_TEXT = "🛒 <b>Buy</b>\n\nকোন ক্যাটাগরি কিনতে চান?\n" + ("\u3164" * BUY_PAD_CHARS)


def _wide(text, group=None):
    """Proxy মেনু ও Proxy প্যাকেজের সাব-মেনুর মেসেজ চওড়া করে (বাটনও চওড়া হয়) — Buy মেনুর মতোই।
    group=None বা Proxy এর প্যাকেজ হলে অদৃশ্য লাইন যোগ হয়; VPN/Mail এর মেসেজ অপরিবর্তিত থাকে।"""
    if group is None:
        return text + "\n" + ("\u3164" * PROXY_PAD_CHARS)
    if group == "__vpn__":
        return text + "\n" + ("\u3164" * VPN_PAD_CHARS)
    if group in CATALOG and CATALOG[group]["parent"] == "proxy":
        return text + "\n" + ("\u3164" * PROXY_SUB_PAD_CHARS)
    if group in CATALOG and CATALOG[group]["parent"] == "vpn":
        return text + "\n" + ("\u3164" * VPN_SUB_PAD_CHARS)
    return text


def buy_main_inline():
    """Buy মেনু: প্রথম সারিতে ২টা, বাকিগুলো পুরো প্রস্থে, সবার নিচে Cancel।
    (ডিফল্ট: Proxy | VPN, তার নিচে Mail, তার নিচে Cancel)"""
    kb = types.InlineKeyboardMarkup()
    keys = [k for k in ("proxy", "vpn", "mail") if catalog_visible(k)]
    if len(keys) >= 2:
        kb.row(_cat_btn(keys[0], "buy_"), _cat_btn(keys[1], "buy_"))
        keys = keys[2:]
    for k in keys:
        kb.row(_cat_btn(k, "buy_"))
    kb.row(types.InlineKeyboardButton("❌ Cancel", callback_data="buy_cancel"))
    return kb


def buy_mail_inline():
    """Mail ক্যাটাগরি: ON থাকা প্রোডাক্টগুলো প্রতি সারিতে ১টা (1 by 1), সবার নিচে Back"""
    kb = types.InlineKeyboardMarkup()
    for k in catalog_children("mail"):
        if catalog_on(k):
            kb.row(_cat_btn(k, "buyitem_"))
    kb.row(types.InlineKeyboardButton("⬅️ Back", callback_data="buy_back"))
    return kb


def buy_proxy_inline():
    """Proxy ক্যাটাগরি: ON থাকা প্রোডাক্টগুলো 2x2 আকারে, সবার নিচে Back একা"""
    kb = types.InlineKeyboardMarkup()
    btns = [_cat_btn(k, "buyitem_") for k in catalog_children("proxy") if catalog_visible(k)]
    for i in range(0, len(btns), 2):
        kb.row(*btns[i:i + 2])
    kb.row(types.InlineKeyboardButton("⬅️ Back", callback_data="buy_back"))
    return kb


def buy_vpn_inline():
    """VPN ক্যাটাগরি: ON থাকা প্যাকেজগুলো 2x2, নিচে Back"""
    kb = types.InlineKeyboardMarkup()
    btns = [_cat_btn(k, "buyitem_") for k in catalog_children("vpn") if catalog_visible(k)]
    for i in range(0, len(btns), 2):
        kb.row(*btns[i:i + 2])
    kb.row(types.InlineKeyboardButton("⬅️ Back", callback_data="buy_back"))
    return kb


def buy_vpn_sub_inline(group):
    """প্যাকেজের ভেতরের ON থাকা বাটন: Proxy প্যাকেজে প্রতি সারিতে ১টা (1 by 1), VPN প্যাকেজে 2x2; নিচে Back"""
    kb = types.InlineKeyboardMarkup()
    btns = [_cat_btn(k, "buyitem_") for k in catalog_children(group) if catalog_on(k)]
    per_row = 1 if CATALOG[group]["parent"] == "proxy" else 2   # Proxy প্যাকেজের ৪টা বাটন 1 by 1, VPN এর 2x2
    for i in range(0, len(btns), per_row):
        kb.row(*btns[i:i + per_row])
    kb.row(types.InlineKeyboardButton("⬅️ Back", callback_data=f"buy_{CATALOG[group]['parent']}"))
    return kb


def referral_inline():
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton("🔗 Share your link and earn!", switch_inline_query="join_now"))
    return kb


def upload_file_product_inline():
    """Admin ফাইল আপলোডের আগে কোন প্রোডাক্টের স্টক আপডেট হবে সেটা বেছে নেয়।"""
    kb = types.InlineKeyboardMarkup(row_width=2)
    _ensure_mail_products()
    for key, p in products.items():
        if _is_group_sub(key):
            continue
        kb.add(types.InlineKeyboardButton(_prod_btn_label(key, _prod_name(key)), callback_data=f"uploadprod_{key}"))
    for g in VPN_GROUPS + PROXY_GROUPS:
        kb.add(types.InlineKeyboardButton(_prod_btn_label(g), callback_data=f"vpnpick_u_{g}"))
    return kb


def upload_confirm_inline():
    """Stock ফাইল parse হওয়ার পর আসলে stock এ যুক্ত করার আগে কনফার্মেশন।"""
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(
        types.InlineKeyboardButton("🆗 Confirm & Add", callback_data="stockup_confirm"),
        types.InlineKeyboardButton("❌ Cancel", callback_data="stockup_cancel"),
    )
    return kb


def stock_broadcast_confirm_inline():
    """নতুন Stock Add হওয়ার পর সেই আপডেটটা সব ইউজারকে broadcast করবে কিনা জিজ্ঞেস করে।"""
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(
        types.InlineKeyboardButton("🔊 হ্যাঁ, Broadcast করুন", callback_data="stockbroadcast_yes"),
        types.InlineKeyboardButton("🙅 না", callback_data="stockbroadcast_no"),
    )
    return kb


def deposit_balance_inline():
    """Deposit ফ্লো শুরু হওয়ার সময় Balance স্ক্রিনে দেখানো ➕ Deposit বাটন।"""
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton("💸 Deposit", callback_data="dep_start"))
    return kb


# প্রতিটা Deposit মেথডের জন্য আলাদা (unique) নরমাল emoji — Premium emoji ম্যাপ করার সুবিধার জন্য।
# অন্য কোনো মেথড যোগ করলে 🪙 দেখাবে।
METHOD_EMOJI = {
    "bkash": "🌸",
    "nagad": "🟠",
    "rocket": "🚀",
    "binance": "🟡",
}


def method_emoji(name):
    return METHOD_EMOJI.get(str(name).strip().lower(), "🪙")


def deposit_methods_inline():
    """ইউজারকে Deposit মেথড বেছে নেওয়ার বাটন দেখায় (bot_settings['deposit_methods'] থেকে),
    ২টা করে এক সারিতে গ্রিড আকারে।"""
    kb = types.InlineKeyboardMarkup(row_width=2)
    buttons = [
        types.InlineKeyboardButton(f"{method_emoji(m)} {m}", callback_data=f"depmethod_{m}")
        for m in bot_settings["deposit_methods"]
    ]
    for i in range(0, len(buttons), 2):
        kb.row(*buttons[i:i + 2])
    kb.add(types.InlineKeyboardButton("⬅️ Back", callback_data="dep_back"))
    return kb


def deposit_cancel_inline():
    """Deposit amount ইনপুট ধাপে Back এর বদলে দেখানো Cancel বাটন।"""
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton("❌ Cancel", callback_data="deposit_cancel"))
    return kb


def deposit_review_inline(dep_id):
    """Admin কে পাঠানো pending deposit নোটিফিকেশনে Approve/Reject বাটন।"""
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(
        types.InlineKeyboardButton("✅ Approve", callback_data=f"depapprove_{dep_id}"),
        types.InlineKeyboardButton("🚫 Reject", callback_data=f"depreject_{dep_id}"),
    )
    return kb


def _track_deposit_admin_msg(dep, chat_id, message_id):
    """যতগুলো Admin-কে (বা যতবার Pending Deposits লিস্টে) এই deposit-এর
    Approve/Reject বাটনসহ মেসেজ পাঠানো হয়েছে, তার chat_id/message_id মনে রাখে।
    যাতে একজন Admin Approve/Reject করার পর বাকি সব কপি থেকেও বাটন সরিয়ে দেওয়া যায়
    (অন্য কোনো Admin যেন পুরনো বাটনে ক্লিক করে বিভ্রান্ত না হয়)।"""
    dep.setdefault("admin_msgs", []).append({"chat_id": chat_id, "message_id": message_id})


def _clear_deposit_admin_buttons(dep):
    """dep['admin_msgs'] এ জমা থাকা সব মেসেজ থেকে Approve/Reject বাটন সরিয়ে দেয়
    (best-effort — কোনো মেসেজ এডিট করতে না পারলে চুপচাপ স্কিপ করে)।"""
    for ref in dep.get("admin_msgs", []):
        try:
            bot.edit_message_reply_markup(ref["chat_id"], ref["message_id"], reply_markup=None)
        except Exception:
            pass


def deposit_numbers_inline():
    """Admin প্যানেলে ম্যানুয়াল মেথডগুলোর পেমেন্ট নাম্বার/অ্যাড্রেস সেট করার বাটন।"""
    kb = types.InlineKeyboardMarkup(row_width=1)
    for m in DEPOSIT_MANUAL_METHODS:
        num = bot_settings["deposit_numbers"].get(m) or "❌ সেট করা নেই"
        kb.add(types.InlineKeyboardButton(f"{method_emoji(m)} {m}: {num}", callback_data=f"depnum_{m}"))
    kb.add(types.InlineKeyboardButton("⬅️ Back", callback_data="settings_back"))
    return kb


def set_price_product_inline():
    """Admin price পরিবর্তনের আগে কোন প্রোডাক্টের price বদলাবে সেটা বেছে নেয়।"""
    kb = types.InlineKeyboardMarkup(row_width=2)
    _ensure_mail_products()
    for key, p in products.items():
        if _is_group_sub(key):
            continue
        kb.add(types.InlineKeyboardButton(_prod_btn_label(key, _prod_name(key)), callback_data=f"priceprod_{key}"))
    for g in VPN_GROUPS + PROXY_GROUPS:
        kb.add(types.InlineKeyboardButton(_prod_btn_label(g), callback_data=f"vpnpick_p_{g}"))
    return kb


def vpn_pick_inline(mode, group):
    """Admin: VPN প্যাকেজের ১০টা বাটনের মধ্যে কোনটার স্টক আপলোড (u) / দাম সেট (p) হবে"""
    kb = types.InlineKeyboardMarkup(row_width=2)
    _ensure_mail_products()
    prefix = "uploadprod_" if mode == "u" else "priceprod_"
    btns = []
    for k in catalog_children(group):
        p = products.get(k) or {}
        label = _prod_btn_label(k, f"{catalog_name(k)} · {len(p.get('stock_list') or [])}")
        btns.append(types.InlineKeyboardButton(label, callback_data=f"{prefix}{k}"))
    for i in range(0, len(btns), 2):
        kb.row(*btns[i:i + 2])
    kb.row(types.InlineKeyboardButton("⬅️ Back", callback_data=f"vpnpick_{mode}_back"))
    return kb


@bot.callback_query_handler(func=lambda c: c.data.startswith("vpnpick_") and is_admin(c.from_user.id))
def cb_vpn_pick(call):
    _, mode, group = call.data.split("_", 2)
    bot.answer_callback_query(call.id)
    if group == "back":
        text = "📤 কোন প্রোডাক্টের জন্য স্টক ফাইল আপলোড করবেন?" if mode == "u" else "💰 কোন প্রোডাক্টের price পরিবর্তন করবেন?"
        kb = upload_file_product_inline() if mode == "u" else set_price_product_inline()
    elif group in VPN_GROUPS + PROXY_GROUPS:
        text = f"📂 <b>{_html.escape(catalog_name(group))}</b> — কোন বাটন?"
        kb = vpn_pick_inline(mode, group)
    else:
        return
    try:
        bot.edit_message_text(text, call.message.chat.id, call.message.message_id, reply_markup=kb)
    except Exception:
        bot.send_message(call.message.chat.id, text, reply_markup=kb)


def admin_panel_inline():
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(
        types.InlineKeyboardButton("📤 Upload File", callback_data="admin_upload_file"),
        types.InlineKeyboardButton("💰 Set Price", callback_data="admin_set_price_stock"),
    )
    kb.add(
        types.InlineKeyboardButton("💱 Set Dollar Rate", callback_data="admin_set_usd_rate"),
    )
    kb.add(
        types.InlineKeyboardButton("👥 Users List", callback_data="admin_users_list"),
        types.InlineKeyboardButton("📊 Statistics", callback_data="admin_statistics"),
    )
    kb.add(
        types.InlineKeyboardButton("🔎 User Info", callback_data="admin_user_info"),
        types.InlineKeyboardButton("📈 Sells Inventory", callback_data="sellinv_menu"),
    )
    kb.add(
        types.InlineKeyboardButton("📢 Broadcast", callback_data="admin_broadcast"),
        types.InlineKeyboardButton("💵 Add/Remove Balance", callback_data="admin_balance_edit"),
    )
    kb.add(
        types.InlineKeyboardButton("🧾 Orders", callback_data="admin_orders"),
        types.InlineKeyboardButton("🎛️ Bot Settings", callback_data="admin_bot_settings"),
    )
    kb.add(
        types.InlineKeyboardButton("🏦 Deposit Requests", callback_data="admin_deposit_requests"),
        types.InlineKeyboardButton("📮 Deposit Numbers", callback_data="admin_deposit_numbers"),
    )
    kb.add(
        types.InlineKeyboardButton("🗄️ Export DB", callback_data="admin_export_db"),
        types.InlineKeyboardButton("📥 Import DB", callback_data="admin_import_db"),
    )
    kb.add(types.InlineKeyboardButton("📦 Unsold Product Export", callback_data="admin_export_unsold"))
    kb.add(types.InlineKeyboardButton("🧩 Products (ON/OFF · Rename)", callback_data="pcat_list"))
    kb.add(types.InlineKeyboardButton("🔐 Force Join", callback_data="admin_force_join"))
    kb.add(types.InlineKeyboardButton("🏠 Back to Menu", callback_data="admin_back_to_menu"))
    return kb


def bot_settings_inline():
    """⚙️ Bot Settings সাব-মেনু: বর্তমান ভ্যালুসহ বাটন দেখায়, চাপলে বদলানো যায়।"""
    kb = types.InlineKeyboardMarkup(row_width=1)
    kb.add(
        types.InlineKeyboardButton(
            f"🤝 Referral Bonus: {bot_settings['referral_bonus']} BDT",
            callback_data="settings_referral_bonus",
        )
    )
    kb.add(
        types.InlineKeyboardButton(
            f"🧮 Deposit Limit: {bot_settings['min_deposit']} - {bot_settings['max_deposit']} BDT",
            callback_data="settings_deposit_limits",
        )
    )
    kb.add(
        types.InlineKeyboardButton(
            "🏧 Deposit Methods: " + ", ".join(bot_settings["deposit_methods"]),
            callback_data="settings_deposit_methods",
        )
    )
    kb.add(
        types.InlineKeyboardButton(
            "🛠️ Maintenance Mode: " + ("✅ ON" if bot_settings["maintenance_mode"] else "❌ OFF"),
            callback_data="settings_toggle_maintenance",
        )
    )
    kb.add(
        types.InlineKeyboardButton(
            "🙋 Support Username: " + (bot_settings["support_username"] or "সেট করা নেই"),
            callback_data="settings_support_username",
        )
    )
    kb.add(
        types.InlineKeyboardButton(
            f"📹 Method Videos: {len(bot_settings['method_videos'])} টি যুক্ত আছে",
            callback_data="settings_method_video",
        )
    )
    kb.add(types.InlineKeyboardButton("⬅️ Back", callback_data="settings_back"))
    return kb


# ---------------------------------------------------------------------------
# TEXT TEMPLATES
# ---------------------------------------------------------------------------
def profile_text(u):
    """প্রোফাইলের ডিটেইলস Bold লেবেল ফরম্যাটে; শুধু User ID <code> (monospace) এ
    থাকে (কপি করার সুবিধার জন্য), বাকি সব ভ্যালু সাধারণ (regular) টেক্সটে থাকে।"""
    return (
        f"👤 <b>Profile</b>\n\n"
        f"🆔 <b>User ID:</b> <code>{u['id']}</code>\n"
        f"👤 <b>Full Name:</b> {u['full_name']}\n"
        f"📝 <b>Username:</b> {u['username']}\n"
        f"💰 <b>Balance:</b> {fmt_amount(u['balance'])}\n"
        f"📊 <b>Total Purchased:</b> {u['total_purchased']}\n"
        f"💸 <b>Today Spent:</b> {fmt_amount(u['today_spent'])}\n"
        f"💳 <b>Today Deposit:</b> {fmt_amount(u['today_deposit'])}"
    )


def referral_text(user_id, data):
    return (
        "🎁 <b>Referral Program</b>\n\n\n"
        f"🎁 Your Referral Link:\nhttps://t.me/{BOT_USERNAME}?start={user_id}\n\n"
        f"💰 Bonus per referral: {fmt_amount(bot_settings['referral_bonus'])}\n"
        f"👥 Total referrals: {data['referrals']}\n"
        f"💵 Total earned: {fmt_amount(data['earned'])}"
    )


def product_detail_text(p):
    return (
        f"<b>{p['name']}</b>\n\n"
        f"💵 Price: {fmt_amount(p['price'])}\n"
        f"📦 Total Stock: {p['stock']}\n"
        f"📝 Description: {p['description']}"
    )


def otp_link_display(otp_link):
    """আসল URL হলে ক্লিকযোগ্য লিংক হিসেবে, না হলে (যেমন 'N/A' বা placeholder) mono টেক্সট হিসেবে দেখায়।"""
    if otp_link and str(otp_link).startswith(("http://", "https://")):
        return f'<a href="{otp_link}">🔗 OTP Link</a>'
    return f"<code>{otp_link}</code>"


def purchase_success_text(order):
    return (
        "🎉 <b>Purchase Successful!</b>\n\n"
        f"🆔 <b>Order ID:</b> <code>{order['order_id']}</code>\n"
        f"📦 <b>Product:</b> <code>{order['product_name']}</code>\n"
        f"🔢 <b>Quantity:</b> <code>{order['qty']} pcs</code>\n"
        f"💵 <b>Per piece:</b> <code>{fmt_amount(order['price'])}</code>\n"
        f"💰 <b>Total:</b> <code>{fmt_amount(order['total'])}</code>\n"
        f"💳 <b>Remaining Balance:</b> <code>{fmt_amount(order['remaining_balance'])}</code>\n"
        f"📅 <b>Date:</b> <code>{order['date']}</code>\n\n"
        f"👨‍💻 <b>Account:</b> <code>{_order_account_text(order)}</code>"
    )


# ---------------------------------------------------------------------------
# /start
# ---------------------------------------------------------------------------
@bot.message_handler(commands=["start"])
def cmd_start(message):
    if maintenance_block(message):
        return

    uid = message.from_user.id
    is_new_user = uid not in users

    u = get_user(message)
    u["id"] = uid
    user_state[uid] = {"menu": "main"}
    if is_new_user:
        save_db()   # ✅ নতুন ইউজার তৈরি হলো, ডিস্কে persist করা হলো (persistent DB)

    # --- Referral: /start <referrer_id> ---
    parts = (message.text or "").split(maxsplit=1)
    if is_new_user and len(parts) > 1 and parts[1].strip().isdigit():
        referrer_id = int(parts[1].strip())
        if referrer_id != uid and referrer_id in users and not u.get("referred_by"):
            u["referred_by"] = referrer_id
            referrer = users[referrer_id]
            bonus = bot_settings["referral_bonus"]
            referrer["referrals"] += 1
            referrer["earned"] += bonus
            referrer["balance"] += bonus
            save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)
            try:
                bot.send_message(
                    referrer_id,
                    "🎉 <b>New Referral!</b>\n\n"
                    f"আপনার লিংক দিয়ে একজন নতুন ইউজার জয়েন করেছে।\n"
                    f"?? বোনাস যুক্ত হয়েছে: {fmt_amount(bonus)}",
                )
            except Exception:
                pass  # referrer হয়তো বটকে ব্লক করেছে

    # --- Force Join: চ্যানেল/গ্রুপ সেট করা থাকলে জয়েন না করা পর্যন্ত বট ব্যবহার করতে দেওয়া হবে না ---
    if not is_admin(uid) and get_force_join_channels() and not check_user_joined_all(uid):
        u["force_join_passed"] = False
        user_state[uid] = {"menu": "force_join_wait"}
        send_force_join_prompt(message.chat.id)
        return

    u["force_join_passed"] = True
    user_state[uid] = {"menu": "main"}
    bot.send_message(message.chat.id, profile_text(u), reply_markup=main_menu_keyboard(u["id"]))


@bot.callback_query_handler(func=lambda c: c.data == "check_join")
def cb_check_join(call):
    """✅ Join Check বাটন — জয়েন হয়ে থাকলে বট আনলক করে দেয়, নাহলে আবার জয়েন করতে বলে।"""
    uid = call.from_user.id
    chat_id = call.message.chat.id
    u = get_user(call)
    u["id"] = uid

    if is_admin(uid) or check_user_joined_all(uid):
        bot.answer_callback_query(call.id, "✅ ধন্যবাদ! আপনি সব চ্যানেলে জয়েন করেছেন।")
        u["force_join_passed"] = True
        save_db()
        user_state[uid] = {"menu": "main"}
        bot.send_message(chat_id, profile_text(u), reply_markup=main_menu_keyboard(u["id"]))
    else:
        bot.answer_callback_query(
            call.id,
            "❌ আপনি এখনও সব চ্যানেল/গ্রুপে জয়েন করেননি। আগে জয়েন করে আবার চেষ্টা করুন।",
            show_alert=True,
        )


# ---------------------------------------------------------------------------
# MAIN MENU (Reply keyboard) HANDLERS
# ---------------------------------------------------------------------------
@bot.message_handler(func=lambda m: m.text == "🛒 Buy")
def menu_buy(message):
    if maintenance_block(message):
        return
    if require_force_join(message):
        return
    user_state[message.from_user.id] = {"menu": "buy"}
    bot.send_message(message.chat.id, BUY_MAIN_TEXT, reply_markup=buy_main_inline())


@bot.message_handler(func=lambda m: m.text == "👤 Profile")
def menu_profile(message):
    if maintenance_block(message):
        return
    if require_force_join(message):
        return
    u = get_user(message)
    u["id"] = message.from_user.id
    user_state[message.from_user.id] = {"menu": "profile"}
    bot.send_message(message.chat.id, profile_text(u), reply_markup=main_menu_keyboard(u["id"]))


def deposit_balance_text(u):
    """Deposit ফ্লোর প্রথম ধাপ — বর্তমান ব্যালেন্স দেখানোর মেসেজ।"""
    return (
        "💳 <b>Deposit</b>\n\n"
        f"💰 <b>বর্তমান ব্যালেন্স:</b> <code>{fmt_amount(u['balance'])}</code>\n\n"
        "নিচের বাটনে ক্লিক করে ডিপোজিট শুরু করুন:"
    )


@bot.message_handler(func=lambda m: m.text == "💳 Deposit")
def menu_deposit(message):
    """Deposit ফ্লোর শুরু: Balance স্ক্রিন পাঠায় এবং তার message_id সেভ করে রাখে,
    যাতে পরের প্রতিটা ধাপ এই একটামাত্র মেসেজই এডিট করে দেখাতে পারে।"""
    if maintenance_block(message):
        return
    if require_force_join(message):
        return
    uid = message.from_user.id
    u = get_user(message)
    u["id"] = uid

    sent = bot.send_message(
        message.chat.id,
        deposit_balance_text(u),
        reply_markup=deposit_balance_inline(),
    )
    user_state[uid] = {"menu": "deposit_balance", "msg_id": sent.message_id}


@bot.callback_query_handler(func=lambda c: c.data == "dep_start")
def cb_deposit_start(call):
    """➕ Deposit বাটনে ক্লিক -> একই মেসেজ এডিট করে মেথড সিলেকশন গ্রিড দেখায়।"""
    if maintenance_block(call):
        bot.answer_callback_query(call.id)
        return
    bot.answer_callback_query(call.id)
    uid = call.from_user.id
    chat_id = call.message.chat.id

    limit_line = ""
    if bot_settings["min_deposit"] or bot_settings["max_deposit"]:
        limit_line = (
            f"📉 Min Deposit: {fmt_amount(bot_settings['min_deposit'])}\n"
            f"📈 Max Deposit: {fmt_amount(bot_settings['max_deposit'])}\n\n"
        )

    msg_id = safe_edit_or_send(
        chat_id,
        call.message.message_id,
        "💳 <b>Deposit</b>\n\n" + limit_line + "নিচ থেকে পেমেন্ট মেথড বেছে নিন:",
        reply_markup=deposit_methods_inline(),
    )
    user_state[uid] = {"menu": "deposit_method", "msg_id": msg_id}


@bot.callback_query_handler(func=lambda c: c.data.startswith("depmethod_") or c.data == "dep_back")
def cb_deposit_method_select(call):
    if maintenance_block(call):
        bot.answer_callback_query(call.id)
        return
    bot.answer_callback_query(call.id)
    uid = call.from_user.id
    chat_id = call.message.chat.id
    state = user_state.get(uid, {})
    msg_id = state.get("msg_id") or call.message.message_id

    if call.data == "dep_back":
        u = get_user(call)
        u["id"] = uid
        msg_id = safe_edit_or_send(
            chat_id,
            msg_id,
            deposit_balance_text(u),
            reply_markup=deposit_balance_inline(),
        )
        user_state[uid] = {"menu": "deposit_balance", "msg_id": msg_id}
        return

    method = call.data.replace("depmethod_", "")
    if method not in bot_settings["deposit_methods"]:
        msg_id = safe_edit_or_send(
            chat_id,
            msg_id,
            "⚠️ এই মেথডটি আর available নেই। আবার Deposit মেনু থেকে চেষ্টা করুন।",
            reply_markup=deposit_methods_inline(),
        )
        user_state[uid] = {"menu": "deposit_method", "msg_id": msg_id}
        return

    num = bot_settings["deposit_numbers"].get(method)
    num_line = f"📮 এই নাম্বার/অ্যাড্রেসে টাকা পাঠান: <code>{num}</code>\n\n" if num else ""

    if method == "Binance":
        rate = bot_settings.get("usd_rate") or 0
        rate_line = f"💱 বর্তমান রেট: 1 USDT = {rate} BDT\n\n" if rate else ""
        prompt = (
            f"💳 <b>{method} Deposit</b>\n\n{num_line}{rate_line}"
            "Deposit করার amount USDT তে লিখে পাঠান (শুধু সংখ্যা):"
        )
    else:
        prompt = f"💳 <b>{method} Deposit</b>\n\n{num_line}Deposit করার amount লিখে পাঠান (শুধু সংখ্যা):"

    msg_id = safe_edit_or_send(chat_id, msg_id, prompt, reply_markup=deposit_cancel_inline())
    user_state[uid] = {"menu": "deposit_amount", "method": method, "msg_id": msg_id}
    bot.register_next_step_handler(call.message, process_deposit_amount)


@bot.callback_query_handler(func=lambda c: c.data == "deposit_cancel")
def cb_deposit_cancel(call):
    """Deposit amount ইনপুট ধাপে Cancel বাটনে ক্লিক করলে pending input বাতিল করে
    একই মেসেজটা এডিট করে Cancel মেসেজ দেখায় (নতুন মেসেজ যায় না)।"""
    uid = call.from_user.id
    chat_id = call.message.chat.id
    bot.answer_callback_query(call.id)
    bot.clear_step_handler_by_chat_id(chat_id)
    state = user_state.get(uid, {})
    msg_id = state.get("msg_id") or call.message.message_id

    safe_edit_or_send(
        chat_id,
        msg_id,
        "❌ <b>Deposit Cancelled!</b>\n\nDeposit প্রক্রিয়াটি বাতিল করা হয়েছে।",
        reply_markup=None,
    )
    user_state[uid] = {"menu": "main"}


def process_deposit_amount(message):
    """ইউজারের দেওয়া amount validate করে min/max লিমিট চেক করে, তারপর TrxID/Binance Username চায়।
    Binance এর জন্য ইউজার USDT এ amount দেয়; bot_settings['usd_rate'] দিয়ে BDT এ কনভার্ট করে।
    ইউজারের টাইপ করা মেসেজ (এই message অবজেক্ট) কখনো ডিলিট/এডিট করা হয় না — শুধু আগের
    অ্যাংকর বট-মেসেজটাই (state এর msg_id) এডিট হয়।"""
    uid = message.from_user.id
    chat_id = message.chat.id
    text = (message.text or "").strip()

    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return

    state = user_state.get(uid, {})
    method = state.get("method")
    msg_id = state.get("msg_id")
    if state.get("menu") != "deposit_amount" or not method:
        bot.send_message(chat_id, "⚠️ আগে 💳 Deposit মেনু থেকে একটা মেথড বেছে নিন।")
        return

    try:
        entered = float(text)
    except ValueError:
        entered = None

    unit = "USDT" if method == "Binance" else "সংখ্যায়"
    if entered is None or entered <= 0:
        msg_id = safe_edit_or_send(
            chat_id,
            msg_id,
            f"⚠️ সঠিক amount {unit} লিখুন (যেমন: 100)।",
            reply_markup=deposit_cancel_inline(),
        )
        state["msg_id"] = msg_id
        bot.register_next_step_handler(message, process_deposit_amount)
        return

    amount_usdt = None
    rate = None
    if method == "Binance":
        rate = bot_settings.get("usd_rate") or 0
        if rate <= 0:
            safe_edit_or_send(
                chat_id,
                msg_id,
                "⚠️ এখনো USDT rate সেট করা হয়নি। Admin কে জানান, তারপর আবার চেষ্টা করুন।",
                reply_markup=None,
            )
            user_state[uid] = {"menu": "main"}
            return
        amount_usdt = entered
        if amount_usdt == int(amount_usdt):
            amount_usdt = int(amount_usdt)
        amount = round(entered * rate, 2)
    else:
        amount = entered

    min_dep = bot_settings["min_deposit"]
    max_dep = bot_settings["max_deposit"]
    if min_dep and amount < min_dep:
        msg_id = safe_edit_or_send(
            chat_id,
            msg_id,
            f"⚠️ Minimum deposit amount {fmt_amount(min_dep)}। আবার লিখুন।",
            reply_markup=deposit_cancel_inline(),
        )
        state["msg_id"] = msg_id
        bot.register_next_step_handler(message, process_deposit_amount)
        return
    if max_dep and amount > max_dep:
        msg_id = safe_edit_or_send(
            chat_id,
            msg_id,
            f"⚠️ Maximum deposit amount {fmt_amount(max_dep)}। আবার লিখুন।",
            reply_markup=deposit_cancel_inline(),
        )
        state["msg_id"] = msg_id
        bot.register_next_step_handler(message, process_deposit_amount)
        return

    if amount == int(amount):
        amount = int(amount)

    if method == "Binance":
        prompt = (
            f"💳 Binance — Amount: {amount_usdt} USDT (1 USDT = {rate} BDT) = {fmt_amount(amount)}\n\n"
            "send your binance username:👇"
        )
    else:
        prompt = f"💳 {method} — Amount: {fmt_amount(amount)}\n\nsend your transaction id(TrxID):👇"

    msg_id = safe_edit_or_send(chat_id, msg_id, prompt, reply_markup=deposit_cancel_inline())

    new_state = {"menu": "deposit_trxid", "method": method, "amount": amount, "msg_id": msg_id}
    if amount_usdt is not None:
        new_state["amount_usdt"] = amount_usdt
    user_state[uid] = new_state
    bot.register_next_step_handler(message, process_deposit_trxid)


def process_deposit_trxid(message):
    """TrxID/Username নিয়ে deposit রিকোয়েস্ট তৈরি করে — ম্যানুয়াল মেথড হলে Admin রিভিউতে
    পাঠায়, নাহলে সাথে সাথে ব্যালেন্স যোগ করে অটো-অ্যাপ্রুভ করে দেয়। প্রতিটা ধাপ একই
    অ্যাংকর মেসেজ (state এর msg_id) এডিট করে দেখায়; ইউজারের টাইপ করা মেসেজ অক্ষত থাকে।"""
    uid = message.from_user.id
    chat_id = message.chat.id
    text = (message.text or "").strip()

    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return

    state = user_state.get(uid, {})
    method = state.get("method")
    amount = state.get("amount")
    msg_id = state.get("msg_id")
    if state.get("menu") != "deposit_trxid" or not method or amount is None:
        bot.send_message(chat_id, "⚠️ আগে 💳 Deposit মেনু থেকে আবার শুরু করুন।")
        return

    trx_id = text
    if not trx_id:
        msg_id = safe_edit_or_send(
            chat_id,
            msg_id,
            f"⚠️ সঠিক {_id_label(method)} লিখুন।",
            reply_markup=deposit_cancel_inline(),
        )
        state["msg_id"] = msg_id
        bot.register_next_step_handler(message, process_deposit_trxid)
        return

    u = get_user(message)
    u["id"] = uid

    # 🛡️ Duplicate TrxID guard: একই TrxID দিয়ে আগেই কোনো Pending/Approved Deposit
    # থাকলে নতুন করে আরেকটা Deposit request তৈরি হতে দেওয়া হবে না — নাহলে Admin
    # (বা SMS auto-approve) না বুঝে দুইটা আলাদা Request-ই Approve করে ফেললে একই
    # আসল পেমেন্টের জন্য দুইবার ব্যালেন্স যোগ হয়ে যেতে পারে।
    # 🔒 "আগে থেকে আছে কিনা চেক" + "নতুন deposit তৈরি" — দুটো একসাথে _deposit_lock এর ভেতরে
    # (atomic), নাহলে একই TrxID দিয়ে দুইজন একই মুহূর্তে সাবমিট করলে দুটো pending তৈরি হয়ে
    # যেত এবং Admin দুটোই Approve করলে একই পেমেন্টে দুইবার ব্যালেন্স যোগ হতো।
    dep = None
    dep_id = None
    with _deposit_lock:
        if method == "Binance":
            # Binance এ একই ইউজার বারবার একই username দিয়ে deposit করে — তাই শুধু "একই username +
            # একই USDT amount এর pending request আগে থেকে আছে কিনা" দেখা হয়। (একই পেমেন্ট দুইবার
            # ধরা ঠেকায় SMS এর is_used ফ্ল্যাগ — প্রতিটা Binance পেমেন্ট শুধু একবারই ব্যবহার হয়।)
            existing_trx = next(
                (
                    d for d in deposits.values()
                    if d.get("method") == "Binance"
                    and d.get("status") == "pending"
                    and _norm_trx("Binance", d.get("trx_id")) == _norm_trx("Binance", trx_id)
                    and d.get("amount_usdt") == state.get("amount_usdt")
                ),
                None,
            )
        else:
            existing_trx = next(
                (
                    d for d in deposits.values()
                    if d.get("method") == method
                    and (d.get("trx_id") or "").strip().upper() == trx_id.strip().upper()
                    and d.get("status") in ("pending", "approved")
                ),
                None,
            )
        if existing_trx is None:
            dep_id = _next_deposit_id()
            dep = {
                "id": dep_id,
                "user_id": uid,
                "method": method,
                "amount": amount,
                "trx_id": trx_id,
                "status": "pending",
                "date": datetime.datetime.now().strftime("%Y-%m-%d %H:%M"),
            }
            if state.get("amount_usdt") is not None:
                dep["amount_usdt"] = state["amount_usdt"]
            deposits[dep_id] = dep
    if existing_trx:
        status_bn = (
            "ইতিমধ্যে ✅ Approved হয়ে গেছে"
            if existing_trx["status"] == "approved"
            else "ইতিমধ্যে ⏳ Pending অবস্থায় Admin রিভিউতে আছে"
        )
        msg_id = safe_edit_or_send(
            chat_id,
            msg_id,
            f"⚠️ এই {_id_label(method)} (<code>{trx_id}</code>) দিয়ে আগেই একটা Deposit "
            f"(DEP-{existing_trx['id']}) {status_bn}। একই TrxID দিয়ে একাধিকবার Deposit "
            "request করা যায় না।\n\nভুল হয়ে থাকলে সঠিক TrxID দিয়ে আবার চেষ্টা করুন, "
            "অথবা 🆘 Support এ যোগাযোগ করুন।",
            reply_markup=deposit_cancel_inline(),
        )
        state["msg_id"] = msg_id
        bot.register_next_step_handler(message, process_deposit_trxid)
        return

    save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)

    # -----------------------------------------------------------------
    # bKash / Nagad / Rocket -> প্রথমে চেক হয় SMS Forwarder থেকে আগে থেকেই
    # কোনো ম্যাচিং SMS এসে গেছে কিনা (ইউজার SMS আসার পরে TrxID লিখলে) —
    # মিললে সাথে সাথে অটো-অ্যাপ্রুভ, ভুল তথ্য দিলে সাথে সাথে reject। কোনো
    # ম্যাচ না পেলে (SMS এখনো আসেনি) Admin Approve/Reject এর জন্য pending থাকবে।
    # Binance -> আগে থেকে সেইভ করা Binance নোটিফিকেশনের সাথে Username + USDT Amount
    # হুবহু মিললে সাথে সাথে অটো-অ্যাপ্রুভ; না মিললে (পেমেন্ট এখনো আসেনি) pending থাকবে
    # এবং নোটিফিকেশন পরে এলে তখন অটো-ম্যাচ হবে। (ভুল মিললেও reject হয় না, Admin দেখতে পারবে)
    # বাকি সব (অন্য যেকোনো) মেথড -> সাথে সাথে অটো-অ্যাপ্রুভ, SMS লাগে না।
    # -----------------------------------------------------------------
    if method in DEPOSIT_MANUAL_METHODS:
        if method in SMS_AUTO_APPROVE_METHODS:
            sms_match = try_auto_approve_from_stored_sms(dep)
            if sms_match in ("approved", "rejected_mismatch"):
                # ইউজার/এডমিন নোটিফিকেশন try_auto_approve_from_stored_sms() থেকেই পাঠানো হয়ে গেছে।
                user_state[uid] = {"menu": "main"}
                return

        usdt_line = f"💵 USDT Amount: {dep['amount_usdt']} USDT\n" if dep.get("amount_usdt") is not None else ""
        bot.send_message(
            chat_id,
            "⏳ <b>Deposit request submitted!</b>\n\n"
            f"🆔 Request: DEP-{dep_id}\n"
            f"💳 Method: {method}\n"
            f"{usdt_line}"
            f"💰 Amount: {fmt_amount(amount)}\n"
            f"🧾 {_id_label(method)}: {trx_id}\n\n"
            "Payment verify হলে আটোমেটিক approve হবে",
        )
        user_state[uid] = {"menu": "main"}
        admin_text = (
            "💰 <b>New Deposit Request</b>\n\n"
            f"🆔 Request: DEP-{dep_id}\n"
            f"👤 User: {u['full_name']} ({u['username']}) | <code>{uid}</code>\n"
            f"💳 Method: {method}\n"
            f"{usdt_line}"
            f"💰 Amount: {fmt_amount(amount)}\n"
            f"🧾 {_id_label(method)}: <code>{trx_id}</code>"
        )
        for admin_id in ADMIN_IDS:
            try:
                sent = bot.send_message(admin_id, admin_text, reply_markup=deposit_review_inline(dep_id))
                _track_deposit_admin_msg(dep, admin_id, sent.message_id)
            except Exception:
                pass
        save_db()   # ✅ admin_msgs রেফারেন্স ডিস্কে persist করা হলো
    else:
        dep["status"] = "approved"
        u["balance"] += amount
        u["today_deposit"] += amount
        save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)
        bot.send_message(
            chat_id,
            "✅ <b>Deposit Auto-Approved!</b>\n\n"
            f"🆔 Request: DEP-{dep_id}\n"
            f"💳 Method: {method}\n"
            f"💰 +{fmt_amount(amount)} added\n"
            f"💰 New Balance: {fmt_amount(u['balance'])}",
        )
        user_state[uid] = {"menu": "main"}
        for admin_id in ADMIN_IDS:
            try:
                bot.send_message(
                    admin_id,
                    "🤖 <b>Auto-Approved Deposit</b>\n\n"
                    f"🆔 DEP-{dep_id} | 👤 <code>{uid}</code> | 💳 {method} | "
                    f"💰 {fmt_amount(amount)} | 🧾 {trx_id}",
                )
            except Exception:
                pass


@bot.callback_query_handler(
    func=lambda c: (c.data.startswith("depapprove_") or c.data.startswith("depreject_"))
    and is_admin(c.from_user.id)
)
def cb_deposit_review(call):
    """Admin এর Approve/Reject বাটনে ক্লিক হ্যান্ডল করে।

    🔒 Race-condition fix: দুইজন Admin (বা একজন Admin ডাবল-ট্যাপ করলে) প্রায়
    একই মুহূর্তে Approve/Reject চাপলে যেন দুইবার ব্যালেন্স যোগ না হয়ে যায়,
    তাই "status এখনও pending কিনা চেক করা -> approved/rejected এ সেট করা ->
    ব্যালেন্স যোগ করা" — পুরো অংশটা _deposit_lock দিয়ে atomic রাখা হয়েছে।

    🛡️ Data-safety fix: ইউজার রেকর্ড কোনো কারণে খুঁজে না পেলে (যেমন ডেটা
    করাপশন) deposit-টা approved মার্ক করে ব্যালেন্স যোগ না করে ফেলে রাখার
    বদলে সেটা pending-ই রেখে Admin-কে সরাসরি এরর জানানো হয়, যাতে
    "Approved হয়ে গেছে কিন্তু ব্যালেন্স যোগ হয়নি" — এই অবস্থা কখনো তৈরি না হয়।
    """
    bot.answer_callback_query(call.id)
    chat_id = call.message.chat.id

    if call.data.startswith("depapprove_"):
        action = "approve"
        dep_id = int(call.data.replace("depapprove_", ""))
    else:
        action = "reject"
        dep_id = int(call.data.replace("depreject_", ""))

    dep = deposits.get(dep_id)
    if not dep:
        bot.send_message(chat_id, "⚠️ এই Deposit Request খুঁজে পাওয়া যায়নি।")
        return

    with _deposit_lock:
        if dep["status"] != "pending":
            bot.send_message(
                chat_id,
                f"⚠️ এই Deposit ইতিমধ্যে '{dep['status']}' করা হয়ে গেছে (অন্য কোনো Admin আগেই "
                "রিভিউ করে ফেলেছেন) — আবার কিছু করা হয়নি।",
            )
            _clear_deposit_admin_buttons(dep)
            return

        user_id = dep["user_id"]
        u = users.get(user_id)

        if action == "approve":
            if u is None:
                # ইউজার রেকর্ড খুঁজে পাওয়া যায়নি — ব্যালেন্স ছাড়া Approve করে দিলে
                # সেটা "Approved কিন্তু balance যোগ হয়নি" বাগে পরিণত হবে, তাই
                # pending-ই রেখে Admin-কে জানানো হচ্ছে।
                bot.send_message(
                    chat_id,
                    f"❌ DEP-{dep_id}: ইউজার (<code>{user_id}</code>) খুঁজে পাওয়া যায়নি, তাই "
                    "Approve করা যায়নি (ব্যালেন্স যোগ হয়নি)। এটা এখনও 'pending' অবস্থায় আছে — "
                    "Export DB দিয়ে ডেটা চেক করুন।",
                )
                return

            dep["status"] = "approved"
            u["balance"] += dep["amount"]
            u["today_deposit"] += dep["amount"]
            # 🔒 Admin ম্যানুয়ালি approve করলে মিলে যাওয়া SMS/নোটিফিকেশনটাও "used" করে দেওয়া হয়,
            # নাহলে পরে একই username+amount এর নতুন deposit ওই পুরোনো পেমেন্ট দিয়ে আবার অটো-approve হতো।
            _consume_matching_sms(dep)
            save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)
            _clear_deposit_admin_buttons(dep)   # অন্য সব Admin-এর কপি থেকেও বাটন সরানো হলো

            bot.send_message(chat_id, f"✅ DEP-{dep_id} Approved হয়েছে।")
            try:
                bot.send_message(
                    user_id,
                    "✅ <b>Deposit Approved!</b>\n\n"
                    f"🆔 Request: DEP-{dep_id}\n"
                    f"💰 +{fmt_amount(dep['amount'])} added\n"
                    f"💰 New Balance: {fmt_amount(u['balance'])}",
                )
            except Exception:
                pass
        else:
            dep["status"] = "rejected"
            save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)
            _clear_deposit_admin_buttons(dep)   # অন্য সব Admin-এর কপি থেকেও বাটন সরানো হলো

            bot.send_message(chat_id, f"❌ DEP-{dep_id} Rejected হয়েছে।")
            try:
                bot.send_message(
                    user_id,
                    f"❌ <b>Deposit Rejected.</b>\n\n🆔 Request: DEP-{dep_id}\nProblem হলে Support এ যোগাযোগ করুন।",
                )
            except Exception:
                pass


@bot.message_handler(func=lambda m: m.text == "🎁 Referral")
def menu_referral(message):
    if maintenance_block(message):
        return
    if require_force_join(message):
        return
    u = get_user(message)
    u["id"] = message.from_user.id
    user_state[message.from_user.id] = {"menu": "referral"}
    bot.send_message(
        message.chat.id,
        referral_text(u["id"], u),
        reply_markup=referral_inline(),
    )


DEVELOPER_USERNAME = "relax1472"   # hard-coded, Bot Settings দিয়ে বদলানো যায় না


@bot.message_handler(func=lambda m: m.text == "🆘 Support")
def menu_support(message):
    if maintenance_block(message):
        return
    if require_force_join(message):
        return
    # main menu keyboard এই থেকেই যায় — সাপোর্ট আলাদা কোনো sub-menu এ যায় না
    user_state[message.from_user.id] = {"menu": "main"}

    kb = types.InlineKeyboardMarkup(row_width=2)
    buttons = []
    support_username = (bot_settings.get("support_username") or "").lstrip("@").strip()
    if support_username:   # Admin Panel -> Bot Settings -> Support Username থেকে সেট হয়
        buttons.append(types.InlineKeyboardButton("💬 Live Chat", url=f"https://t.me/{support_username}"))
    buttons.append(types.InlineKeyboardButton("👨‍💻 Developer", url=f"https://t.me/{DEVELOPER_USERNAME}"))
    kb.add(*buttons)

    bot.send_message(
        message.chat.id,
        "☎️ <b>Support</b>\n\n"
        "📞 Need help? Contact us: 👇",
        reply_markup=kb,
    )


@bot.message_handler(func=lambda m: m.text == "⚙️ Method")
def menu_method(message):
    if maintenance_block(message):
        return
    if require_force_join(message):
        return
    user_state[message.from_user.id] = {"menu": "main"}

    videos = bot_settings.get("method_videos") or []
    if not videos:
        bot.send_message(
            message.chat.id,
            "⚙️ <b>Method</b>\n\nএখনো কোনো টিউটোরিয়াল ভিডিও সেট করা হয়নি।",
        )
        return

    kb = types.InlineKeyboardMarkup()
    for v in videos:
        _t = str(v["title"])
        kb.add(types.InlineKeyboardButton(_t if not _t[:1].isalnum() else f"🎥 {_t}", url=v["link"]))
    bot.send_message(
        message.chat.id,
        "⚙️ <b>Method</b>\n\nকিভাবে ডিপোজিট/পারচেজ করবেন তা এই ভিডিওগুলোতে দেখুন: 👇",
        reply_markup=kb,
    )


@bot.message_handler(func=lambda m: m.text in ["🏠 Back to Menu", "⬅️ Back"])
def go_back(message):
    """সব জায়গা থেকে ধাপে ধাপে Back করার লজিক।"""
    uid = message.from_user.id

    # প্রোডাক্ট ডিটেইলস (Hotmail/Outlook...) থেকে Back -> Mail মেনুতে
    if user_state.get(uid, {}).get("menu") == "buy_item" and message.text == "⬅️ Back":
        _pk = user_state.get(uid, {}).get("product")
        _grp = CATALOG[_pk]["parent"] if _is_group_sub(_pk) else None
        user_state[uid] = {"menu": "buy_vpn_sub", "group": _grp} if _grp else {"menu": "buy_mail"}
        # নিচের কীবোর্ড Main Menu কীবোর্ডে ফেরাতে একটা মেসেজ লাগে; "🏠 Main Menu" লেখা যেন
        # না দেখা যায় তাই অদৃশ্য ক্যারেক্টারে পাঠিয়ে সাথে সাথে ডিলিট করা হয়।
        try:
            _tmp = bot.send_message(message.chat.id, "\u2800", reply_markup=main_menu_keyboard(uid))
            bot.delete_message(message.chat.id, _tmp.message_id)
        except Exception:
            pass
        if _grp:
            bot.send_message(
                message.chat.id,
                _wide(f"<b>{_html.escape(catalog_name(_grp))}</b>\n\nএকটি অপশন বেছে নিন:", _grp),
                reply_markup=buy_vpn_sub_inline(_grp),
            )
            return
        bot.send_message(
            message.chat.id,
            f"<b>{_html.escape(catalog_name('mail'))}</b>\n\nএকটি অপশন বেছে নিন:",
            reply_markup=buy_mail_inline(),
        )
        return

    # Buy মেনুর যেকোনো ধাপ থেকে
    # Back চাপলে সরাসরি Main Menu তে ফিরে যেতে হবে।
    # সব জায়গা থেকে -> main menu
    u = get_user(message)
    u["id"] = uid
    user_state[uid] = {"menu": "main"}
    bot.send_message(message.chat.id, "🏠 Main Menu", reply_markup=main_menu_keyboard(uid))


# ---------------------------------------------------------------------------
# INLINE CALLBACKS: Buy মেনু (Mail / Proxy / VPN / Cancel)
# ---------------------------------------------------------------------------
def _buy_edit(call, text, markup):
    """একই মেসেজ এডিট করে মেনু বদলায়; এডিট ব্যর্থ হলে নতুন মেসেজ পাঠায়।"""
    try:
        bot.edit_message_text(text, call.message.chat.id, call.message.message_id, reply_markup=markup)
    except Exception:
        bot.send_message(call.message.chat.id, text, reply_markup=markup)


@bot.callback_query_handler(func=lambda c: c.data in ("buy_mail", "buy_vpn", "buy_proxy", "buy_back", "buy_cancel"))
def cb_buy_menu(call):
    if require_force_join(call):
        bot.answer_callback_query(call.id)
        return
    if maintenance_block(call):
        bot.answer_callback_query(call.id)
        return

    uid = call.from_user.id
    data = call.data

    if data in ("buy_mail", "buy_vpn", "buy_proxy") and not catalog_visible(data[4:]):
        bot.answer_callback_query(call.id, "⛔ এটি এখন বন্ধ আছে।", show_alert=True)
        _buy_edit(call, BUY_MAIN_TEXT, buy_main_inline())
        return

    if data == "buy_mail":
        bot.answer_callback_query(call.id)
        user_state[uid] = {"menu": "buy_mail"}
        _buy_edit(call, f"<b>{_html.escape(catalog_name('mail'))}</b>\n\nএকটি অপশন বেছে নিন:", buy_mail_inline())
    elif data == "buy_vpn":
        bot.answer_callback_query(call.id)
        user_state[uid] = {"menu": "buy_vpn"}
        _buy_edit(call, _wide(f"<b>{_html.escape(catalog_name('vpn'))}</b>\n\nএকটি ক্যাটাগরি বেছে নিন:", "__vpn__"), buy_vpn_inline())
    elif data == "buy_proxy":
        bot.answer_callback_query(call.id)
        user_state[uid] = {"menu": "buy_proxy"}
        _buy_edit(call, _wide(f"<b>{_html.escape(catalog_name('proxy'))}</b>\n\nএকটি অপশন বেছে নিন:"), buy_proxy_inline())
    elif data == "buy_back":
        bot.answer_callback_query(call.id)
        user_state[uid] = {"menu": "buy"}
        _buy_edit(call, BUY_MAIN_TEXT, buy_main_inline())
    elif data == "buy_cancel":
        bot.answer_callback_query(call.id, "Cancelled.")
        user_state[uid] = {"menu": "main"}
        try:
            bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception:
            pass


def _mail_item(email, password, token):
    """স্টকের একটা মেইল অ্যাকাউন্ট। number/otp_link পুরোনো কোডের সাথে সামঞ্জস্যের জন্য রাখা।"""
    return {"email": email, "password": password, "token": token, "number": email, "otp_link": token}


def parse_mail_stock_line(line):
    """`Email|Password|M.C...` লাইন পার্স করে। token = আপলোড করা পুরো লাইনটাই।
    Email বা Password না থাকলে None।"""
    line = (line or "").strip()
    if not line or "|" not in line:
        return None
    parts = line.split("|", 2)
    email, password = parts[0].strip(), parts[1].strip()
    if not email or not password:
        return None
    return _mail_item(email, password, line)


def _item_fields(item):
    """(email, password, token) — নতুন ও পুরোনো দুই ধরনের স্টক আইটেম থেকেই"""
    email = item.get("email") or item.get("number", "")
    password = item.get("password") or ""
    token = item.get("token") or (f"{email}|{item.get('otp_link', '')}" if item.get("otp_link") not in (None, "", "N/A") else email)
    return email, password, token


def _e(v):
    return _html.escape(str(v))


def _receipt_fields(order):
    """Single ও Bulk — দুই রসিদেই একই ৫টা ফিল্ড (Bold + প্রতিটার আলাদা ইউনিক emoji)।
    emoji গুলো পুরো বটে আর কোথাও ব্যবহার হয়নি; দুই রসিদ একই ফাংশন ব্যবহার করে বলে
    কোডে প্রতিটা emoji মাত্র একবারই আছে।"""
    return (
        f"🔖 <b>Product:</b> {_e(order['product_name'])}\n"
        f"🧺 <b>Quantity:</b> {order['qty']}\n"
        f"🎯 <b>Price:</b> {fmt_amount(order['price'])}\n"
        f"🧮 <b>Total:</b> {fmt_amount(order['total'])}\n"
        f"🗓️ <b>Date:</b> {order['date']}\n\n"
    )


def _vpn_content(item):
    return str(item.get("content") or item.get("email") or item.get("number") or "")


def _proxy_fields(item):
    """Proxy আইটেমের [(Heading, Value), ...] — Sheet এর হেডিং অনুযায়ী"""
    f = item.get("fields")
    if f:
        return [(str(h), str(v)) for h, v in f]
    return [("Data", _vpn_content(item))]


def _proxy_table(items):
    """সব আইটেমের হেডিং (ক্রম ঠিক রেখে union) ও সারি রিটার্ন করে"""
    headers = []
    for it in items:
        for h, _v in _proxy_fields(it):
            if h not in headers:
                headers.append(h)
    rows = []
    for it in items:
        d = dict(_proxy_fields(it))
        rows.append([d.get(h, "") for h in headers])
    return headers, rows


def mail_single_text(order, item):
    if order.get("kind") == "proxy":
        lines = "\n".join(f"<b>{_e(h)}:</b> <code>{_e(v)}</code>" for h, v in _proxy_fields(item) if v != "")
        return (
            "🎉 <b>Purchase Successful</b>\n\n"
            + _receipt_fields(order) +
            "🌐 <b>Proxy Details:</b>\n\n"
            f"{lines}\n\n"
            f"🆔 <b>Order:</b> <code>{order['order_id']}</code>\n"
            "⚠️ <b>Please Save This info</b>"
        )
    if order.get("kind") == "vpn":
        return (
            "🎉 <b>Purchase Successful</b>\n\n"
            + _receipt_fields(order) +
            "🔐 <b>VPN Details:</b>\n\n"
            f"<code>{_e(_vpn_content(item))}</code>\n\n"
            f"🆔 <b>Order:</b> <code>{order['order_id']}</code>\n"
            "⚠️ <b>Please Save This info</b>"
        )
    email, password, token = _item_fields(item)
    return (
        "🎉 <b>Purchase Successful</b>\n\n"
        + _receipt_fields(order) +
        "📬 <b>Account Details:</b>\n\n"
        f"<b>Email:</b> <code>{_e(email)}</code>\n"
        f"<b>Password:</b> <code>{_e(password)}</code>\n"
        f"<b>Token:</b> <code>{_e(token)}</code>\n\n"
        f"🆔 <b>Order:</b> <code>{order['order_id']}</code>\n"
        "⚠️ <b>Please Save This info</b>"
    )


def mail_bulk_text(order):
    if order.get("kind") == "proxy":
        cols = " | ".join(_proxy_table(order.get("items") or [])[0]) or "Proxy"
    else:
        cols = "VPN Details" if order.get("kind") == "vpn" else "Email | Password | Token"
    return (
        "🎉 <b>Purchase Successful</b>\n\n"
        + _receipt_fields(order) +
        f"📎 অ্যাকাউন্টগুলো নিচের .xlsx ফাইলে ({cols})\n\n"
        f"🆔 <b>Order:</b> <code>{order['order_id']}</code>\n"
        "⚠️ <b>Please Save This info</b>"
    )


def build_proxy_xlsx(items):
    """Proxy: স্টকের Sheet এর হেডিং অনুযায়ী কলাম, প্রতি সারিতে ১ পিস"""
    from openpyxl import Workbook
    from openpyxl.styles import Font, PatternFill

    headers, rows = _proxy_table(items)
    wb = Workbook()
    ws = wb.active
    ws.title = "Proxy"
    ws.append(headers)
    for cell in ws[1]:
        cell.font = Font(bold=True, color="FFFFFF")
        cell.fill = PatternFill(start_color="4472C4", end_color="4472C4", fill_type="solid")
    for r in rows:
        ws.append(r)
    for i in range(len(headers)):
        ws.column_dimensions[chr(65 + i) if i < 26 else "AA"].width = 24
    buf = io.BytesIO()
    wb.save(buf)
    buf.seek(0)
    return buf


def build_vpn_xlsx(items):
    """VPN: ১টা কলাম (VPN Details), প্রতি সারিতে ১টা আইটেম"""
    from openpyxl import Workbook
    from openpyxl.styles import Font, PatternFill

    wb = Workbook()
    ws = wb.active
    ws.title = "VPN"
    ws.append(["VPN Details"])
    ws["A1"].font = Font(bold=True, color="FFFFFF")
    ws["A1"].fill = PatternFill(start_color="4472C4", end_color="4472C4", fill_type="solid")
    for it in items:
        ws.append([_vpn_content(it)])
    ws.column_dimensions["A"].width = 100
    buf = io.BytesIO()
    wb.save(buf)
    buf.seek(0)
    return buf


def build_mail_xlsx(items):
    """1st column Email, 2nd Password, 3rd Token (email|password|M.C...) — BytesIO রিটার্ন করে"""
    from openpyxl import Workbook
    from openpyxl.styles import Font, PatternFill

    wb = Workbook()
    ws = wb.active
    ws.title = "Accounts"
    ws.append(["Email", "Password", "Token"])
    for cell in ws[1]:
        cell.font = Font(bold=True, color="FFFFFF")
        cell.fill = PatternFill(start_color="4472C4", end_color="4472C4", fill_type="solid")
    for it in items:
        ws.append(list(_item_fields(it)))
    ws.column_dimensions["A"].width = 32
    ws.column_dimensions["B"].width = 22
    ws.column_dimensions["C"].width = 80
    buf = io.BytesIO()
    wb.save(buf)
    buf.seek(0)
    return buf


def send_mail_xlsx(chat_id, order, reply_markup=None):
    items = order.get("items") or []
    safe = re.sub(r"[^A-Za-z0-9_.-]+", "_", order["product_name"]).strip("_") or "accounts"
    kind = order.get("kind")
    is_vpn = kind in ("vpn", "proxy")
    try:
        buf = (build_proxy_xlsx(items) if kind == "proxy"
               else build_vpn_xlsx(items) if kind == "vpn" else build_mail_xlsx(items))
        buf.name = f"{safe}_{order['order_id']}.xlsx"
        bot.send_document(chat_id, buf, reply_markup=reply_markup)
    except ImportError:
        lines = [_vpn_content(it) if is_vpn else _item_fields(it)[2] for it in items]
        if kind == "proxy":
            _h, _rows = _proxy_table(items)
            lines = [" | ".join(_h)] + [" | ".join(r) for r in _rows]
        txt = io.BytesIO("\n".join(lines).encode("utf-8"))
        txt.name = f"{safe}_{order['order_id']}.txt"
        bot.send_document(chat_id, txt, reply_markup=reply_markup)


def mail_bulk_inline(order_id):
    kb = types.InlineKeyboardMarkup()
    kb.row(types.InlineKeyboardButton("⏬ Download again (.xlsx)", callback_data=f"mxlsx_{order_id}"))
    return kb


@bot.callback_query_handler(func=lambda c: c.data.startswith("mxlsx_"))
def cb_mail_xlsx_again(call):
    order = orders.get(call.data[len("mxlsx_"):])
    if not order or order.get("user_id") != call.from_user.id or not order.get("items"):
        bot.answer_callback_query(call.id, "⚠️ অর্ডারটি খুঁজে পাওয়া যায়নি।", show_alert=True)
        return
    bot.answer_callback_query(call.id)
    try:
        send_mail_xlsx(call.message.chat.id, order)
    except Exception as e:
        bot.send_message(call.message.chat.id, f"❌ ফাইল পাঠাতে সমস্যা হয়েছে: {e}")


def mail_product_text(key):
    p = products[key]
    price = fmt_amount(p["price"]) if p.get("price", 0) > 0 else "Not set"
    return (
        f"🏷️ <b>Product name:</b> {_html.escape(_prod_name(key))}\n"
        f"💲 <b>Price:</b> {price}\n"
        f"🗃️ <b>Available:</b> {len(p.get('stock_list') or [])}"
    )


def mail_product_keyboard():
    """প্রোডাক্ট ডিটেইলসের নিচের কীবোর্ড: Single pcs, Bulk buy, Back — প্রতি সারিতে ১টা (1 by 1)"""
    kb = types.ReplyKeyboardMarkup(resize_keyboard=True, row_width=1)
    kb.row(types.KeyboardButton("🛍️ Single pcs"))
    kb.row(types.KeyboardButton("🚚 Bulk buy"))
    kb.row(types.KeyboardButton("⬅️ Back"))
    return kb


def _show_buy_menu(chat_id, uid):
    """কেনার পর ইউজার Buy মেনুতেই থাকে: মূল Buy ইনলাইন মেনু (Proxy | VPN, Mail, Cancel) আবার দেখায়।"""
    user_state[uid] = {"menu": "buy"}
    bot.send_message(chat_id, BUY_MAIN_TEXT, reply_markup=buy_main_inline())


def _show_mail_detail(chat_id, uid, key):
    _ensure_mail_products()
    user_state[uid] = {"menu": "buy_item", "product": key}
    bot.send_message(chat_id, mail_product_text(key), reply_markup=mail_product_keyboard())


def _show_mail_detail_edit(call, key):
    """Hotmail/Outlook/Outlook.fr চাপলে মেসেজ ডিলিট না করে EDIT হয়ে Product name/Price/Available
    দেখায়। Telegram এ রিপ্লাই কীবোর্ড (Single pcs / Bulk buy / Back) edit দিয়ে বসানো যায় না,
    তাই edit এর পর ছোট একটা নতুন মেসেজের সাথে কীবোর্ড পাঠানো হয়।"""
    chat_id = call.message.chat.id
    uid = call.from_user.id
    _ensure_mail_products()
    user_state[uid] = {"menu": "buy_item", "product": key}
    text = mail_product_text(key)
    try:
        bot.edit_message_text(text, chat_id, call.message.message_id)
    except Exception:
        bot.send_message(chat_id, text, reply_markup=mail_product_keyboard())
        return
    # রিপ্লাই কীবোর্ড শুধু নতুন মেসেজের সাথেই বসে, তাই একটা ছোট মেসেজ পাঠানো হয় (ডিলিট করলে কীবোর্ড চলে যায়, তাই রাখা হলো)
    bot.send_message(chat_id, "🎛️ নিচের বাটন থেকে বেছে নিন", reply_markup=mail_product_keyboard())


@bot.callback_query_handler(func=lambda c: c.data.startswith("buyitem_"))
def cb_buy_item(call):
    if require_force_join(call) or maintenance_block(call):
        bot.answer_callback_query(call.id)
        return
    key = call.data[len("buyitem_"):]
    if key not in CATALOG or not catalog_on(key):
        bot.answer_callback_query(call.id, "⛔ এই প্রোডাক্ট এখন বন্ধ আছে।", show_alert=True)
        return
    if CATALOG[key]["parent"] in GROUP_PARENTS and catalog_children(key):
        if not catalog_visible(key):
            bot.answer_callback_query(call.id, "⛔ এই প্রোডাক্ট এখন বন্ধ আছে।", show_alert=True)
            return
        bot.answer_callback_query(call.id)
        user_state[call.from_user.id] = {"menu": "buy_vpn_sub", "group": key}
        _buy_edit(call, _wide(f"<b>{_html.escape(catalog_name(key))}</b>\n\nএকটি অপশন বেছে নিন:", key), buy_vpn_sub_inline(key))
        return
    if _is_stock_key(key):
        _ensure_mail_products()
        products[key]["name"] = catalog_name(key)
        bot.answer_callback_query(call.id)
        _show_mail_detail_edit(call, key)
        return
    bot.answer_callback_query(call.id, f"⏳ {catalog_name(key)} শীঘ্রই চালু হবে।", show_alert=True)


def _mail_order(u, uid, p, key, qty, items):
    total = p["price"] * qty
    u["balance"] -= total
    u["total_purchased"] += qty
    u["today_spent"] += total
    order_id = f"ORD-{uuid.uuid4().hex[:8].upper()}"
    order = {
        "order_id": order_id,
        "user_id": uid,
        "product_name": catalog_name(key),
        "qty": qty,
        "kind": _stock_kind(key),
        "price": p["price"],
        "total": total,
        "remaining_balance": u["balance"],
        "date": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "number": _item_fields(items[0])[0] if qty == 1 else "📎 xlsx ফাইলে দেখুন",
        "otp_link": _item_fields(items[0])[2] if qty == 1 else "📎 xlsx ফাইলে দেখুন",
        "items": items,
    }
    orders[order_id] = order
    return order


def _mail_purchase(user_ctx, chat_id, key, qty, answer=None):
    """Single/Bulk কেনার কমন লজিক (চেক + stock pop + balance deduct + save একসাথে লকের ভেতরে)।
    সফল হলে order রিটার্ন করে; ব্যর্থ হলে মেসেজ/অ্যালার্ট দিয়ে None।"""
    def fail(text, alert=None):
        if answer and alert:
            answer(alert)
        else:
            bot.send_message(chat_id, text)
        return None

    _ensure_mail_products()
    p = products.get(key)
    if not p or not catalog_on(key):
        return fail("⛔ এই প্রোডাক্ট এখন বন্ধ আছে।", "⛔ এই প্রোডাক্ট এখন বন্ধ আছে।")
    if p["price"] <= 0:
        return fail("⚠️ এই প্রোডাক্টের দাম এখনও সেট করা হয়নি। এডমিনের সাথে যোগাযোগ করুন।",
                    "⚠️ দাম এখনও সেট করা হয়নি।")
    uid = user_ctx.from_user.id
    u = get_user(user_ctx)
    u["id"] = uid
    with _stock_lock:
        stock_list = p.setdefault("stock_list", [])
        if not stock_list:
            return fail("❌ <b>Stock Out!</b>\n\nদুঃখিত, এই প্রোডাক্টের স্টক এখন খালি।", "❌ Stock Out!")
        if qty > len(stock_list):
            return fail(
                f"❌ <b>Stock Not Enough!</b>\n\n📦 বর্তমান স্টক: {len(stock_list)} পিস\nএর বেশি পরিমাণ এখন কেনা সম্ভব নয়।",
                f"❌ স্টক আছে মাত্র {len(stock_list)} পিস।",
            )
        total = p["price"] * qty
        if u["balance"] < total:
            return fail(
                "❌ <b>Insufficient Balance!</b>\n\n"
                f"💰 আপনার ব্যালেন্স: {fmt_amount(u['balance'])}\n"
                f"💵 প্রয়োজন: {fmt_amount(total)}\n\nঅনুগ্রহ করে আগে Deposit করুন।",
                "❌ ব্যালেন্স যথেষ্ট নয়, আগে Deposit করুন।",
            )
        items = [stock_list.pop(0) for _ in range(qty)]
        p["stock"] = len(stock_list)
        order = _mail_order(u, uid, p, key, qty, items)
    # 💾 ডিস্কে সেভ লকের বাইরে — লকের ভেতরে ধীর disk write করলে অন্য ক্রেতারা আটকে থাকত।
    # (item ইতিমধ্যে লকের ভেতরে স্টক থেকে বের হয়ে গেছে, তাই আর কেউ একই item পাবে না)
    save_db()
    return order


def _mail_selected_key(message):
    st = user_state.get(message.from_user.id, {})
    key = st.get("product") if st.get("menu") == "buy_item" else None
    if not _is_stock_key(key):
        bot.send_message(message.chat.id, "⚠️ আগে Buy মেনু থেকে একটা প্রোডাক্ট সিলেক্ট করুন।")
        return None
    return key


@bot.message_handler(func=lambda m: m.text == "🛍️ Single pcs")
def mail_single_pcs(message):
    if maintenance_block(message) or require_force_join(message):
        return
    key = _mail_selected_key(message)
    if not key:
        return
    order = _mail_purchase(message, message.chat.id, key, 1)
    if order:
        uid = message.from_user.id
        # কেনার পরও Single pcs / Bulk buy / Back মেনুতেই স্থির থাকে (Back = আগের ১ ধাপ)
        user_state[uid] = {"menu": "buy_item", "product": key}
        bot.send_message(message.chat.id, mail_single_text(order, order["items"][0]), reply_markup=mail_product_keyboard())


@bot.message_handler(func=lambda m: m.text == "🚚 Bulk buy")
def mail_bulk_buy(message):
    if maintenance_block(message) or require_force_join(message):
        return
    key = _mail_selected_key(message)
    if not key:
        return
    _ensure_mail_products()
    p = products[key]
    if not catalog_on(key):
        bot.send_message(message.chat.id, "⛔ এই প্রোডাক্ট এখন বন্ধ আছে।")
        return
    if p["price"] <= 0:
        bot.send_message(message.chat.id, "⚠️ এই প্রোডাক্টের দাম এখনও সেট করা হয়নি। এডমিনের সাথে যোগাযোগ করুন।")
        return
    if not p["stock_list"]:
        bot.send_message(message.chat.id, "❌ <b>Stock Out!</b>\n\nদুঃখিত, এই প্রোডাক্টের স্টক এখন খালি।", reply_markup=mail_product_keyboard())
        return
    sent = bot.send_message(message.chat.id, "কত pcs নিতে চান নিচে লিখে দিন👇", reply_markup=back_only_keyboard())
    bot.register_next_step_handler(sent, process_mail_bulk_qty, key)


def process_mail_bulk_qty(message, key):
    text = (message.text or "").strip()
    chat_id = message.chat.id
    uid = message.from_user.id
    if text in ("⬅️ Back", "🏠 Back to Menu"):          # প্রোডাক্ট ডিটেইলসে ফেরা
        _show_mail_detail(chat_id, uid, key)
        return
    if text.startswith("/"):
        user_state[uid] = {"menu": "main"}
        bot.send_message(chat_id, "❎ Bulk Buy বাতিল করা হয়েছে।", reply_markup=main_menu_keyboard(uid))
        return
    if not text.isdigit() or int(text) <= 0:
        sent = bot.send_message(chat_id, "⚠️ সঠিক একটি সংখ্যা লিখুন (যেমন: 5)।")
        bot.register_next_step_handler(sent, process_mail_bulk_qty, key)
        return
    order = _mail_purchase(message, chat_id, key, int(text))
    if not order:
        _show_mail_detail(chat_id, uid, key)
        return
    bot.send_message(chat_id, mail_bulk_text(order), reply_markup=mail_bulk_inline(order["order_id"]))
    try:
        send_mail_xlsx(chat_id, order, reply_markup=mail_product_keyboard())
    except Exception as e:
        bot.send_message(chat_id, f"⚠️ ফাইল পাঠাতে সমস্যা হয়েছে ({e})। উপরের 📥 Download again বাটনে চাপ দিন।", reply_markup=mail_product_keyboard())
    user_state[uid] = {"menu": "buy_item", "product": key}   # কেনার পরও প্রোডাক্ট মেনুতেই থাকে


# ---------------------------------------------------------------------------
# ADMIN PANEL: 🧩 Products — ON/OFF ও Rename
# ---------------------------------------------------------------------------
def _cat_depth(key):
    d = 0
    while CATALOG[key]["parent"]:
        key = CATALOG[key]["parent"]
        d += 1
    return d


def catalog_admin_inline(group=None):
    """group=None -> মূল তালিকা (গভীরতা ২ পর্যন্ত); group=<key> -> ওই প্যাকেজের ভেতরের বাটনগুলো।
    (Telegram এ এক কীবোর্ডে সর্বোচ্চ ১০০ বাটন, তাই VPN এর ১০টা করে বাটন আলাদা পেজে দেখানো হয়)"""
    kb = types.InlineKeyboardMarkup()
    if group is None:
        keys = [k for k in CATALOG if _cat_depth(k) <= 1]
    else:
        keys = catalog_children(group)
    for key in keys:
        meta = CATALOG[key]
        on = (bot_settings.get("catalog") or {}).get(key, {}).get("enabled", True)
        indent = "↳ " if meta["parent"] else ""
        t = types.InlineKeyboardButton(
            f"{'🔛' if on else '📴'} {indent}{catalog_name(key)}", callback_data=f"pcat_t_{key}"
        )
        t.style = "success" if on else "danger"
        row = [t, types.InlineKeyboardButton("✏️ Rename", callback_data=f"pcat_r_{key}")]
        if catalog_children(key) and _cat_depth(key) >= 1 and group is None and meta["parent"] in GROUP_PARENTS:
            row.append(types.InlineKeyboardButton("📂", callback_data=f"pcat_o_{key}"))
        kb.row(*row)
    if group is None:
        kb.row(types.InlineKeyboardButton("⬅️ Back", callback_data="pcat_back"))
    else:
        kb.row(types.InlineKeyboardButton("⬅️ Back", callback_data="pcat_list"))
    return kb


def _cat_view_group(key):
    """key বদলানোর পর অ্যাডমিন কোন পেজে ফিরবে: গভীরতা ২ এর আইটেম হলে তার প্যাকেজ পেজে, নাহলে মূল তালিকায়"""
    if key in CATALOG and _cat_depth(key) >= 2:
        return CATALOG[key]["parent"]
    return None


def catalog_admin_text(group=None):
    if group is None:
        return CATALOG_ADMIN_TEXT
    return (
        f"🧩 <b>{_html.escape(catalog_name(group))}</b> — ভেতরের বাটন\n\n"
        "✅ = চালু · ❌ = বন্ধ\n"
        "নামের বাটন চাপলে ON/OFF হবে, ✏️ Rename চাপলে নাম বদলানো যাবে।"
    )


CATALOG_ADMIN_TEXT = (
    "🧩 <b>Products</b>\n\n"
    "✅ = চালু · ❌ = বন্ধ (ইউজারের মেনু থেকে লুকানো থাকবে)\n"
    "নামের বাটন চাপলে ON/OFF হবে, ✏️ Rename চাপলে নাম বদলানো যাবে।\n"
    "ক্যাটাগরি (Proxy/VPN/Mail) OFF করলে তার সব সাব-প্রোডাক্টও লুকিয়ে যায়।"
)


@bot.callback_query_handler(func=lambda c: c.data.startswith("pcat_") and is_admin(c.from_user.id))
def cb_catalog_admin(call):
    data = call.data
    chat_id = call.message.chat.id
    uid = call.from_user.id

    def _show(group=None):
        try:
            bot.edit_message_text(catalog_admin_text(group), chat_id, call.message.message_id, reply_markup=catalog_admin_inline(group))
        except Exception:
            bot.send_message(chat_id, catalog_admin_text(group), reply_markup=catalog_admin_inline(group))

    if data == "pcat_list":
        bot.answer_callback_query(call.id)
        _show()
    elif data == "pcat_back":
        bot.answer_callback_query(call.id)
        try:
            bot.edit_message_text("👮 <b>Admin Panel</b>", chat_id, call.message.message_id, reply_markup=admin_panel_inline())
        except Exception:
            bot.send_message(chat_id, "👮 <b>Admin Panel</b>", reply_markup=admin_panel_inline())
    elif data.startswith("pcat_t_"):
        key = data[len("pcat_t_"):]
        if key not in CATALOG:
            bot.answer_callback_query(call.id, "Unknown product.")
            return
        cat = bot_settings.setdefault("catalog", {})
        entry = cat.setdefault(key, {})
        entry["enabled"] = not entry.get("enabled", True)
        save_db()
        bot.answer_callback_query(call.id, f"{'✅ চালু' if entry['enabled'] else '❌ বন্ধ'}: {catalog_name(key)}")
        _show(_cat_view_group(key))
    elif data.startswith("pcat_o_"):
        key = data[len("pcat_o_"):]
        if key not in CATALOG or not catalog_children(key):
            bot.answer_callback_query(call.id, "Unknown product.")
            return
        bot.answer_callback_query(call.id)
        _show(key)
    elif data.startswith("pcat_r_"):
        key = data[len("pcat_r_"):]
        if key not in CATALOG:
            bot.answer_callback_query(call.id, "Unknown product.")
            return
        bot.answer_callback_query(call.id)
        sent = bot.send_message(
            chat_id,
            f"✏️ <b>{_html.escape(catalog_name(key))}</b> এর নতুন নাম লিখুন (সর্বোচ্চ ৪০ অক্ষর)।\n"
            "emoji ও দিতে পারেন। ডিফল্ট নামে ফিরতে <code>reset</code> লিখুন, বাতিল করতে /cancel।",
        )
        bot.register_next_step_handler(sent, process_catalog_rename, key)


def process_catalog_rename(message, key):
    if not message.from_user or not is_admin(message.from_user.id):
        return
    text = (message.text or "").strip()
    if not text or text.startswith("/"):
        bot.send_message(message.chat.id, "❎ Rename বাতিল করা হয়েছে।")
        return
    entry = bot_settings.setdefault("catalog", {}).setdefault(key, {})
    if text.lower() == "reset":
        entry.pop("name", None)
    else:
        entry["name"] = text[:40]
    _ensure_mail_products()
    save_db()
    bot.send_message(
        message.chat.id,
        f"✅ নাম আপডেট হয়েছে: <b>{_html.escape(catalog_name(key))}</b>",
    )
    _g = _cat_view_group(key)
    bot.send_message(message.chat.id, catalog_admin_text(_g), reply_markup=catalog_admin_inline(_g))


def bulk_file_format_inline(order_id):
    """Bulk Buy এর পর ইউজার কোন ফরম্যাটে ডেটা চান (TXT / CSV / Inline) সেটা বেছে নেওয়ার বাটন।"""
    kb = types.InlineKeyboardMarkup(row_width=3)
    kb.add(
        types.InlineKeyboardButton("📄 TXT", callback_data=f"bulkfile_txt_{order_id}"),
        types.InlineKeyboardButton("🗂️ CSV", callback_data=f"bulkfile_csv_{order_id}"),
        types.InlineKeyboardButton("📋 Inline", callback_data=f"bulkfile_inline_{order_id}"),
    )
    return kb


@bot.callback_query_handler(func=lambda c: c.data.startswith("bulkfile_"))
def cb_bulk_file_format(call):
    """Bulk Buy অর্ডারের আইটেমগুলো ইউজারের বেছে নেওয়া ফরম্যাটে (txt/csv/inline) পাঠায়।"""
    uid = call.from_user.id
    _, fmt, order_id = call.data.split("_", 2)
    order = orders.get(order_id)
    bot.answer_callback_query(call.id)

    if not order or order.get("user_id") != uid:
        bot.send_message(call.message.chat.id, "⚠️ অর্ডারটি খুঁজে পাওয়া যায়নি বা এটি আপনার অর্ডার নয়।")
        return

    items = order.get("items", [])
    if not items:
        bot.send_message(call.message.chat.id, "⚠️ এই অর্ডারে কোনো আইটেম পাওয়া যায়নি।")
        return

    product_key = next((k for k, pv in products.items() if pv["name"] == order["product_name"]), "items")

    if fmt == "inline":
        chunk_lines = [f"{i+1}. <code>{it['number']}</code>" for i, it in enumerate(items)]
        header = (
            f"📋 <b>আপনার {len(items)} টি {order['product_name']}</b>\n"
            "\n"
        )
        text = header
        for line in chunk_lines:
            if len(text) + len(line) + 1 > 3500:
                bot.send_message(call.message.chat.id, text)
                text = ""
            text += line + "\n"
        if text.strip():
            bot.send_message(call.message.chat.id, text)
        return

    if fmt == "csv":
        lines = ["number"] + [f"{it['number']}" for it in items]
        filename = f"{order_id}_{product_key}.csv"
    else:  # txt
        lines = [f"{it['number']}" for it in items]
        filename = f"{order_id}_{product_key}.txt"

    file_content = "\n".join(lines).encode("utf-8")
    bot.send_document(
        call.message.chat.id,
        io.BytesIO(file_content),
        visible_file_name=filename,
        caption=f"📥 আপনার {len(items)} টি {order['product_name']}",
    )


# ---------------------------------------------------------------------------
# ADMIN PANEL
# ---------------------------------------------------------------------------
@bot.message_handler(func=lambda m: m.text == "👮 Admin Panel" and is_admin(m.from_user.id))
def menu_admin_panel(message):
    user_state[message.from_user.id] = {"menu": "admin_panel"}
    bot.send_message(message.chat.id, "👮 <b>Admin Panel</b>", reply_markup=admin_panel_inline())


# ---------------------------------------------------------------------------
# ADMIN PANEL: 📈 Sells Inventory (আজ / ৩ দিন / ৭ দিন / ১ মাসের বিক্রির হিসাব)
# ---------------------------------------------------------------------------
# দিনের হিসাব ক্যালেন্ডার-ডে ভিত্তিক (আজ = আজ ০০:০০ থেকে এখন পর্যন্ত; ৩ দিন = আজসহ ৩ দিন;
# ৭ দিন = আজসহ ৭ দিন; ১ মাস = আজসহ ৩০ দিন)। সময় orders/deposits এ যে ক্লকে সেভ হয়
# (সার্ভারের datetime.now()) সেই ক্লকেই হিসাব হয়।
SELLINV_PERIODS = {
    "today": ("📅 আজকের হিসাব", 1),
    "3d": ("🗓️ গত ৩ দিনের হিসাব", 3),
    "7d": ("🗓️ গত ৭ দিনের হিসাব", 7),
    "30d": ("🗓️ গত ১ মাসের হিসাব", 30),
}


def _parse_dt(value):
    for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M"):
        try:
            return datetime.datetime.strptime(str(value), fmt)
        except Exception:
            continue
    return None


def _tk(value):
    try:
        value = round(float(value), 2)
    except Exception:
        return "0৳"
    return f"{int(value) if value == int(value) else value}৳"


def sellinv_menu_inline():
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(
        types.InlineKeyboardButton("📅 আজ", callback_data="sellinv_today"),
        types.InlineKeyboardButton("🗓️ ৩ দিন", callback_data="sellinv_3d"),
    )
    kb.add(
        types.InlineKeyboardButton("📆 ৭ দিন", callback_data="sellinv_7d"),
        types.InlineKeyboardButton("🌕 ১ মাস", callback_data="sellinv_30d"),
    )
    kb.add(types.InlineKeyboardButton("⬅️ Back", callback_data="sellinv_back"))
    return kb


def build_sells_inventory_report(period_key):
    """রিপোর্টের টেক্সট রিটার্ন করে (Telegram এর ৪০৯৬ অক্ষরের সীমার জন্য একাধিক অংশে ভাগ করা লিস্ট)।"""
    label, days = SELLINV_PERIODS[period_key]
    now = datetime.datetime.now()
    start = datetime.datetime.combine(now.date(), datetime.time.min) - datetime.timedelta(days=days - 1)

    # snapshot — হিসাব চলাকালীন নতুন অর্ডার/ডিপোজিট এলেও dict iteration এ সমস্যা হবে না
    order_list = list(orders.values())
    deposit_list = list(deposits.values())
    user_list = list(users.values())
    product_list = list(products.items())

    per_product = {}   # product_name -> [pcs, amount]
    total_orders = total_pcs = 0
    total_sales = 0
    for o in order_list:
        dt = _parse_dt(o.get("date"))
        if not dt or dt < start:
            continue
        qty = o.get("qty") or 0
        amt = o.get("total") or 0
        total_orders += 1
        total_pcs += qty
        total_sales += amt
        row = per_product.setdefault(o.get("product_name") or "Unknown", [0, 0])
        row[0] += qty
        row[1] += amt

    dep_count = 0
    dep_total = 0
    for d in deposit_list:
        if d.get("status") != "approved":
            continue
        dt = _parse_dt(d.get("date"))
        if not dt or dt < start:
            continue
        dep_count += 1
        dep_total += d.get("amount") or 0

    total_users = len(user_list)
    total_balance = sum((u.get("balance") or 0) for u in user_list)
    users_with_balance = sum(1 for u in user_list if (u.get("balance") or 0) > 0)

    stock_by_name = {}
    stock_pcs = 0
    stock_value = 0
    for k, p in product_list:
        n = len(p.get("stock_list") or [])
        stock_pcs += n
        stock_value += n * (p.get("price") or 0)
        try:
            stock_by_name[catalog_name(k)] = n
        except Exception:
            stock_by_name[p.get("name", k)] = n

    blocks = []
    blocks.append(
        f"📈 <b>Sells Inventory</b>\n{label}\n"
        f"🕒 {start.strftime('%d/%m/%Y')} → {now.strftime('%d/%m/%Y %H:%M:%S')}"
    )
    blocks.append(
        "🛒 <b>বিক্রি</b>\n"
        f"🧾 Orders: <b>{total_orders}</b>\n"
        f"📦 বিক্রি হয়েছে: <b>{total_pcs}</b> পিস\n"
        f"💰 মোট বিক্রি: <b>{fmt_amount(total_sales)}</b>"
    )

    if per_product:
        lines = ["📊 <b>কোন প্রোডাক্ট কত বিক্রি</b>"]
        ranked = sorted(per_product.items(), key=lambda kv: kv[1][1], reverse=True)
        for i, (name, (pcs, amt)) in enumerate(ranked, 1):
            left = stock_by_name.get(name)
            left_txt = f" | স্টক বাকি: {left}" if left is not None else ""
            lines.append(f"{i}. {_html.escape(str(name))} — {pcs} পিস — <b>{_tk(amt)}</b>{left_txt}")
        blocks.append("\n".join(lines))
    else:
        blocks.append("📊 এই সময়ে কোনো প্রোডাক্ট বিক্রি হয়নি।")

    blocks.append(
        "💳 <b>Deposit (Approved)</b>\n"
        f"🧾 সংখ্যা: <b>{dep_count}</b>\n"
        f"💵 মোট: <b>{fmt_amount(dep_total)}</b>"
    )
    blocks.append(
        "👥 <b>ইউজার (এখনকার অবস্থা)</b>\n"
        f"👤 মোট ইউজার: <b>{total_users}</b>\n"
        f"💰 ইউজারদের মোট ব্যালেন্স: <b>{fmt_amount(total_balance)}</b>\n"
        f"✅ ব্যালেন্স আছে এমন ইউজার: <b>{users_with_balance}</b>"
    )
    blocks.append(
        "📦 <b>বর্তমান স্টক (এখনকার অবস্থা)</b>\n"
        f"🗃️ মোট অবিক্রিত: <b>{stock_pcs}</b> পিস\n"
        f"💎 স্টকের মূল্য (বিক্রয়মূল্য ধরে): <b>{fmt_amount(stock_value)}</b>"
    )

    # ৪০৯৬ অক্ষরের সীমা এড়াতে ~৩৫০০ অক্ষরের অংশে ভাগ (লম্বা প্রোডাক্ট লিস্ট হলে)
    chunks, cur = [], ""
    for b in blocks:
        if len(b) > 3500:
            lines = b.split("\n")
            piece = ""
            for ln in lines:
                if len(piece) + len(ln) + 1 > 3500:
                    chunks.append(piece)
                    piece = ""
                piece += ln + "\n"
            b = piece.rstrip("\n")
        if cur and len(cur) + len(b) + 2 > 3500:
            chunks.append(cur)
            cur = b
        else:
            cur = f"{cur}\n\n{b}" if cur else b
    if cur:
        chunks.append(cur)
    return chunks


@bot.callback_query_handler(func=lambda c: c.data.startswith("sellinv_") and is_admin(c.from_user.id))
def cb_sells_inventory(call):
    bot.answer_callback_query(call.id)
    chat_id = call.message.chat.id
    msg_id = call.message.message_id
    key = call.data.replace("sellinv_", "", 1)

    def _edit(text, markup):
        try:
            bot.edit_message_text(text, chat_id, msg_id, reply_markup=markup)
        except Exception:
            try:
                bot.send_message(chat_id, text, reply_markup=markup)
            except Exception:
                pass

    if key == "back":
        user_state[call.from_user.id] = {"menu": "admin_panel"}
        _edit("👮 <b>Admin Panel</b>", admin_panel_inline())
        return
    if key == "menu":
        _edit("📈 <b>Sells Inventory</b>\n\nকোন সময়ের হিসাব দেখতে চান?", sellinv_menu_inline())
        return
    if key not in SELLINV_PERIODS:
        return

    try:
        chunks = build_sells_inventory_report(key)
    except Exception as e:
        _edit(f"❌ হিসাব বের করতে সমস্যা হয়েছে: {_html.escape(str(e))}", sellinv_menu_inline())
        return

    if len(chunks) == 1:
        _edit(chunks[0], sellinv_menu_inline())
    else:
        _edit(chunks[0], None)
        for c in chunks[1:-1]:
            bot.send_message(chat_id, c)
        bot.send_message(chat_id, chunks[-1], reply_markup=sellinv_menu_inline())


# ---------------------------------------------------------------------------
# ADMIN PANEL: inline button callbacks
# ---------------------------------------------------------------------------
@bot.callback_query_handler(func=lambda c: c.data.startswith("admin_") and is_admin(c.from_user.id))
def cb_admin_panel(call):
    uid = call.from_user.id
    data = call.data
    chat_id = call.message.chat.id
    bot.answer_callback_query(call.id)

    if data == "admin_upload_file":
        user_state[uid] = {"menu": "admin_upload_file_select"}
        bot.send_message(
            chat_id,
            "📤 কোন প্রোডাক্টের জন্য স্টক ফাইল আপলোড করবেন?",
            reply_markup=upload_file_product_inline(),
        )

    elif data == "admin_set_price_stock":
        user_state[uid] = {"menu": "admin_set_price_select"}
        bot.send_message(
            chat_id,
            "💰 কোন প্রোডাক্টের price পরিবর্তন করবেন?",
            reply_markup=set_price_product_inline(),
        )

    elif data == "admin_set_usd_rate":
        user_state[uid] = {"menu": "admin_set_usd_rate"}
        current = bot_settings.get("usd_rate") or 0
        bot.send_message(
            chat_id,
            "💱 নতুন Dollar Rate লিখে পাঠান (1 USD = কত BDT)।\n"
            f"বর্তমান রেট: {current if current else 'সেট করা নেই'}\n\n"
            "উদাহরণ: 122 অথবা 121.50",
        )
        bot.register_next_step_handler(call.message, process_set_usd_rate)

    elif data == "admin_users_list":
        # TODO: pagination সহ real user list
        bot.send_message(chat_id, f"👥 মোট ইউজার: {len(users)}\n(তালিকা লজিক পরে যুক্ত হবে)")

    elif data == "admin_statistics":
        # TODO: real total sales, revenue, today stats ইত্যাদি
        bot.send_message(
            chat_id,
            "📊 <b>Statistics</b>\n\n"
            f"👥 Total Users: {len(users)}\n"
            f"🧾 Total Orders: {len(orders)}\n"
            "💰 Total Revenue: TODO\n"
            "📅 Today's Sales: TODO",
        )

    elif data == "admin_broadcast":
        user_state[uid] = {"menu": "admin_broadcast"}
        bot.send_message(chat_id, "📢 যে মেসেজটি সব ইউজারকে পাঠাতে চান লিখুন।")
        bot.register_next_step_handler(call.message, process_broadcast_message)

    elif data == "admin_balance_edit":
        user_state[uid] = {"menu": "admin_balance_edit_wait_uid"}
        bot.send_message(
            chat_id,
            "💵 <b>Add/Remove Balance</b>\n\n"
            "যে ইউজারের ব্যালেন্স বদলাতে চান, তার Telegram User ID লিখে পাঠান।",
            reply_markup=back_to_main_keyboard(),
        )
        bot.register_next_step_handler(call.message, process_balance_edit_uid)

    elif data == "admin_user_info":
        user_state[uid] = {"menu": "admin_user_info_wait_uid"}
        bot.send_message(
            chat_id,
            "🔎 <b>User Info</b>\n\n"
            "যে ইউজারের সব তথ্য দেখতে চান, তার Telegram User ID লিখে পাঠান।",
            reply_markup=back_to_main_keyboard(),
        )
        bot.register_next_step_handler(call.message, process_admin_user_info_uid)

    elif data == "admin_orders":
        # TODO: pagination সহ real orders list / filter
        bot.send_message(chat_id, f"🧾 মোট অর্ডার: {len(orders)}\n(তালিকা লজিক পরে যুক্ত হবে)")

    elif data == "admin_export_db":
        try:
            json_bytes = _serialize_payload_bytes()
        except Exception as e:
            bot.send_message(chat_id, f"❌ Export করতে সমস্যা হয়েছে: {e}")
        else:
            stamp = datetime.datetime.now().strftime('%Y%m%d_%H%M%S')
            filename = f"db_backup_{stamp}.json"
            note = ""
            # Telegram এ বট ২০MB এর বড় ফাইল ডাউনলোড (Import) করতে পারে না — তাই বড় হলে gzip করে পাঠানো
            # হয় (.json.gz); Import এ .json ও .json.gz দুটোই চলে, ডেটা একই থাকে।
            if len(json_bytes) > 15 * 1024 * 1024:
                json_bytes = gzip.compress(json_bytes, compresslevel=9)
                filename += ".gz"
                note = "\n🗜️ ফাইল বড় হওয়ায় gzip (.json.gz) করা হয়েছে — Import এ সরাসরি এটাই দিন।"
            if len(json_bytes) > 49 * 1024 * 1024:
                bot.send_message(chat_id, "❌ Export ফাইল Telegram এর ৫০MB সীমার চেয়ে বড় — আগে পুরোনো অর্ডার/SMS লগ কমান।")
            else:
                stock_total = sum(len(p.get("stock_list") or []) for p in list(products.values()))
                bot.send_document(
                    chat_id,
                    io.BytesIO(json_bytes),
                    visible_file_name=filename,
                    caption=(
                        "📤 <b>DB Export সম্পন্ন!</b>\n\n"
                        f"👥 Users: {len(users)}\n"
                        f"🧾 Orders: {len(orders)}\n"
                        f"💰 Deposits: {len(deposits)}\n"
                        f"📩 SMS Log: {len(sms_log)}\n"
                        f"📦 Products: {len(products)} (স্টকে অবিক্রিত: {stock_total} পিস)\n"
                        "⚙️ Bot Settings + 💎 Premium emoji + 🧩 Product ON/OFF/নাম সহ সব আছে।"
                        f"{note}\n\n"
                        "⚠️ এই ফাইলে ইউজারদের ব্যালেন্স/ডেটা থাকে — নিরাপদ জায়গায় রাখুন।"
                    ),
                )

    elif data == "admin_export_unsold":
        # Export এর সময়কার স্টকের স্ন্যাপশট (লকের ভেতরে), যাতে export চলাকালীন কেউ কিনলেও
        # শুধু export হওয়া আইটেমগুলোই পরে মুছে যায় — নতুন আসা/বাকি আইটেম নয়।
        try:
            with _stock_lock:
                wb = _build_unsold_export_workbook()
                exported = {k: {id(it) for it in (p.get("stock_list") or [])} for k, p in products.items()}
                total_unsold = sum(len(v) for v in exported.values())
        except Exception as e:
            bot.send_message(chat_id, f"❌ Export করতে সমস্যা হয়েছে: {e}")
        else:
            if wb is None:
                bot.send_message(chat_id, "📦 এই মুহূর্তে কোনো Unsold (অবিক্রিত) প্রোডাক্ট নেই।")
            else:
                buf = io.BytesIO()
                wb.save(buf)
                buf.seek(0)
                filename = f"unsold_stock_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.xlsx"
                try:
                    bot.send_document(
                        chat_id,
                        buf,
                        visible_file_name=filename,
                        caption=(
                            "📦 <b>Unsold Product Export সম্পন্ন!</b>\n\n"
                            f"📊 মোট অবিক্রিত পিস: {total_unsold}\n"
                            "প্রতিটা প্রোডাক্টের জন্য আলাদা শীটে ডেটা দেওয়া আছে।\n\n"
                            "🧹 Export হওয়া সব স্টক এখন বট থেকে খালি করা হয়েছে।"
                        ),
                    )
                except Exception as e:
                    # ফাইল পাঠানো ব্যর্থ হলে স্টক মোছা হয় না
                    bot.send_message(chat_id, f"❌ ফাইল পাঠাতে সমস্যা হয়েছে, তাই স্টক খালি করা হয়নি: {e}")
                else:
                    with _stock_lock:
                        for k, ids in exported.items():
                            p = products.get(k)
                            if not p or not ids:
                                continue
                            p["stock_list"] = [it for it in (p.get("stock_list") or []) if id(it) not in ids]
                            p["stock"] = len(p["stock_list"])
                        save_db()
                    bot.send_message(chat_id, f"✅ {total_unsold} পিস স্টক export হয়ে বট থেকে খালি হয়েছে।")

    elif data == "admin_import_db":
        user_state[uid] = {"menu": "admin_import_db_wait_file"}
        bot.send_message(
            chat_id,
            "📥 <b>DB Import</b>\n\n"
            "⚠️ এটা করলে বর্তমান সব ডেটা (Users/ব্যালেন্স/Orders/Deposits/SMS Log) মুছে "
            "আপলোড করা ব্যাকআপ (.json) ফাইল দিয়ে রিপ্লেস হয়ে যাবে।\n\n"
            "আগে এই বটের Export করা ব্যাকআপ ফাইলটা (.json বা .json.gz) পাঠান।",
            reply_markup=back_to_main_keyboard(),
        )

    elif data == "admin_deposit_requests":
        pending = [d for d in deposits.values() if d["status"] == "pending"]
        if not pending:
            bot.send_message(chat_id, "💰 <b>Pending Deposits</b>\n\nএখন কোনো pending deposit নেই।")
        else:
            for d in pending[:20]:
                du = users.get(d["user_id"], {})
                usdt_line = f"💵 USDT Amount: {d['amount_usdt']} USDT\n" if d.get("amount_usdt") is not None else ""
                sent = bot.send_message(
                    chat_id,
                    "💰 <b>Pending Deposit</b>\n\n"
                    f"🆔 DEP-{d['id']}\n"
                    f"👤 User: {du.get('full_name', '—')} | <code>{d['user_id']}</code>\n"
                    f"💳 Method: {d['method']}\n"
                    f"{usdt_line}"
                    f"💰 Amount: {fmt_amount(d['amount'])}\n"
                    f"🧾 {_id_label(d['method'])}: <code>{d['trx_id']}</code>\n"
                    f"📅 {d['date']}",
                    reply_markup=deposit_review_inline(d["id"]),
                )
                _track_deposit_admin_msg(d, chat_id, sent.message_id)
            save_db()   # ✅ admin_msgs রেফারেন্স ডিস্কে persist করা হলো

    elif data == "admin_deposit_numbers":
        user_state[uid] = {"menu": "admin_deposit_numbers"}
        bot.send_message(
            chat_id,
            "📮 <b>Deposit Payment Numbers</b>\n\nযে মেথডের নাম্বার/অ্যাড্রেস সেট করবেন সেটায় ক্লিক করুন।",
            reply_markup=deposit_numbers_inline(),
        )

    elif data == "admin_bot_settings":
        user_state[uid] = {"menu": "admin_bot_settings"}
        bot.send_message(
            chat_id,
            "⚙️ <b>Bot Settings</b>\n\nযে সেটিংসটি বদলাতে চান, তাতে ক্লিক করুন।",
            reply_markup=bot_settings_inline(),
        )

    elif data == "admin_force_join":
        user_state[uid] = {"menu": "admin_force_join"}
        bot.send_message(
            chat_id,
            "🔐 <b>Force Join Settings</b>\n\n"
            "ইউজার প্রথমবার বট স্টার্ট করলে নিচের চ্যানেল/গ্রুপ(গুলো)-এ জয়েন করতে "
            "বলা হবে। জয়েন না করা পর্যন্ত বট ব্যবহার করতে পারবে না।",
            reply_markup=force_join_admin_inline(),
        )

    elif data == "admin_back_to_menu":
        user_state[uid] = {"menu": "main"}
        bot.send_message(chat_id, "🏠 Main Menu", reply_markup=main_menu_keyboard(uid))


# ---------------------------------------------------------------------------
# ADMIN PANEL: 🔐 Force Join সাব-মেনুর callbacks
# ---------------------------------------------------------------------------
@bot.callback_query_handler(func=lambda c: c.data.startswith("fj_") and is_admin(c.from_user.id))
def cb_force_join_admin(call):
    uid = call.from_user.id
    chat_id = call.message.chat.id
    data = call.data
    bot.answer_callback_query(call.id)

    if data == "fj_noop":
        return

    if data == "fj_back":
        user_state[uid] = {"menu": "admin_panel"}
        bot.send_message(chat_id, "👮 <b>Admin Panel</b>", reply_markup=admin_panel_inline())
        return

    if data == "fj_add":
        user_state[uid] = {"menu": "admin_fj_add_name", "fj_new": {}}
        bot.send_message(
            chat_id,
            "🔐 <b>নতুন Force Join Channel/Group যুক্ত করুন</b>\n\n"
            "প্রথমে চ্যানেল/গ্রুপের নাম (লেবেল) লিখে পাঠান, যেমন: My Channel",
            reply_markup=back_to_main_keyboard(),
        )
        bot.register_next_step_handler(call.message, process_fj_name)
        return

    if data.startswith("fj_remove_"):
        try:
            idx = int(data.replace("fj_remove_", ""))
        except ValueError:
            idx = -1
        channels = get_force_join_channels()
        if 0 <= idx < len(channels):
            removed = channels.pop(idx)
            save_db()
            bot.send_message(
                chat_id,
                f"🗑️ Removed: {removed.get('name', 'Channel')}",
                reply_markup=force_join_admin_inline(),
            )
        else:
            bot.send_message(chat_id, "⚠️ খুঁজে পাওয়া যায়নি।", reply_markup=force_join_admin_inline())
        return


def process_fj_name(message):
    uid = message.from_user.id
    if not is_admin(uid):
        return
    text = (message.text or "").strip()
    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return
    if not text:
        bot.send_message(message.chat.id, "⚠️ সঠিক নাম লিখুন।")
        bot.register_next_step_handler(message, process_fj_name)
        return

    state = user_state.get(uid, {})
    fj_new = state.get("fj_new", {})
    fj_new["name"] = text
    user_state[uid] = {"menu": "admin_fj_add_link", "fj_new": fj_new}
    bot.send_message(
        message.chat.id,
        "🔗 এখন জয়েন করার Invite Link পাঠান।\n"
        "উদাহরণ: https://t.me/your_channel অথবা https://t.me/+AbCdEfGh...",
    )
    bot.register_next_step_handler(message, process_fj_link)


def process_fj_link(message):
    uid = message.from_user.id
    if not is_admin(uid):
        return
    text = (message.text or "").strip()
    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return
    if not text.startswith(("http://", "https://", "t.me/", "@")):
        bot.send_message(message.chat.id, "⚠️ সঠিক লিংক পাঠান (https://t.me/... দিয়ে শুরু)।")
        bot.register_next_step_handler(message, process_fj_link)
        return

    state = user_state.get(uid, {})
    fj_new = state.get("fj_new", {})
    fj_new["link"] = text
    user_state[uid] = {"menu": "admin_fj_add_chatid", "fj_new": fj_new}
    bot.send_message(
        message.chat.id,
        "🆔 এখন চ্যানেল/গ্রুপের ID অথবা @username পাঠান (Membership যাচাই করার জন্য "
        "বট এই চ্যানেল/গ্রুপে অবশ্যই Admin হিসেবে থাকতে হবে)।\n\n"
        "উদাহরণ: @your_channel অথবা -1001234567890",
    )
    bot.register_next_step_handler(message, process_fj_chatid)


def process_fj_chatid(message):
    uid = message.from_user.id
    if not is_admin(uid):
        return
    text = (message.text or "").strip()
    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return
    if not text:
        bot.send_message(message.chat.id, "⚠️ সঠিক ID/username লিখুন।")
        bot.register_next_step_handler(message, process_fj_chatid)
        return

    chat_ref = text
    if not (chat_ref.startswith("@") or chat_ref.startswith("-") or chat_ref.lstrip("-").isdigit()):
        chat_ref = f"@{chat_ref.lstrip('@')}"

    # বট আসলেই ঐ চ্যানেল/গ্রুপে অ্যাক্সেস পায় কিনা যাচাই করা হচ্ছে
    try:
        chat = bot.get_chat(chat_ref)
    except Exception as e:
        bot.send_message(
            message.chat.id,
            "❌ এই চ্যানেল/গ্রুপ খুঁজে পাওয়া যায়নি অথবা বট এখানে নেই।\n"
            f"এরর: {e}\n\n"
            "বটকে আগে ঐ চ্যানেল/গ্রুপে Admin হিসেবে যুক্ত করে আবার ID/username পাঠান, "
            "অথবা ⬅️ Back চাপুন।",
        )
        bot.register_next_step_handler(message, process_fj_chatid)
        return

    state = user_state.get(uid, {})
    fj_new = state.get("fj_new", {})
    fj_new["chat_id"] = chat.id
    fj_new.setdefault("name", chat.title or chat_ref)
    bot_settings.setdefault("force_join_channels", []).append(fj_new)
    save_db()

    bot.send_message(
        message.chat.id,
        f"✅ যুক্ত হয়েছে: <b>{fj_new.get('name')}</b>\n"
        f"🆔 <code>{fj_new['chat_id']}</code>",
        reply_markup=force_join_admin_inline(),
    )
    user_state[uid] = {"menu": "admin_force_join"}


# ---------------------------------------------------------------------------
# ADMIN PANEL: ⚙️ Bot Settings সাব-মেনুর callbacks
# ---------------------------------------------------------------------------
@bot.callback_query_handler(func=lambda c: c.data.startswith("settings_") and is_admin(c.from_user.id))
def cb_bot_settings(call):
    uid = call.from_user.id
    chat_id = call.message.chat.id
    data = call.data
    bot.answer_callback_query(call.id)

    if data == "settings_back":
        user_state[uid] = {"menu": "admin_panel"}
        bot.send_message(chat_id, "👮 <b>Admin Panel</b>", reply_markup=admin_panel_inline())
        return

    if data == "settings_toggle_maintenance":
        bot_settings["maintenance_mode"] = not bot_settings["maintenance_mode"]
        save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)
        status = "চালু ✅" if bot_settings["maintenance_mode"] else "বন্ধ ❌"
        bot.send_message(
            chat_id,
            f"🛠️ Maintenance Mode এখন {status} করা হয়েছে।",
            reply_markup=bot_settings_inline(),
        )
        return

    if data == "settings_referral_bonus":
        user_state[uid] = {"menu": "admin_settings_referral_bonus"}
        bot.send_message(
            chat_id,
            "🎁 প্রতি রেফারেলে নতুন বোনাস অ্যামাউন্ট লিখে পাঠান।\n"
            f"বর্তমান: {fmt_amount(bot_settings['referral_bonus'])}\n\n"
            "উদাহরণ: 15 অথবা 20.50",
        )
        bot.register_next_step_handler(call.message, process_settings_referral_bonus)
        return

    if data == "settings_deposit_limits":
        user_state[uid] = {"menu": "admin_settings_deposit_limits"}
        bot.send_message(
            chat_id,
            "💳 Min ও Max Deposit লিখে পাঠান, কমা দিয়ে আলাদা করে।\n"
            f"বর্তমান: {bot_settings['min_deposit']} , {bot_settings['max_deposit']}\n\n"
            "উদাহরণ: 50,5000  (সীমা রাখতে না চাইলে 0,0 লিখুন)",
        )
        bot.register_next_step_handler(call.message, process_settings_deposit_limits)
        return

    if data == "settings_deposit_methods":
        user_state[uid] = {"menu": "admin_settings_deposit_methods"}
        bot.send_message(
            chat_id,
            "💳 কমা দিয়ে আলাদা করে Deposit Method গুলো লিখে পাঠান।\n"
            f"বর্তমান: {', '.join(bot_settings['deposit_methods'])}\n\n"
            "উদাহরণ: bKash,Nagad,Rocket,Binance,Manual Bank\n\n"
            f"⚠️ শুধু {', '.join(DEPOSIT_MANUAL_METHODS)} — এই কয়টা মেথড সবসময় ম্যানুয়াল Admin "
            "approval এ যাবে; বাকি যেকোনো নতুন মেথড (যেমন 'Manual Bank') যোগ করলে সেটা সাথে "
            "সাথে অটো-অ্যাপ্রুভ হয়ে যাবে।",
        )
        bot.register_next_step_handler(call.message, process_settings_deposit_methods)
        return

    if data == "settings_support_username":
        user_state[uid] = {"menu": "admin_settings_support_username"}
        bot.send_message(
            chat_id,
            "🆘 Support এর Telegram username লিখে পাঠান (@ সহ বা ছাড়া, দুটোই চলবে)।\n"
            f"বর্তমান: {bot_settings['support_username'] or 'সেট করা নেই'}\n\n"
            "উদাহরণ: @relax1472",
        )
        bot.register_next_step_handler(call.message, process_settings_support_username)
        return

    if data == "settings_method_video":
        user_state[uid] = {"menu": "admin_method_video_list"}
        bot.send_message(
            chat_id,
            "🎥 <b>Method Videos</b>\n\n"
            "বর্তমান ভিডিও বাটনগুলো নিচে দেখানো হলো। ডিলেট করতে চাইলে সংশ্লিষ্ট "
            "🗑️ Remove বাটনে ক্লিক করুন, অথবা নতুন যুক্ত করতে ➕ Add New Video চাপুন।",
            reply_markup=method_video_admin_inline(),
        )
        return


def process_settings_method_video_title(message):
    uid = message.from_user.id
    if not is_admin(uid):
        return

    text = (message.text or "").strip()
    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return

    if not text:
        bot.send_message(message.chat.id, "⚠️ সঠিক একটি Title লিখুন।")
        bot.register_next_step_handler(message, process_settings_method_video_title)
        return

    user_state[uid] = {"menu": "admin_settings_method_video_link", "video_title": text}
    bot.send_message(
        message.chat.id,
        f"🎥 Title: {text}\n\nএখন এই বাটনের জন্য ভিডিও লিংক লিখে পাঠান।\n\nউদাহরণ: https://youtu.be/xxxxxxx",
    )
    bot.register_next_step_handler(message, process_settings_method_video_link)


def process_settings_method_video_link(message):
    uid = message.from_user.id
    if not is_admin(uid):
        return

    text = (message.text or "").strip()
    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return

    state = user_state.get(uid, {})
    title = state.get("video_title")
    if state.get("menu") != "admin_settings_method_video_link" or not title:
        bot.send_message(message.chat.id, "⚠️ সেশন খুঁজে পাওয়া যায়নি। Bot Settings থেকে আবার চেষ্টা করুন।")
        user_state[uid] = {"menu": "admin_bot_settings"}
        return

    if not text.startswith(("http://", "https://")):
        bot.send_message(message.chat.id, "⚠️ সঠিক একটি লিংক লিখুন (http:// বা https:// দিয়ে শুরু)।")
        bot.register_next_step_handler(message, process_settings_method_video_link)
        return

    bot_settings["method_videos"].append({"title": title, "link": text})
    save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)
    bot.send_message(
        message.chat.id,
        f"✅ নতুন Method বাটন যুক্ত হয়েছে!\n\n🎥 Title: {title}\n🔗 Link: {text}",
        reply_markup=method_video_admin_inline(),
    )
    user_state[uid] = {"menu": "admin_method_video_list"}


# ---------------------------------------------------------------------------
# ADMIN PANEL: 🎥 Method Videos সাব-মেনুর callbacks (Add / Remove)
# ---------------------------------------------------------------------------
@bot.callback_query_handler(func=lambda c: c.data.startswith("mv_") and is_admin(c.from_user.id))
def cb_method_video_admin(call):
    uid = call.from_user.id
    chat_id = call.message.chat.id
    data = call.data
    bot.answer_callback_query(call.id)

    if data == "mv_noop":
        return

    if data == "mv_add":
        current = bot_settings["method_videos"]
        current_line = ""
        if current:
            listing = "\n".join(f"• {v['title']}" for v in current)
            current_line = f"বর্তমান ভিডিও বাটনগুলো:\n{listing}\n\n"
        user_state[uid] = {"menu": "admin_settings_method_video_title"}
        bot.send_message(
            chat_id,
            "🎥 ⚙️ Method বাটনে নতুন একটা ভিডিও বাটন যোগ করতে প্রথমে বাটনের Title লিখে পাঠান।\n\n"
            f"{current_line}উদাহরণ: bKash Tutorial",
        )
        bot.register_next_step_handler(call.message, process_settings_method_video_title)
        return

    if data.startswith("mv_remove_"):
        try:
            idx = int(data.replace("mv_remove_", ""))
        except ValueError:
            idx = -1
        videos = bot_settings.get("method_videos") or []
        if 0 <= idx < len(videos):
            removed = videos.pop(idx)
            save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)
            bot.send_message(
                chat_id,
                f"🗑️ Removed: {removed.get('title', 'Video')}",
                reply_markup=method_video_admin_inline(),
            )
        else:
            bot.send_message(chat_id, "⚠️ খুঁজে পাওয়া যায়নি।", reply_markup=method_video_admin_inline())
        return

    if data == "mv_back":
        user_state[uid] = {"menu": "admin_bot_settings"}
        bot.send_message(
            chat_id,
            "⚙️ <b>Bot Settings</b>\n\nযে সেটিংসটি বদলাতে চান, তাতে ক্লিক করুন।",
            reply_markup=bot_settings_inline(),
        )
        return


def process_settings_support_username(message):
    uid = message.from_user.id
    if not is_admin(uid):
        return

    text = (message.text or "").strip()
    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return

    username = text.lstrip("@").strip()
    if not username:
        bot.send_message(message.chat.id, "⚠️ সঠিক একটি username লিখুন (যেমন: @relax1472)।")
        bot.register_next_step_handler(message, process_settings_support_username)
        return

    bot_settings["support_username"] = username
    save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)
    bot.send_message(
        message.chat.id,
        f"✅ Support Username আপডেট হয়েছে: @{username}",
        reply_markup=bot_settings_inline(),
    )
    user_state[uid] = {"menu": "admin_bot_settings"}


def process_settings_deposit_methods(message):
    uid = message.from_user.id
    if not is_admin(uid):
        return

    text = (message.text or "").strip()
    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return

    methods = [p.strip() for p in text.split(",") if p.strip()]
    if not methods:
        bot.send_message(message.chat.id, "⚠️ অন্তত একটা মেথড লিখুন।")
        bot.register_next_step_handler(message, process_settings_deposit_methods)
        return

    bot_settings["deposit_methods"] = methods
    save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)
    for m in methods:
        bot_settings["deposit_numbers"].setdefault(m, "")

    bot.send_message(
        message.chat.id,
        f"✅ Deposit Methods আপডেট হয়েছে: {', '.join(methods)}",
        reply_markup=bot_settings_inline(),
    )
    user_state[uid] = {"menu": "admin_bot_settings"}


def process_settings_referral_bonus(message):
    uid = message.from_user.id
    if not is_admin(uid):
        return

    text = (message.text or "").strip()
    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return

    try:
        new_bonus = float(text)
    except ValueError:
        new_bonus = None

    if new_bonus is None or new_bonus < 0:
        bot.send_message(message.chat.id, "⚠️ সঠিক একটি সংখ্যা লিখুন (যেমন: 15 অথবা 20.50)।")
        bot.register_next_step_handler(message, process_settings_referral_bonus)
        return

    if new_bonus == int(new_bonus):
        new_bonus = int(new_bonus)

    bot_settings["referral_bonus"] = new_bonus
    save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)
    bot.send_message(
        message.chat.id,
        f"✅ Referral Bonus আপডেট হয়েছে: {fmt_amount(new_bonus)}",
        reply_markup=bot_settings_inline(),
    )
    user_state[uid] = {"menu": "admin_bot_settings"}


def process_settings_deposit_limits(message):
    uid = message.from_user.id
    if not is_admin(uid):
        return

    text = (message.text or "").strip()
    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return

    parts = [p.strip() for p in text.split(",")]
    if len(parts) != 2 or not all(p.replace(".", "", 1).isdigit() for p in parts):
        bot.send_message(message.chat.id, "⚠️ সঠিক ফরম্যাটে লিখুন, যেমন: 50,5000")
        bot.register_next_step_handler(message, process_settings_deposit_limits)
        return

    min_dep, max_dep = float(parts[0]), float(parts[1])
    min_dep = int(min_dep) if min_dep == int(min_dep) else min_dep
    max_dep = int(max_dep) if max_dep == int(max_dep) else max_dep

    if max_dep and min_dep > max_dep:
        bot.send_message(message.chat.id, "⚠️ Min, Max এর থেকে বেশি হতে পারবে না। আবার লিখুন।")
        bot.register_next_step_handler(message, process_settings_deposit_limits)
        return

    bot_settings["min_deposit"] = min_dep
    save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)
    bot_settings["max_deposit"] = max_dep
    bot.send_message(
        message.chat.id,
        f"✅ Deposit Limit আপডেট হয়েছে: {min_dep} - {max_dep} BDT",
        reply_markup=bot_settings_inline(),
    )
    user_state[uid] = {"menu": "admin_bot_settings"}


@bot.callback_query_handler(func=lambda c: c.data.startswith("depnum_") and is_admin(c.from_user.id))
def cb_deposit_number_set_start(call):
    method = call.data.replace("depnum_", "")
    bot.answer_callback_query(call.id)
    user_state[call.from_user.id] = {"menu": "admin_deposit_number_value", "method": method}
    current = bot_settings["deposit_numbers"].get(method) or "সেট করা নেই"
    bot.send_message(
        call.message.chat.id,
        f"📮 <b>{method}</b> এর জন্য নতুন Number/Address লিখে পাঠান।\nবর্তমান: {current}",
    )
    bot.register_next_step_handler(call.message, process_deposit_number_value)


def process_deposit_number_value(message):
    uid = message.from_user.id
    if not is_admin(uid):
        return

    text = (message.text or "").strip()
    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return

    state = user_state.get(uid, {})
    method = state.get("method")
    if not method:
        bot.send_message(message.chat.id, "⚠️ মেথড খুঁজে পাওয়া যায়নি। আবার চেষ্টা করুন।")
        user_state[uid] = {"menu": "admin_panel"}
        return

    bot_settings["deposit_numbers"][method] = text   # TODO: DB তে persist করুন
    bot.send_message(
        message.chat.id,
        f"✅ {method} এর Number/Address আপডেট হয়েছে:\n<code>{text}</code>",
        reply_markup=deposit_numbers_inline(),
    )
    user_state[uid] = {"menu": "admin_deposit_numbers"}


def broadcast_to_all_users(text):
    """সব ইউজারকে একটা মেসেজ পাঠায়, কতজনকে পাঠানো গেছে/ব্যর্থ হয়েছে তার কাউন্ট রিটার্ন করে।"""
    sent, failed = 0, 0
    for user_id in list(users.keys()):
        try:
            bot.send_message(user_id, text)
            sent += 1
        except Exception:
            failed += 1  # ইউজার হয়তো বটকে ব্লক করেছে
    return sent, failed


def process_broadcast_message(message):
    """Admin এর লেখা মেসেজ সব ইউজারকে broadcast করে।"""
    uid = message.from_user.id
    if not is_admin(uid):
        return

    text = (message.text or "").strip()

    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return

    if not text:
        bot.send_message(message.chat.id, "⚠️ মেসেজ খালি রাখা যাবে না। আবার লিখুন।")
        bot.register_next_step_handler(message, process_broadcast_message)
        return

    sent, failed = broadcast_to_all_users(text)
    bot.send_message(
        message.chat.id,
        "✅ <b>Broadcast সম্পন্ন!</b>\n\n"
        f"👥 পাঠানো হয়েছে: {sent} জনকে\n"
        f"❌ ব্যর্থ: {failed} জন",
        reply_markup=admin_panel_inline(),
    )
    user_state[uid] = {"menu": "admin_panel"}


@bot.callback_query_handler(func=lambda c: c.data.startswith("uploadprod_") and is_admin(c.from_user.id))
def cb_admin_upload_product_select(call):
    product_key = call.data.replace("uploadprod_", "")
    p = products.get(product_key)
    if not p:
        bot.answer_callback_query(call.id, "Product not found.")
        return

    user_state[call.from_user.id] = {"menu": "admin_upload_file", "product": product_key}
    bot.answer_callback_query(call.id)
    if _is_proxy_sub(product_key):
        bot.send_message(
            call.message.chat.id,
            f"📤 <b>{_html.escape(catalog_name(product_key))}</b> এর জন্য Proxy স্টক ফাইল পাঠান (.xlsx / .csv / .txt)।\n\n"
            "📊 ১ম সারি = হেডিং (যেমন: <code>Server</code> | <code>Port</code> | <code>Username</code> | <code>Password</code>), "
            "এরপর প্রতি সারিতে ১ পিস প্রক্সি।\n"
            "ইউজার কিনলে ঠিক এই হেডিং অনুযায়ীই ডেটা পাবে, যেমন:\n"
            "<code>Server: 1.2.3.4</code>\n<code>Port: 8080</code>\n\n"
            "📄 .csv/.txt এও ১ম লাইন হেডিং, বাকি লাইনে ডেটা (আলাদা করতে <code>|</code> বা <code>,</code> বা Tab)।\n\n"
            "ফাইল পাঠানোর পর stock এ যুক্ত করার আগে confirm করতে বলা হবে।",
        )
        return
    if _is_vpn_sub(product_key):
        bot.send_message(
            call.message.chat.id,
            f"📤 <b>{_html.escape(catalog_name(product_key))}</b> এর জন্য VPN স্টক ফাইল পাঠান (.txt / .csv / .xlsx)।\n\n"
            "📄 প্রতি লাইনে ১টা VPN (যেমন: username|password অথবা কী/কনফিগ/লিংক) — "
            "প্রতিটা লাইন ১ পিস স্টক হবে এবং ইউজার কিনলে পুরো লাইনটাই পাবে।\n"
            "📊 .xlsx এ প্রতি সারি ১ পিস (একাধিক ঘর থাকলে ' | ' দিয়ে জোড়া লাগবে)।\n\n"
            "ফাইল পাঠানোর পর stock এ যুক্ত করার আগে confirm করতে বলা হবে।",
        )
        return
    bot.send_message(
        call.message.chat.id,
        f"📤 <b>{p['name']}</b> এর জন্য স্টক ফাইল পাঠান (.txt / .csv / .xlsx)।\n\n"
        "📄 .txt বা .csv এ প্রতি লাইনে ১টা অ্যাকাউন্ট এই ফরম্যাটে দিন:\n"
        "<code>Email|Password|M.C...</code>\n\n"
        "📊 .xlsx এ প্রতি সারিতে হয় পুরো লাইনটা (<code>Email|Password|M.C...</code>) এক ঘরে দিন, "
        "অথবা ১ম কলামে Email, ২য় কলামে Password, ৩য় কলামে Token দিন।\n\n"
        "ইউজার কিনলে Token হিসেবে আপলোড করা পুরো লাইনটাই পাবে।\n\n"
        "ফাইল পাঠানোর পর stock এ যুক্ত করার আগে আপনাকে confirm করতে বলা হবে।",
    )


def _build_unsold_export_workbook():
    """যেসব প্রোডাক্টের stock_list এ এখনও অবিক্রিত (unsold) নাম্বার আছে, তাদের জন্য
    একটা .xlsx ওয়ার্কবুক বানায় — প্রতিটা প্রোডাক্টের জন্য আলাদা শীট, কলাম:
    Email | Password | Token। কোনো প্রোডাক্টেই স্টক না থাকলে None রিটার্ন করে।"""
    from openpyxl import Workbook  # লেজি ইমপোর্ট: শুধু এক্সপোর্ট করার সময়ই দরকার
    from openpyxl.styles import Font, PatternFill

    wb = Workbook()
    wb.remove(wb.active)   # ডিফল্ট খালি শীট বাদ দেওয়া হলো

    header_font = Font(bold=True, color="FFFFFF")
    header_fill = PatternFill(start_color="4472C4", end_color="4472C4", fill_type="solid")

    used_titles = set()
    any_stock = False
    for key, p in products.items():
        stock_list = p.get("stock_list") or []
        if not stock_list:
            continue
        any_stock = True

        # Excel শীটের নাম সর্বোচ্চ ৩১ ক্যারেক্টার, ডুপ্লিকেট হলে সাফিক্স যোগ করা হচ্ছে
        base_title = (p.get("name") or key).strip()[:31] or key
        title = base_title
        n = 2
        while title in used_titles:
            suffix = f" ({n})"
            title = base_title[: 31 - len(suffix)] + suffix
            n += 1
        used_titles.add(title)

        ws = wb.create_sheet(title=title)
        if _is_proxy_sub(key):
            _h, _rows = _proxy_table(stock_list)
            ws.append(_h)
            for cell in ws[1]:
                cell.font = header_font
                cell.fill = header_fill
            for r in _rows:
                ws.append(r)
            continue
        if _is_vpn_sub(key):
            ws.append(["VPN Details"])
            ws["A1"].font = header_font
            ws["A1"].fill = header_fill
            for item in stock_list:
                ws.append([_vpn_content(item)])
            ws.column_dimensions["A"].width = 100
            continue
        ws.append(["Email", "Password", "Token"])
        for cell in ws[1]:
            cell.font = header_font
            cell.fill = header_fill
        for item in stock_list:
            ws.append(list(_item_fields(item)))
        ws.column_dimensions["A"].width = 32
        ws.column_dimensions["B"].width = 22
        ws.column_dimensions["C"].width = 80

    if not any_stock:
        return None
    return wb


def _vpn_item(line):
    """VPN স্টকের ১ পিস: পুরো লাইনটাই কনটেন্ট। বাকি কী-গুলো মেইল-ফরম্যাটের কোডের (export/order) সাথে মেলানোর জন্য।"""
    line = (line or "").strip()
    return {"content": line, "email": line, "password": "", "token": line, "number": line, "otp_link": ""}


def _proxy_item(headers, values):
    """হেডিং ↔ ভ্যালু জোড়া। বাকি কী-গুলো মেইল-ফরম্যাটের কোডের (order/export) সাথে মেলানোর জন্য।"""
    pairs = [[h, v] for h, v in zip(headers, values)]
    line = " | ".join(v for _h, v in pairs if v != "")
    return {"fields": pairs, "content": line, "email": line, "password": "", "token": line, "number": line, "otp_link": ""}


def _clean_headers(cells):
    out = []
    for i, c in enumerate(cells, 1):
        h = str(c if c is not None else "").strip() or f"Column {i}"
        while h in out:
            h += "_"
        out.append(h)
    return out


def parse_proxy_stock_rows(rows):
    """rows = [[cell, ...], ...] — ১ম non-empty সারি হেডিং। (items, skipped)"""
    rows = [[("" if c is None else str(c).strip()) for c in r] for r in rows]
    rows = [r for r in rows if any(r)]
    if len(rows) < 2:
        return [], 0
    headers = _clean_headers(rows[0])
    items, skipped = [], 0
    for r in rows[1:]:
        vals = (r + [""] * len(headers))[:len(headers)]
        if not any(vals):
            skipped += 1
            continue
        items.append(_proxy_item(headers, vals))
    return items, skipped


def parse_proxy_stock_from_xlsx(file_bytes):
    from openpyxl import load_workbook

    wb = load_workbook(io.BytesIO(file_bytes), data_only=True, read_only=True)
    ws = wb.active
    return parse_proxy_stock_rows([list(r or ()) for r in ws.iter_rows(values_only=True)])


def parse_proxy_stock_from_text(text):
    lines = [l for l in text.splitlines() if l.strip()]
    if len(lines) < 2:
        return [], 0
    delim = max(("|", ",", "\t", ";"), key=lambda d: lines[0].count(d))
    if lines[0].count(delim) == 0:
        delim = ","
    import csv as _csv
    return parse_proxy_stock_rows(list(_csv.reader(lines, delimiter=delim)))


def parse_vpn_stock_from_xlsx(file_bytes):
    """VPN xlsx: প্রতি সারি = ১ পিস (একাধিক ঘর থাকলে ' | ' দিয়ে জোড়া)। (items, skipped)"""
    from openpyxl import load_workbook

    wb = load_workbook(io.BytesIO(file_bytes), data_only=True, read_only=True)
    ws = wb.active
    items = []
    for row in ws.iter_rows(values_only=True):
        cells = [str(c).strip() for c in (row or ()) if c not in (None, "")]
        if not cells:
            continue
        if len(items) == 0 and cells[0].lower() in ("vpn details", "vpn", "details"):
            continue
        items.append(_vpn_item(" | ".join(cells)))
    return items, 0


def parse_stock_from_xlsx(file_bytes):
    """xlsx এর প্রথম শীট থেকে মেইল অ্যাকাউন্ট রিড করে। (items, skipped) রিটার্ন করে।
    সারিতে শুধু এক ঘর থাকলে সেটা পুরো `Email|Password|Token` লাইন ধরা হয়;
    নাহলে ১ম কলাম Email, ২য় Password, ৩য় Token (না থাকলে email|password)।"""
    from openpyxl import load_workbook  # লেজি ইমপোর্ট: শুধু .xlsx আপলোড হলেই দরকার

    wb = load_workbook(io.BytesIO(file_bytes), data_only=True, read_only=True)
    ws = wb.active
    items, skipped = [], 0
    for row in ws.iter_rows(values_only=True):
        cells = [str(c).strip() for c in (row or ()) if c not in (None, "")]
        if not cells:
            continue
        if cells[0].lower() in ("email", "e-mail", "mail"):
            continue
        if len(cells) == 1:
            it = parse_mail_stock_line(cells[0])
        else:
            email, password = cells[0], cells[1]
            token = cells[2] if len(cells) > 2 else f"{email}|{password}"
            it = _mail_item(email, password, token) if email and password else None
        if it:
            items.append(it)
        else:
            skipped += 1
    return items, skipped


@bot.message_handler(content_types=["document"])
def handle_document_upload(message):
    uid = message.from_user.id
    if not is_admin(uid):
        return
    state = user_state.get(uid, {})
    menu = state.get("menu")

    if menu == "admin_import_db_wait_file":
        handle_db_import_file(message)
        return

    if menu != "admin_upload_file":
        return

    product_key = state.get("product")
    p = products.get(product_key)
    if not p:
        bot.send_message(message.chat.id, "⚠️ প্রোডাক্ট খুঁজে পাওয়া যায়নি। Admin Panel থেকে আবার চেষ্টা করুন।")
        user_state[uid] = {"menu": "admin_panel"}
        return

    file_name = message.document.file_name or ""
    if not file_name.lower().endswith((".txt", ".csv", ".xlsx")):
        bot.send_message(message.chat.id, "⚠️ শুধুমাত্র .txt, .csv বা .xlsx ফাইল সাপোর্ট করে। আবার পাঠান।")
        return

    # ফাইল ডাউনলোড ও parse করা হচ্ছে - এখনো stock এ যুক্ত হয়নি, শুধু preview/confirmation এর জন্য
    try:
        file_info = bot.get_file(message.document.file_id)
        downloaded = bot.download_file(file_info.file_path)
    except Exception as e:
        bot.send_message(message.chat.id, f"❌ ফাইল ডাউনলোড করতে সমস্যা হয়েছে: {e}")
        return

    parsed_items = []
    skipped = 0
    is_vpn = _is_vpn_sub(product_key)
    is_proxy = _is_proxy_sub(product_key)
    try:
        if file_name.lower().endswith(".xlsx"):
            if is_proxy:
                parsed_items, skipped = parse_proxy_stock_from_xlsx(downloaded)
            else:
                parsed_items, skipped = parse_vpn_stock_from_xlsx(downloaded) if is_vpn else parse_stock_from_xlsx(downloaded)
        elif is_proxy:
            parsed_items, skipped = parse_proxy_stock_from_text(downloaded.decode("utf-8-sig", errors="ignore"))
        else:
            text = downloaded.decode("utf-8-sig", errors="ignore")
            for raw_line in text.splitlines():
                line = raw_line.strip()
                if not line:
                    continue
                it = _vpn_item(line) if is_vpn else parse_mail_stock_line(line)
                if it:
                    parsed_items.append(it)
                else:
                    skipped += 1
    except ImportError:
        bot.send_message(
            message.chat.id,
            "❌ .xlsx ফাইল পড়ার জন্য সার্ভারে openpyxl লাইব্রেরি ইনস্টল নেই।\n"
            "ইনস্টল করুন: pip install openpyxl",
        )
        return
    except Exception as e:
        bot.send_message(message.chat.id, f"❌ ফাইল পার্স করতে সমস্যা হয়েছে: {e}")
        return

    if not parsed_items:
        if is_proxy:
            bot.send_message(message.chat.id, "⚠️ ফাইলে হেডিং সহ অন্তত ১টা ডেটা সারি থাকতে হবে। ১ম সারিতে হেডিং (Server, Port...) দিয়ে আবার পাঠান।")
        else:
            bot.send_message(message.chat.id, "⚠️ ফাইলে কোনো valid লাইন পাওয়া যায়নি। ফরম্যাট চেক করে আবার পাঠান।")
        return

    # price আর জিজ্ঞেস করা হয় না — প্রোডাক্টের নিজস্ব price (Admin Panel থেকে সেট করা)
    # ব্যবহার হয়, তাই ফাইল parse হওয়ার সাথে সাথেই সরাসরি Confirm ধাপে যাওয়া হচ্ছে।
    user_state[uid] = {
        "menu": "admin_upload_confirm",
        "product": product_key,
        "pending_items": parsed_items,
    }

    if is_proxy:
        _h = _proxy_table(parsed_items)[0]
        preview = "🧾 হেডিং: " + _e(" | ".join(_h)) + "\n" + "\n".join(
            "• " + _e(" | ".join(v for _hh, v in _proxy_fields(it) if v != "")[:70]) for it in parsed_items[:3])
    elif is_vpn:
        preview = "\n".join(f"• {_e(_vpn_content(it)[:60])}" for it in parsed_items[:3])
    else:
        preview = "\n".join(f"• {_e(it['email'])} | {_e(it['password'])}" for it in parsed_items[:3])
    if len(parsed_items) > 3:
        preview += f"\n...আরও {len(parsed_items) - 3} টি"

    current_stock = len(p.setdefault("stock_list", []))
    bot.send_message(
        message.chat.id,
        "🔎 <b>Confirm Stock Upload</b>\n\n"
        f"📦 প্রোডাক্ট: {p['name']}\n"
        f"📄 ফাইল: {file_name}\n"
        f"🔢 ফাইলে পাওয়া গেছে: {len(parsed_items)} পিস\n"
        + (f"⚠️ ভুল ফরম্যাটের {skipped} লাইন বাদ গেছে (ফরম্যাট: Email|Password|M.C...)\n" if skipped else "")
        + "\n"
        f"প্রিভিউ:\n{preview}\n\n"
        f"📊 বর্তমান স্টক: {current_stock} → Confirm করলে হবে: {current_stock + len(parsed_items)}\n\n"
        "এই এন্ট্রিগুলো stock এ যুক্ত করতে চান?",
        reply_markup=upload_confirm_inline(),
    )


@bot.callback_query_handler(
    func=lambda c: c.data in ("stockup_confirm", "stockup_cancel") and is_admin(c.from_user.id)
)
def cb_admin_upload_confirm(call):
    uid = call.from_user.id
    chat_id = call.message.chat.id
    state = user_state.get(uid, {})
    bot.answer_callback_query(call.id)

    if state.get("menu") != "admin_upload_confirm":
        bot.send_message(chat_id, "⚠️ কোনো pending upload নেই। আগে একটা ফাইল পাঠান।")
        return

    if call.data == "stockup_cancel":
        bot.send_message(
            chat_id,
            "❌ Upload বাতিল করা হয়েছে। কিছুই stock এ যুক্ত হয়নি।",
            reply_markup=admin_panel_inline(),
        )
        user_state[uid] = {"menu": "admin_panel"}
        return

    # stockup_confirm
    product_key = state.get("product")
    pending_items = state.get("pending_items", [])
    p = products.get(product_key)

    if not p or not pending_items:
        bot.send_message(chat_id, "⚠️ Pending ডেটা খুঁজে পাওয়া যায়নি। আবার আপলোড করুন।")
        user_state[uid] = {"menu": "admin_panel"}
        return

    with _stock_lock:   # 🔒 ক্রেতারা যখন pop করছে তখন একই সময়ে স্টক বদলানো নিরাপদ রাখতে
        stock_list = p.setdefault("stock_list", [])
        stock_list.extend(pending_items)
        p["stock"] = len(stock_list)
    save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)

    stock_added_text = (
        "🔔 <b>New Stock Added!</b>\n\n"
        f"📱 Product: {p['name']}\n"
        f"📦 Added: {len(pending_items)} numbers\n"
        f"💵 Price: {fmt_amount(p['price'])} (প্রতি পিস)\n"
        f"📊 Total {p['name']} Stock: {p['stock']}"
    )
    bot.send_message(chat_id, stock_added_text)
    bot.send_message(
        chat_id,
        "📢 এই স্টক আপডেট সব ইউজারকে broadcast করতে চান?",
        reply_markup=stock_broadcast_confirm_inline(),
    )
    user_state[uid] = {"menu": "admin_panel", "pending_broadcast_text": stock_added_text}


# ---------------------------------------------------------------------------
# ADMIN: Price পরিবর্তন (Set Price)
# ---------------------------------------------------------------------------
@bot.callback_query_handler(
    func=lambda c: c.data in ("stockbroadcast_yes", "stockbroadcast_no") and is_admin(c.from_user.id)
)
def cb_stock_broadcast(call):
    uid = call.from_user.id
    chat_id = call.message.chat.id
    bot.answer_callback_query(call.id)
    state = user_state.get(uid, {})
    text = state.get("pending_broadcast_text")

    if call.data == "stockbroadcast_no" or not text:
        bot.send_message(chat_id, "❌ Broadcast করা হয়নি।", reply_markup=admin_panel_inline())
        user_state[uid] = {"menu": "admin_panel"}
        return

    sent, failed = broadcast_to_all_users(text)
    bot.send_message(
        chat_id,
        "✅ <b>Broadcast সম্পন্ন!</b>\n\n"
        f"👥 পাঠানো হয়েছে: {sent} জনকে\n"
        f"❌ ব্যর্থ: {failed} জন",
        reply_markup=admin_panel_inline(),
    )
    user_state[uid] = {"menu": "admin_panel"}


@bot.callback_query_handler(func=lambda c: c.data.startswith("priceprod_") and is_admin(c.from_user.id))
def cb_admin_price_product_select(call):
    product_key = call.data.replace("priceprod_", "")
    p = products.get(product_key)
    if not p:
        bot.answer_callback_query(call.id, "Product not found.")
        return

    user_state[call.from_user.id] = {"menu": "admin_set_price", "product": product_key}
    bot.answer_callback_query(call.id)
    bot.send_message(
        call.message.chat.id,
        f"💰 <b>{p['name']}</b> এর জন্য নতুন price লিখে পাঠান।\n"
        f"বর্তমান price: {fmt_amount(p['price'])}\n\n"
        "উদাহরণ: 50 অথবা 49.99",
    )
    bot.register_next_step_handler(call.message, process_set_price)


def process_set_price(message):
    """Admin এর দেওয়া নতুন price validate করে products dict এ সেট করে।"""
    uid = message.from_user.id
    if not is_admin(uid):
        return

    text = (message.text or "").strip()

    # ইউজার মাঝপথে Back/Menu এ চলে যেতে চাইলে next-step এর সাথে conflict এড়ানো হচ্ছে
    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return

    state = user_state.get(uid, {})
    product_key = state.get("product")
    p = products.get(product_key)
    if not p:
        bot.send_message(message.chat.id, "⚠️ প্রোডাক্ট খুঁজে পাওয়া যায়নি। Admin Panel থেকে আবার চেষ্টা করুন।")
        user_state[uid] = {"menu": "admin_panel"}
        return

    try:
        new_price = float(text)
    except ValueError:
        new_price = None

    if new_price is None or new_price <= 0:
        bot.send_message(message.chat.id, "⚠️ সঠিক একটি price সংখ্যায় লিখুন (যেমন: 50 অথবা 49.99)।")
        bot.register_next_step_handler(message, process_set_price)
        return

    if new_price == int(new_price):
        new_price = int(new_price)

    old_price = p["price"]
    p["price"] = new_price
    save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)

    bot.send_message(
        message.chat.id,
        "✅ <b>Price আপডেট হয়েছে!</b>\n\n"
        f"📦 প্রোডাক্ট: {p['name']}\n"
        f"💵 পুরাতন Price: {fmt_amount(old_price)}\n"
        f"💵 নতুন Price: {fmt_amount(p['price'])}",
        reply_markup=admin_panel_inline(),
    )
    user_state[uid] = {"menu": "admin_panel"}


# ---------------------------------------------------------------------------
# ADMIN: Dollar Rate সেট করা (fmt_amount সব জায়গায় এই রেট ব্যবহার করে)
# ---------------------------------------------------------------------------
def process_set_usd_rate(message):
    """Admin এর দেওয়া নতুন USD->BDT রেট validate করে bot_settings এ সেট করে।"""
    uid = message.from_user.id
    if not is_admin(uid):
        return

    text = (message.text or "").strip()

    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return

    try:
        new_rate = float(text)
    except ValueError:
        new_rate = None

    if new_rate is None or new_rate <= 0:
        bot.send_message(message.chat.id, "⚠️ সঠিক একটি রেট সংখ্যায় লিখুন (যেমন: 122 অথবা 121.50)।")
        bot.register_next_step_handler(message, process_set_usd_rate)
        return

    if new_rate == int(new_rate):
        new_rate = int(new_rate)

    old_rate = bot_settings.get("usd_rate") or 0
    bot_settings["usd_rate"] = new_rate
    save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)

    bot.send_message(
        message.chat.id,
        "✅ <b>Dollar Rate আপডেট হয়েছে!</b>\n\n"
        f"💱 পুরাতন রেট: {(f'1 USD = {old_rate} BDT') if old_rate else 'সেট করা নেই'}\n"
        f"💱 নতুন রেট: 1 USD = {new_rate} BDT",
        reply_markup=admin_panel_inline(),
    )
    user_state[uid] = {"menu": "admin_panel"}


# ---------------------------------------------------------------------------
# ADMIN PANEL: 💵 Add/Remove Balance — Admin একটা user_id দিবে, তারপর
# +amount বা -amount দিয়ে সেই ইউজারের ব্যালেন্স বাড়াবে/কমাবে।
# ---------------------------------------------------------------------------
def process_balance_edit_uid(message):
    uid = message.from_user.id
    if not is_admin(uid):
        return

    text = (message.text or "").strip()
    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return

    try:
        target_id = int(text)
    except ValueError:
        target_id = None

    if target_id is None or target_id not in users:
        bot.send_message(
            message.chat.id,
            "⚠️ এই User ID খুঁজে পাওয়া যায়নি। সঠিক Telegram User ID লিখে আবার পাঠান।",
        )
        bot.register_next_step_handler(message, process_balance_edit_uid)
        return

    target = users[target_id]
    user_state[uid] = {"menu": "admin_balance_edit_wait_amount", "target_uid": target_id}
    bot.send_message(
        message.chat.id,
        f"👤 User: {target.get('full_name', '—')} ({target.get('username', '—')}) | <code>{target_id}</code>\n"
        f"💰 বর্তমান Balance: {fmt_amount(target.get('balance', 0))}\n\n"
        "কত টাকা যোগ/বিয়োগ করতে চান লিখে পাঠান।\n"
        "যোগ করতে: <code>+100</code>\nবিয়োগ করতে: <code>-100</code>",
        reply_markup=back_to_main_keyboard(),
    )
    bot.register_next_step_handler(message, process_balance_edit_amount)


def process_balance_edit_amount(message):
    uid = message.from_user.id
    if not is_admin(uid):
        return

    text = (message.text or "").strip()
    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return

    state = user_state.get(uid, {})
    if state.get("menu") != "admin_balance_edit_wait_amount" or not state.get("target_uid"):
        bot.send_message(message.chat.id, "⚠️ সেশন খুঁজে পাওয়া যায়নি। Admin Panel থেকে আবার চেষ্টা করুন।")
        user_state[uid] = {"menu": "admin_panel"}
        return

    try:
        delta = float(text.replace("+", ""))
    except ValueError:
        delta = None

    if delta is None or delta == 0:
        bot.send_message(
            message.chat.id,
            "⚠️ সঠিক একটি amount লিখুন (যেমন: +100 অথবা -50)।",
        )
        bot.register_next_step_handler(message, process_balance_edit_amount)
        return

    target_id = state["target_uid"]
    target = users.get(target_id)
    if not target:
        bot.send_message(message.chat.id, "⚠️ এই ইউজার আর খুঁজে পাওয়া যাচ্ছে না।")
        user_state[uid] = {"menu": "admin_panel"}
        return

    old_balance = target.get("balance", 0)
    new_balance = old_balance + delta
    target["balance"] = new_balance
    save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)

    action_word = "যোগ" if delta > 0 else "বিয়োগ"
    bot.send_message(
        message.chat.id,
        "✅ <b>Balance আপডেট হয়েছে!</b>\n\n"
        f"👤 User: {target.get('full_name', '—')} | <code>{target_id}</code>\n"
        f"{'➕' if delta > 0 else '➖'} {action_word}: {fmt_amount(abs(delta))}\n"
        f"💰 পুরাতন Balance: {fmt_amount(old_balance)}\n"
        f"💰 নতুন Balance: {fmt_amount(new_balance)}",
        reply_markup=admin_panel_inline(),
    )
    user_state[uid] = {"menu": "admin_panel"}

    try:
        bot.send_message(
            target_id,
            ("💵 <b>আপনার ব্যালেন্সে যোগ করা হয়েছে!</b>\n\n" if delta > 0 else
             "💵 <b>আপনার ব্যালেন্স থেকে কাটা হয়েছে!</b>\n\n") +
            f"{'➕' if delta > 0 else '➖'} Amount: {fmt_amount(abs(delta))}\n"
            f"💰 নতুন Balance: {fmt_amount(new_balance)}",
        )
    except Exception:
        pass


# ---------------------------------------------------------------------------
# ADMIN PANEL: 🔎 User Info — Admin একটা user_id দিলে সেই ইউজারের সব তথ্য
# (প্রোফাইল + Deposits + Orders সামারি) একসাথে দেখায়।
# ---------------------------------------------------------------------------
def _user_deposits(target_id):
    """একজন ইউজারের সব ডিপোজিট, সবচেয়ে নতুনটা আগে।"""
    return sorted(
        (d for d in deposits.values() if d.get("user_id") == target_id),
        key=lambda d: d.get("id", 0),
        reverse=True,
    )


def _user_orders(target_id):
    """একজন ইউজারের সব অর্ডার, সবচেয়ে নতুনটা আগে।"""
    return sorted(
        (o for o in orders.values() if o.get("user_id") == target_id),
        key=lambda o: o.get("date", ""),
        reverse=True,
    )


def admin_user_info_text(target_id, target):
    """Admin এর জন্য একজন নির্দিষ্ট ইউজারের সম্পূর্ণ তথ্য (প্রোফাইল + Deposits +
    Orders সামারি, সর্বশেষ ৫টা করে দেখানো হয়) তৈরি করে।"""
    referred_by_line = ""
    referred_by = target.get("referred_by")
    if referred_by:
        ref_user = users.get(referred_by)
        ref_name = ref_user.get("full_name", "—") if ref_user else "—"
        referred_by_line = f"🔗 <b>Referred By:</b> <code>{referred_by}</code> ({ref_name})\n"

    status_emoji = {"approved": "✅", "pending": "⏳", "rejected": "❌"}

    dep_list = _user_deposits(target_id)
    total_deposited = sum(d.get("amount", 0) for d in dep_list if d.get("status") == "approved")
    if dep_list:
        dep_lines = "".join(
            f"{status_emoji.get(d.get('status'), '•')} DEP-{d['id']} | {d.get('method', '—')} | "
            f"{fmt_amount(d.get('amount', 0))} | {d.get('status', '—')} | {d.get('date', '—')}\n"
            for d in dep_list[:5]
        )
    else:
        dep_lines = "কোনো ডিপোজিট নেই।\n"
    more_dep = f"…আরও {len(dep_list) - 5}টি পুরোনো ডিপোজিট আছে।\n" if len(dep_list) > 5 else ""

    order_list = _user_orders(target_id)
    total_spent_all = sum(o.get("total", 0) for o in order_list)
    if order_list:
        order_lines = "".join(
            f"🧾 {o['order_id']} | {o.get('product_name', '—')} x{o.get('qty', 1)} | "
            f"{fmt_amount(o.get('total', 0))} | {o.get('date', '—')}\n"
            for o in order_list[:5]
        )
    else:
        order_lines = "কোনো অর্ডার নেই।\n"
    more_order = f"…আরও {len(order_list) - 5}টি পুরোনো অর্ডার আছে।\n" if len(order_list) > 5 else ""

    return (
        "🔎 <b>User Info</b>\n\n"
        f"🆔 <b>User ID:</b> <code>{target_id}</code>\n"
        f"👤 <b>Full Name:</b> <code>{target.get('full_name', '—')}</code>\n"
        f"📝 <b>Username:</b> <code>{target.get('username', '—')}</code>\n"
        f"💰 <b>Balance:</b> <code>{fmt_amount(target.get('balance', 0))}</code>\n"
        f"📊 <b>Total Purchased:</b> <code>{target.get('total_purchased', 0)}</code>\n"
        f"💸 <b>Today Spent:</b> <code>{fmt_amount(target.get('today_spent', 0))}</code>\n"
        f"💳 <b>Today Deposit:</b> <code>{fmt_amount(target.get('today_deposit', 0))}</code>\n"
        f"👥 <b>Referrals:</b> <code>{target.get('referrals', 0)}</code>\n"
        f"🎁 <b>Referral Earned:</b> <code>{fmt_amount(target.get('earned', 0))}</code>\n"
        f"{referred_by_line}\n"
        f"💰 <b>Deposits</b> (মোট: {len(dep_list)} | Approved Total: {fmt_amount(total_deposited)})\n"
        f"{dep_lines}{more_dep}\n"
        f"🧾 <b>Orders</b> (মোট: {len(order_list)} | Total Spent: {fmt_amount(total_spent_all)})\n"
        f"{order_lines}{more_order}"
    )


def process_admin_user_info_uid(message):
    """Admin এর দেওয়া User ID validate করে সেই ইউজারের সব তথ্য দেখায়।"""
    uid = message.from_user.id
    if not is_admin(uid):
        return

    text = (message.text or "").strip()
    if text in ["⬅️ Back", "🏠 Back to Menu"]:
        go_back(message)
        return

    try:
        target_id = int(text)
    except ValueError:
        target_id = None

    if target_id is None or target_id not in users:
        bot.send_message(
            message.chat.id,
            "⚠️ এই User ID খুঁজে পাওয়া যায়নি। সঠিক Telegram User ID লিখে আবার পাঠান।",
        )
        bot.register_next_step_handler(message, process_admin_user_info_uid)
        return

    target = users[target_id]
    bot.send_message(
        message.chat.id,
        admin_user_info_text(target_id, target),
        reply_markup=admin_panel_inline(),
    )
    user_state[uid] = {"menu": "admin_panel"}


# ---------------------------------------------------------------------------
# ADMIN: DB Export / Import (Backup ও Restore) — এখনো in-memory ডেটা, তাই
# bot restart হলে সব হারিয়ে যায়; এই ফিচার দিয়ে ম্যানুয়ালি Export/Import করা
# যাবে (TODO: ভবিষ্যতে persistent DB এলে auto-load এর দরকার থাকবে না)।
# ---------------------------------------------------------------------------
def _serialize_payload_bytes(payload=None):
    """payload কে JSON bytes এ রূপান্তর করে। অন্য থ্রেড একই সময়ে ডেটা বদলালে Python
    "dictionary changed size during iteration" দিতে পারে — তাই কয়েকবার retry করা হয়
    (প্রতিবার নতুন করে payload বানিয়ে), যাতে export/auto-save কখনো এই কারণে ব্যর্থ না হয়।"""
    last_err = None
    for _ in range(5):
        try:
            data = payload if payload is not None else _build_db_export_payload()
            return json.dumps(data, ensure_ascii=False).encode("utf-8")
        except RuntimeError as e:   # dict/list পরিবর্তনের race
            last_err = e
            payload = None
            time.sleep(0.05)
    raise last_err


def _build_db_export_payload():
    return {
        "version": 1,
        "exported_at": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "users": users,
        "products": products,
        "orders": orders,
        "deposits": deposits,
        "sms_log": sms_log,
        "bot_settings": bot_settings,
        "next_deposit_id": _deposit_id_counter[0],
        "next_sms_id": _sms_id_counter[0],
    }


def _restore_db_from_payload(payload):
    """ব্যাকআপ payload থেকে in-memory সব ডেটা রিপ্লেস করে — Export করার মুহূর্তের অবস্থায়
    হুবহু ফিরিয়ে আনে। users/deposits এর key (user_id/deposit_id) JSON এ string হয়ে যায়,
    তাই আবার int এ কনভার্ট করা হচ্ছে।

    • আগে সব ডেটা parse/validate হয় (কিছু ভুল থাকলে এখানেই এরর — বর্তমান ডেটা অক্ষত থাকে)
    • তারপর _stock_lock + _deposit_lock ধরে একসাথে রিপ্লেস হয় (restore চলাকালীন কেউ কিনলে/
      deposit approve করলে ডেটা গুলিয়ে যাবে না)
    • bot_settings আগে ডিফল্টে রিসেট হয়, তারপর ব্যাকআপের সেটিংস বসে (বাড়তি/পুরোনো কিছু মিশে থাকে না)
    • deposit/sms id কাউন্টার সবসময় বিদ্যমান সর্বোচ্চ id এর চেয়ে বড় রাখা হয় (id ডুপ্লিকেট এড়াতে)"""
    if not isinstance(payload, dict):
        raise ValueError("ব্যাকআপ ফাইলের ফরম্যাট ঠিক নেই")

    new_users = {int(k): v for k, v in (payload.get("users") or {}).items()}
    new_deposits = {int(k): v for k, v in (payload.get("deposits") or {}).items()}
    new_orders = dict(payload.get("orders") or {})
    new_products = payload.get("products")
    new_sms_log = list(payload.get("sms_log") or [])
    new_settings = payload.get("bot_settings")
    if new_products is not None and not isinstance(new_products, dict):
        raise ValueError("products অংশটা সঠিক নয়")
    if new_settings is not None and not isinstance(new_settings, dict):
        raise ValueError("bot_settings অংশটা সঠিক নয়")

    def _as_int(v, default=0):
        try:
            return int(v)
        except (TypeError, ValueError):
            return default

    dep_counter = max(
        _as_int(payload.get("next_deposit_id"), 1000),
        max(new_deposits.keys(), default=0),
        1000,
    )
    sms_counter = max(
        _as_int(payload.get("next_sms_id"), 0),
        max((_as_int(x.get("id")) for x in new_sms_log if isinstance(x, dict)), default=0),
    )

    with _stock_lock, _deposit_lock:
        users.clear()
        users.update(new_users)

        orders.clear()
        orders.update(new_orders)

        deposits.clear()
        deposits.update(new_deposits)

        sms_log.clear()
        sms_log.extend(new_sms_log)

        if new_products is not None:
            products.clear()
            products.update(new_products)
            for _old_key in ("whatsapp", "telegram"):   # সরানো প্রোডাক্ট
                products.pop(_old_key, None)
        _ensure_mail_products()

        bot_settings.clear()
        bot_settings.update(copy.deepcopy(_BOT_SETTINGS_DEFAULTS))
        if new_settings is not None:
            bot_settings.update(new_settings)
        bot_settings.setdefault("deposit_methods", ["bKash", "Nagad", "Rocket", "Binance"])
        bot_settings.setdefault("deposit_numbers", {})
        bot_settings.setdefault("force_join_channels", [])

        _deposit_id_counter[0] = dep_counter
        _sms_id_counter[0] = sms_counter


# ---------------------------------------------------------------------------
# ✅ PERSISTENT DATABASE (এখন আর শুধু in-memory না — ডিস্কে JSON ফাইলে অটো-সেভ)
# --------------------------------------------------------------------------
# আগে সব ডেটা (users/products/orders/deposits/sms_log/bot_settings) শুধু RAM এ
# থাকতো -> bot restart হলে সব হারিয়ে যেতো। এখন উপরের _build_db_export_payload()/
# _restore_db_from_payload() ফাংশন দুটো ব্যবহার করেই পুরো ডেটাসেট নিয়মিত ডিস্কে
# (DB_FILE_PATH) সেভ হয়, আর বট চালু হওয়ার সময় সেখান থেকে অটোমেটিক লোড হয়ে যায়।
# Railway তে persistent থাকতে হলে এই ফাইলের path একটা attached Volume এ রাখুন
# (env var DB_FILE_PATH দিয়ে কাস্টম path সেট করা যাবে)।
DB_FILE_PATH = os.environ.get("DB_FILE_PATH", "").strip() or os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "bot_data.json"
)
_db_save_lock = threading.Lock()


def save_db():
    """সব in-memory ডেটা ডিস্কে JSON ফাইলে সেভ করে (atomic write: আগে .tmp ফাইলে
    লিখে তারপর আসল ফাইলের নামে rename করা হয়, যাতে সেভের মাঝপথে বট ক্র্যাশ
    করলেও ফাইল করাপ্ট না হয়ে যায়)।"""
    try:
        raw = _serialize_payload_bytes()
        with _db_save_lock:
            tmp_path = DB_FILE_PATH + ".tmp"
            with open(tmp_path, "wb") as f:
                f.write(raw)
            os.replace(tmp_path, DB_FILE_PATH)
    except Exception as e:
        print(f"⚠️ save_db() ব্যর্থ হয়েছে: {e}")


def load_db():
    """বট চালু হওয়ার সময় ডিস্কে আগে সেভ করা DB_FILE_PATH ফাইল (থাকলে) থেকে সব
    ডেটা অটোমেটিক লোড করে। ফাইল না থাকলে (প্রথমবার রান) ফ্রেশ/খালি ডেটা দিয়ে
    শুরু হবে।"""
    if not os.path.exists(DB_FILE_PATH):
        print(f"ℹ️  কোনো আগের DB ফাইল পাওয়া যায়নি ({DB_FILE_PATH}) — ফ্রেশ ডেটা দিয়ে শুরু হচ্ছে।")
        return
    try:
        with open(DB_FILE_PATH, "r", encoding="utf-8") as f:
            payload = json.load(f)
        _restore_db_from_payload(payload)
        print(
            f"✅ DB লোড হয়েছে -> {DB_FILE_PATH} "
            f"(Users: {len(users)}, Orders: {len(orders)}, Deposits: {len(deposits)})"
        )
    except Exception as e:
        print(f"⚠️ load_db() ব্যর্থ হয়েছে, ফ্রেশ ডেটা দিয়ে শুরু হচ্ছে: {e}")


def _autosave_loop():
    """প্রতি ১০ সেকেন্ড পরপর ব্যাকগ্রাউন্ডে অটোমেটিক DB সেভ করে, যাতে কোনো
    জায়গায় সরাসরি save_db() কল করতে ভুলে গেলেও ডেটা বেশিক্ষণ (max ১০ সেকেন্ড)
    আন-সেভড না থাকে।"""
    while True:
        time.sleep(10)
        save_db()


def start_persistent_db():
    """লোড + ব্যাকগ্রাউন্ড অটোসেভ থ্রেড চালু করে। Polling ও Webhook — দুই মোডেই
    রান হওয়ার আগে একবার কল হয়।"""
    load_db()
    threading.Thread(target=_autosave_loop, daemon=True).start()


def handle_db_import_file(message):
    """Admin এর পাঠানো .json ব্যাকআপ ফাইল ডাউনলোড/পার্স করে, Restore করার আগে
    কাউন্টসহ Confirm/Cancel বাটন দেখায় — সরাসরি ডেটা রিপ্লেস করে না।"""
    uid = message.from_user.id
    file_name = message.document.file_name or ""
    if not file_name.lower().endswith((".json", ".json.gz")):
        bot.send_message(message.chat.id, "⚠️ শুধুমাত্র .json বা .json.gz ব্যাকআপ ফাইল সাপোর্ট করে। আবার পাঠান।")
        return

    try:
        file_info = bot.get_file(message.document.file_id)
        downloaded = bot.download_file(file_info.file_path)
        if file_name.lower().endswith(".gz") or downloaded[:2] == b"\x1f\x8b":
            downloaded = gzip.decompress(downloaded)
        payload = json.loads(downloaded.decode("utf-8-sig"))
    except Exception as e:
        bot.send_message(message.chat.id, f"❌ ফাইল পড়তে/পার্স করতে সমস্যা হয়েছে: {e}")
        return

    if not isinstance(payload, dict) or "users" not in payload:
        bot.send_message(message.chat.id, "⚠️ এটা এই বটের সঠিক ব্যাকআপ ফাইল বলে মনে হচ্ছে না।")
        return

    user_state[uid] = {"menu": "admin_import_db_confirm", "pending_import": payload}

    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(
        types.InlineKeyboardButton("🔄 Confirm & Restore", callback_data="dbimport_confirm"),
        types.InlineKeyboardButton("❌ Cancel", callback_data="dbimport_cancel"),
    )
    bot.send_message(
        message.chat.id,
        "🔎 <b>Confirm DB Import</b>\n\n"
        f"📄 ফাইল: {file_name}\n"
        f"👥 Users: {len(payload.get('users') or {})}\n"
        f"🧾 Orders: {len(payload.get('orders') or {})}\n"
        f"💰 Deposits: {len(payload.get('deposits') or {})}\n"
        f"📩 SMS Log: {len(payload.get('sms_log') or [])}\n"
        f"📦 Products: {len(payload.get('products') or {})} "
        f"(স্টকে অবিক্রিত: {sum(len((p or {}).get('stock_list') or []) for p in (payload.get('products') or {}).values() if isinstance(p, dict))} পিস)\n"
        f"⚙️ Settings: {len(payload.get('bot_settings') or {})} টি | "
        f"💎 Premium emoji: {len(((payload.get('bot_settings') or {}).get('premium_emoji')) or {})} টি\n"
        f"📅 Backup নেওয়া হয়েছিল: {payload.get('exported_at', '—')}\n\n"
        "⚠️ Confirm করলে বর্তমান সব ডেটা মুছে এই ব্যাকআপ দিয়ে রিপ্লেস হয়ে যাবে। এই কাজ Undo করা যাবে না।",
        reply_markup=kb,
    )


@bot.callback_query_handler(
    func=lambda c: c.data in ("dbimport_confirm", "dbimport_cancel") and is_admin(c.from_user.id)
)
def cb_db_import_confirm(call):
    uid = call.from_user.id
    chat_id = call.message.chat.id
    state = user_state.get(uid, {})
    bot.answer_callback_query(call.id)

    if state.get("menu") != "admin_import_db_confirm":
        bot.send_message(chat_id, "⚠️ কোনো pending import নেই। আগে একটা ব্যাকআপ (.json) ফাইল পাঠান।")
        return

    if call.data == "dbimport_cancel":
        bot.send_message(
            chat_id,
            "❌ Import বাতিল করা হয়েছে। কিছুই পরিবর্তন হয়নি।",
            reply_markup=admin_panel_inline(),
        )
        user_state[uid] = {"menu": "admin_panel"}
        return

    payload = state.get("pending_import") or {}
    try:
        _restore_db_from_payload(payload)
        save_db()
        _prime_reply_label_map()   # 💎 restore হওয়া Premium emoji ম্যাপ অনুযায়ী reply-কীবোর্ডের লেবেল ম্যাপ নতুন করে বানানো
    except Exception as e:
        bot.send_message(chat_id, f"❌ Restore করতে সমস্যা হয়েছে: {e}")
        user_state[uid] = {"menu": "admin_panel"}
        return

    bot.send_message(
        chat_id,
        "✅ <b>DB Import সম্পন্ন!</b>\n\n"
        f"👥 Users: {len(users)}\n"
        f"🧾 Orders: {len(orders)}\n"
        f"💰 Deposits: {len(deposits)}\n"
        f"📩 SMS Log: {len(sms_log)}\n"
        f"📦 Products: {len(products)} (স্টকে অবিক্রিত: {sum(len(p.get('stock_list') or []) for p in list(products.values()))} পিস)\n"
        f"⚙️ Settings + 💎 Premium emoji ({len(bot_settings.get('premium_emoji') or {})} টি) সহ সব আগের মতো ফিরে এসেছে।",
        reply_markup=admin_panel_inline(),
    )
    user_state[uid] = {"menu": "admin_panel"}


# ---------------------------------------------------------------------------
# 💎 PREMIUM (CUSTOM) EMOJI
# Bot API 9.4+: বটের owner এর Telegram Premium থাকলে বট মেসেজ ও বাটনে custom emoji
# ব্যবহার করতে পারে। এখানে একটা "নরমাল emoji -> premium emoji ID" ম্যাপ রাখা হয়
# (bot_settings["premium_emoji"], DB তে persist হয়), আর bot.send_message /
# edit_message_text / send_document / send_photo কে wrap করা হয়েছে, যাতে কোডের বাকি
# অংশ না বদলেও:
#   • মেসেজ/ক্যাপশনের ম্যাপ করা সব নরমাল emoji অটো <tg-emoji> premium emoji হয়ে যায়
#   • বাটনের শুরুর ম্যাপ করা emoji বাদ গিয়ে বাটনে premium icon বসে
# কোনো কারণে Telegram premium emoji রিজেক্ট করলে অটো নরমাল emoji দিয়ে আবার পাঠানো হয়।
#
# ম্যাপ বানানোর নিয়ম (শুধু Admin): বটকে এমন মেসেজ পাঠান যেখানে প্রতিটা premium emoji এর
# ঠিক আগে যে নরমাল emoji টা বদলাতে চান সেটা লেখা আছে, যেমন:   🛒 <premium> 💳 <premium>
# (আগে নরমাল emoji না থাকলে premium emoji এর নিজের fallback emoji টাই ম্যাপ হবে)।
# কমান্ড: /emoji (স্ট্যাটাস) · /emoji_on · /emoji_off · /emoji_clear · /emoji_export · /emoji_import
# ---------------------------------------------------------------------------
import copy

_EMOJI_BASE = (
    r"[\U0001F000-\U0001FAFF\u2190-\u21FF\u2300-\u23FF\u24C2\u25A0-\u27BF\u2900-\u297F"
    r"\u2B00-\u2BFF\u00A9\u00AE\u203C\u2049\u2122\u2139\u3030\u303D\u3297\u3299]"
)
_EMOJI_MOD = r"(?:\uFE0F|[\U0001F3FB-\U0001F3FF])?"
_EMOJI_RE_STR = (
    r"(?:[\U0001F1E6-\U0001F1FF]{2}|[#*0-9]\uFE0F?\u20E3|"
    + _EMOJI_BASE + _EMOJI_MOD + r"(?:\u200D" + _EMOJI_BASE + _EMOJI_MOD + r")*)"
)
_EMOJI_END_RE = re.compile("(" + _EMOJI_RE_STR + ")$")
_PREMIUM_MAX_PER_MESSAGE = 90          # Telegram এর entity সীমা এড়াতে
_STRIPPED_TO_ORIG = {"⬅️ Back to Menu": "🏠 Back to Menu"}   # reply-keyboard এর "emoji ছাড়া লেবেল" -> আসল লেবেল (+ পুরোনো কীবোর্ডে থাকা আগের লেবেল)
_prem_cache = {"keys": None, "regex": None}
_TAG_RE = re.compile(r"(<[^>]*>)")


def _emoji_key(s):
    return (s or "").replace("\ufe0f", "")


def _premium_map():
    if not bot_settings.get("premium_emoji_enabled", True):
        return {}
    return bot_settings.get("premium_emoji") or {}


def _prem_regex(m):
    keys = tuple(sorted(m.keys(), key=len, reverse=True))
    if _prem_cache["keys"] != keys:
        _prem_cache["regex"] = re.compile("|".join(re.escape(k) + "\ufe0f?" for k in keys)) if keys else None
        _prem_cache["keys"] = keys
    return _prem_cache["regex"]


def premiumize_html(text):
    """HTML টেক্সটের ম্যাপ করা নরমাল emoji গুলোকে <tg-emoji> premium emoji বানায়
    (<code>/<pre>/আগে থেকে থাকা <tg-emoji> এর ভেতরে বদলায় না)।"""
    m = _premium_map()
    if not m or not text:
        return text
    rx = _prem_regex(m)
    if rx is None:
        return text
    count = [0]

    def repl(mo):
        eid = m.get(_emoji_key(mo.group(0)))
        if not eid or count[0] >= _PREMIUM_MAX_PER_MESSAGE:
            return mo.group(0)
        count[0] += 1
        return f'<tg-emoji emoji-id="{eid}">{mo.group(0)}</tg-emoji>'

    out, skip = [], 0
    for part in _TAG_RE.split(text):
        if part.startswith("<") and part.endswith(">"):
            low = part.lower()
            if re.match(r"</?(code|pre|tg-emoji)\b", low):
                skip = max(skip + (-1 if low.startswith("</") else 1), 0)
            out.append(part)
        else:
            out.append(part if skip else rx.sub(repl, part))
    return "".join(out)


def _split_leading_emoji(label):
    """বাটন লেবেলের শুরুতে ম্যাপ করা emoji থাকলে (emoji_id, বাকি টেক্সট) রিটার্ন করে।"""
    m = _premium_map()
    if not m or not label:
        return None
    rx = _prem_regex(m)
    mo = rx.match(label) if rx else None
    if not mo:
        return None
    eid = m.get(_emoji_key(mo.group(0)))
    rest = label[mo.end():].lstrip()
    if not eid or not rest:
        return None
    return eid, rest


def _apply_button_icon(btn, is_reply):
    if isinstance(btn, dict):
        label = btn.get("text")
    elif isinstance(btn, str):
        return False
    else:
        label = getattr(btn, "text", None)
    sp = _split_leading_emoji(label)
    if not sp:
        return False
    eid, rest = sp
    if isinstance(btn, dict):
        btn["text"] = rest
        btn["icon_custom_emoji_id"] = eid
    else:
        btn.text = rest
        btn.icon_custom_emoji_id = eid
        orig_to_dict = btn.to_dict

        def _to_dict(_o=orig_to_dict, _e=eid):
            d = _o()
            if isinstance(d, dict):
                d["icon_custom_emoji_id"] = _e
            return d

        btn.to_dict = _to_dict
    if is_reply:
        _STRIPPED_TO_ORIG[rest] = label
    return True


def _premiumize_markup(markup):
    """কীবোর্ডের কপি বানিয়ে তাতে premium icon বসায় (আসল অবজেক্ট অপরিবর্তিত থাকে)।"""
    if markup is None or not _premium_map():
        return markup
    try:
        if isinstance(markup, types.InlineKeyboardMarkup):
            is_reply = False
        elif isinstance(markup, types.ReplyKeyboardMarkup):
            is_reply = True
        else:
            return markup
        new = copy.deepcopy(markup)
        changed = False
        for row in new.keyboard:
            for btn in row:
                changed |= _apply_button_icon(btn, is_reply)
        return new if changed else markup
    except Exception as e:
        print(f"⚠️ premium emoji (markup) skipped: {e}")
        return markup


def _is_premium_error(e):
    s = str(e).lower()
    return any(k in s for k in ("emoji", "entit", "icon", "can't parse"))


def _make_premium_wrapper(orig, text_param, max_plain_args):
    def wrapper(*args, **kwargs):
        if not _premium_map():
            return orig(*args, **kwargs)
        a, kw = list(args), dict(kwargs)
        changed = False
        try:
            if kw.get("parse_mode") in (None, "HTML") and not kw.get("entities") and not kw.get("caption_entities"):
                if isinstance(kw.get(text_param), str):
                    nt = premiumize_html(kw[text_param])
                    changed |= nt != kw[text_param]
                    kw[text_param] = nt
                elif text_param == "text" and a and len(a) <= max_plain_args:
                    idx = 1 if orig.__name__ == "send_message" else 0
                    if len(a) > idx and isinstance(a[idx], str):
                        nt = premiumize_html(a[idx])
                        changed |= nt != a[idx]
                        a[idx] = nt
            if kw.get("reply_markup") is not None:
                nm = _premiumize_markup(kw["reply_markup"])
                changed |= nm is not kw["reply_markup"]
                kw["reply_markup"] = nm
        except Exception as e:
            print(f"⚠️ premium emoji skipped: {e}")
            return orig(*args, **kwargs)
        if not changed:
            return orig(*args, **kwargs)
        try:
            return orig(*a, **kw)
        except Exception as e:
            if _is_premium_error(e):
                print(f"⚠️ premium emoji রিজেক্ট হয়েছে, নরমাল emoji দিয়ে আবার পাঠানো হচ্ছে: {e}")
                return orig(*args, **kwargs)
            raise

    wrapper.__name__ = getattr(orig, "__name__", "wrapper")
    return wrapper


for _name, _param, _maxargs in (
    ("send_message", "text", 2),
    ("edit_message_text", "text", 3),
    ("send_document", "caption", 0),
    ("send_photo", "caption", 0),
):
    setattr(bot, _name, _make_premium_wrapper(getattr(bot, _name), _param, _maxargs))

# reply-keyboard বাটন চাপলে Telegram শুধু বাটনের টেক্সট পাঠায় (icon ছাড়া), তাই
# emoji-ছাড়া লেবেলকে আবার আসল লেবেলে ফিরিয়ে দেওয়া হয় যাতে আগের হ্যান্ডলারগুলো কাজ করে।
_orig_process_new_messages = bot.process_new_messages


# মেইন মেনু কীবোর্ডের লেআউট/রঙ বদলালে এই ভার্সন বদলান — Telegram পুরোনো রিপ্লাই কীবোর্ড
# ইউজারের স্ক্রিনে ধরে রাখে, তাই ইউজারের পরের মেসেজে বট একবার নতুন কীবোর্ড পাঠিয়ে দেয়।
KEYBOARD_VERSION = "2026-10-02-v3"


def _refresh_stale_keyboard(m):
    try:
        if not getattr(m, "from_user", None) or getattr(m.chat, "type", "") != "private":
            return
        uid = m.from_user.id
        u = users.get(uid)
        if not u or u.get("kb_version") == KEYBOARD_VERSION:
            return
        u["kb_version"] = KEYBOARD_VERSION
        if (getattr(m, "text", "") or "").startswith("/start"):
            return   # /start নিজেই নতুন কীবোর্ড পাঠায়
        bot.send_message(m.chat.id, "🔄 মেনু আপডেট হয়েছে।", reply_markup=main_menu_keyboard(uid))
    except Exception as e:
        print(f"⚠️ keyboard refresh skipped: {e}")


def _process_new_messages_premium(new_messages):
    for m in new_messages:
        _refresh_stale_keyboard(m)
    try:
        for m in new_messages:
            t = getattr(m, "text", None)
            if t and t in _STRIPPED_TO_ORIG:
                m.text = _STRIPPED_TO_ORIG[t]
    except Exception:
        pass
    return _orig_process_new_messages(new_messages)


bot.process_new_messages = _process_new_messages_premium


def _prime_reply_label_map():
    """বট রিস্টার্টের পরও ইউজারের স্ক্রিনে থাকা পুরোনো কীবোর্ডের বাটন যেন কাজ করে।"""
    try:
        for uid in [0] + list(ADMIN_IDS[:1]):
            _premiumize_markup(main_menu_keyboard(uid))
        _premiumize_markup(back_to_main_keyboard())
        _premiumize_markup(back_only_keyboard())
        _premiumize_markup(mail_product_keyboard())
    except Exception as e:
        print(f"⚠️ premium emoji prime skipped: {e}")


def _custom_emoji_entities(m):
    return [e for e in (getattr(m, "entities", None) or []) if getattr(e, "type", "") == "custom_emoji"]


@bot.message_handler(
    func=lambda m: bool(m.from_user) and is_admin(m.from_user.id) and bool(_custom_emoji_entities(m)),
    content_types=["text"],
)
def admin_learn_premium_emoji(message):
    """Admin premium emoji পাঠালে সেগুলোর ID ম্যাপে সেভ করে।"""
    text = message.text or ""
    u16 = text.encode("utf-16-le")
    ents = _custom_emoji_entities(message)
    covered = [(e.offset, e.offset + e.length) for e in ents]
    mp = bot_settings.setdefault("premium_emoji", {})
    learned = []
    for e in ents:
        fallback = u16[e.offset * 2:(e.offset + e.length) * 2].decode("utf-16-le")
        before = u16[:e.offset * 2].decode("utf-16-le")
        stripped = before.rstrip(" \t=:→>-–—")
        key = _emoji_key(fallback)
        mo = _EMOJI_END_RE.search(stripped)
        if mo:
            start = len(stripped[:mo.start()].encode("utf-16-le")) // 2
            end = start + len(mo.group(1).encode("utf-16-le")) // 2
            if not any(a < end and b > start for a, b in covered):
                key = _emoji_key(mo.group(1))
        if key and e.custom_emoji_id:
            mp[key] = e.custom_emoji_id
            learned.append((key, e.custom_emoji_id))
    if not learned:
        return
    bot_settings["premium_emoji_enabled"] = True
    save_db()
    _prime_reply_label_map()
    lines = "\n".join(f"{k} → <code>{i}</code>" for k, i in learned)
    bot.send_message(
        message.chat.id,
        f"✅ <b>{len(learned)} টি Premium emoji ম্যাপ হয়েছে</b>\n\n{lines}\n\n"
        f"মোট ম্যাপ করা: {len(mp)} টি। বটের মেসেজ/বাটনে এখন থেকে এগুলো দেখাবে।",
    )


@bot.message_handler(
    commands=["emoji", "emoji_on", "emoji_off", "emoji_clear", "emoji_export", "emoji_import"],
    func=lambda m: bool(m.from_user) and is_admin(m.from_user.id),
)
def admin_premium_emoji_cmd(message):
    cmd = (message.text or "").split()[0].split("@")[0].lstrip("/").lower()
    if cmd == "emoji_on":
        bot_settings["premium_emoji_enabled"] = True
        save_db()
        bot.send_message(message.chat.id, "✅ Premium emoji চালু করা হয়েছে।")
        return
    if cmd == "emoji_off":
        bot_settings["premium_emoji_enabled"] = False
        save_db()
        bot.send_message(message.chat.id, "⏸️ Premium emoji বন্ধ করা হয়েছে (নরমাল emoji দেখাবে)।")
        return
    if cmd == "emoji_export":
        mp = bot_settings.get("premium_emoji") or {}
        if not mp:
            bot.send_message(message.chat.id, "⚠️ এক্সপোর্ট করার মতো কোনো Premium emoji ম্যাপ নেই।")
            return
        payload = {
            "type": "premium_emoji_preset",
            "version": 1,
            "enabled": bool(bot_settings.get("premium_emoji_enabled", True)),
            "map": mp,
        }
        buf = io.BytesIO(json.dumps(payload, ensure_ascii=False, indent=2).encode("utf-8"))
        buf.name = f"premium_emoji_preset_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        bot.send_document(
            message.chat.id,
            buf,
            caption=f"📤 Premium emoji preset ({len(mp)} টি)। পরে /emoji_import দিয়ে এই ফাইলটা ইমপোর্ট করতে পারবেন।",
        )
        return
    if cmd == "emoji_import":
        user_state[message.from_user.id] = {"menu": "premium_emoji_import"}
        sent = bot.send_message(
            message.chat.id,
            "📥 <b>Premium emoji preset Import</b>\n\n"
            "এক্সপোর্ট করা <b>.json</b> ফাইলটা পাঠান (অথবা JSON টেক্সট পেস্ট করুন)।\n"
            "⚠️ এতে বর্তমান ম্যাপ preset এর ম্যাপ দিয়ে <b>রিপ্লেস</b> হবে। বাতিল করতে /cancel লিখুন।",
        )
        bot.register_next_step_handler(sent, process_premium_emoji_import)
        return
    if cmd == "emoji_clear":
        bot_settings["premium_emoji"] = {}
        save_db()
        bot.send_message(message.chat.id, "🗑️ সব Premium emoji ম্যাপ মুছে ফেলা হয়েছে।")
        return
    mp = bot_settings.get("premium_emoji") or {}
    on = bot_settings.get("premium_emoji_enabled", True)
    listing = "\n".join(f"{k} → <code>{i}</code>" for k, i in mp.items()) or "কোনো ম্যাপ নেই"
    bot.send_message(
        message.chat.id,
        f"💎 <b>Premium Emoji</b> — {'চালু ✅' if on else 'বন্ধ ⏸️'}\n\n{listing}\n\n"
        "ম্যাপ যোগ করতে এমন মেসেজ পাঠান: নরমাল emoji + তার পরে premium emoji\n"
        "(যেমন: 🛒 [premium] 💳 [premium])\n\n"
        "/emoji_export · /emoji_import\n"
        "/emoji_on · /emoji_off · /emoji_clear",
    )


@bot.message_handler(commands=["kbtest"], func=lambda m: bool(m.from_user) and is_admin(m.from_user.id))
def admin_keyboard_test(message):
    """ডায়াগনস্টিক: কোড ডিপ্লয় হয়েছে কিনা, কীবোর্ডের JSON এ style যাচ্ছে কিনা, আর রঙ দেখা যাচ্ছে কিনা।"""
    uid = message.from_user.id
    try:
        payload = main_menu_keyboard(uid).to_json()
    except Exception as e:
        payload = f"error: {e}"
    ikb = types.InlineKeyboardMarkup(row_width=3)
    ikb.add(
        types.InlineKeyboardButton("🔵 Blue", callback_data="kbtest_noop"),
        types.InlineKeyboardButton("🟢 Green", callback_data="kbtest_noop"),
        types.InlineKeyboardButton("🔴 Red", callback_data="kbtest_noop"),
    )
    ikb.keyboard[0][1].style = "success"
    ikb.keyboard[0][2].style = "danger"
    bot.send_message(
        message.chat.id,
        f"🧪 <b>Keyboard Test</b>\n\n"
        f"telebot: <code>{getattr(telebot, '__version__', '?')}</code>\n"
        f"Keyboard version: <code>{KEYBOARD_VERSION}</code>\n\n"
        f"<b>Main menu JSON:</b>\n<pre>{_html.escape(str(payload))[:1500]}</pre>\n"
        "নিচের ৩টা বাটন নীল / সবুজ / লাল দেখালে আপনার Telegram অ্যাপে রঙ সাপোর্ট করছে।",
        reply_markup=ikb,
    )
    bot.send_message(message.chat.id, "⌨️ নতুন মেনু কীবোর্ড পাঠানো হলো।", reply_markup=main_menu_keyboard(uid))


@bot.callback_query_handler(func=lambda c: c.data == "kbtest_noop")
def cb_kbtest_noop(call):
    bot.answer_callback_query(call.id)


def _parse_premium_emoji_preset(raw):
    """JSON টেক্সট থেকে {normal_emoji: emoji_id} ম্যাপ বের করে; ভুল হলে ValueError।"""
    data = json.loads(raw)
    if isinstance(data, dict) and isinstance(data.get("map"), dict):
        data = data["map"]
    if not isinstance(data, dict) or not data:
        raise ValueError("ফাইলে কোনো emoji ম্যাপ পাওয়া যায়নি")
    if len(data) > 1000:
        raise ValueError("ম্যাপে অনেক বেশি এন্ট্রি আছে")
    clean = {}
    for k, v in data.items():
        key = _emoji_key(str(k)).strip()
        vid = str(v).strip()
        if not key or not vid.isdigit():
            raise ValueError(f"ভুল এন্ট্রি: {k!r} → {v!r} (ID শুধু সংখ্যা হতে হবে)")
        clean[key] = vid
    return clean


def process_premium_emoji_import(message):
    uid = message.from_user.id
    if not is_admin(uid):
        return
    user_state[uid] = {"menu": "main"}
    text = (message.text or "").strip()
    if text.startswith("/"):
        bot.send_message(message.chat.id, "❎ Import বাতিল করা হয়েছে।")
        return
    try:
        if getattr(message, "document", None):
            name = (message.document.file_name or "").lower()
            if not name.endswith(".json"):
                raise ValueError("শুধু .json ফাইল সাপোর্ট করে")
            info = bot.get_file(message.document.file_id)
            raw = bot.download_file(info.file_path).decode("utf-8-sig")
        elif text:
            raw = text
        else:
            raise ValueError(".json ফাইল অথবা JSON টেক্সট পাঠান")
        clean = _parse_premium_emoji_preset(raw)
    except Exception as e:
        bot.send_message(message.chat.id, f"❌ Import ব্যর্থ: {_html.escape(str(e))}\n\nআবার /emoji_import দিয়ে চেষ্টা করুন।")
        return

    bot_settings["premium_emoji"] = clean
    bot_settings["premium_emoji_enabled"] = True
    save_db()
    _prime_reply_label_map()
    bot.send_message(
        message.chat.id,
        f"✅ <b>Preset Import সম্পন্ন!</b>\n\n💎 মোট {len(clean)} টি Premium emoji ম্যাপ হয়েছে।\n"
        + "\n".join(f"{k} → <code>{i}</code>" for k, i in list(clean.items())[:30])
        + ("\n…" if len(clean) > 30 else ""),
    )


# ---------------------------------------------------------------------------
# FALLBACK
# ---------------------------------------------------------------------------
@bot.message_handler(func=lambda m: True, content_types=["text"])
def fallback(message):
    # TODO: register_next_step_handler গুলো active থাকলে সেগুলো এখানে conflict না করার
    #       ব্যাপারে খেয়াল রাখবেন
    if require_force_join(message):
        return
    bot.send_message(
        message.chat.id,
        "❓ বুঝতে পারিনি। নিচের মেনু থেকে বেছে নিন।",
        reply_markup=main_menu_keyboard(message.from_user.id),
    )


# ---------------------------------------------------------------------------
# SMS AUTO-DEPOSIT: পেমেন্ট SMS/নোটিফিকেশন পার্স করা ও pending deposit এর
# সাথে ম্যাচ করা (bKash/Nagad/Rocket/Binance)
# ---------------------------------------------------------------------------
_SMS_INCOMING_HINTS = (
    "you have received", "received tk", "received taka", "cash in",
    "money received", "credited", "পেমেন্ট", "রিসিভ",
)
_SMS_OUTGOING_HINTS = (
    "you have sent", "payment sent", "cash out", "withdrawn", "debited",
    "you sent", "send money",
)

_AMOUNT_RE = re.compile(r"(?:tk|taka|bdt)\.?\s*([\d,]+(?:\.\d{1,2})?)", re.IGNORECASE)
_TRXID_RE = re.compile(
    r"(?:trx\s*id|txn\s*id|transaction\s*id|trxid|txnid|trx\s*no\.?|txn\s*no\.?|ref(?:erence)?\s*id)"
    r"[\s:\-]*([a-z0-9]{4,})",
    re.IGNORECASE,
)
# 🪙 Binance ওয়ালেট নোটিফিকেশনে TrxID থাকে না, বরং sender username থাকে (স্পেসসহ
# হতে পারে) — উদাহরণ: "You have received a payment of 0.1 USDT from Garth
# Mantifel wpgu on 2026-09-15 04:01:53(UTC)"
_BINANCE_RECEIVED_RE = re.compile(
    r"received\s+(?:a\s+)?payment\s+of\s*([\d]+(?:\.\d+)?)\s*([a-z]{2,10})\s+from\s+(.+?)\s+on\s+\d{4}-\d{1,2}-\d{1,2}",
    re.IGNORECASE,
)
_SENDER_METHOD_CODES = {"16216": "Rocket"}   # Rocket এর অফিসিয়াল sender short-code
_SENDER_METHOD_NAMES = {"nagad": "Nagad"}


def _normalize_binance_name(name):
    return re.sub(r"\s+", " ", name.strip())


def _id_label(method):
    return "Binance Username" if method == "Binance" else "TrxID"


def _amount_unit(method):
    return "USDT" if method == "Binance" else "BDT"


def _method_from_sender(sender):
    if not sender:
        return ""
    sender_l = sender.strip().lower()
    for name, method in _SENDER_METHOD_NAMES.items():
        if name in sender_l:
            return method
    s = re.sub(r"[^0-9]", "", sender)
    for code, method in _SENDER_METHOD_CODES.items():
        if s == code or s.endswith(code):
            return method
    return ""


def parse_payment_sms(text, hint_method="", sender=""):
    """একটা raw SMS টেক্সট থেকে method/amount/trx_id বের করার চেষ্টা করে।
    ইনকামিং পেমেন্ট SMS না মনে হলে, বা amount/trx_id না পেলে None রিটার্ন করে।"""
    if not text:
        return None
    t = text.strip()
    tl = t.lower()

    if any(h in tl for h in _SMS_OUTGOING_HINTS) and not any(h in tl for h in _SMS_INCOMING_HINTS):
        return None  # টাকা পাঠানো/ক্যাশ-আউটের SMS, ডিপোজিটের জন্য না

    bm = _BINANCE_RECEIVED_RE.search(t)
    if bm:
        try:
            b_amount = float(bm.group(1))
        except ValueError:
            b_amount = None
        b_name = _normalize_binance_name(bm.group(3))
        if b_amount is not None and b_name:
            return {"method": "Binance", "amount": b_amount, "trx_id": b_name}
        return None

    method = _method_from_sender(sender)
    if not method:
        if "bkash" in tl:
            method = "bKash"
        elif "nagad" in tl:
            method = "Nagad"
        elif "rocket" in tl or "dbbl" in tl:
            method = "Rocket"
        if not method and re.search(r"(?<!\d)16216(?!\d)", t):
            method = "Rocket"
    if not method and hint_method:
        method = hint_method.strip()

    amount = None
    m = _AMOUNT_RE.search(t)
    if m:
        try:
            amount = float(m.group(1).replace(",", ""))
        except ValueError:
            amount = None

    trx_id = None
    m2 = _TRXID_RE.search(t)
    if m2:
        trx_id = m2.group(1).strip().upper()

    if amount is None or not trx_id:
        return None
    return {"method": method, "amount": amount, "trx_id": trx_id}


def _norm_trx(method, value):
    """ম্যাচিংয়ের জন্য TrxID/Username স্ট্যান্ডার্ড করে। Binance username: বড়/ছোট হাতের অক্ষর,
    বাড়তি স্পেস ও শুরুর '@' উপেক্ষা করা হয়; বাকিদের TrxID: uppercase।"""
    v = (value or "").strip()
    if method == "Binance":
        return re.sub(r"\s+", " ", v.lstrip("@")).strip().lower()
    return v.upper()


def _consume_matching_sms(dep):
    """(_deposit_lock এর ভেতরে কল করতে হবে) Admin ম্যানুয়ালি approve করা deposit এর সাথে মিলে যাওয়া
    ব্যবহার-না-হওয়া SMS থাকলে সেটা used মার্ক করে — একই পেমেন্ট আবার ব্যবহার ঠেকাতে।"""
    try:
        method = dep.get("method")
        key = _norm_trx(method, dep.get("trx_id"))
        if not key:
            return
        for sms in list(sms_log):
            if sms.get("is_used") or sms.get("method") != method:
                continue
            if _norm_trx(method, sms.get("trx_id")) != key:
                continue
            if method == "Binance" and not _amounts_match("Binance", dep.get("amount_usdt"), sms.get("amount")):
                continue
            sms["is_used"] = True
            sms["used_by_deposit_id"] = dep["id"]
            return
    except Exception as e:
        print(f"⚠️ _consume_matching_sms error: {e}")


def _methods_match(a, b):
    """কোনোটা খালি থাকলে মিল ধরা হয় না — method যাচাই না করে auto-approve করা যাবে না।"""
    a = (a or "").strip().lower()
    b = (b or "").strip().lower()
    return bool(a) and bool(b) and a == b


def _amounts_match(method, a, b):
    if a is None or b is None:
        return False
    eps = 0.0005 if method == "Binance" else 0.01
    return abs(a - b) < eps


def _auto_approve_deposit_with_sms(dep, sms):
    """dep + sms দুটোকেই approved/used হিসেবে মার্ক করে ব্যালেন্স যোগ করে।

    🔒 Race-condition fix: dep['status']=='pending' ও sms['is_used']==False কিনা
    চেক করা থেকে শুরু করে approved/used সেট করা পর্যন্ত পুরোটা _deposit_lock দিয়ে
    atomic রাখা হয়েছে — একই deposit/SMS দুইবার (যেমন duplicate SMS webhook কল বা
    একই সময়ে ম্যানুয়াল Approve) ম্যাচ হয়ে দুইবার ব্যালেন্স যোগ হওয়া এতে ঠেকানো যায়।

    🛡️ Data-safety fix: ইউজার রেকর্ড খুঁজে না পেলে deposit approved মার্ক না করে
    (ব্যালেন্স-বিহীন approved অবস্থা এড়াতে) pending-ই রাখা হয় এবং Admin-কে সতর্ক
    করা হয়।"""
    with _deposit_lock:
        if dep["status"] != "pending" or sms["is_used"]:
            return False

        u = users.get(dep["user_id"])
        if u is None:
            for admin_id in ADMIN_IDS:
                try:
                    bot.send_message(
                        admin_id,
                        "⚠️ <b>SMS ম্যাচ হয়েছে কিন্তু ইউজার খুঁজে পাওয়া যায়নি!</b>\n\n"
                        f"🆔 DEP-{dep['id']} | 👤 <code>{dep['user_id']}</code>\n"
                        "ব্যালেন্স যোগ করা হয়নি, deposit এখনও 'pending' আছে। ম্যানুয়ালি চেক করুন।",
                    )
                except Exception:
                    pass
            return False

        dep["status"] = "approved"
        sms["is_used"] = True
        sms["used_by_deposit_id"] = dep["id"]
        u["balance"] += dep["amount"]
        u["today_deposit"] += dep["amount"]
        save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)
        _clear_deposit_admin_buttons(dep)   # আগে দেখানো থাকলে Pending Deposits লিস্টের বাটনও সরানো হলো

    try:
        bot.send_message(
            dep["user_id"],
            "✅ <b>Deposit Auto-Approved!</b>\n\n"
            f"🆔 Request: DEP-{dep['id']}\n"
            f"💳 Method: {dep['method']}\n"
            f"💰 +{fmt_amount(dep['amount'])} added\n"
            f"💰 New Balance: {fmt_amount(u['balance'])}",
        )
    except Exception:
        pass
    for admin_id in ADMIN_IDS:
        try:
            bot.send_message(
                admin_id,
                "🤖 <b>Auto-Approved Deposit (SMS matched)</b>\n\n"
                f"🆔 DEP-{dep['id']} | 👤 <code>{dep['user_id']}</code>\n"
                f"💳 {dep['method']} | ?? {fmt_amount(dep['amount'])}\n"
                f"🔑 {_id_label(dep['method'])}: <code>{dep['trx_id']}</code>\n"
                f"📩 Matched SMS #{sms['id']}",
            )
        except Exception:
            pass
    return True


def _auto_reject_mismatched_deposit(dep, sms, method_ok, amount_ok):
    """TrxID মিলেছে কিন্তু Method/Amount মিলেনি — ইউজার ভুল তথ্য দিয়েছে, তাই
    pending না রেখে সাথে সাথে reject করে ইউজারকে জানানো হচ্ছে।
    🔒 এখানেও status চেক + সেট করার অংশটা _deposit_lock দিয়ে atomic রাখা হয়েছে।"""
    with _deposit_lock:
        if dep["status"] != "pending":
            return
        dep["status"] = "rejected"
        save_db()   # ✅ ডিস্কে persist করা হলো (persistent DB)
        _clear_deposit_admin_buttons(dep)

    mismatch_lines = []
    if not method_ok:
        mismatch_lines.append(f"💳 Method মিলছে না — Deposit: {dep['method']} vs SMS: {sms['method'] or '—'}")
    if not amount_ok:
        mismatch_lines.append(
            f"💰 Amount মিলছে না — Deposit: {dep['amount']} vs SMS: {sms['amount']} {_amount_unit(sms['method'])}"
        )

    try:
        bot.send_message(
            dep["user_id"],
            "❌ <b>আপনার দেওয়া তথ্য সঠিক নয়!</b>\n\n"
            f"🆔 Request: DEP-{dep['id']}\n\n"
            "আপনার দেওয়া Amount/Method আসল পেমেন্টের সাথে মিলছে না। সঠিক তথ্য দিয়ে "
            "আবার Deposit চেষ্টা করুন, অথবা Support এ যোগাযোগ করুন।",
        )
    except Exception:
        pass
    for admin_id in ADMIN_IDS:
        try:
            bot.send_message(
                admin_id,
                "🚫 <b>Deposit Auto-Rejected — Mismatch</b>\n\n"
                f"🆔 DEP-{dep['id']} (user {dep['user_id']})\n"
                f"🔑 {_id_label(sms['method'])}: <code>{sms['trx_id']}</code> (মিলেছে)\n\n"
                + "\n".join(mismatch_lines),
            )
        except Exception:
            pass


def try_auto_approve_from_stored_sms(dep):
    """একটা নতুন pending deposit তৈরি হওয়ার সাথে সাথেই, আগে থেকেই সেইভ করা কোনো
    ব্যবহার-না-হওয়া SMS এর সাথে TrxID মিলছে কিনা চেক করে; method+amount ও
    মিললে তবেই অটো-অ্যাপ্রুভ করে। রিটার্ন করে: "approved" | "rejected_mismatch" | "no_match" """
    if dep["method"] not in SMS_AUTO_APPROVE_METHODS:
        return "no_match"   # SMS_AUTO_APPROVE_METHODS এর বাইরের মেথড -> অটো-অ্যাপ্রুভ চেষ্টা হয় না

    trx = (dep.get("trx_id") or "").strip().upper()
    if not trx:
        return "no_match"

    if dep["method"] == "Binance":
        # Binance: Username + USDT Amount দুটোই হুবহু মিলতে হবে; না মিললে pending (reject নয়)
        key = _norm_trx("Binance", dep.get("trx_id"))
        bsms = next(
            (
                s for s in list(sms_log)
                if not s["is_used"] and s.get("method") == "Binance"
                and _norm_trx("Binance", s["trx_id"]) == key
                and _amounts_match("Binance", dep.get("amount_usdt"), s["amount"])
            ),
            None,
        )
        if not bsms:
            return "no_match"
        return "approved" if _auto_approve_deposit_with_sms(dep, bsms) else "no_match"

    sms = next((s for s in sms_log if not s["is_used"] and s["trx_id"].upper() == trx), None)
    if not sms:
        return "no_match"

    amount_ok = _amounts_match(dep["method"], dep.get("amount"), sms["amount"])
    method_ok = _methods_match(dep["method"], sms["method"])
    if amount_ok and method_ok:
        return "approved" if _auto_approve_deposit_with_sms(dep, sms) else "no_match"

    _auto_reject_mismatched_deposit(dep, sms, method_ok, amount_ok)
    return "rejected_mismatch"


def store_sms_and_try_match(text, sender="", hint_method=""):
    """ওয়েবহুক থেকে আসা SMS/নোটিফিকেশন পার্স + সেইভ করে, এবং কোনো pending
    ডিপোজিটের সাথে (TrxID দিয়ে) ম্যাচ করলে সাথে সাথে অটো-অ্যাপ্রুভ করে দেয়।
    ফরোয়ার্ডার অ্যাপ রিট্রাই করলে (একই SMS দুইবার আসলে) ডুপ্লিকেট এন্ট্রি বানায় না।"""
    parsed = parse_payment_sms(text, hint_method=hint_method, sender=sender)
    if not parsed:
        return {"stored": False, "reason": "not_a_payment_sms"}

    for s in sms_log:
        if parsed["method"] == "Binance":
            if s["raw_text"] == text[:1000]:
                return {"stored": True, "sms_id": s["id"], "duplicate": True}
        else:
            if s["trx_id"] == parsed["trx_id"] and s["amount"] is not None and abs(s["amount"] - parsed["amount"]) < 0.01:
                return {"stored": True, "sms_id": s["id"], "duplicate": True}

    sms_id = _next_sms_id()
    sms = {
        "id": sms_id,
        "method": parsed["method"],
        "amount": parsed["amount"],
        "trx_id": parsed["trx_id"],
        "raw_text": text[:1000],
        "sender": (sender or "")[:64],
        "is_used": False,
        "used_by_deposit_id": None,
        "date": datetime.datetime.now().strftime("%d/%m/%Y %I:%M %p"),
    }
    sms_log.append(sms)

    for admin_id in ADMIN_IDS:
        try:
            bot.send_message(
                admin_id,
                "📥 <b>New Payment received</b>\n\n"
                f"💳 Method: {sms['method'] or '—'}\n"
                f"🔑 {_id_label(sms['method'])}: <code>{sms['trx_id']}</code>\n"
                f"💰 Amount: {sms['amount']} {_amount_unit(sms['method'])}\n"
                f"📅 Time: {sms['date']}",
            )
        except Exception:
            pass

    matched_dep_id = None
    if sms["method"] == "Binance":
        # Binance: pending Binance deposit এর Username + USDT Amount হুবহু মিললে অটো-অ্যাপ্রুভ
        # (একাধিক মিললে সবচেয়ে পুরোনোটা; এক পেমেন্ট শুধু একটা deposit এই লাগবে)
        bkey = _norm_trx("Binance", sms["trx_id"])
        bdep = next(
            (
                d for d in list(deposits.values())
                if d["status"] == "pending" and d.get("method") == "Binance"
                and _norm_trx("Binance", d.get("trx_id")) == bkey
                and _amounts_match("Binance", d.get("amount_usdt"), sms["amount"])
            ),
            None,
        )
        if bdep and _auto_approve_deposit_with_sms(bdep, sms):
            matched_dep_id = bdep["id"]
    else:
        dep = next(
            (
                d for d in deposits.values()
                if d["status"] == "pending"
                and d.get("trx_id")
                and d["trx_id"].strip().upper() == sms["trx_id"].upper()
            ),
            None,
        )
        if dep:
            amount_ok = _amounts_match(sms["method"], dep.get("amount"), sms["amount"])
            method_ok = _methods_match(dep.get("method"), sms["method"])
            if amount_ok and method_ok:
                if _auto_approve_deposit_with_sms(dep, sms):
                    matched_dep_id = dep["id"]
            else:
                _auto_reject_mismatched_deposit(dep, sms, method_ok, amount_ok)

    return {"stored": True, "sms_id": sms_id, "matched_deposit_id": matched_dep_id}


# ---------------------------------------------------------------------------
# SMS AUTO-DEPOSIT WEBHOOK SERVER (SMS Forwarder App -> এই বট)
# ---------------------------------------------------------------------------
# ফোনে ইনস্টল করা SMS Forwarder App (যেমন "SMS Forwarder", "Sms2Telegram" ইত্যাদি)
# থেকে bKash/Nagad/Rocket/Binance এর পেমেন্ট SMS এখানে ফরোয়ার্ড করা হবে। যেকেউ
# রিকোয়েস্ট পাঠিয়ে ভুয়া ব্যালেন্স যোগ করার চেষ্টা করতে পারে, তাই একটা গোপন
# TOKEN বাধ্যতামূলক — .env / Railway Variables এ SMS_WEBHOOK_TOKEN সেট করুন।
SMS_WEBHOOK_TOKEN = os.environ.get("SMS_WEBHOOK_TOKEN", "").strip()
SMS_WEBHOOK_PATH = os.environ.get("SMS_WEBHOOK_PATH", "/sms-webhook").strip() or "/sms-webhook"
if not SMS_WEBHOOK_TOKEN:
    SMS_WEBHOOK_TOKEN = uuid.uuid4().hex
    print(
        "⚠️  SMS_WEBHOOK_TOKEN সেট করা ছিল না — একটা টেম্পোরারি টোকেন তৈরি করা হয়েছে "
        f"(বট রিস্টার্টে বদলে যাবে): {SMS_WEBHOOK_TOKEN}\n"
        f"   স্থায়ী রাখতে .env / Railway Variables এ যোগ করুন: SMS_WEBHOOK_TOKEN={SMS_WEBHOOK_TOKEN}"
    )

try:
    from flask import Flask, request as flask_request

    flask_app = Flask(__name__)
except ImportError:
    flask_app = None
    print("⚠️  Flask ইনস্টল করা নেই, তাই SMS auto-deposit webhook চালু হবে না। ইনস্টল করুন: pip install flask")

_SMS_TEXT_FIELD_NAMES = ("text", "message", "body", "content", "sms", "msg", "text_message", "sms_body", "smsBody", "key")
_SMS_SENDER_FIELD_NAMES = ("from", "sender", "number", "phone", "sms_from", "smsFrom", "originator")


def _dig_field(d, names):
    """dict এর মধ্যে (nested dict হলেও একটু খুঁজে) common field name গুলো চেক করে।"""
    if not isinstance(d, dict):
        return ""
    for k in names:
        v = d.get(k)
        if isinstance(v, str) and v.strip():
            return v.strip()
    for v in d.values():
        if isinstance(v, dict):
            found = _dig_field(v, names)
            if found:
                return found
    return ""


def _check_sms_token(req):
    token = req.args.get("token") or req.headers.get("X-Webhook-Token") or ""
    return token == SMS_WEBHOOK_TOKEN


if flask_app is not None:

    @flask_app.route(SMS_WEBHOOK_PATH, methods=["GET", "POST"])
    def sms_webhook_handler():
        if not _check_sms_token(flask_request):
            return {"ok": False, "error": "invalid_token"}, 401

        text = flask_request.args.get("text") or flask_request.args.get("message") or ""
        sender = flask_request.args.get("from") or flask_request.args.get("sender") or ""
        hint_method = flask_request.args.get("method") or ""

        if flask_request.method == "POST":
            try:
                raw_body_str = flask_request.get_data(as_text=True) or ""
            except Exception:
                raw_body_str = ""

            body = {}
            if raw_body_str:
                try:
                    parsed_json = json.loads(raw_body_str)
                    if isinstance(parsed_json, dict):
                        body = parsed_json
                except Exception:
                    if "=" in raw_body_str and "&" in raw_body_str:
                        try:
                            from urllib.parse import parse_qs

                            parsed_form = parse_qs(raw_body_str)
                            body = {k: v[0] for k, v in parsed_form.items() if v}
                        except Exception:
                            body = {}

            if body:
                text = text or _dig_field(body, _SMS_TEXT_FIELD_NAMES)
                sender = sender or _dig_field(body, _SMS_SENDER_FIELD_NAMES)
                hint_method = hint_method or _dig_field(body, ("method", "app", "provider"))

            if not text and raw_body_str and not raw_body_str.lstrip().startswith(("{", "[")):
                text = raw_body_str

        if not text:
            # ✅ SMS Forwarder app যেন সবসময় HTTP 200 পায় (নাহলে app এটাকে Fail/Retry ধরে)
            return {"ok": True, "note": "no_text_field"}, 200

        try:
            result = store_sms_and_try_match(text, sender=sender, hint_method=hint_method)
        except Exception as e:
            print(f"❌ sms_webhook_handler error: {e}")
            return {"ok": True, "note": "internal_error_logged"}, 200

        return {"ok": True, **result}, 200

    @flask_app.route("/", methods=["GET"])
    def _sms_webhook_health():
        return {"ok": True, "service": "sms-webhook", "path": SMS_WEBHOOK_PATH}, 200


def _print_sms_webhook_url():
    if RAILWAY_URL:
        full_url = f"{RAILWAY_URL}{SMS_WEBHOOK_PATH}?token={SMS_WEBHOOK_TOKEN}"
    else:
        full_url = f"http://<your-server-ip>:{PORT}{SMS_WEBHOOK_PATH}?token={SMS_WEBHOOK_TOKEN}"
    print(
        f"📩 SMS webhook ready → {full_url}\n"
        "   ফরোয়ার্ডার অ্যাপে GET/POST params হিসেবে পাঠান: text (SMS বডি), from (sender, ঐচ্ছিক)"
    )


# ---------------------------------------------------------------------------
# RUN (Polling for local test / Webhook for Railway)
# ---------------------------------------------------------------------------
def run_polling():
    start_persistent_db()   # ✅ ডিস্কে সেভ করা DB লোড + অটোসেভ থ্রেড চালু
    _prime_reply_label_map()   # 💎 Premium emoji: রিস্টার্টের পরও পুরোনো কীবোর্ড বাটন কাজ করবে
    print("Bot running in POLLING mode...")
    if flask_app is not None:
        # SMS webhook এর জন্য আলাদা থ্রেডে ছোট একটা Flask সার্ভার চালু হচ্ছে,
        # যাতে polling মোডেও SMS Forwarder App থেকে অটো-ডিপোজিট কাজ করে।
        threading.Thread(
            target=lambda: flask_app.run(host="0.0.0.0", port=PORT, use_reloader=False),
            daemon=True,
        ).start()
        _print_sms_webhook_url()
    bot.remove_webhook()
    bot.infinity_polling()


def run_webhook():
    start_persistent_db()   # ✅ ডিস্কে সেভ করা DB লোড + অটোসেভ থ্রেড চালু
    _prime_reply_label_map()   # 💎 Premium emoji: রিস্টার্টের পরও পুরোনো কীবোর্ড বাটন কাজ করবে
    if flask_app is None:
        print("❌ Flask ইনস্টল করা নেই, তাই WEBHOOK mode চালু করা যাচ্ছে না। ইনস্টল করুন: pip install flask")
        return

    app = flask_app
    webhook_path = f"/webhook/{BOT_TOKEN}"

    @app.route(webhook_path, methods=["POST"])
    def telegram_webhook():
        json_str = flask_request.get_data().decode("utf-8")
        update = telebot.types.Update.de_json(json_str)
        bot.process_new_updates([update])
        return "OK", 200

    bot.remove_webhook()
    bot.set_webhook(url=f"{RAILWAY_URL}{webhook_path}")
    print(f"Bot running in WEBHOOK mode on port {PORT} -> {RAILWAY_URL}{webhook_path}")
    _print_sms_webhook_url()
    app.run(host="0.0.0.0", port=PORT)


if __name__ == "__main__":
    if RAILWAY_URL:
        run_webhook()
    else:
        run_polling()
