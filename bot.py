import os
import json
import time
import asyncio
import random
import sqlite3
import re
from datetime import datetime
from typing import Optional, List, Tuple

import aiohttp
from aiogram import Bot, Dispatcher, F
from aiogram.types import (
    Message,
    CallbackQuery,
    ReplyKeyboardMarkup,
    KeyboardButton,
    InlineKeyboardMarkup,
    InlineKeyboardButton,
    FSInputFile,
    BotCommand,
    MenuButtonCommands,
)
from aiogram.filters import Command
from aiogram.client.default import DefaultBotProperties

from telethon import TelegramClient
from telethon.errors import (
    SessionPasswordNeededError,
    ChannelsTooMuchError,
    ChannelInvalidError,
    ChannelPrivateError,
    FloodWaitError,
    UsernameInvalidError,
    InviteRequestSentError,
    UserAlreadyParticipantError,
    InviteHashInvalidError,
    InviteHashExpiredError,
)
from telethon.tl.functions.channels import JoinChannelRequest
from telethon.tl.functions.messages import ImportChatInviteRequest


BOT_TOKEN = ""
CRYPTO_PAY_TOKEN = ""
CRYPTO_API = "https://pay.crypt.bot/api"

ADMIN_IDS = {1077765720}
SUPPORT_CONTACT = "@Haskidobre"
TRIAL_DAYS = 1

PLANS = {
    1: {"usd": 4, "days": 30},
    2: {"usd": 8, "days": 60},
    3: {"usd": 12, "days": 90},
}
ASSETS = ["USDT", "TON", "BTC", "ETH"]
STALE_ACCOUNT_DAYS = 30

BASE = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(BASE, "data")
ACCOUNTS_DIR = os.path.join(BASE, "accounts")
LOGS_DIR = os.path.join(BASE, "logs")
os.makedirs(DATA_DIR, exist_ok=True)
os.makedirs(ACCOUNTS_DIR, exist_ok=True)
os.makedirs(LOGS_DIR, exist_ok=True)

DB_PATH = os.path.join(DATA_DIR, "bot.db")
SETTINGS_PATH = os.path.join(DATA_DIR, "settings.json")


def db():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def ensure_column(conn, table: str, col: str, col_def: str):
    cur = conn.execute(f"PRAGMA table_info({table})")
    cols = [r[1] for r in cur.fetchall()]
    if col not in cols:
        conn.execute(f"ALTER TABLE {table} ADD COLUMN {col} {col_def}")


def init_db():
    with db() as c:
        c.executescript(
            """
            CREATE TABLE IF NOT EXISTS users (
                user_id INTEGER PRIMARY KEY
            );

            CREATE TABLE IF NOT EXISTS subs (
                user_id INTEGER PRIMARY KEY,
                expire_ts INTEGER DEFAULT 0,
                trial_used INTEGER DEFAULT 0
            );

            CREATE TABLE IF NOT EXISTS accounts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                phone TEXT,
                session_path TEXT
            );

            CREATE TABLE IF NOT EXISTS logs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                phone TEXT,
                level TEXT,
                message TEXT,
                ts INTEGER
            );

            CREATE TABLE IF NOT EXISTS invoices (
                invoice_id INTEGER PRIMARY KEY,
                user_id INTEGER,
                days INTEGER,
                usd INTEGER,
                asset TEXT,
                status TEXT,
                created_ts INTEGER
            );
            """
        )
        ensure_column(c, "users", "created_ts", "INTEGER")
        ensure_column(c, "users", "referrer_id", "INTEGER")
        ensure_column(c, "users", "ref_balance_usd", "REAL DEFAULT 0")
        ensure_column(c, "subs", "expire_ts", "INTEGER DEFAULT 0")
        ensure_column(c, "subs", "trial_used", "INTEGER DEFAULT 0")
        ensure_column(c, "invoices", "created_ts", "INTEGER")
        ensure_column(c, "accounts", "created_ts", "INTEGER")
        ensure_column(c, "accounts", "last_used_ts", "INTEGER")


def now_ts() -> int:
    return int(time.time())


def fmt_ts(ts: int) -> str:
    return datetime.fromtimestamp(ts).strftime("%Y-%m-%d %H:%M:%S")


def log_event(uid: int, phone: Optional[str], level: str, msg: str):
    ts = now_ts()
    p = phone or "-"
    with db() as c:
        c.execute(
            "INSERT INTO logs (user_id, phone, level, message, ts) VALUES (?,?,?,?,?)",
            (uid, p, level, msg, ts),
        )


def load_settings():
    if not os.path.exists(SETTINGS_PATH):
        return {"api_id": None, "api_hash": None}
    with open(SETTINGS_PATH, "r", encoding="utf-8") as f:
        return json.load(f)


def save_settings(api_id, api_hash):
    with open(SETTINGS_PATH, "w", encoding="utf-8") as f:
        json.dump({"api_id": api_id, "api_hash": api_hash}, f)


settings = load_settings()
API_ID = settings.get("api_id")
API_HASH = settings.get("api_hash")


bot = Bot(BOT_TOKEN, default=DefaultBotProperties(parse_mode="HTML"))
dp = Dispatcher()

clients = {}
pending_add = {}
pending_sub = {}
stop_flags = {}
progress = {}


def sub_expire(uid: int) -> int:
    with db() as c:
        row = c.execute("SELECT expire_ts FROM subs WHERE user_id=?", (uid,)).fetchone()
        return int(row["expire_ts"]) if row else 0


def sub_active(uid: int) -> bool:
    return sub_expire(uid) > now_ts()


def trial_used(uid: int) -> bool:
    with db() as c:
        row = c.execute("SELECT trial_used FROM subs WHERE user_id=?", (uid,)).fetchone()
        return bool(row and int(row["trial_used"]) == 1)


def grant_trial(uid: int) -> int:
    exp = now_ts() + TRIAL_DAYS * 86400
    with db() as c:
        c.execute(
            """
            INSERT INTO subs (user_id, expire_ts, trial_used)
            VALUES (?,?,1)
            ON CONFLICT(user_id) DO UPDATE SET expire_ts=excluded.expire_ts, trial_used=1
            """,
            (uid, exp),
        )
    return exp


def normalize_phone(phone: str, default_country="+7"):
    digits = "".join(c for c in phone if c.isdigit())
    if not digits:
        return None
    if digits.startswith("8") and len(digits) == 11:
        return "+7" + digits[1:]
    if digits.startswith("7") and len(digits) == 11:
        return "+" + digits
    if len(digits) == 10:
        return default_country + digits
    if len(digits) >= 11:
        return "+" + digits
    return None


def list_accounts(uid: int):
    with db() as c:
        rows = c.execute(
            "SELECT phone, session_path, COALESCE(last_used_ts, 0) as last_used_ts FROM accounts WHERE user_id=? ORDER BY id DESC",
            (uid,),
        ).fetchall()
    return [(r["phone"], r["session_path"], int(r["last_used_ts"])) for r in rows]


def save_account(uid: int, phone: str, session_path: str):
    ts = now_ts()
    with db() as c:
        c.execute("DELETE FROM accounts WHERE user_id=? AND phone=?", (uid, phone))
        c.execute(
            "INSERT INTO accounts (user_id, phone, session_path, created_ts, last_used_ts) VALUES (?,?,?,?,?)",
            (uid, phone, session_path, ts, ts),
        )


def touch_account(uid: int, phone: str):
    with db() as c:
        c.execute(
            "UPDATE accounts SET last_used_ts=? WHERE user_id=? AND phone=?",
            (now_ts(), uid, phone),
        )


def delete_account(uid: int, phone: str) -> bool:
    session_path = None
    with db() as c:
        row = c.execute(
            "SELECT session_path FROM accounts WHERE user_id=? AND phone=? ORDER BY id DESC LIMIT 1",
            (uid, phone),
        ).fetchone()
        if row:
            session_path = row["session_path"]
        c.execute("DELETE FROM accounts WHERE user_id=? AND phone=?", (uid, phone))

    cl = clients.get(uid, {}).pop(phone, None)
    if cl:
        try:
            asyncio.create_task(cl.disconnect())
        except Exception:
            pass

    removed_files = 0
    if session_path:
        for path in [session_path, f"{session_path}.session", f"{session_path}.session-journal"]:
            if path and os.path.exists(path):
                try:
                    os.remove(path)
                    removed_files += 1
                except Exception:
                    pass
    return removed_files >= 0


async def prune_stale_accounts(uid: int, stale_days: int) -> Tuple[int, int]:
    cutoff = now_ts() - stale_days * 86400
    deleted = 0
    checked = 0
    for phone, _, last_used in list_accounts(uid):
        checked += 1
        if last_used and last_used >= cutoff:
            continue
        if delete_account(uid, phone):
            deleted += 1
    return deleted, checked


def is_admin(uid: int) -> bool:
    return uid in ADMIN_IDS


async def get_client(uid: int, phone: str) -> TelegramClient:
    if not API_ID or not API_HASH:
        raise RuntimeError("API_ID/API_HASH не заданы")

    client = clients.get(uid, {}).get(phone)
    if client:
        if not client.is_connected():
            await client.connect()
        if await client.is_user_authorized():
            touch_account(uid, phone)
            return client

    session_path = None
    for ph, sp, _ in list_accounts(uid):
        if ph == phone:
            session_path = sp
            break
    if not session_path:
        raise RuntimeError("Аккаунт не найден в БД")

    last_exc = None
    for _ in range(3):
        try:
            client = TelegramClient(session_path, API_ID, API_HASH)
            await client.connect()
            if await client.is_user_authorized():
                clients.setdefault(uid, {})[phone] = client
                touch_account(uid, phone)
                return client
            await client.disconnect()
            raise RuntimeError("Сессия не авторизована")
        except Exception as e:
            last_exc = e
            await asyncio.sleep(2)
    raise RuntimeError(f"Не удалось подключить аккаунт: {last_exc}")


def main_kb(uid: int):
    kb = [
        [KeyboardButton(text="📂 Меню"), KeyboardButton(text="📊 Статистика")],
        [KeyboardButton(text="🆘 Поддержка")],
    ]
    return ReplyKeyboardMarkup(keyboard=kb, resize_keyboard=True)


def quick_menu_kb(uid: int):
    rows = [
        [InlineKeyboardButton(text="💳 Купить подписку", callback_data="ui:buy"), InlineKeyboardButton(text="🎁 Пробный", callback_data="ui:trial")],
        [InlineKeyboardButton(text="➕ Добавить аккаунт", callback_data="ui:add_acc"), InlineKeyboardButton(text="▶️ Начать", callback_data="ui:start_sub")],
        [InlineKeyboardButton(text="⛔ Стоп", callback_data="ui:stop"), InlineKeyboardButton(text="🗑 Очистить чаты", callback_data="ui:clear")],
        [InlineKeyboardButton(text="❌ Удалить аккаунт", callback_data="ui:del_acc"), InlineKeyboardButton(text="🧹 Удалить старые", callback_data="ui:prune_old")],
        [InlineKeyboardButton(text="⚙️ API", callback_data="ui:api")],
    ]
    return InlineKeyboardMarkup(inline_keyboard=rows)


def accounts_kb(uid: int, prefix: str):
    accs = list_accounts(uid)
    if not accs:
        return InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="Нет аккаунтов", callback_data="none")]])
    rows = []
    for phone, _, last_used in accs:
        tail = f" · {fmt_ts(last_used)}" if last_used else ""
        rows.append([InlineKeyboardButton(text=f"{phone}{tail}", callback_data=f"{prefix}:{phone}")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


async def try_join(client: TelegramClient, typ: str, value: str) -> Tuple[bool, str]:
    while True:
        try:
            if typ == "invite":
                await client(ImportChatInviteRequest(value))
            else:
                await client(JoinChannelRequest(value))
            return True, "ok"
        except UserAlreadyParticipantError:
            return True, "already"
        except FloodWaitError as e:
            await asyncio.sleep(int(getattr(e, "seconds", 0) or 0) + 2)
        except (
            ChannelsTooMuchError,
            ChannelInvalidError,
            ChannelPrivateError,
            UsernameInvalidError,
            InviteRequestSentError,
            InviteHashInvalidError,
            InviteHashExpiredError,
        ) as e:
            return False, e.__class__.__name__
        except Exception as e:
            return False, str(e)


def parse_targets(raw_text: str) -> List[Tuple[str, str]]:
    targets = []
    seen = set()
    for line in raw_text.splitlines():
        line = line.strip()
        if not line:
            continue
        m = re.search(r"(?:https?://)?t\.me/(?:joinchat/|\+)?([A-Za-z0-9_\-]+)", line)
        if m:
            val = m.group(1)
            typ = "invite" if "joinchat/" in line or "t.me/+" in line else "username"
            key = (typ, val.lower())
            if key not in seen:
                seen.add(key)
                targets.append((typ, val))
            continue
        if line.startswith("@") and len(line) > 1:
            val = line[1:]
            key = ("username", val.lower())
            if key not in seen:
                seen.add(key)
                targets.append(("username", val))
    return targets


@dp.message(Command("start"))
async def cmd_start(msg: Message):
    uid = msg.from_user.id
    with db() as c:
        c.execute("INSERT OR IGNORE INTO users (user_id, created_ts) VALUES (?,?)", (uid, now_ts()))
    await msg.answer("Готово", reply_markup=main_kb(uid))


@dp.message(F.text == "📂 Меню")
async def menu(msg: Message):
    await msg.answer("Выбери:", reply_markup=quick_menu_kb(msg.from_user.id))


@dp.callback_query()
async def callbacks(cb: CallbackQuery):
    uid = cb.from_user.id
    data = cb.data or ""
    await cb.answer()

    if data == "ui:add_acc":
        pending_add[uid] = {"step": "phone"}
        await cb.message.answer("📞 Введи номер телефона")
    elif data == "ui:start_sub":
        await cb.message.answer("Выбери аккаунт:", reply_markup=accounts_kb(uid, "sub"))
    elif data == "ui:clear":
        await cb.message.answer("Выбери аккаунт:", reply_markup=accounts_kb(uid, "clear"))
    elif data == "ui:del_acc":
        await cb.message.answer("Выбери аккаунт для удаления:", reply_markup=accounts_kb(uid, "del"))
    elif data == "ui:prune_old":
        deleted, checked = await prune_stale_accounts(uid, STALE_ACCOUNT_DAYS)
        await cb.message.answer(f"🧹 Проверено: <b>{checked}</b>\nУдалено старых: <b>{deleted}</b>")
    elif data.startswith("del:"):
        phone = data.split(":", 1)[1]
        ok = delete_account(uid, phone)
        if ok:
            await cb.message.answer(f"✅ Аккаунт <b>{phone}</b> удалён")
        else:
            await cb.message.answer("❌ Не удалось удалить аккаунт")
    elif data.startswith("sub:"):
        phone = data.split(":", 1)[1]
        pending_sub[uid] = phone
        await cb.message.answer("Отправь ссылки t.me списком")
    elif data.startswith("clear:"):
        phone = data.split(":", 1)[1]
        client = await get_client(uid, phone)
        dialogs = await client.get_dialogs()
        deleted = 0
        for d in dialogs:
            try:
                await client.delete_dialog(d.entity)
                deleted += 1
                await asyncio.sleep(0.2)
            except Exception:
                pass
        await cb.message.answer(f"✅ Удалено чатов: {deleted}")


@dp.message(F.text)
async def fallback(msg: Message):
    uid = msg.from_user.id
    text = msg.text.strip()

    if uid in pending_add:
        st = pending_add[uid]
        if st.get("step") == "phone":
            phone = normalize_phone(text)
            if not phone:
                await msg.answer("❌ Неверный формат телефона")
                return
            session_path = os.path.join(ACCOUNTS_DIR, f"{uid}_{phone}")
            client = TelegramClient(session_path, API_ID, API_HASH)
            await client.connect()
            if await client.is_user_authorized():
                clients.setdefault(uid, {})[phone] = client
                save_account(uid, phone, session_path)
                pending_add.pop(uid, None)
                await msg.answer("✅ Аккаунт добавлен")
                return
            try:
                await client.send_code_request(phone, force_sms=True)
            except TypeError:
                await client.send_code_request(phone)
            st.update({"step": "code", "phone": phone, "session_path": session_path, "client": client})
            await msg.answer("📨 Введи код")
            return
        if st.get("step") == "code":
            try:
                await st["client"].sign_in(st["phone"], text)
            except SessionPasswordNeededError:
                st["step"] = "2fa"
                await msg.answer("🔐 Введи пароль 2FA")
                return
            clients.setdefault(uid, {})[st["phone"]] = st["client"]
            save_account(uid, st["phone"], st["session_path"])
            pending_add.pop(uid, None)
            await msg.answer("✅ Аккаунт добавлен")
            return
        if st.get("step") == "2fa":
            await st["client"].sign_in(password=text)
            clients.setdefault(uid, {})[st["phone"]] = st["client"]
            save_account(uid, st["phone"], st["session_path"])
            pending_add.pop(uid, None)
            await msg.answer("✅ Аккаунт добавлен")
            return

    if uid in pending_sub:
        phone = pending_sub.pop(uid)
        if not sub_active(uid) and not is_admin(uid):
            await msg.answer("❌ Нет подписки")
            return
        links = parse_targets(text)
        if not links:
            await msg.answer("❌ Нет валидных ссылок")
            return
        client = await get_client(uid, phone)
        done, failed = 0, 0
        progress.setdefault(uid, {})[phone] = {"done": 0, "total": len(links), "status": "running"}
        for typ, val in links:
            ok, _ = await try_join(client, typ, val)
            if ok:
                done += 1
                progress[uid][phone]["done"] = done
            else:
                failed += 1
            await asyncio.sleep(random.randint(8, 15))
        progress[uid][phone]["status"] = "finished"
        await msg.answer(f"✅ Завершено\nУспешно: <b>{done}</b>\nОшибок: <b>{failed}</b>")


async def setup_menu_commands():
    await bot.set_my_commands([BotCommand(command="start", description="Открыть меню")])
    await bot.set_chat_menu_button(menu_button=MenuButtonCommands())


async def main():
    init_db()
    await setup_menu_commands()
    await dp.start_polling(bot)


if __name__ == "__main__":
    asyncio.run(main())
