#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from __future__ import annotations

import asyncio
import importlib.util
import json
import random
import re
import urllib.parse
import sys
from contextlib import closing, suppress
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

from telegram import BotCommand, InlineKeyboardButton, InlineKeyboardMarkup, InputFile, InputTextMessageContent, Poll, Update
from telegram.constants import ParseMode
from telegram.error import TelegramError
from telegram.ext import Application, InlineQueryHandler
from telegram import InlineQueryResultArticle

BASE_PATH = Path(__file__).resolve().with_name("bot_base.py")
spec = importlib.util.spec_from_file_location("bot_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"Could not load bot_base.py from {BASE_PATH}")
base = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = base
spec.loader.exec_module(base)


# ============================================================
# Advanced overlay: feasible additions without OCR / paid APIs
# ============================================================

CHECKMARKS = ("✅", "☑", "✔", "✓")
TEXT_IMPORT_STATES = {"adv_await_import_text", "adv_await_clone_source"}
SPEED_PRESETS = {
    "slow": (1.50, "slow"),
    "normal": (1.00, "normal"),
    "fast": (0.75, "fast"),
}
OPTION_RE = re.compile(r"^\s*(?:[-*•]|\(?[A-Ja-j1-9]\)|[A-Ja-j1-9][\).:-])\s*(.+?)\s*$")
ANSWER_RE = re.compile(r"^\s*(?:answer|ans|correct|right)\s*[:\-]\s*(.+?)\s*$", re.I)
EXPL_RE = re.compile(r"^\s*(?:explanation|explain|reason|note)\s*[:\-]\s*(.+?)\s*$", re.I)
QUESTION_PREFIX_RE = re.compile(r"^\s*(?:Q(?:uestion)?\s*\d+|\d+)\s*[\).:\-]\s*", re.I)
COUNTER_RE = re.compile(r"^\s*[\[(]?\s*\d+\s*/\s*\d+\s*[\])]?\s*", re.I)
URL_RE = re.compile(r"(?:https?://\S+|t\.me/\S+)", re.I)
USERNAME_RE = re.compile(r"(?<!\w)@[A-Za-z0-9_]{3,}")
QUIZBOT_TOKEN_RE = re.compile(r"(?:@quizbot\s+)?quiz\s*:\s*([A-Za-z0-9_-]{4,})", re.I)


def ensure_column(table: str, column: str, definition: str) -> None:
    with closing(base.DBH.connect()) as conn:
        cols = {str(r["name"]) for r in conn.execute(f"PRAGMA table_info({table})").fetchall()}
        if column not in cols:
            conn.execute(f"ALTER TABLE {table} ADD COLUMN {column} {definition}")
            conn.commit()


base.DBH.executescript(
    """
    CREATE TABLE IF NOT EXISTS draft_sections (
        draft_id TEXT NOT NULL,
        section_no INTEGER NOT NULL,
        title TEXT NOT NULL,
        start_q INTEGER NOT NULL,
        end_q INTEGER NOT NULL,
        question_time INTEGER,
        PRIMARY KEY (draft_id, section_no)
    );

    CREATE TABLE IF NOT EXISTS clone_sessions (
        user_id INTEGER PRIMARY KEY,
        draft_id TEXT NOT NULL,
        clone_token TEXT,
        source_text TEXT,
        active INTEGER NOT NULL DEFAULT 1,
        created_at INTEGER NOT NULL,
        updated_at INTEGER NOT NULL
    );
    """
)
ensure_column("sessions", "speed_factor", "REAL DEFAULT 1.0")
ensure_column("sessions", "speed_mode", "TEXT DEFAULT 'normal'")
ensure_column("sessions", "paused_at", "INTEGER")
ensure_column("session_questions", "section_title", "TEXT")
ensure_column("session_questions", "question_time_override", "INTEGER")


base._FINAL_SUPPORTED_GROUP_COMMANDS = set(getattr(base, "_FINAL_SUPPORTED_GROUP_COMMANDS", set())) | {
    "pauseq",
    "resumeq",
    "skipq",
    "speed",
}


def clean_forwarded_text(text: str) -> str:
    value = base.normalize_visual_text(text or "")
    value = urllib.parse.unquote(value)
    value = COUNTER_RE.sub("", value)
    value = re.sub(r"\bvia\b\s+@?[A-Za-z0-9_]+", " ", value, flags=re.I)
    value = URL_RE.sub(" ", value)
    value = USERNAME_RE.sub(" ", value)
    value = re.sub(r"\s+", " ", value)
    return value.strip(" -–—|•")



def _strip_checkmark(text: str) -> Tuple[str, bool]:
    raw = text or ""
    marked = any(mark in raw for mark in CHECKMARKS)
    for mark in CHECKMARKS:
        raw = raw.replace(mark, "")
    return base.normalize_visual_text(raw), marked



def question_signature(question: str, options: Iterable[str]) -> str:
    merged = " || ".join([clean_forwarded_text(question)] + [clean_forwarded_text(x) for x in options])
    merged = merged.casefold()
    merged = re.sub(r"\s+", " ", merged)
    return merged.strip()



def existing_question_signatures(draft_id: str) -> set[str]:
    seen: set[str] = set()
    for row in base.get_draft_questions(draft_id):
        opts = base.jload(row["options"], []) or []
        seen.add(question_signature(str(row["question"]), [str(x) for x in opts]))
    return seen



def dedup_add_question_to_draft(draft_id: str, question: str, options: List[str], correct_option: int, explanation: str, src: str) -> Tuple[bool, Optional[int]]:
    sig = question_signature(question, options)
    if sig in existing_question_signatures(draft_id):
        return False, None
    q_no = base.add_question_to_draft(draft_id, clean_forwarded_text(question), [clean_forwarded_text(o) for o in options], int(correct_option), clean_forwarded_text(explanation), src)
    return True, q_no



def parse_answer_ref(ref: str, options: List[str]) -> Optional[int]:
    raw = base.normalize_visual_text(ref or "")
    if not raw:
        return None
    raw_up = raw.upper()
    if len(raw_up) == 1 and "A" <= raw_up <= "J":
        idx = ord(raw_up) - ord("A")
        if idx < len(options):
            return idx
    if raw.isdigit():
        idx = int(raw) - 1
        if 0 <= idx < len(options):
            return idx
    for idx, opt in enumerate(options):
        if base.normalize_visual_text(opt).casefold() == raw.casefold():
            return idx
    return None



def parse_marked_questions_from_text(text: str) -> List[Dict[str, Any]]:
    raw = (text or "").replace("\r", "")
    raw = raw.strip()
    if not raw:
        return []

    # JSON array support
    try:
        payload = json.loads(raw)
        if isinstance(payload, list):
            items: List[Dict[str, Any]] = []
            for item in payload:
                if not isinstance(item, dict):
                    continue
                q = clean_forwarded_text(str(item.get("question") or item.get("questions") or ""))
                opts = item.get("options") or []
                if isinstance(opts, dict):
                    opts = list(opts.values())
                opts = [clean_forwarded_text(str(x)) for x in opts if str(x).strip()]
                ans = parse_answer_ref(str(item.get("answer") or item.get("correct") or ""), opts)
                if q and len(opts) >= 2 and ans is not None:
                    items.append({
                        "question": q,
                        "options": opts,
                        "correct_option": ans,
                        "explanation": clean_forwarded_text(str(item.get("explanation") or "")),
                    })
            if items:
                return items
    except Exception:
        pass

    blocks = [b.strip() for b in re.split(r"\n\s*\n+", raw) if b.strip()]
    parsed: List[Dict[str, Any]] = []

    for block in blocks:
        lines = [base.normalize_visual_text(x) for x in block.split("\n") if base.normalize_visual_text(x)]
        if not lines:
            continue
        question_parts: List[str] = []
        options: List[str] = []
        answer_ref: Optional[str] = None
        explanation_parts: List[str] = []
        correct_option: Optional[int] = None

        for idx, line in enumerate(lines):
            ans_m = ANSWER_RE.match(line)
            if ans_m:
                answer_ref = ans_m.group(1).strip()
                continue
            expl_m = EXPL_RE.match(line)
            if expl_m:
                explanation_parts.append(expl_m.group(1).strip())
                continue
            opt_m = OPTION_RE.match(line)
            if opt_m:
                opt_text, marked = _strip_checkmark(opt_m.group(1).strip())
                if opt_text:
                    options.append(opt_text)
                    if marked:
                        correct_option = len(options) - 1
                continue
            if idx == 0 and not options:
                q_line = clean_forwarded_text(QUESTION_PREFIX_RE.sub("", line))
                if q_line:
                    question_parts.append(q_line)
                continue
            if options:
                # treat trailing free text as explanation or option continuation
                if explanation_parts:
                    explanation_parts.append(line)
                elif options:
                    options[-1] = base.normalize_visual_text(f"{options[-1]} {line}")
                continue
            question_parts.append(line)

        question = clean_forwarded_text(" ".join(question_parts))
        if correct_option is None and answer_ref is not None:
            correct_option = parse_answer_ref(answer_ref, options)
        if question and len(options) >= 2 and correct_option is not None:
            parsed.append(
                {
                    "question": question,
                    "options": options,
                    "correct_option": int(correct_option),
                    "explanation": clean_forwarded_text(" ".join(explanation_parts)),
                }
            )

    return parsed



def resolve_editable_draft(user_id: int, raw_code: str) -> Optional[Any]:
    code = base.normalize_visual_text(raw_code or "").upper()
    draft_id = code or (base.get_active_draft_id(user_id) or "")
    if not draft_id:
        return None
    draft = base.get_draft(draft_id)
    if not draft:
        return None
    if int(draft["owner_id"]) != user_id and not getattr(base, "is_all_access_admin", lambda _x: False)(user_id):
        return None
    return draft



def list_sections(draft_id: str) -> List[Any]:
    return base.DBH.fetchall("SELECT * FROM draft_sections WHERE draft_id=? ORDER BY section_no ASC", (draft_id,))



def set_section(draft_id: str, start_q: int, end_q: int, title: str, question_time: Optional[int]) -> None:
    next_no_row = base.DBH.fetchone("SELECT COALESCE(MAX(section_no), 0) AS mx FROM draft_sections WHERE draft_id=?", (draft_id,))
    next_no = int(next_no_row["mx"] if next_no_row else 0) + 1
    base.DBH.execute(
        "INSERT INTO draft_sections(draft_id, section_no, title, start_q, end_q, question_time) VALUES(?,?,?,?,?,?)",
        (draft_id, next_no, base.normalize_visual_text(title), int(start_q), int(end_q), int(question_time) if question_time else None),
    )



def clear_sections(draft_id: str) -> None:
    base.DBH.execute("DELETE FROM draft_sections WHERE draft_id=?", (draft_id,))



def apply_sections_to_session(session_id: str, draft_id: str) -> None:
    for row in list_sections(draft_id):
        base.DBH.execute(
            "UPDATE session_questions SET section_title=?, question_time_override=? WHERE session_id=? AND q_no BETWEEN ? AND ?",
            (
                row["title"],
                row["question_time"],
                session_id,
                int(row["start_q"]),
                int(row["end_q"]),
            ),
        )



def extract_clone_token(text: str) -> Optional[str]:
    raw = urllib.parse.unquote(base.normalize_visual_text(text or ""))
    m = QUIZBOT_TOKEN_RE.search(raw)
    if m:
        return m.group(1)
    m = re.search(r"(?:^|\b)quiz[:=]([A-Za-z0-9_-]{4,})", raw, flags=re.I)
    if m:
        return m.group(1)
    return None



def start_clone_session(user_id: int, draft_id: str, clone_token: str, source_text: str) -> None:
    base.DBH.execute(
        "INSERT OR REPLACE INTO clone_sessions(user_id, draft_id, clone_token, source_text, active, created_at, updated_at) VALUES(?,?,?,?,1,COALESCE((SELECT created_at FROM clone_sessions WHERE user_id=?),?),?)",
        (user_id, draft_id, clone_token, source_text, user_id, base.now_ts(), base.now_ts()),
    )



def get_clone_session(user_id: int) -> Optional[Any]:
    return base.DBH.fetchone("SELECT * FROM clone_sessions WHERE user_id=? AND active=1", (user_id,))



def stop_clone_session(user_id: int) -> None:
    base.DBH.execute("DELETE FROM clone_sessions WHERE user_id=?", (user_id,))



def format_draft_info(draft: Any) -> str:
    q_rows = base.get_draft_questions(draft["id"])
    sections = list_sections(draft["id"])
    lines = [
        f"<b>Draft Info</b>",
        f"Title: <b>{base.html_escape(draft['title'])}</b>",
        f"Code: <code>{draft['id']}</code>",
        f"Owner: <code>{draft['owner_id']}</code>",
        f"Questions: <b>{len(q_rows)}</b>",
        f"Time / question: <b>{draft['question_time']} sec</b>",
        f"Negative / wrong: <b>{draft['negative_mark']}</b>",
        f"Created: <b>{base.fmt_dt(draft['created_at'])}</b>",
        f"Updated: <b>{base.fmt_dt(draft['updated_at'])}</b>",
    ]
    if sections:
        lines.append("")
        lines.append("<b>Sections</b>")
        for row in sections:
            lines.append(
                f"• {base.html_escape(row['title'])} — Q{row['start_q']}-Q{row['end_q']}"
                + (f" — {row['question_time']} sec" if row["question_time"] else "")
            )
    return "\n".join(lines)



def delete_question_numbers(draft_id: str, q_numbers: List[int]) -> int:
    if not q_numbers:
        return 0
    with closing(base.DBH.connect()) as conn:
        removed = 0
        for q_no in sorted(set(int(x) for x in q_numbers), reverse=True):
            cur = conn.execute("DELETE FROM draft_questions WHERE draft_id=? AND q_no=?", (draft_id, q_no))
            removed += int(cur.rowcount or 0)
        rows = conn.execute("SELECT id, q_no FROM draft_questions WHERE draft_id=? ORDER BY q_no ASC", (draft_id,)).fetchall()
        for new_no, row in enumerate(rows, start=1):
            conn.execute("UPDATE draft_questions SET q_no=? WHERE id=?", (new_no, row["id"]))
        conn.commit()
    base.refresh_draft_status(draft_id)
    return removed



def parse_q_number_list(raw: str) -> List[int]:
    out: List[int] = []
    for part in re.split(r"\s*,\s*", raw.strip()):
        if not part:
            continue
        if "-" in part:
            a, b = part.split("-", 1)
            if a.strip().isdigit() and b.strip().isdigit():
                x, y = int(a), int(b)
                if x <= y:
                    out.extend(list(range(x, y + 1)))
            continue
        if part.isdigit():
            out.append(int(part))
    return sorted(set(out))



def shuffle_draft_questions(draft_id: str) -> None:
    rows = [dict(r) for r in base.get_draft_questions(draft_id)]
    if len(rows) < 2:
        return
    random.shuffle(rows)
    with closing(base.DBH.connect()) as conn:
        conn.execute("DELETE FROM draft_questions WHERE draft_id=?", (draft_id,))
        for idx, row in enumerate(rows, start=1):
            conn.execute(
                "INSERT INTO draft_questions(draft_id, q_no, question, options, correct_option, explanation, src) VALUES(?,?,?,?,?,?,?)",
                (
                    draft_id,
                    idx,
                    row["question"],
                    row["options"],
                    row["correct_option"],
                    row["explanation"],
                    row["src"],
                ),
            )
        conn.commit()
    base.refresh_draft_status(draft_id)



def copy_draft(draft_id: str, owner_id: int) -> str:
    draft = base.get_draft(draft_id)
    if not draft:
        raise ValueError("Draft not found")
    new_id = base.create_draft(owner_id, f"{draft['title']} (Copy)", int(draft['question_time']), float(draft['negative_mark']))
    for row in base.get_draft_questions(draft_id):
        base.add_question_to_draft(
            new_id,
            str(row["question"]),
            [str(x) for x in (base.jload(row["options"], []) or [])],
            int(row["correct_option"]),
            str(row["explanation"] or ""),
            str(row["src"] or "copy"),
        )
    for row in list_sections(draft_id):
        set_section(new_id, int(row["start_q"]), int(row["end_q"]), str(row["title"]), int(row["question_time"]) if row["question_time"] else None)
    return new_id


async def import_text_into_draft(message, context, draft_id: str, text: str, src: str = "text") -> None:
    parsed = parse_marked_questions_from_text(text)
    if not parsed:
        await base.safe_reply(
            message,
            "No valid questions were found. Supported format: one question block with options, and the correct option marked with ✅ or an Answer: line.",
        )
        return
    added = 0
    skipped = 0
    for item in parsed:
        ok, _q_no = dedup_add_question_to_draft(
            draft_id,
            item["question"],
            list(item["options"]),
            int(item["correct_option"]),
            str(item.get("explanation") or ""),
            src,
        )
        if ok:
            added += 1
        else:
            skipped += 1
    draft = base.get_draft(draft_id)
    await base.send_draft_card(
        context,
        message.chat.id,
        message.from_user.id,
        draft_id,
        header=f"✅ Text import complete. Added: {added} | Skipped duplicates: {skipped}",
    )
    if draft:
        base.audit(message.from_user.id, "import_text", draft_id, {"added": added, "skipped": skipped})


_previous_create_session_from_draft = base.create_session_from_draft

def create_session_from_draft(draft_id: str, chat_id: int, actor_id: int) -> Optional[str]:
    session_id = _previous_create_session_from_draft(draft_id, chat_id, actor_id)
    if session_id:
        apply_sections_to_session(session_id, draft_id)
        base.DBH.execute(
            "UPDATE sessions SET speed_factor=COALESCE(speed_factor, 1.0), speed_mode=COALESCE(speed_mode, 'normal'), paused_at=NULL WHERE id=?",
            (session_id,),
        )
    return session_id


base.create_session_from_draft = create_session_from_draft


async def begin_or_advance_exam(context, session_id: str) -> None:
    session = base.get_session(session_id)
    if not session or session["status"] != "running":
        return
    next_index = int(session["current_index"] or 0) + 1
    total = int(session["total_questions"] or 0)
    if next_index > total:
        await base.finish_exam(context, session_id, reason="completed")
        return
    q = base.get_session_question(session_id, next_index)
    if not q:
        await base.finish_exam(context, session_id, reason="missing_question")
        return
    options = base.jload(q["options"], []) or []
    section_title = base.normalize_visual_text(q["section_title"] or "")
    base_seconds = int(q["question_time_override"] or session["question_time"] or 30)
    speed_factor = float(session["speed_factor"] or 1.0)
    effective_seconds = max(5, int(round(base_seconds * speed_factor)))

    try:
        prefix_parts = [f"[{next_index}/{total}]"]
        if section_title:
            prefix_parts.append(f"[{section_title}]")
        prefix_parts.append(f"[{base.normalize_visual_text(session['title'])}]")
        question_prefix = " ".join(prefix_parts) + "\n"
        poll_question = (question_prefix + str(q["question"])).strip()
        if len(poll_question) > 300:
            allowed_q = max(10, 300 - len(question_prefix))
            poll_question = question_prefix + str(q["question"])[: allowed_q - 1].rstrip() + "…"
        explanation_text = base.normalize_visual_text(q["explanation"] or f"Question {next_index} of {total}")
        if len(explanation_text) > 200:
            explanation_text = explanation_text[:199] + "…"
        msg = await context.bot.send_poll(
            chat_id=session["chat_id"],
            question=poll_question,
            options=options,
            type=Poll.QUIZ,
            is_anonymous=False,
            allows_multiple_answers=False,
            correct_option_id=int(q["correct_option"]),
            explanation=explanation_text,
            open_period=effective_seconds,
        )
    except TelegramError as exc:
        base.logger.exception("Failed to send poll: %s", exc)
        await base.finish_exam(context, session_id, reason="send_poll_error")
        return

    poll_id = msg.poll.id
    with closing(base.DBH.connect()) as conn:
        conn.execute(
            "UPDATE session_questions SET poll_id=?, message_id=?, open_ts=?, close_ts=? WHERE session_id=? AND q_no=?",
            (poll_id, msg.message_id, base.now_ts(), base.now_ts() + effective_seconds, session_id, next_index),
        )
        conn.execute(
            "UPDATE sessions SET current_index=?, active_poll_id=?, active_poll_message_id=? WHERE id=?",
            (next_index, poll_id, msg.message_id, session_id),
        )
        conn.commit()

    context.job_queue.run_once(
        base.close_poll_job,
        when=max(1, effective_seconds),
        data={"session_id": session_id, "q_no": next_index},
        name=f"close:{session_id}:{next_index}",
    )


base.begin_or_advance_exam = begin_or_advance_exam


async def send_private_results(context, session_id: str) -> None:
    session = base.get_session(session_id)
    if not session:
        return
    chat_row = base.DBH.fetchone("SELECT username FROM known_chats WHERE chat_id=?", (session["chat_id"],))
    username = chat_row["username"] if chat_row else None
    ranking = base.get_session_ranking(session_id)
    rank_map = {int(r["user_id"]): r for r in ranking}
    total_users = max(1, len(ranking))
    qrows = base.DBH.fetchall("SELECT q_no, message_id FROM session_questions WHERE session_id=? ORDER BY q_no", (session_id,))
    q_map = {int(r["q_no"]): r for r in qrows}
    participants = base.DBH.fetchall("SELECT * FROM participants WHERE session_id=? AND eligible=1", (session_id,))
    total_questions = int(session["total_questions"] or 0)

    for p in participants:
        row = base.DBH.fetchone("SELECT started FROM known_users WHERE user_id=?", (p["user_id"],))
        if not row or int(row["started"] or 0) != 1:
            continue
        rank_item = rank_map.get(int(p["user_id"]))
        if not rank_item:
            continue
        if not await base.is_required_channel_member(context, int(p["user_id"])):
            continue
        answers = base.DBH.fetchall("SELECT * FROM answers WHERE session_id=? AND user_id=? ORDER BY q_no", (session_id, p["user_id"]))
        answer_by_q = {int(a["q_no"]): a for a in answers}
        correct_links: List[str] = []
        wrong_links: List[str] = []
        skipped_links: List[str] = []
        for q_no, q in q_map.items():
            link = base.get_message_link(int(session["chat_id"]), int(q["message_id"] or 0), username)
            label = f"<a href=\"{link}\">Q{q_no}</a>" if link else f"Q{q_no}"
            ans = answer_by_q.get(q_no)
            if ans is None:
                skipped_links.append(label)
            elif int(ans["is_correct"]) == 1:
                correct_links.append(label)
            else:
                wrong_links.append(label)
        correct = int(rank_item["correct"])
        wrong = int(rank_item["wrong"])
        attempted = max(1, correct + wrong)
        accuracy = (correct / attempted) * 100.0
        percentage = (correct / max(1, total_questions)) * 100.0
        if total_users <= 1:
            percentile = 100.0
        else:
            percentile = ((total_users - int(rank_item["rank"])) / (total_users - 1)) * 100.0
        text = (
            f"<b>{base.html_escape(session['title'])}</b>\n"
            f"Your rank: <b>#{rank_item['rank']}</b> / {total_users}\n"
            f"✅ Correct: <b>{correct}</b>\n"
            f"❌ Wrong: <b>{wrong}</b>\n"
            f"➖ Skipped: <b>{rank_item['skipped']}</b>\n"
            f"🏁 Final Score: <b>{rank_item['score']}</b>\n\n"
            f"Accuracy: <b>{accuracy:.2f}%</b>\n"
            f"Percentage: <b>{percentage:.2f}%</b>\n"
            f"Percentile: <b>{percentile:.2f}</b>\n\n"
            f"<b>Correct Links</b>\n{', '.join(correct_links) or '—'}\n\n"
            f"<b>Wrong Links</b>\n{', '.join(wrong_links) or '—'}\n\n"
            f"<b>Skipped Links</b>\n{', '.join(skipped_links) or '—'}"
        )
        with suppress(TelegramError):
            await context.bot.send_message(
                chat_id=int(p["user_id"]),
                text=text,
                parse_mode=ParseMode.HTML,
                disable_web_page_preview=True,
            )


base.send_private_results = send_private_results


async def _stop_current_poll_and_jobs(context, session: Any) -> None:
    sid = str(session["id"])
    current_index = int(session["current_index"] or 0)
    close_job_name = f"close:{sid}:{current_index}"
    for job in list(context.job_queue.get_jobs_by_name(close_job_name)):
        job.schedule_removal()
    for job in list(context.job_queue.get_jobs_by_name(f"advance:{sid}")):
        job.schedule_removal()
    for job in list(context.job_queue.jobs()):
        if job.name and str(job.name).startswith(f"advance:{sid}:"):
            job.schedule_removal()
    if session["active_poll_message_id"]:
        with suppress(TelegramError):
            await context.bot.stop_poll(chat_id=session["chat_id"], message_id=int(session["active_poll_message_id"]))
    base.set_session_active_poll(sid, None, None)


async def handle_inline_query(update: Update, context) -> None:
    iq = update.inline_query
    if not iq or not iq.from_user:
        return
    user_id = iq.from_user.id
    if not base.user_has_staff_access(user_id):
        await iq.answer([], cache_time=0, is_personal=True)
        return
    query = base.normalize_visual_text(iq.query or "")
    drafts = base.list_user_drafts(user_id)
    filtered = []
    for row in drafts:
        q_count = int(row.get("q_count", 0) if isinstance(row, dict) else row["q_count"])
        if q_count <= 0:
            continue
        title = str(row["title"])
        code = str(row["id"])
        if not query:
            filtered.append(row)
            continue
        q_lower = query.casefold()
        if q_lower in code.casefold() or q_lower in title.casefold() or q_lower == f"quiz:{code.casefold()}":
            filtered.append(row)
    filtered = filtered[:20]
    bot_username = context.bot_data.get("bot_username", "")
    results: List[InlineQueryResultArticle] = []
    for row in filtered:
        practice = base.ensure_practice_link(str(row["id"]), int(row["owner_id"]))
        practice_url = f"https://t.me/{bot_username}?start=practice_{practice['token']}" if bot_username else ""
        text = (
            f"<b>{base.html_escape(row['title'])}</b>\n"
            f"Quiz ID: <code>{row['id']}</code>\n"
            f"Questions: <b>{row['q_count']}</b>\n"
            f"Time / question: <b>{row['question_time']} sec</b>\n"
            f"Negative / wrong: <b>{row['negative_mark']}</b>"
        )
        if practice_url:
            text += f"\n\nPractice link:\n{practice_url}"
        results.append(
            InlineQueryResultArticle(
                id=str(row["id"]),
                title=f"{row['title']} [{row['id']}]",
                description=f"Q: {row['q_count']} | {row['question_time']}s | -{row['negative_mark']}",
                input_message_content=InputTextMessageContent(text, parse_mode=ParseMode.HTML),
            )
        )
    await iq.answer(results, cache_time=0, is_personal=True)


_prev_build_app = base.build_app

def build_app() -> Application:
    app = _prev_build_app()
    app.add_handler(InlineQueryHandler(handle_inline_query), group=3)
    return app


base.build_app = build_app


def everyone_private_commands() -> List[BotCommand]:
    return [
        BotCommand("start", "Activate bot / open practice links"),
        BotCommand("help", "Help and commands"),
        BotCommand("commands", "Command list"),
        BotCommand("pauseq", "Pause your private practice"),
        BotCommand("resumeq", "Resume your private practice"),
        BotCommand("skipq", "Skip current private question"),
        BotCommand("stoptqex", "Stop active private exam or practice"),
    ]



def admin_private_commands() -> List[BotCommand]:
    return everyone_private_commands() + [
        BotCommand("panel", "Admin panel"),
        BotCommand("newexam", "Create new exam draft"),
        BotCommand("drafts", "My drafts"),
        BotCommand("csvformat", "CSV import format"),
        BotCommand("importtext", "Import MCQs from text / TXT"),
        BotCommand("txtquiz", "Alias of importtext"),
        BotCommand("clonequiz", "Start QuizBot clone workflow"),
        BotCommand("cloneend", "Finish clone workflow"),
        BotCommand("draftinfo", "Show draft details"),
        BotCommand("settitle", "Edit draft title"),
        BotCommand("settime", "Edit time per question"),
        BotCommand("setneg", "Edit negative marking"),
        BotCommand("shuffle", "Shuffle draft questions"),
        BotCommand("delq", "Delete question numbers"),
        BotCommand("section", "Add section timing"),
        BotCommand("sections", "List draft sections"),
        BotCommand("clearsections", "Remove all sections"),
        BotCommand("creator", "Show draft creator info"),
        BotCommand("renamefile", "Rename a file in bot inbox"),
        BotCommand("setthumb", "Set preview thumbnail"),
        BotCommand("clearthumb", "Clear thumbnail"),
        BotCommand("thumbstatus", "Thumbnail status"),
        BotCommand("cancel", "Cancel current input flow"),
    ]



def owner_private_commands() -> List[BotCommand]:
    return admin_private_commands() + [
        BotCommand("addadmin", "Add isolated admin"),
        BotCommand("addadminalp", "Add all-access admin"),
        BotCommand("rmadmin", "Remove admin"),
        BotCommand("admins", "List admin roles"),
        BotCommand("audit", "Recent admin actions"),
        BotCommand("logs", "Bot logs summary"),
        BotCommand("broadcast", "Broadcast to groups and users"),
        BotCommand("announce", "Announce to one chat"),
        BotCommand("restart", "Restart bot"),
    ]



def group_admin_commands() -> List[BotCommand]:
    return [
        BotCommand("binddraft", "Bind a draft to this group"),
        BotCommand("examstatus", "Show current draft and exam state"),
        BotCommand("starttqex", "Show ready button or start selected exam"),
        BotCommand("pauseq", "Pause after the current question"),
        BotCommand("resumeq", "Resume a paused exam"),
        BotCommand("skipq", "Skip the current question"),
        BotCommand("speed", "Change next-question speed"),
        BotCommand("stoptqex", "Stop the running exam"),
        BotCommand("schedule", "Schedule the active or bound draft"),
        BotCommand("listschedules", "List scheduled exams"),
        BotCommand("cancelschedule", "Cancel a schedule"),
    ]



def build_commands_text(chat_type: str, is_admin_user: bool, is_owner_user: bool) -> str:
    lines: List[str] = [
        "<b>Command List</b>",
        "All commands work with both <b>/</b> and <b>.</b> prefixes.",
        "",
    ]
    if chat_type == "private":
        lines.extend([
            "<b>Everyone</b>",
            "• /start — activate the bot / open practice links / receive DM results",
            "• /start practice_TOKEN — open a generated practice exam",
            "• /pauseq — pause your private practice after the current question",
            "• /resumeq — resume a paused private practice",
            "• /skipq — skip the current private question",
            "• /stoptqex — stop your current private practice or exam",
            "• /help or /commands — command list",
        ])
        if is_admin_user:
            lines.extend([
                "",
                "<b>Admin / Owner (Private)</b>",
                "• /panel — open the admin panel",
                "• /newexam — create a new exam draft",
                "• /drafts or /mydrafts — list drafts",
                "• /importtext or /txtquiz — import questions from pasted text or a TXT file",
                "• /clonequiz — create a new draft for forwarded @QuizBot quiz polls",
                "• /cloneend — finish the current clone workflow",
                "• /draftinfo [CODE] — show full draft details",
                "• /settitle CODE | New Title — change draft title",
                "• /settime CODE 30 — change default time per question",
                "• /setneg CODE 0.25 — change negative marking",
                "• /shuffle CODE — shuffle draft questions",
                "• /delq CODE 3,5-7 — delete question numbers",
                "• /section CODE 1-10 | Biology | 30 — add a timed section",
                "• /sections CODE — list draft sections",
                "• /clearsections CODE — remove all sections from a draft",
                "• /creator CODE — show quiz creator info",
                "• /csvformat — CSV import format",
                "• /renamefile — rename a file in bot inbox and resend it",
                "• /setthumb — set a custom preview thumbnail",
                "• /clearthumb — remove the custom thumbnail",
                "• /thumbstatus — show current thumbnail status",
                "• inline query: type <code>@YourBotName quiz:CODE</code> after enabling inline mode in BotFather",
                "• /cancel — cancel the current input flow",
            ])
        if is_owner_user:
            lines.extend([
                "",
                "<b>Owner Only</b>",
                "• /addadmin USER_ID — add an isolated admin",
                "• /addadminalp USER_ID — add an all-access admin",
                "• /rmadmin USER_ID — remove an admin",
                "• /admins — list admin roles",
                "• /audit — recent admin actions",
                "• /logs — memory, uptime, and recent errors",
                "• /broadcast [pin] — broadcast to groups and users",
                "• /announce CHAT_ID [pin] — announce to one chat",
                "• /restart — restart the bot process",
            ])
    else:
        lines.extend([
            "<b>Group Admin / Bot Admin</b>",
            "• /binddraft CODE — bind a draft to this group",
            "• /examstatus — show the current binding and exam status",
            "• /starttqex [DRAFTCODE] — show the ready button or start a selected exam",
            "• /pauseq — pause after the current question",
            "• /resumeq — resume a paused exam",
            "• /skipq — skip the current question",
            "• /speed slow|normal|fast — apply a new speed from the next question",
            "• /stoptqex — stop the running exam",
            "• /schedule YYYY-MM-DD HH:MM — schedule the active or bound draft",
            "• /listschedules — list scheduled exams for this group",
            "• /cancelschedule SCHEDULE_ID — cancel a schedule",
        ])
    return "\n".join(lines)


base.everyone_private_commands = everyone_private_commands
base.admin_private_commands = admin_private_commands
base.owner_private_commands = owner_private_commands
base.group_admin_commands = group_admin_commands
base.build_commands_text = build_commands_text


_prev_handle_document_upload = base.handle_document_upload


async def handle_document_upload(update: Update, context) -> None:
    message = update.effective_message
    user = update.effective_user
    chat = update.effective_chat
    if message and user and chat and message.document and chat.type == "private" and base.user_has_staff_access(user.id):
        state, payload = base.get_user_state(user.id)
        lower_name = (message.document.file_name or "").lower()
        if state == "adv_await_import_text" and lower_name.endswith((".txt", ".md", ".json")):
            file = await message.document.get_file()
            data = bytes(await file.download_as_bytearray())
            clear_text = data.decode("utf-8-sig", errors="replace")
            draft_id = str(payload.get("draft_id") or "")
            base.clear_user_state(user.id)
            if not draft_id:
                await base.safe_reply(message, "No draft is selected for text import.")
                return
            await import_text_into_draft(message, context, draft_id, clear_text, src=f"txt:{message.document.file_name or 'upload.txt'}")
            return
    return await _prev_handle_document_upload(update, context)


base.handle_document_upload = handle_document_upload


_prev_handle_poll_import = base.handle_poll_import


async def handle_poll_import(update: Update, context) -> None:
    message = update.effective_message
    user = update.effective_user
    chat = update.effective_chat
    if not message or not user or not chat or not message.poll:
        return await _prev_handle_poll_import(update, context)
    if chat.type == "private" and base.is_bot_admin(user.id):
        clone = get_clone_session(user.id)
        draft_id = str(clone["draft_id"]) if clone else (base.get_active_draft_id(user.id) or "")
        if draft_id and message.poll.type == Poll.QUIZ and message.poll.correct_option_id is not None:
            cleaned_question = clean_forwarded_text(message.poll.question)
            cleaned_options = [clean_forwarded_text(opt.text) for opt in message.poll.options]
            cleaned_expl = clean_forwarded_text(message.poll.explanation or "")
            ok, q_no = dedup_add_question_to_draft(
                draft_id,
                cleaned_question,
                cleaned_options,
                int(message.poll.correct_option_id),
                cleaned_expl,
                "quizbot_clone" if clone else "forwarded_quiz",
            )
            if ok:
                header = f"✅ {'Clone' if clone else 'Draft'} updated. Added question Q{q_no}"
            else:
                header = "ℹ️ Duplicate question skipped."
            await base.send_draft_card(context, user.id, user.id, draft_id, header=header)
            base.audit(user.id, "clone_import" if clone else "add_quiz_question", draft_id, {"added": bool(ok), "q_no": q_no})
            return
    return await _prev_handle_poll_import(update, context)


base.handle_poll_import = handle_poll_import


_prev_handle_text = base.handle_text


async def handle_text(update: Update, context) -> None:
    message = update.effective_message
    user = update.effective_user
    chat = update.effective_chat
    if not message or not user or not chat or not getattr(message, "text", None):
        return await _prev_handle_text(update, context)

    state, payload = base.get_user_state(user.id)
    cmd, args = base.extract_command(message.text, context.bot_data.get("bot_username", ""))
    cmd = (cmd or "").lower()

    if chat.type == "private" and state == "adv_await_import_text" and not cmd:
        draft_id = str(payload.get("draft_id") or "")
        base.clear_user_state(user.id)
        if not draft_id:
            await base.safe_reply(message, "No draft is selected for this text import.")
            return
        await import_text_into_draft(message, context, draft_id, message.text, src="pasted_text")
        return

    if chat.type == "private" and state == "adv_await_clone_source" and not cmd:
        token = extract_clone_token(message.text)
        if not token:
            await base.safe_reply(message, "Send a valid @QuizBot inline text like <code>@QuizBot quiz:ABCDE</code> or a message that contains <code>quiz:ABCDE</code>.", parse_mode=ParseMode.HTML)
            return
        title = str(payload.get("title") or f"QuizBot Clone {token}")
        draft_id = base.create_draft(user.id, title, 30, 0.0)
        start_clone_session(user.id, draft_id, token, message.text)
        base.clear_user_state(user.id)
        await base.send_draft_card(
            context,
            user.id,
            user.id,
            draft_id,
            header=(
                "✅ Clone draft created.\n"
                "Now forward the quiz polls from @QuizBot to this bot inbox. Each forwarded quiz poll will be cleaned and added automatically.\n"
                "Use /cloneend when finished."
            ),
        )
        return

    if chat.type == "private" and base.user_has_staff_access(user.id):
        if cmd in {"importtext", "txtquiz"}:
            draft = resolve_editable_draft(user.id, args.strip())
            if not draft:
                await base.safe_reply(message, "Select an active draft first, or pass the draft code: /importtext DRAFTCODE")
                return
            base.set_user_state(user.id, "adv_await_import_text", {"draft_id": draft["id"]})
            await base.safe_reply(
                message,
                "Send the MCQ text now, or upload a .txt/.md/.json file.\n\nSupported format example:\n\n1. What is the capital of France?\nA. Berlin\nB. Madrid\nC. Paris ✅\nD. Rome\nExplanation: Paris is the capital.",
            )
            return

        if cmd == "clonequiz":
            raw = args.strip()
            if raw:
                if "|" in raw:
                    title_part, source_part = [x.strip() for x in raw.split("|", 1)]
                else:
                    title_part, source_part = "", raw
                token = extract_clone_token(source_part)
                if token:
                    draft_id = base.create_draft(user.id, title_part or f"QuizBot Clone {token}", 30, 0.0)
                    start_clone_session(user.id, draft_id, token, source_part)
                    await base.send_draft_card(
                        context,
                        user.id,
                        user.id,
                        draft_id,
                        header=(
                            "✅ Clone draft created.\n"
                            "Forward the quiz polls from @QuizBot to this bot inbox. Each forwarded quiz poll will be cleaned and added automatically.\n"
                            "Use /cloneend when finished."
                        ),
                    )
                    return
            base.set_user_state(user.id, "adv_await_clone_source", {"title": ""})
            await base.safe_reply(
                message,
                "Send the @QuizBot inline text or any message that contains <code>quiz:YOUR_ID</code>.\n\nNote: Telegram Bot API cannot directly fetch another bot's inline quiz payload by only reading the pasted token. This build uses a guided clone workflow: it creates a draft, then imports the forwarded quiz polls automatically.",
                parse_mode=ParseMode.HTML,
            )
            return

        if cmd == "cloneend":
            clone = get_clone_session(user.id)
            if not clone:
                await base.safe_reply(message, "There is no active clone session.")
                return
            stop_clone_session(user.id)
            await base.send_draft_card(context, user.id, user.id, clone["draft_id"], header="✅ Clone session finished.")
            return

        if cmd == "draftinfo":
            draft = resolve_editable_draft(user.id, args.strip())
            if not draft:
                await base.safe_reply(message, "Draft not found, or you do not have access.")
                return
            await base.safe_reply(message, format_draft_info(draft), parse_mode=ParseMode.HTML)
            return

        if cmd == "creator":
            code = base.normalize_visual_text(args).upper()
            if not code:
                await base.safe_reply(message, "Usage: /creator DRAFTCODE")
                return
            draft = base.get_draft(code)
            if not draft:
                await base.safe_reply(message, "Draft not found.")
                return
            q_count_row = base.DBH.fetchone("SELECT COUNT(*) AS c FROM draft_questions WHERE draft_id=?", (code,))
            role = "owner" if base.is_owner(int(draft["owner_id"])) else ("all-access admin" if getattr(base, "is_all_access_admin", lambda _x: False)(int(draft["owner_id"])) else "admin")
            text = (
                f"<b>Creator Info</b>\n"
                f"Draft: <b>{base.html_escape(draft['title'])}</b>\n"
                f"Code: <code>{draft['id']}</code>\n"
                f"Creator ID: <code>{draft['owner_id']}</code>\n"
                f"Role: <b>{role}</b>\n"
                f"Questions: <b>{int(q_count_row['c'] if q_count_row else 0)}</b>\n"
                f"Created: <b>{base.fmt_dt(draft['created_at'])}</b>\n"
                f"Updated: <b>{base.fmt_dt(draft['updated_at'])}</b>"
            )
            await base.safe_reply(message, text, parse_mode=ParseMode.HTML)
            return

        if cmd == "settitle":
            if "|" not in args:
                await base.safe_reply(message, "Usage: /settitle DRAFTCODE | New Title")
                return
            code_part, title_part = [x.strip() for x in args.split("|", 1)]
            draft = resolve_editable_draft(user.id, code_part)
            if not draft or not title_part:
                await base.safe_reply(message, "Draft not found or title is empty.")
                return
            base.DBH.execute("UPDATE drafts SET title=?, updated_at=? WHERE id=?", (base.normalize_visual_text(title_part), base.now_ts(), draft["id"]))
            await base.send_draft_card(context, user.id, user.id, draft["id"], header="✅ Draft title updated.")
            return

        if cmd == "settime":
            parts = args.split()
            if len(parts) < 2 or not parts[-1].isdigit():
                await base.safe_reply(message, "Usage: /settime DRAFTCODE 30")
                return
            draft = resolve_editable_draft(user.id, " ".join(parts[:-1]))
            if not draft:
                await base.safe_reply(message, "Draft not found, or you do not have access.")
                return
            secs = max(5, int(parts[-1]))
            base.DBH.execute("UPDATE drafts SET question_time=?, updated_at=? WHERE id=?", (secs, base.now_ts(), draft["id"]))
            await base.send_draft_card(context, user.id, user.id, draft["id"], header=f"✅ Default time updated to {secs} sec.")
            return

        if cmd == "setneg":
            parts = args.split()
            if len(parts) < 2:
                await base.safe_reply(message, "Usage: /setneg DRAFTCODE 0.25")
                return
            try:
                neg = float(parts[-1])
            except ValueError:
                await base.safe_reply(message, "Send a valid decimal value. Example: 0.25")
                return
            draft = resolve_editable_draft(user.id, " ".join(parts[:-1]))
            if not draft:
                await base.safe_reply(message, "Draft not found, or you do not have access.")
                return
            base.DBH.execute("UPDATE drafts SET negative_mark=?, updated_at=? WHERE id=?", (neg, base.now_ts(), draft["id"]))
            await base.send_draft_card(context, user.id, user.id, draft["id"], header=f"✅ Negative mark updated to {neg}.")
            return

        if cmd == "shuffle":
            draft = resolve_editable_draft(user.id, args.strip())
            if not draft:
                await base.safe_reply(message, "Draft not found, or you do not have access.")
                return
            shuffle_draft_questions(draft["id"])
            await base.send_draft_card(context, user.id, user.id, draft["id"], header="✅ Draft questions shuffled.")
            return

        if cmd == "delq":
            parts = args.split(maxsplit=1)
            if len(parts) != 2:
                await base.safe_reply(message, "Usage: /delq DRAFTCODE 3,5-7")
                return
            draft = resolve_editable_draft(user.id, parts[0])
            if not draft:
                await base.safe_reply(message, "Draft not found, or you do not have access.")
                return
            numbers = parse_q_number_list(parts[1])
            removed = delete_question_numbers(draft["id"], numbers)
            await base.send_draft_card(context, user.id, user.id, draft["id"], header=f"✅ Removed {removed} question(s).")
            return

        if cmd == "section":
            if "|" not in args:
                await base.safe_reply(message, "Usage: /section DRAFTCODE 1-10 | Biology | 30")
                return
            left, title, time_part = [x.strip() for x in args.split("|", 2)] if args.count("|") >= 2 else [x.strip() for x in args.split("|", 1)] + [""]
            bits = left.split()
            if len(bits) < 2:
                await base.safe_reply(message, "Usage: /section DRAFTCODE 1-10 | Biology | 30")
                return
            draft = resolve_editable_draft(user.id, bits[0])
            if not draft:
                await base.safe_reply(message, "Draft not found, or you do not have access.")
                return
            rng = bits[1]
            if "-" not in rng:
                await base.safe_reply(message, "Use a question range like 1-10.")
                return
            a, b = rng.split("-", 1)
            if not (a.strip().isdigit() and b.strip().isdigit()):
                await base.safe_reply(message, "Use numeric question ranges like 1-10.")
                return
            q_time = int(time_part) if time_part.strip().isdigit() else None
            set_section(draft["id"], int(a), int(b), title or f"Section {a}-{b}", q_time)
            await base.safe_reply(message, f"✅ Section added to <code>{draft['id']}</code>.", parse_mode=ParseMode.HTML)
            return

        if cmd == "sections":
            draft = resolve_editable_draft(user.id, args.strip())
            if not draft:
                await base.safe_reply(message, "Draft not found, or you do not have access.")
                return
            rows = list_sections(draft["id"])
            if not rows:
                await base.safe_reply(message, "No sections are configured for this draft.")
                return
            lines = [f"<b>Sections for {base.html_escape(draft['title'])}</b>"]
            for row in rows:
                lines.append(
                    f"• {base.html_escape(row['title'])} — Q{row['start_q']}-Q{row['end_q']}" + (f" — {row['question_time']} sec" if row['question_time'] else "")
                )
            await base.safe_reply(message, "\n".join(lines), parse_mode=ParseMode.HTML)
            return

        if cmd == "clearsections":
            draft = resolve_editable_draft(user.id, args.strip())
            if not draft:
                await base.safe_reply(message, "Draft not found, or you do not have access.")
                return
            clear_sections(draft["id"])
            await base.safe_reply(message, f"✅ All sections removed from <code>{draft['id']}</code>.", parse_mode=ParseMode.HTML)
            return

    # Everyone can control their own private practice.
    if chat.type == "private" and cmd in {"pauseq", "resumeq", "skipq"}:
        session = base.get_active_session(user.id)
        if cmd == "resumeq":
            paused = base.DBH.fetchone("SELECT * FROM sessions WHERE chat_id=? AND status='paused' ORDER BY started_at DESC LIMIT 1", (user.id,))
            if not paused:
                await base.safe_reply(message, "There is no paused private practice.")
                return
            base.DBH.execute("UPDATE sessions SET status='running', paused_at=NULL WHERE id=?", (paused["id"],))
            context.job_queue.run_once(base.begin_or_advance_exam_job, when=0.4, data={"session_id": paused["id"]}, name=f"advance:{paused['id']}:resume")
            await base.safe_reply(message, "▶️ Private practice resumed.")
            return
        if not session:
            await base.safe_reply(message, "There is no active private practice right now.")
            return
        if cmd == "pauseq":
            await _stop_current_poll_and_jobs(context, session)
            base.DBH.execute("UPDATE sessions SET status='paused', paused_at=? WHERE id=?", (base.now_ts(), session["id"]))
            await base.safe_reply(message, "⏸ Private practice paused. Use /resumeq to continue.")
            return
        if cmd == "skipq":
            await _stop_current_poll_and_jobs(context, session)
            context.job_queue.run_once(base.begin_or_advance_exam_job, when=0.4, data={"session_id": session["id"]}, name=f"advance:{session['id']}:skip")
            await base.safe_reply(message, "⏭ Current question skipped.")
            return

    if chat.type in {"group", "supergroup"} and cmd in {"pauseq", "resumeq", "skipq", "speed"}:
        if not await base.is_group_admin_or_global(update, context):
            return await base.handle_group_denied_command(update, context)
        if cmd == "resumeq":
            paused = base.DBH.fetchone("SELECT * FROM sessions WHERE chat_id=? AND status='paused' ORDER BY started_at DESC LIMIT 1", (chat.id,))
            if not paused:
                await base.safe_reply(message, "There is no paused exam in this group.")
                return
            base.DBH.execute("UPDATE sessions SET status='running', paused_at=NULL WHERE id=?", (paused["id"],))
            context.job_queue.run_once(base.begin_or_advance_exam_job, when=0.6, data={"session_id": paused["id"]}, name=f"advance:{paused['id']}:resume")
            await base.safe_reply(message, "▶️ Exam resumed. The next question is coming now.")
            return

        session = base.get_active_session(chat.id)
        if not session:
            await base.safe_reply(message, "There is no active exam in this group.")
            return

        if cmd == "pauseq":
            await _stop_current_poll_and_jobs(context, session)
            base.DBH.execute("UPDATE sessions SET status='paused', paused_at=? WHERE id=?", (base.now_ts(), session["id"]))
            await base.safe_reply(message, "⏸ Exam paused. Use /resumeq to continue.")
            return

        if cmd == "skipq":
            await _stop_current_poll_and_jobs(context, session)
            context.job_queue.run_once(base.begin_or_advance_exam_job, when=0.6, data={"session_id": session["id"]}, name=f"advance:{session['id']}:skip")
            await base.safe_reply(message, "⏭ Current question skipped.")
            return

        if cmd == "speed":
            mode = base.normalize_visual_text(args).lower()
            if mode not in SPEED_PRESETS:
                await base.safe_reply(message, "Usage: /speed slow|normal|fast")
                return
            factor, mode_name = SPEED_PRESETS[mode]
            base.DBH.execute("UPDATE sessions SET speed_factor=?, speed_mode=? WHERE id=?", (factor, mode_name, session["id"]))
            await base.safe_reply(message, f"⚙️ Speed set to <b>{mode_name}</b>. It will apply from the next question.", parse_mode=ParseMode.HTML)
            return

    return await _prev_handle_text(update, context)


base.handle_text = handle_text


_prev_send_admin_pdf_report = base.send_admin_pdf_report


async def send_admin_pdf_report(context, session_id: str, ranking: List[Dict[str, Any]]) -> None:
    session = base.get_session(session_id)
    if not session:
        return
    rows = base.DBH.fetchall("SELECT score FROM participants WHERE session_id=? AND eligible=1", (session_id,))
    scores = [float(r["score"]) for r in rows] or [0.0]
    creator_id = int(session["created_by"])
    if hasattr(base, 'get_user_theme'):
        _name, theme, _custom = base.get_user_theme(creator_id)
    else:
        theme = getattr(base, 'BUILTIN_THEMES', {'midnight': {'bg':'#03101F','text':'#EAF2FF','muted':'#B9C7DD','table':'#07162D','card1':'#132744','card2':'#0E2037','subtext':'#C8D8F4','accent':'#D7F7CC','footer':'#95A0B4','outline':'#18324B'}})['midnight']
    summary = {
        "participants": len(ranking),
        "questions": int(session["total_questions"]),
        "average_score": base.fmt_score(sum(scores) / len(scores)),
        "highest_score": base.fmt_score(max(scores)),
        "lowest_score": base.fmt_score(min(scores)),
        "negative_mark": session["negative_mark"],
        "started_at": base.fmt_dt(session["started_at"]),
        "ended_at": base.fmt_dt(session["ended_at"]),
    }
    compact = []
    for r in ranking:
        name = r["name"]
        if r.get("sub_name"):
            name = f"{name} {r['sub_name']}"
        compact.append({**r, "name": name, "sub_name": "", "time": r.get("time_label", "0s")})
    pdf_bytes = await asyncio.to_thread(base.render_report_pdf, session["title"], summary, compact, theme)
    html_doc = base._report_html(base.normalize_visual_text(session["title"]), summary, compact, theme) if hasattr(base, '_report_html') else None
    thumb_bytes = base.get_report_thumbnail_bytes(creator_id, session["title"]) if hasattr(base, 'get_report_thumbnail_bytes') else None
    recipients: List[int] = []
    for uid in [creator_id] + list(base.CONFIG.owner_ids) + base.all_admin_ids():
        if uid not in recipients:
            recipients.append(uid)
    for uid in recipients:
        try:
            kwargs = {}
            if thumb_bytes:
                kwargs['thumbnail'] = InputFile(base.io.BytesIO(thumb_bytes), filename='report_preview.jpg')
            await context.bot.send_document(
                uid,
                document=InputFile(base.io.BytesIO(pdf_bytes), filename=f"{base.pdf_safe_filename(session['title'])}_report.pdf"),
                caption=f"📄 {base.normalize_visual_text(session['title'])} analysis report",
                **kwargs,
            )
            if html_doc:
                await context.bot.send_document(
                    uid,
                    document=InputFile(base.io.BytesIO(html_doc.encode('utf-8')), filename=f"{base.pdf_safe_filename(session['title'])}_report.html"),
                    caption='HTML report (light/dark capable in browser).',
                )
        except TelegramError as exc:
            base.logger.warning("Could not send report files to %s: %s", uid, exc)


base.send_admin_pdf_report = send_admin_pdf_report



# ============================================================
# Final polish patch: draft browser, result card, prefix toggle, cleaner clone flow
# ============================================================

ensure_column("drafts", "show_title_prefix", "INTEGER DEFAULT 1")
base.DBH.execute("UPDATE drafts SET show_title_prefix=1 WHERE show_title_prefix IS NULL")

DRAFT_BROWSER_PAGE_SIZE = 4


def clean_forwarded_text(text: str) -> str:
    value = base.normalize_visual_text(text or "")
    value = urllib.parse.unquote(value)
    value = COUNTER_RE.sub("", value)
    value = re.sub(r"/(?:view|start)_[A-Za-z0-9_]+(?:_[0-9]+)?", " ", value, flags=re.I)
    value = re.sub(r"^\s*(?:🎲|🎯|📘)?\s*Quiz\s*['\"“”‘’].*?['\"“”‘’]\s*", "", value, flags=re.I)
    value = re.sub(r"^\s*(?:\[[^\[\]]{1,80}\]\s*)+", "", value)
    value = re.sub(r"(?:\s*\[[^\[\]]{1,80}\])+$", "", value)
    value = re.sub(r"\bvia\b\s+@?[A-Za-z0-9_]+", " ", value, flags=re.I)
    value = URL_RE.sub(" ", value)
    value = USERNAME_RE.sub(" ", value)
    value = re.sub(r"^\s*\d+[\).:-]?\s*", "", value)
    value = re.sub(r"\s+", " ", value)
    return value.strip(" -–—|•")


def extract_clone_token(text: str) -> Optional[str]:
    raw = urllib.parse.unquote(base.normalize_visual_text(text or ""))
    raw = raw.replace("@QuizBot", "@quizbot")
    patterns = [
        r"(?:https?://)?t\.me/QuizBot\?start=([A-Za-z0-9_-]{4,})",
        r"(?:https?://)?telegram\.me/QuizBot\?start=([A-Za-z0-9_-]{4,})",
        r"(?:^|\b)start=([A-Za-z0-9_-]{4,})",
        r"(?:@quizbot\s+)?quiz\s*:\s*([A-Za-z0-9_-]{4,})",
        r"(?:^|\b)quiz[:=]([A-Za-z0-9_-]{4,})",
    ]
    for pat in patterns:
        m = re.search(pat, raw, flags=re.I)
        if m:
            return m.group(1)
    return None


def _ordinal(n: int) -> str:
    n = int(max(1, n))
    if 10 <= (n % 100) <= 20:
        suffix = 'th'
    else:
        suffix = {1: 'st', 2: 'nd', 3: 'rd'}.get(n % 10, 'th')
    return f"{n}{suffix}"


def _visible_drafts_for_user(user_id: int) -> List[Any]:
    drafts = list(base.list_user_drafts(user_id))
    if getattr(base, 'is_all_access_admin', lambda _x: False)(user_id) or base.is_owner(user_id):
        extra = [r for r in base.list_ready_drafts() if r['id'] not in {d['id'] for d in drafts}]
        drafts.extend(extra)
        drafts.sort(key=lambda r: int(r['updated_at']), reverse=True)
    return drafts


def _clamp_browser_page(page: int, total: int, size: int = DRAFT_BROWSER_PAGE_SIZE) -> int:
    if total <= 0:
        return 0
    max_page = max(0, (total - 1) // max(1, size))
    return max(0, min(int(page), max_page))


def _section_summary_for_draft(draft_id: str) -> List[str]:
    rows = list_sections(draft_id)
    if not rows:
        return ["No sections configured."]
    out = []
    for row in rows:
        bit = f"• {base.html_escape(row['title'])} — Q{row['start_q']}-Q{row['end_q']}"
        if row['question_time']:
            bit += f" — {row['question_time']} sec"
        out.append(bit)
    return out


async def send_draft_card(context, chat_id: int, user_id: int, draft_id: str, header: str = "") -> None:
    draft = base.get_draft(draft_id)
    if not draft:
        await context.bot.send_message(chat_id, 'This draft no longer exists.')
        return
    q_rows = base.get_draft_questions(draft_id)
    count = len(q_rows)
    bot_username = context.bot_data.get('bot_username', '')
    practice_url = base._build_practice_url(bot_username, draft_id, int(draft['owner_id'])) if count > 0 and hasattr(base, '_build_practice_url') else None
    practice = base.ensure_practice_link(draft_id, int(draft['owner_id'])) if practice_url else None
    title_prefix = 'ON' if int(draft['show_title_prefix'] or 1) else 'OFF'
    lines = []
    if header:
        lines.extend([header, ""])
    lines.extend([
        "<b>Draft Ready</b>",
        f"Title: <b>{base.html_escape(base.normalize_visual_text(draft['title']))}</b>",
        f"Code: <code>{draft['id']}</code>",
        f"Questions: <b>{count}</b>",
        f"Time / question: <b>{draft['question_time']} sec</b>",
        f"Negative / wrong: <b>{draft['negative_mark']}</b>",
        f"Title prefix in poll: <b>{title_prefix}</b>",
        f"Status: <b>{'Ready' if count else 'Draft'}</b>",
    ])
    if practice_url and practice:
        max_attempts = int(practice['max_attempts'])
        lines.extend([
            "",
            "<b>Practice Link</b>",
            f"<a href=\"{practice_url}\">Open practice in bot inbox</a>",
            f"Attempts per user: <b>{'Unlimited' if max_attempts <= 0 else max_attempts}</b>",
        ])
    text = "\n".join(lines)
    kb_rows = [
        [
            InlineKeyboardButton('📂 Open Draft', callback_data=f'ap:view:{draft_id}:0'),
            InlineKeyboardButton('🔄 Set Active', callback_data=f'ap:set:{draft_id}:0'),
        ],
        [
            InlineKeyboardButton('⚙️ Toggle Title Prefix', callback_data=f'ap:prefix:{draft_id}:0'),
            InlineKeyboardButton('🎲 Shuffle', callback_data=f'ap:shuffle:{draft_id}:0'),
        ],
        [InlineKeyboardButton('📚 Draft Browser', callback_data='panel:drafts')],
    ]
    if practice_url:
        kb_rows.insert(2, [InlineKeyboardButton('🧪 Practice Link', url=practice_url)])
    kb = InlineKeyboardMarkup(kb_rows)
    if hasattr(base, '_drop_home_panel_if_present'):
        await base._drop_home_panel_if_present(context, user_id)
    if hasattr(base, '_replace_single_panel_message'):
        await base._replace_single_panel_message(context, chat_id, ('draft-card', user_id), text, kb)
    else:
        await context.bot.send_message(chat_id, text, parse_mode=ParseMode.HTML, reply_markup=kb, disable_web_page_preview=True)


base.send_draft_card = send_draft_card


def _build_draft_browser_list_text_markup(user_id: int, page: int = 0, header: str = "") -> Tuple[str, InlineKeyboardMarkup]:
    drafts = _visible_drafts_for_user(user_id)
    if not drafts:
        text = ((f"{header}\n\n" if header else "") +
                "<b>Your Drafts</b>\n\n"
                "You do not have any visible drafts yet.\n"
                "Create a new exam to get started.")
        return text, InlineKeyboardMarkup([[InlineKeyboardButton('⬅️ Back', callback_data='panel:home')]])

    page = _clamp_browser_page(page, len(drafts))
    total_pages = max(1, (len(drafts) + DRAFT_BROWSER_PAGE_SIZE - 1) // DRAFT_BROWSER_PAGE_SIZE)
    start = page * DRAFT_BROWSER_PAGE_SIZE
    rows = drafts[start:start + DRAFT_BROWSER_PAGE_SIZE]
    active_id = base.get_active_draft_id(user_id)

    lines: List[str] = []
    if header:
        lines.extend([header, ""])
    lines.append("<b>Draft Browser</b>")
    lines.append(f"Page <b>{page + 1}/{total_pages}</b> • Showing <b>{start + 1}-{start + len(rows)}</b> of <b>{len(drafts)}</b>")
    lines.append("")
    for idx, row in enumerate(rows, start=start + 1):
        flags = []
        if int(row['q_count'] or 0) > 0:
            flags.append('Ready')
        else:
            flags.append('Draft')
        if row['id'] == active_id:
            flags.append('ACTIVE')
        if int(row['owner_id']) != user_id:
            flags.append(f"Owner {row['owner_id']}")
        lines.append(f"<b>{idx}. {base.html_escape(base.normalize_visual_text(row['title']))}</b>")
        lines.append(f"Code: <code>{row['id']}</code>")
        lines.append(f"Questions: <b>{row['q_count']}</b>    Time: <b>{row['question_time']} sec</b>")
        lines.append(f"Negative: <b>{row['negative_mark']}</b>    Prefix: <b>{'ON' if int(row['show_title_prefix'] or 1) else 'OFF'}</b>")
        lines.append(f"Status: <b>{' • '.join(flags)}</b>")
        lines.append("")

    kb_rows: List[List[InlineKeyboardButton]] = []
    for row in rows:
        kb_rows.append([
            InlineKeyboardButton(f"📂 {row['id']}", callback_data=f"ap:view:{row['id']}:{page}"),
            InlineKeyboardButton('✅ Active' if row['id'] == active_id else '🔄 Set Active', callback_data=f"ap:set:{row['id']}:{page}"),
        ])
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton('⬅️ Previous', callback_data=f'ap:page:{page - 1}'))
    if page < total_pages - 1:
        nav.append(InlineKeyboardButton('➡️ Next', callback_data=f'ap:page:{page + 1}'))
    if nav:
        kb_rows.append(nav)
    kb_rows.append([InlineKeyboardButton('⬅️ Back', callback_data='panel:home')])
    return "\n".join(lines).strip(), InlineKeyboardMarkup(kb_rows)


def _build_draft_detail_text_markup(user_id: int, draft_id: str, page: int = 0, header: str = "") -> Tuple[str, InlineKeyboardMarkup]:
    draft = base.get_draft(draft_id)
    if not draft:
        return _build_draft_browser_list_text_markup(user_id, page=page, header='⚠️ Draft not found.')
    if int(draft['owner_id']) != user_id and not getattr(base, 'is_all_access_admin', lambda _x: False)(user_id) and not base.is_owner(user_id):
        return _build_draft_browser_list_text_markup(user_id, page=page, header='⚠️ You do not have access to this draft.')
    q_rows = base.get_draft_questions(draft_id)
    bot_username = getattr(base, '_build_practice_url', None)
    practice_url = base._build_practice_url(context_bot_username if False else '', draft_id, int(draft['owner_id'])) if False else None
    sections_text = _section_summary_for_draft(draft_id)
    title_prefix = 'ON' if int(draft['show_title_prefix'] or 1) else 'OFF'
    lines = []
    if header:
        lines.extend([header, ""])
    lines.extend([
        "<b>Draft Details</b>",
        f"Title: <b>{base.html_escape(base.normalize_visual_text(draft['title']))}</b>",
        f"Code: <code>{draft['id']}</code>",
        f"Questions: <b>{len(q_rows)}</b>",
        f"Time / question: <b>{draft['question_time']} sec</b>",
        f"Negative / wrong: <b>{draft['negative_mark']}</b>",
        f"Title prefix in poll: <b>{title_prefix}</b>",
        f"Created: <b>{base.fmt_dt(draft['created_at'])}</b>",
        f"Updated: <b>{base.fmt_dt(draft['updated_at'])}</b>",
        "",
        "<b>Sections</b>",
        *sections_text,
    ])
    bot_username = getattr(base, '_cached_bot_username_for_browser', '')
    practice_url = base._build_practice_url(bot_username, draft_id, int(draft['owner_id'])) if bot_username and len(q_rows) > 0 and hasattr(base, '_build_practice_url') else None
    kb_rows = [
        [
            InlineKeyboardButton('🔄 Set Active', callback_data=f'ap:set:{draft_id}:{page}'),
            InlineKeyboardButton('⚙️ Prefix ' + ('ON' if int(draft['show_title_prefix'] or 1) else 'OFF'), callback_data=f'ap:prefix:{draft_id}:{page}'),
        ],
        [
            InlineKeyboardButton('✏️ Edit Title', callback_data=f'ap:title:{draft_id}:{page}'),
            InlineKeyboardButton('⏱ Edit Time', callback_data=f'ap:time:{draft_id}:{page}'),
        ],
        [
            InlineKeyboardButton('➖ Edit Negative', callback_data=f'ap:neg:{draft_id}:{page}'),
            InlineKeyboardButton('🎲 Shuffle', callback_data=f'ap:shuffle:{draft_id}:{page}'),
        ],
        [
            InlineKeyboardButton('🗑 Delete', callback_data=f'ap:del:{draft_id}:{page}'),
            InlineKeyboardButton('📚 Back to Drafts', callback_data=f'ap:page:{page}'),
        ],
    ]
    if practice_url:
        kb_rows.insert(3, [InlineKeyboardButton('🧪 Practice Link', url=practice_url)])
    return "\n".join(lines).strip(), InlineKeyboardMarkup(kb_rows)


async def _show_draft_browser(context, user_id: int, page: int = 0, header: str = "") -> None:
    text, kb = _build_draft_browser_list_text_markup(user_id, page=page, header=header)
    if hasattr(base, '_drop_home_panel_if_present'):
        await base._drop_home_panel_if_present(context, user_id)
    if hasattr(base, '_replace_single_panel_message'):
        await base._replace_single_panel_message(context, user_id, ('draft-browser', user_id), text, kb)
    else:
        await context.bot.send_message(user_id, text, parse_mode=ParseMode.HTML, reply_markup=kb, disable_web_page_preview=True)


async def _show_draft_detail(context, user_id: int, draft_id: str, page: int = 0, header: str = "") -> None:
    text, kb = _build_draft_detail_text_markup(user_id, draft_id, page=page, header=header)
    if hasattr(base, '_drop_home_panel_if_present'):
        await base._drop_home_panel_if_present(context, user_id)
    if hasattr(base, '_replace_single_panel_message'):
        await base._replace_single_panel_message(context, user_id, ('draft-browser', user_id), text, kb)
    else:
        await context.bot.send_message(user_id, text, parse_mode=ParseMode.HTML, reply_markup=kb, disable_web_page_preview=True)


async def show_drafts(update: Update, context, user_id: int, page: int = 0, header: str = "") -> None:
    bot_username = context.bot_data.get('bot_username', '')
    setattr(base, '_cached_bot_username_for_browser', bot_username)
    await _show_draft_browser(context, user_id, page=page, header=header)


base.show_drafts = show_drafts


_previous_callback_router_professional = base.callback_router


async def callback_router(update: Update, context) -> None:
    query = update.callback_query
    if not query or not query.data:
        return await _previous_callback_router_professional(update, context)
    data = query.data
    user = query.from_user
    if user:
        base.record_user(user)
    if data == 'panel:drafts' or data.startswith('ap:'):
        await query.answer()
        if not user or not base.user_has_staff_access(user.id):
            warn_kb = InlineKeyboardMarkup([[InlineKeyboardButton('📘 Commands', callback_data='panel:commands')]])
            await base.panel_show_message(query.message, user.id if user else 0, base.warning_text(), reply_markup=warn_kb)
            return
        setattr(base, '_cached_bot_username_for_browser', context.bot_data.get('bot_username', ''))
        parts = data.split(':')
        if data == 'panel:drafts':
            text, kb = _build_draft_browser_list_text_markup(user.id, page=0)
            await base.panel_show_message(query.message, user.id, text, reply_markup=kb)
            return
        action = parts[1] if len(parts) > 1 else ''
        if action == 'page':
            page = int(parts[2]) if len(parts) > 2 and parts[2].isdigit() else 0
            text, kb = _build_draft_browser_list_text_markup(user.id, page=page)
            await base.panel_show_message(query.message, user.id, text, reply_markup=kb)
            return
        if action == 'view' and len(parts) >= 4:
            draft_id = parts[2]
            page = int(parts[3]) if parts[3].isdigit() else 0
            text, kb = _build_draft_detail_text_markup(user.id, draft_id, page=page)
            await base.panel_show_message(query.message, user.id, text, reply_markup=kb)
            return
        if action == 'set' and len(parts) >= 4:
            draft_id = parts[2]
            page = int(parts[3]) if parts[3].isdigit() else 0
            draft = base.get_draft(draft_id)
            if not draft:
                text, kb = _build_draft_browser_list_text_markup(user.id, page=page, header='⚠️ Draft not found.')
                await base.panel_show_message(query.message, user.id, text, reply_markup=kb)
                return
            if int(draft['owner_id']) != user.id and not getattr(base, 'is_all_access_admin', lambda _x: False)(user.id) and not base.is_owner(user.id):
                text, kb = _build_draft_browser_list_text_markup(user.id, page=page, header='⚠️ You do not have access to activate this draft.')
                await base.panel_show_message(query.message, user.id, text, reply_markup=kb)
                return
            base.set_active_draft(user.id, draft_id)
            text, kb = _build_draft_detail_text_markup(user.id, draft_id, page=page, header=f'✅ Active draft set to <code>{draft_id}</code>.')
            await base.panel_show_message(query.message, user.id, text, reply_markup=kb)
            return
        if action == 'del' and len(parts) >= 4:
            draft_id = parts[2]
            page = int(parts[3]) if parts[3].isdigit() else 0
            draft = base.get_draft(draft_id)
            if not draft:
                text, kb = _build_draft_browser_list_text_markup(user.id, page=page, header='⚠️ Draft already deleted.')
                await base.panel_show_message(query.message, user.id, text, reply_markup=kb)
                return
            if int(draft['owner_id']) != user.id and not base.is_owner(user.id):
                text, kb = _build_draft_detail_text_markup(user.id, draft_id, page=page, header='⚠️ Only the draft owner or bot owner can delete this draft.')
                await base.panel_show_message(query.message, user.id, text, reply_markup=kb)
                return
            base.delete_draft(draft_id, user.id)
            text, kb = _build_draft_browser_list_text_markup(user.id, page=page, header=f'🗑 Draft <code>{draft_id}</code> deleted.')
            await base.panel_show_message(query.message, user.id, text, reply_markup=kb)
            return
        if action in {'title','time','neg'} and len(parts) >= 4:
            draft_id = parts[2]
            page = int(parts[3]) if parts[3].isdigit() else 0
            draft = resolve_editable_draft(user.id, draft_id)
            if not draft:
                text, kb = _build_draft_browser_list_text_markup(user.id, page=page, header='⚠️ Draft not found or access denied.')
                await base.panel_show_message(query.message, user.id, text, reply_markup=kb)
                return
            state_name = {'title': 'adv_edit_title', 'time': 'adv_edit_time', 'neg': 'adv_edit_neg'}[action]
            base.set_user_state(user.id, state_name, {'draft_id': draft_id, 'page': page})
            prompts = {
                'title': 'Send the new draft title now.',
                'time': 'Send the new default time in seconds. Example: 30',
                'neg': 'Send the new negative mark. Example: 0.25',
            }
            await base.safe_reply(query.message, prompts[action])
            return
        if action == 'prefix' and len(parts) >= 4:
            draft_id = parts[2]
            page = int(parts[3]) if parts[3].isdigit() else 0
            draft = resolve_editable_draft(user.id, draft_id)
            if not draft:
                text, kb = _build_draft_browser_list_text_markup(user.id, page=page, header='⚠️ Draft not found or access denied.')
                await base.panel_show_message(query.message, user.id, text, reply_markup=kb)
                return
            new_val = 0 if int(draft['show_title_prefix'] or 1) else 1
            base.DBH.execute('UPDATE drafts SET show_title_prefix=?, updated_at=? WHERE id=?', (new_val, base.now_ts(), draft_id))
            text, kb = _build_draft_detail_text_markup(user.id, draft_id, page=page, header=f"✅ Title prefix turned <b>{'ON' if new_val else 'OFF'}</b>.")
            await base.panel_show_message(query.message, user.id, text, reply_markup=kb)
            return
        if action == 'shuffle' and len(parts) >= 4:
            draft_id = parts[2]
            page = int(parts[3]) if parts[3].isdigit() else 0
            draft = resolve_editable_draft(user.id, draft_id)
            if not draft:
                text, kb = _build_draft_browser_list_text_markup(user.id, page=page, header='⚠️ Draft not found or access denied.')
                await base.panel_show_message(query.message, user.id, text, reply_markup=kb)
                return
            shuffle_draft_questions(draft_id)
            text, kb = _build_draft_detail_text_markup(user.id, draft_id, page=page, header='✅ Draft questions shuffled.')
            await base.panel_show_message(query.message, user.id, text, reply_markup=kb)
            return
    return await _previous_callback_router_professional(update, context)


base.callback_router = callback_router


_previous_handle_text_polished = base.handle_text


async def handle_text(update: Update, context) -> None:
    message = update.effective_message
    user = update.effective_user
    chat = update.effective_chat
    if not message or not user or not chat or not getattr(message, 'text', None):
        return await _previous_handle_text_polished(update, context)
    state, payload = base.get_user_state(user.id)
    cmd, args = base.extract_command(message.text, context.bot_data.get('bot_username', ''))
    cmd = (cmd or '').lower()

    if chat.type == 'private' and state in {'adv_edit_title', 'adv_edit_time', 'adv_edit_neg'} and not cmd:
        draft_id = str(payload.get('draft_id') or '')
        page = int(payload.get('page') or 0)
        draft = resolve_editable_draft(user.id, draft_id)
        if not draft:
            base.clear_user_state(user.id)
            await base.safe_reply(message, 'Draft not found, or you do not have access.')
            return
        raw = base.normalize_visual_text(message.text)
        if state == 'adv_edit_title':
            if not raw:
                await base.safe_reply(message, 'Title cannot be empty.')
                return
            base.DBH.execute('UPDATE drafts SET title=?, updated_at=? WHERE id=?', (raw, base.now_ts(), draft_id))
            base.clear_user_state(user.id)
            await _show_draft_detail(context, user.id, draft_id, page=page, header='✅ Draft title updated.')
            return
        if state == 'adv_edit_time':
            if not raw.isdigit():
                await base.safe_reply(message, 'Send the time in seconds only. Example: 30')
                return
            secs = max(5, int(raw))
            base.DBH.execute('UPDATE drafts SET question_time=?, updated_at=? WHERE id=?', (secs, base.now_ts(), draft_id))
            base.clear_user_state(user.id)
            await _show_draft_detail(context, user.id, draft_id, page=page, header=f'✅ Default time updated to {secs} sec.')
            return
        if state == 'adv_edit_neg':
            try:
                neg = float(raw)
            except Exception:
                await base.safe_reply(message, 'Send a valid decimal value. Example: 0.25')
                return
            base.DBH.execute('UPDATE drafts SET negative_mark=?, updated_at=? WHERE id=?', (neg, base.now_ts(), draft_id))
            base.clear_user_state(user.id)
            await _show_draft_detail(context, user.id, draft_id, page=page, header=f'✅ Negative mark updated to {neg}.')
            return

    if chat.type == 'private' and base.user_has_staff_access(user.id) and cmd == 'clonequiz':
        raw = args.strip()
        title_part = ''
        source_part = raw
        if '|' in raw:
            title_part, source_part = [x.strip() for x in raw.split('|', 1)]
        token = extract_clone_token(source_part)
        if token:
            draft_id = base.create_draft(user.id, title_part or f'QuizBot Clone {token}', 30, 0.0)
            start_clone_session(user.id, draft_id, token, source_part)
            await base.send_draft_card(
                context,
                user.id,
                user.id,
                draft_id,
                header=(
                    '✅ Clone draft created from the QuizBot link/token.\n'
                    'Now forward the quiz polls from @QuizBot to this bot inbox. Each forwarded quiz poll will be cleaned and added automatically.\n'
                    'Use /cloneend when finished.'
                ),
            )
            return
    return await _previous_handle_text_polished(update, context)


base.handle_text = handle_text


async def begin_or_advance_exam(context, session_id: str) -> None:
    session = base.get_session(session_id)
    if not session or session['status'] != 'running':
        return
    next_index = int(session['current_index'] or 0) + 1
    total = int(session['total_questions'] or 0)
    if next_index > total:
        await base.finish_exam(context, session_id, reason='completed')
        return
    q = base.get_session_question(session_id, next_index)
    if not q:
        await base.finish_exam(context, session_id, reason='missing_question')
        return
    options = base.jload(q['options'], []) or []
    section_title = base.normalize_visual_text(q['section_title'] or '')
    draft_row = base.get_draft(str(session['draft_id']))
    show_title = 1 if not draft_row else int(draft_row['show_title_prefix'] or 1)
    base_seconds = int(q['question_time_override'] or session['question_time'] or 30)
    speed_factor = float(session['speed_factor'] or 1.0)
    effective_seconds = max(5, int(round(base_seconds * speed_factor)))
    try:
        prefix_parts = [f'[{next_index}/{total}]']
        if section_title:
            prefix_parts.append(f'[{section_title}]')
        if show_title:
            prefix_parts.append(f'[{base.normalize_visual_text(session["title"])}]')
        question_prefix = (' '.join(prefix_parts) + '\n') if prefix_parts else ''
        poll_question = (question_prefix + str(q['question'])).strip()
        if len(poll_question) > 300:
            allowed_q = max(10, 300 - len(question_prefix))
            poll_question = question_prefix + str(q['question'])[: allowed_q - 1].rstrip() + '…'
        explanation_text = base.normalize_visual_text(q['explanation'] or f'Question {next_index} of {total}')
        if len(explanation_text) > 200:
            explanation_text = explanation_text[:199] + '…'
        msg = await context.bot.send_poll(
            chat_id=session['chat_id'],
            question=poll_question,
            options=options,
            type=Poll.QUIZ,
            is_anonymous=False,
            allows_multiple_answers=False,
            correct_option_id=int(q['correct_option']),
            explanation=explanation_text,
            open_period=effective_seconds,
        )
    except TelegramError as exc:
        base.logger.exception('Failed to send poll: %s', exc)
        await base.finish_exam(context, session_id, reason='send_poll_error')
        return
    poll_id = msg.poll.id
    with closing(base.DBH.connect()) as conn:
        conn.execute(
            'UPDATE session_questions SET poll_id=?, message_id=?, open_ts=?, close_ts=? WHERE session_id=? AND q_no=?',
            (poll_id, msg.message_id, base.now_ts(), base.now_ts() + effective_seconds, session_id, next_index),
        )
        conn.execute(
            'UPDATE sessions SET current_index=?, active_poll_id=?, active_poll_message_id=? WHERE id=?',
            (next_index, poll_id, msg.message_id, session_id),
        )
        conn.commit()
    context.job_queue.run_once(base.close_poll_job, when=max(1, effective_seconds), data={'session_id': session_id, 'q_no': next_index}, name=f'close:{session_id}:{next_index}')


base.begin_or_advance_exam = begin_or_advance_exam


def _section_breakdown_for_user(session_id: str, user_id: int) -> List[Dict[str, Any]]:
    session = base.get_session(session_id)
    if not session:
        return []
    neg = float(session['negative_mark'] or 0.0)
    qrows = base.DBH.fetchall('SELECT q_no, section_title FROM session_questions WHERE session_id=? ORDER BY q_no', (session_id,))
    ans_rows = base.DBH.fetchall('SELECT q_no, is_correct FROM answers WHERE session_id=? AND user_id=?', (session_id, user_id))
    ans_map = {int(r['q_no']): int(r['is_correct']) for r in ans_rows}
    order = []
    stats: Dict[str, Dict[str, Any]] = {}
    for q in qrows:
        sec = base.normalize_visual_text(q['section_title'] or '') or 'General'
        if sec not in stats:
            stats[sec] = {'title': sec, 'correct': 0, 'wrong': 0, 'skipped': 0, 'score_num': 0.0}
            order.append(sec)
        ans = ans_map.get(int(q['q_no']))
        if ans is None:
            stats[sec]['skipped'] += 1
        elif ans == 1:
            stats[sec]['correct'] += 1
            stats[sec]['score_num'] += 1.0
        else:
            stats[sec]['wrong'] += 1
            stats[sec]['score_num'] -= neg
    return [{**stats[k], 'score': base.fmt_score(stats[k]['score_num'])} for k in order]


async def send_private_results(context, session_id: str) -> None:
    session = base.get_session(session_id)
    if not session:
        return
    chat_row = base.DBH.fetchone('SELECT username, chat_type FROM known_chats WHERE chat_id=?', (session['chat_id'],))
    username = chat_row['username'] if chat_row else None
    chat_type = chat_row['chat_type'] if chat_row else ''
    ranking = base.get_session_ranking(session_id)
    rank_map = {int(r['user_id']): r for r in ranking}
    total_users = max(1, len(ranking))
    qrows = base.DBH.fetchall('SELECT q_no, message_id FROM session_questions WHERE session_id=? ORDER BY q_no', (session_id,))
    q_map = {int(r['q_no']): r for r in qrows}
    participants = base.DBH.fetchall('SELECT * FROM participants WHERE session_id=? AND eligible=1', (session_id,))
    total_questions = int(session['total_questions'] or 0)
    neg = float(session['negative_mark'] or 0.0)
    bot_username = context.bot_data.get('bot_username', '')

    for p in participants:
        row = base.DBH.fetchone('SELECT started FROM known_users WHERE user_id=?', (p['user_id'],))
        if not row or int(row['started'] or 0) != 1:
            continue
        rank_item = rank_map.get(int(p['user_id']))
        if not rank_item:
            continue
        if not await base.is_required_channel_member(context, int(p['user_id'])):
            continue
        answers = base.DBH.fetchall('SELECT * FROM answers WHERE session_id=? AND user_id=? ORDER BY q_no', (session_id, p['user_id']))
        answer_by_q = {int(a['q_no']): a for a in answers}
        correct_links: List[str] = []
        wrong_links: List[str] = []
        skipped_links: List[str] = []
        for q_no, q in q_map.items():
            link = base.get_message_link(int(session['chat_id']), int(q['message_id'] or 0), username)
            label = f'<a href="{link}">Q{q_no}</a>' if link else f'Q{q_no}'
            ans = answer_by_q.get(q_no)
            if ans is None:
                skipped_links.append(label)
            elif int(ans['is_correct']) == 1:
                correct_links.append(label)
            else:
                wrong_links.append(label)
        correct = int(rank_item['correct'])
        wrong = int(rank_item['wrong'])
        skipped = int(rank_item['skipped'])
        attempted = max(1, correct + wrong)
        accuracy = (correct / attempted) * 100.0
        percentage = (correct / max(1, total_questions)) * 100.0
        percentile = 100.0 if total_users <= 1 else ((total_users - int(rank_item['rank'])) / (total_users - 1)) * 100.0
        negative_value = wrong * neg
        section_lines: List[str] = []
        section_data = _section_breakdown_for_user(session_id, int(p['user_id']))
        if len(section_data) > 1 or (section_data and section_data[0]['title'] != 'General'):
            section_lines.append('<b>Section Analysis</b>')
            for item in section_data:
                section_lines.append(
                    f"• <b>{base.html_escape(item['title'])}</b> — ✅ {item['correct']} | ❌ {item['wrong']} | ➖ {item['skipped']} | Score {item['score']}"
                )
            section_lines.append('')

        intro = 'You already took this quiz. Your result on the leaderboard:' if total_users > 1 else 'Your exam result:'
        placement = f"{_ordinal(int(rank_item['rank']))} place out of {total_users}." if total_users > 1 else 'Completed.'
        stats_block = (
            f"✅ Correct — <b>{correct}</b>\n"
            f"❌ Wrong — <b>{wrong}</b>\n"
            f"➖ Missed — <b>{skipped}</b>\n"
            f"📉 Negative — <b>-{negative_value:.2f}</b>\n"
            f"🏁 Score — <b>{rank_item['score']}</b>\n"
            f"🎯 Accuracy — <b>{accuracy:.2f}%</b>\n"
            f"📊 Percentage — <b>{percentage:.2f}%</b>\n"
            f"🏆 Percentile — <b>{percentile:.2f}</b>\n"
            f"⏱️ {base.html_escape(rank_item.get('time_label', '0s'))}"
        )
        text = (
            f"🎲 <b>Quiz '{base.html_escape(base.normalize_visual_text(session['title']))}'</b>\n\n"
            f"<i>{intro}</i>\n\n"
            f"<blockquote>{stats_block}</blockquote>\n\n"
            f"<b>{placement}</b>\n\n"
            + ("\n".join(section_lines) if section_lines else "") +
            f"<b>Correct</b>\n{', '.join(correct_links) or '—'}\n\n"
            f"<b>Wrong</b>\n{', '.join(wrong_links) or '—'}\n\n"
            f"<b>Skipped</b>\n{', '.join(skipped_links) or '—'}"
        )
        kb = None
        if chat_type == 'private' and bot_username and base.get_draft(str(session['draft_id'])):
            practice_url = base._build_practice_url(bot_username, str(session['draft_id']), int(session['created_by'])) if hasattr(base, '_build_practice_url') else None
            if practice_url:
                kb = InlineKeyboardMarkup([[InlineKeyboardButton('🔁 Try Again', url=practice_url)]])
                text += "\n\n<i>You can take this quiz again from the button below.</i>"
        with suppress(TelegramError):
            await context.bot.send_message(
                chat_id=int(p['user_id']),
                text=text,
                parse_mode=ParseMode.HTML,
                disable_web_page_preview=True,
                reply_markup=kb,
            )


base.send_private_results = send_private_results


def _report_html(title: str, summary: Dict[str, Any], ranking: List[Dict[str, Any]], theme: Dict[str, str]) -> str:
    title = base.normalize_visual_text(title) or 'Exam'
    rows = []
    for item in (ranking or []):
        name = base.html_escape(str(item.get('name') or 'Unknown'))
        time_label = base.html_escape(str(item.get('time', item.get('time_label', '0s'))))
        rows.append(
            "<tr>"
            f"<td class='center'>{item.get('rank','')}</td>"
            f"<td><div class='primary'>{name}</div></td>"
            f"<td class='num ok'>{item.get('correct',0)}</td>"
            f"<td class='num bad'>{item.get('wrong',0)}</td>"
            f"<td class='num skip'>{item.get('skipped',0)}</td>"
            f"<td class='num time'>{time_label}</td>"
            f"<td class='num score'>{base.html_escape(str(item.get('score','0.00')))}</td>"
            "</tr>"
        )
    if not rows:
        rows = ["<tr><td class='center'>1</td><td><div class='primary'>No eligible participants</div></td><td class='num ok'>0</td><td class='num bad'>0</td><td class='num skip'>0</td><td class='num time'>0s</td><td class='num score'>0.00</td></tr>"]
    cards = [
        ('Participants', summary.get('participants','0')),
        ('Questions', summary.get('questions','0')),
        ('Average Score', summary.get('average_score','0.00')),
        ('Highest Score', summary.get('highest_score','0.00')),
        ('Lowest Score', summary.get('lowest_score','0.00')),
        ('Negative / Wrong', summary.get('negative_mark','0')),
        ('Started', summary.get('started_at','—')),
        ('Ended', summary.get('ended_at','—')),
    ]
    cards_html = ''.join([f"<div class='card'><div class='k'>{base.html_escape(str(k))}</div><div class='v'>{base.html_escape(str(v))}</div></div>" for k, v in cards])
    return f"""
<!doctype html>
<html><head><meta charset='utf-8'>
<meta name='viewport' content='width=device-width, initial-scale=1'>
<style>
{base._html_font_css() if hasattr(base, '_html_font_css') else ''}
{':root {' + (base._theme_vars(theme) if hasattr(base, '_theme_vars') else '') + '}'}
html,body{{margin:0;padding:0;background:linear-gradient(135deg,#07111d,#0d1e33);color:#eef6ff;font-family:'AppBengali','AppSans',system-ui,sans-serif;}}
.wrap{{max-width:1180px;margin:0 auto;padding:28px 18px 42px;animation:fadeIn .55s ease;}}
.hero{{position:sticky;top:0;background:rgba(7,17,29,.78);backdrop-filter:blur(14px);border:1px solid rgba(255,255,255,.07);border-radius:22px;padding:20px 22px;box-shadow:0 18px 45px rgba(0,0,0,.28);z-index:20;}}
.brand{{font-size:14px;letter-spacing:.08em;text-transform:uppercase;color:#9ec5f8;font-weight:700;}}
.title{{font-size:34px;font-weight:800;margin-top:8px;line-height:1.1;word-break:break-word;}}
.gen{{font-size:13px;color:#bfd3ee;margin-top:6px;}}
.grid{{display:grid;grid-template-columns:repeat(auto-fit,minmax(200px,1fr));gap:14px;margin-top:18px;}}
.card{{background:rgba(18,37,63,.88);border:1px solid rgba(255,255,255,.08);border-radius:18px;padding:14px 16px;box-shadow:0 10px 28px rgba(0,0,0,.22);transform:translateY(14px);opacity:0;animation:cardIn .45s ease forwards;}}
.card:nth-child(2){{animation-delay:.05s}} .card:nth-child(3){{animation-delay:.1s}} .card:nth-child(4){{animation-delay:.15s}} .card:nth-child(5){{animation-delay:.2s}} .card:nth-child(6){{animation-delay:.25s}} .card:nth-child(7){{animation-delay:.3s}} .card:nth-child(8){{animation-delay:.35s}}
.k{{font-size:12px;color:#9db6d3;text-transform:uppercase;letter-spacing:.06em;}}
.v{{font-size:22px;font-weight:800;margin-top:6px;white-space:pre-wrap;word-break:break-word;}}
.section{{font-size:18px;font-weight:800;margin:22px 2px 12px;}}
.table-wrap{{overflow:auto;border-radius:20px;border:1px solid rgba(255,255,255,.08);background:rgba(9,19,34,.82);box-shadow:0 18px 44px rgba(0,0,0,.25);}}
.table{{width:100%;border-collapse:separate;border-spacing:0;min-width:900px;}}
.table thead th{{position:sticky;top:0;background:#10243c;color:#fff;padding:14px 12px;font-size:12px;text-align:left;z-index:3;}}
.table tbody td{{padding:13px 12px;border-top:1px solid rgba(255,255,255,.06);font-size:14px;vertical-align:top;}}
.table tbody tr:hover td{{background:rgba(255,255,255,.03);}}
.center{{text-align:center;}} .num{{text-align:right;}} .ok{{color:#7cf0a1;font-weight:700;}} .bad{{color:#ff8f8f;font-weight:700;}} .skip{{color:#ffd17b;font-weight:700;}} .time{{color:#bfe0ff;}} .score{{font-weight:800;color:#fff;}}
.primary{{font-size:14px;line-height:1.18;white-space:pre-wrap;word-break:break-word;}}
@keyframes fadeIn{{from{{opacity:0}}to{{opacity:1}}}} @keyframes cardIn{{to{{transform:translateY(0);opacity:1}}}}
</style></head>
<body><div class='wrap'>
<div class='hero'>
<div class='brand'>{base.html_escape(base.CONFIG.brand_name)} • Interactive Report</div>
<div class='title'>{base.html_escape(title)}</div>
<div class='gen'>Generated at {base.html_escape(base.fmt_dt(base.now_ts()))}</div>
</div>
<div class='grid'>{cards_html}</div>
<div class='section'>Ranking Analysis</div>
<div class='table-wrap'><table class='table'>
<thead><tr><th style='width:54px'>#</th><th>Name</th><th style='width:90px'>Correct</th><th style='width:90px'>Wrong</th><th style='width:90px'>Skipped</th><th style='width:96px'>Time</th><th style='width:110px'>Score</th></tr></thead>
<tbody>{''.join(rows)}</tbody></table></div>
</div></body></html>
"""


base._report_html = _report_html


if __name__ == "__main__":
    base.main()
