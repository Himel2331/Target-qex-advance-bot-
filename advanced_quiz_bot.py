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
      opened_at = base.now_ts()
      closes_at = opened_at + effective_seconds
      with closing(base.DBH.connect()) as conn:
        conn.execute(
            "UPDATE session_questions SET poll_id=?, message_id=?, open_ts=?, close_ts=? WHERE session_id=? AND q_no=?",
            (poll_id, msg.message_id, opened_at, closes_at, session_id, next_index),
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
    qrows = base.DBH.fetchall("SELECT q_no, message_id, open_ts, close_ts FROM session_questions WHERE session_id=? ORDER BY q_no",(session_id,),)
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
            spent = 0
            if ans is not None:
                open_ts = int(q["open_ts"] or 0)
                close_ts = int(q["close_ts"] or 0)
                answered_at = int(ans["answered_at"] or 0)
                if open_ts and answered_at:
                    spent = max(0, answered_at - open_ts)
                    if close_ts and close_ts > open_ts:
                        spent = min(spent, close_ts - open_ts)
            if ans is None:
                skipped_links.append(label)
            elif int(ans["is_correct"]) == 1:
                correct_links.append(f"{label} 
            ({base.fmt_elapsed(spent)})")
            else:
                wrong_links.append(f"{label} 
            ({base.fmt_elapsed(spent)})")
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


if __name__ == "__main__":
    base.main()
