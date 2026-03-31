# Advanced Quiz Bot (Render-ready)

This package uses your uploaded bot as the base engine and adds an advanced overlay on top of it.

## Kept from the base bot
- draft system
- forwarded quiz poll import
- CSV import
- group exam start / stop / schedule
- private practice links
- leaderboard image
- PDF report delivery
- admin / owner controls
- file rename + thumbnail utilities

## Added in this package
- `@QuizBot` guided clone workflow
- text / TXT / JSON MCQ import with `✅` answer marking
- smart cleanup of forwarded poll text
- duplicate-question skipping while importing
- draft editing commands: title, timer, negative marking, shuffle, delete question
- sectional draft timing
- group exam controls: pause, resume, skip, slow / fast
- inline query sharing by quiz ID
- creator-info lookup by quiz ID
- improved personal result DM: accuracy, percentage, percentile
- HTML report file sent with the PDF report

## Important limit
Directly fetching another bot's full inline quiz payload from only a pasted `@QuizBot quiz:XXXX` token is not supported by the Telegram Bot API. So the clone flow in this build is:
1. `/clonequiz`
2. send the `@QuizBot quiz:XXXX` text
3. the bot creates a new draft
4. you forward the actual quiz polls from `@QuizBot` into the bot inbox
5. the bot auto-cleans and auto-adds them to the draft
6. `/cloneend`

This is the most reliable Bot-API-safe approach.

## Main private commands
- `/newexam`
- `/drafts`
- `/importtext`
- `/txtquiz`
- `/clonequiz`
- `/cloneend`
- `/draftinfo CODE`
- `/settitle CODE | New Title`
- `/settime CODE 30`
- `/setneg CODE 0.25`
- `/shuffle CODE`
- `/delq CODE 3,5-7`
- `/section CODE 1-10 | Biology | 30`
- `/sections CODE`
- `/clearsections CODE`
- `/creator CODE`

## Group commands
- `/binddraft CODE`
- `/examstatus`
- `/starttqex [DRAFTCODE]`
- `/pauseq`
- `/resumeq`
- `/skipq`
- `/speed slow|normal|fast`
- `/stoptqex`
- `/schedule YYYY-MM-DD HH:MM`
- `/listschedules`
- `/cancelschedule SCHEDULE_ID`

## Deploy on Render
1. Create a new Web Service.
2. Upload this folder or connect a repo containing these files.
3. Set the start file to `advanced_quiz_bot.py`.
4. Add the environment variables from `.env.example`.
5. Deploy.

## Local run
```bash
python -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
cp .env.example .env
python advanced_quiz_bot.py
```
