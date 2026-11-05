"""
ui_style.py — look & feel helpers for the bot.

* StyledMarkdown : Telethon parse-mode = normal Telegram markdown PLUS real
                   blockquotes (lines starting with "> ") and an automatic
                   "bold heading + italic quote" styling for plain messages.
* strip_emoji    : buttons are emoji-free.
* infer_style    : button colour (green / blue / red) from the button label.
"""
import re

from telethon.extensions import markdown as _tl_md
from telethon.tl.types import MessageEntityBlockquote

# A message that starts with this invisible marker is already hand-styled:
# the automatic heading / quote styling is skipped for it.
RAW = "\u200b"

# ── bold font: 𝗡𝗢𝗕𝗘𝗟𝗢𝗧𝗦 (Unicode sans-serif bold) ────────────────
def to_bold(text: str) -> str:
    out = []
    for ch in text:
        o = ord(ch)
        if 65 <= o <= 90:
            out.append(chr(0x1D5D4 + o - 65))
        elif 97 <= o <= 122:
            out.append(chr(0x1D5EE + o - 97))
        elif 48 <= o <= 57:
            out.append(chr(0x1D7EC + o - 48))
        else:
            out.append(ch)
    return "".join(out)


def bold_fonts(text: str) -> str:
    """**text** -> real bold-font letters (code spans are left alone)."""
    return re.sub(r"\*\*([^*`]+?)\*\*", lambda m: to_bold(m.group(1)), text)


# ── emoji handling ──────────────────────────────────────────────
_EMOJI = re.compile(
    "[\U0001F000-\U0001FAFF"      # pictographs, flags, emoticons
    "\u2190-\u21FF"               # arrows
    "\u2300-\u23FF"               # misc technical (⏳ ⏭ ...)
    "\u25A0-\u25FF"               # geometric shapes (◀ ▶)
    "\u2600-\u27BF"               # misc symbols + dingbats (✅ ❌ ⚡ ⚙ ✏ ...)
    "\u2900-\u297F"
    "\u2B00-\u2BFF"               # ⭐ ⬅ ...
    "\u2139"
    "\uFE00-\uFE0F\u200D\u20E3"   # variation selectors, ZWJ, keycap
    "]+"
)


def strip_emoji(text: str) -> str:
    """Remove every emoji / pictograph / flag and tidy the spaces left behind."""
    return re.sub(r"\s{2,}", " ", _EMOJI.sub("", text or "")).strip()


# ── button colours ──────────────────────────────────────────────
# Telegram's coloured-button names.  If your Telethon build uses other names,
# change them here — this is the ONLY place they are defined.
STYLE_GREEN = "success"
STYLE_BLUE = "primary"
STYLE_RED = "danger"

_ALIASES = {
    "success": STYLE_GREEN, "green": STYLE_GREEN,
    "primary": STYLE_BLUE, "blue": STYLE_BLUE,
    "danger": STYLE_RED, "red": STYLE_RED,
}

_RED = re.compile(
    r"\b(cancel|reject|decline|delete|remove|ban|disable|revoke|clear|terms of service)\b")
_GREEN = re.compile(
    r"\b(back|home|main menu|accept|approve|confirm|buy|browse|add funds|add credits|"
    r"i have paid|paid|new deposit|save|yes|done|unban|continue|check again|enable)\b")


def infer_style(label: str) -> str:
    """Green = go / back, red = stop / delete / terms, blue = everything else."""
    l = strip_emoji(label).lower()
    if _RED.search(l):
        return STYLE_RED
    if _GREEN.search(l):
        return STYLE_GREEN
    return STYLE_BLUE


def resolve_style(style, label: str):
    """'default' / None -> inferred from the label; names/aliases -> real style."""
    if style in (None, "", "default", "auto"):
        return infer_style(label)
    return _ALIASES.get(str(style).lower(), style)


# ── message styling ─────────────────────────────────────────────
_SEP_ONLY = re.compile(r"^[\s━─—\-_=~•*·]*$")


def _is_data_line(line: str) -> bool:
    """Lines carrying amounts / codes / links are left exactly as written."""
    return (
        "`" in line or "₹" in line or "**" in line or "http" in line
        or line.lstrip().startswith("|")
        or re.search(r"\d\s*(Credits?|Cr)\b", line) is not None
    )


def prepare(text: str) -> str:
    """Automatic styling for every ordinary multi-line message:
         first line            -> bold heading (leading emoji removed, CAPS)
         first plain paragraph -> italic blockquote
       Amount / code / link lines are never touched."""
    if text.startswith(RAW):
        return text[len(RAW):]
    t = text.strip()
    if "\n" not in t:
        if len(t) <= 40 and re.fullmatch(r"[^\w*`]*\*\*[^*]+\*\*:?", t):
            core = re.sub(r"^[^\w*`]+", "", t)
            return re.sub(r"\*\*(.+?)\*\*", lambda m: "**" + m.group(1).upper() + "**", core)
        return text
    lines = text.split("\n")
    i0 = next((i for i, l in enumerate(lines) if l.strip()), None)
    if i0 is None:
        return text
    head = lines[i0]
    if head.lstrip().startswith(">"):
        return text
    core = re.sub(r"^[^\w*`_\[(]+", "", head)
    if not core:
        return text
    if "**" in core:
        core = re.sub(r"\*\*(.+?)\*\*", lambda m: "**" + m.group(1).upper() + "**", core)
    elif len(core) <= 60 and "`" not in core and not re.search(r"[.!?:,]$", core):
        core = "**" + core.upper() + "**"
    lines[i0] = core

    j = i0 + 1
    while j < len(lines) and not lines[j].strip():
        j += 1
    k = j
    while k < len(lines) and lines[k].strip() and not _SEP_ONLY.match(lines[k]):
        k += 1
    para = lines[j:k]
    if para and not any(_is_data_line(l) for l in para):
        lines[j:k] = ["> __" + l.strip() + "__" for l in para]
    return "\n".join(lines)


def _u16(s: str) -> int:
    return len(s.encode("utf-16-le")) // 2


def parse_with_quotes(message: str):
    """Telegram markdown + blockquotes ("> " lines become a real quote block)."""
    groups = []                           # [is_quote, [lines]]
    for ln in message.split("\n"):
        q = ln.startswith("> ") or ln == ">"
        if q:
            ln = ln[2:]
        if groups and groups[-1][0] == q:
            groups[-1][1].append(ln)
        else:
            groups.append([q, [ln]])

    parts, entities, off = [], [], 0
    for is_quote, ls in groups:
        chunk = "\n".join(ls)
        core = chunk.strip("\n")
        if not core.strip():
            piece, txt, ents, lead = chunk, "", [], 0
        else:
            lead = len(chunk) - len(chunk.lstrip("\n"))
            trail = len(chunk) - len(chunk.rstrip("\n"))
            txt, ents = _tl_md.parse(core)
            piece = "\n" * lead + txt + "\n" * trail
        base = off + lead
        for e in ents:
            e.offset += base
            entities.append(e)
        if is_quote and txt:
            entities.append(MessageEntityBlockquote(offset=base, length=_u16(txt)))
        parts.append(piece)
        off += _u16(piece) + 1            # +1 for the "\n" joining the groups
    return "\n".join(parts), entities


class StyledMarkdown:
    """Drop-in Telethon parse mode: bot.parse_mode = StyledMarkdown"""

    @staticmethod
    def parse(message):
        return parse_with_quotes(bold_fonts(prepare(message)))

    @staticmethod
    def unparse(text, entities):
        return _tl_md.unparse(text, entities)
