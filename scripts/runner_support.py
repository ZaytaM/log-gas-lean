"""Result classification, reset times and conservative Lean source inspection."""
from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timedelta
import json
import re
from zoneinfo import ZoneInfo


def classify(data, stderr='', exit_code=0):
    """A worker error is not, by itself, evidence of exhausted allowance."""
    text = json.dumps(data or {}) + '\n' + stderr
    if (data or {}).get('subtype') == 'error_max_turns' or (data or {}).get('terminal_reason') == 'max_turns':
        return 'turn_limit'
    if exit_code in (124, 137, 143):
        return 'timeout'
    if re.search(r'hit your .{0,30}limit|session.?limit|usage.?limit|quota|out of credits|insufficient.{0,20}credits', text, re.I):
        return 'quota'
    if re.search(r'\b429\b|rate.?limit|overloaded', text, re.I):
        return 'rate_limit'
    if re.search(r'not logged in|authentication|invalid.api.key|unauthorized|\b401\b', text, re.I):
        return 'authentication'
    if not data:
        return 'invalid_output'
    if data.get('is_error') or exit_code:
        return 'error'
    return 'success'


def reset_time(text, now, fallback_seconds=300):
    """Return a UTC timestamp, honoring the timezone in Claude's reset message."""
    match = re.search(r'resets?\s+(.*?)(?:[\n"\\]|$)', text, re.I)
    if match:
        value = match.group(1).strip()
        zone_match = re.search(r'\(([^)]+)\)', value)
        try:
            zone = ZoneInfo(zone_match.group(1) if zone_match else 'America/Chicago')
        except (KeyError, ValueError):
            zone = ZoneInfo('America/Chicago')
        local_now = datetime.fromtimestamp(now, zone)
        iso = re.search(r'\d{4}-\d\d-\d\dT\d\d:\d\d(?::\d\d)?(?:Z|[+-]\d\d:\d\d)', value)
        if iso:
            dt = datetime.fromisoformat(iso.group().replace('Z', '+00:00'))
            if dt.timestamp() > now:
                return dt.timestamp() + 60
        clock = re.search(r'(\d{1,2})(?::(\d\d))?\s*(am|pm)', value, re.I)
        if clock:
            hour = int(clock[1]) % 12 + (12 if clock[3].lower() == 'pm' else 0)
            if not 0 <= hour <= 23 or int(clock[2] or 0) > 59:
                return now + fallback_seconds
            dt = local_now.replace(hour=hour, minute=int(clock[2] or 0), second=0, microsecond=0)
            date = re.search(r'([A-Za-z]{3,9})\s+(\d{1,2})', value)
            if date:
                try:
                    month = datetime.strptime(date[1][:3], '%b').month
                    dt = dt.replace(month=month, day=int(date[2]))
                    if dt < local_now:
                        dt = dt.replace(year=dt.year + 1)
                except ValueError:
                    return now + fallback_seconds
            elif 'tomorrow' in value.lower() or dt <= local_now:
                dt += timedelta(days=1)
            return dt.timestamp() + 60
    return now + fallback_seconds


def mask_comments(text):
    """Mask comments/strings, preserving offsets and line breaks; nested comments work."""
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2; continue
            if text.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2; continue
            if text[i] != '\n': out[i] = ' '
        elif string:
            if text[i] == '\\' and i+1 < len(text):
                out[i:i+2] = '  '; i += 2; continue
            if text[i] == '"': string = False
            if text[i] != '\n': out[i] = ' '
        elif text.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2; continue
        elif text.startswith('--', i):
            j = text.find('\n', i)
            if j < 0: j = len(text)
            out[i:j] = ' ' * (j-i); i = j; continue
        elif text[i] == '"':
            out[i] = ' '; string = True
        i += 1
    return ''.join(out)


@dataclass
class Declaration:
    name: str
    start: int
    proof: int
    end: int
    sorry: int


BOUNDARY = re.compile(r'^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*(?P<kind>theorem|lemma|def|instance|structure|class|namespace|section|end|variable|open|attribute|set_option)\b(?P<tail>[^\n]*)', re.M)


def declarations(text):
    masked = mask_comments(text)
    matches = list(BOUNDARY.finditer(masked))
    scopes, result = [], []
    for i, match in enumerate(matches):
        kind, tail = match['kind'], match['tail'].strip()
        if kind in ('namespace', 'section'):
            scopes.append((kind, tail.split()[0] if tail else '')); continue
        if kind == 'end':
            if scopes: scopes.pop()
            continue
        if kind not in ('theorem', 'lemma', 'def', 'instance'): continue
        name_match = re.match(r'([^\s:({\[]+)', tail)
        if not name_match: continue
        name = '.'.join([s for k, s in scopes if k == 'namespace'] + [name_match[1]])
        end = matches[i+1].start() if i+1 < len(matches) else len(text)
        body = masked[match.start():end]
        proof = body.find(':=')
        if proof < 0: continue
        proof += match.start() + 2
        result.append(Declaration(name, match.start(), proof, end,
                                  len(re.findall(r'\bsorry\b', masked[proof:end]))))
    return result


def proof_only_change(before, after, name):
    """Require every byte outside the target proof to remain unchanged."""
    old = next((d for d in declarations(before) if d.name == name), None)
    new = next((d for d in declarations(after) if d.name == name), None)
    if not old or not new: return False
    return (before[:old.proof] == after[:new.proof] and
            before[old.end:] == after[new.end:] and
            not re.search(r'\b(?:axiom|unsafe)\b|skipKernelTC', mask_comments(after[new.proof:new.end])))


def standard_axioms(output):
    if 'does not depend on any axioms' in output: return True
    found = re.search(r'depends on axioms:\s*\[([^]]*)\]', output, re.S)
    return bool(found) and set(re.findall(r'[\w.]+', found[1])) <= {'propext', 'Classical.choice', 'Quot.sound'}
