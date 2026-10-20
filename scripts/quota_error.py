#!/usr/bin/env python3
"""Exit 0 if a `claude -p --output-format json` call did no work because the model was
unavailable (session/usage/rate limit, quota, unknown model, API error); exit 1 otherwise.
Usage: quota_error.py result.json [stderr-file]
"""
import json, os, re, sys

PAT = re.compile(r'rate.?limit|usage.?limit|session.?limit|hit your .{0,30}limit|quota|exceeded'
                 r'|out of credits|insufficient|\b429\b|overloaded|not available|unknown model',
                 re.I)
jf = sys.argv[1]
ef = sys.argv[2] if len(sys.argv) > 2 else None
try:
    d = json.load(open(jf))
except Exception:
    sys.exit(0)                       # empty or non-JSON output: the call never ran
if d.get('is_error') or d.get('terminal_reason') == 'api_error':
    sys.exit(0)
err = open(ef).read() if ef and os.path.exists(ef) else ''
if not d.get('result') and PAT.search(json.dumps(d) + err):
    sys.exit(0)
sys.exit(1)
