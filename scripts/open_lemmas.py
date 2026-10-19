#!/usr/bin/env python3
"""List declarations whose proof still contains `sorry`.
Usage: open_lemmas.py LogGas/*.lean   -> lines "file<TAB>module<TAB>lemma<TAB>sorry_count"
"""
import re, sys, pathlib

DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma|def|instance)\s+([^\s:({\[]+)')

def scan(path):
    lines = pathlib.Path(path).read_text().split('\n')
    module = str(path).replace('/', '.').removesuffix('.lean')
    cur, body = None, []
    out = []
    def flush():
        if cur:
            n = sum(len(re.findall(r'\bsorry\b', l)) for l in body)
            if n:
                out.append((str(path), module, cur, n))
    for l in lines:
        m = DECL.match(l)
        if m:
            flush()
            cur, body = m.group(2), [l]
        elif cur is not None:
            body.append(l)
    flush()
    return out

for p in sys.argv[1:]:
    for f, mod, name, n in scan(p):
        print(f"{f}\t{mod}\t{name}\t{n}")
