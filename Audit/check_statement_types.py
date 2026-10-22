#!/usr/bin/env python3
"""Frozen-statement check.

Usage: lake env lean Audit/statement_types.lean > /tmp/st.txt
       python3 Audit/check_statement_types.py /tmp/st.txt

Every declaration block in the baseline Audit/statement_types.txt (one block per declaration: its
pp.all type, and for frozen-namespace definitions its value) must occur byte-identically in the
new output, except owner-approved changes, which must occur exactly as recorded in
Audit/approved_changes.txt. New declarations (helpers added during proofs) are allowed and listed.
Exit status 1 on any missing/changed/unapplied-approved block.
"""
import re, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
HEAD = re.compile(r"^((?:LogGasPaper|LogGasChallenge|LogGas)\.\S+) : ")

def blocks(path):
    out, cur, name = {}, [], None
    for line in Path(path).read_text(encoding="utf-8").splitlines(keepends=True):
        if line.startswith("#"):
            continue
        m = HEAD.match(line)
        if m:
            if name is not None:
                out[name] = "".join(cur)
            name, cur = m.group(1), [line]
        else:
            cur.append(line)
    if name is not None:
        out[name] = "".join(cur)
    return out

base = blocks(HERE / "statement_types.txt")
approved = blocks(HERE / "approved_changes.txt")
new = blocks(sys.argv[1])
missing = [n for n in base if n not in new]
appr = [n for n in base if n in approved and new.get(n) == approved[n]]
changed = [n for n in base if n in new and new[n] != base[n] and n not in appr]
unused = [n for n in approved if n not in appr]
added = [n for n in new if n not in base]
for n in missing: print("MISSING", n)
for n in changed: print("CHANGED", n)
for n in unused: print("APPROVED CHANGE NOT FOUND", n)
for n in appr: print("approved", n)
for n in added: print("added  ", n)
print(f"baseline {len(base)}, checked identical {len(base) - len(missing) - len(changed) - len(appr)}, "
      f"approved changes {len(appr)}, added {len(added)}")
sys.exit(1 if missing or changed or unused else 0)
