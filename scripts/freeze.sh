#!/bin/bash
# Regenerate the statement-layer freeze artifacts (Audit/FREEZE.md): file hashes of the two frozen
# files, the manuscript hashes, and the pp.all type baseline. Run from the repo root on a machine
# with the pinned toolchain and a built project. Review the diff of Audit/ before committing.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.local/bin:$PATH"; [ -f "$HOME/.elan/env" ] && source "$HOME/.elan/env"
shasum -a 256 PaperChallenge.lean Challenge.lean > Audit/frozen_statements.sha256
if ls manuscript/* >/dev/null 2>&1; then shasum -a 256 manuscript/* > Audit/manuscript.sha256; fi
lake env lean Audit/statement_types.lean > Audit/statement_types.txt
python3 Audit/check_statement_types.py Audit/statement_types.txt
sed -i.bak "s/^Date: .*$/Date: $(date +%F). Commit: $(git rev-parse --short HEAD) (FREEZE_COMMIT)./" Audit/FREEZE.md && rm -f Audit/FREEZE.md.bak
echo "freeze artifacts regenerated at $(git rev-parse --short HEAD)"
