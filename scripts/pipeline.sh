#!/bin/bash
# Compatibility entry point: now runs continuously until stopped or complete.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.local/bin:$PATH"
if [ -f "$HOME/.elan/env" ]; then source "$HOME/.elan/env"; fi
exec python3 scripts/persistent.py run
