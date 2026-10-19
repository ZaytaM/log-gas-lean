#!/bin/bash
# orchestrate.sh <phase-notes.md> [tex files...]
# Runs the Opus orchestrator once to (re)write a phase's Lean skeleton, then builds.
# Example:  bash scripts/orchestrate.sh notes/phase0.md notes/sec3-badevent.tex
set -u
cd "$(dirname "$0")/.."
source scripts/pipeline.conf
export PATH="$HOME/.local/bin:$PATH"; [ -f ~/.elan/env ] && source ~/.elan/env
NOTES=$1; shift; TEX="$*"
prompt=$(sed -e "s|{PHASE_NOTES}|$NOTES|g" -e "s|{TEX_FILES}|$TEX|g" prompts/orchestrator.md)
mkdir -p logs
claude -p --model $MODEL_ORCH --max-turns 60 --dangerously-skip-permissions "$prompt" | tee logs/orchestrate_$(date +%Y%m%d_%H%M%S).log
lake build 2>&1 | tail -5
git add -A && git commit -qm "skeleton from $NOTES" && git push -q
echo "Skeleton committed. Read the lemma statements in LogGas/ before the first nightly run."
