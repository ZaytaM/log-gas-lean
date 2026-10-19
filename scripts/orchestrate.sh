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
LOG=logs/orchestrate_$(date +%Y%m%d_%H%M%S).log
for model in $MODEL_ORCH $MODEL_ORCH_FALLBACK; do
  claude -p --model $model --max-turns 60 --dangerously-skip-permissions --output-format json "$prompt" > $LOG.json 2> $LOG.err
  if python3 - "$LOG.json" "$LOG.err" <<'PY'
import json,sys,re
pat=re.compile(r'rate.?limit|usage.?limit|quota|exceeded|out of credits|insufficient|429|overloaded|not available|unknown model',re.I)
try: d=json.load(open(sys.argv[1]))
except Exception: sys.exit(0)
if d.get('is_error') or (not d.get('result') and pat.search(json.dumps(d)+open(sys.argv[2]).read())): sys.exit(0)
sys.exit(1)
PY
  then echo "$model unavailable, trying fallback"; continue; fi
  python3 -c 'import json,sys; print(json.load(open(sys.argv[1])).get("result",""))' $LOG.json | tee $LOG
  echo "orchestrator model used: $model" | tee -a $LOG; break
done
lake build 2>&1 | tail -5
git add -A && git commit -qm "skeleton from $NOTES" && git push -q
echo "Skeleton committed. Read the lemma statements in LogGas/ before the first nightly run."
