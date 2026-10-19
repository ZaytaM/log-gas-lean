#!/bin/bash
# pipeline.sh — one nightly formalization run. Run from the repo root on dell3,
# normally via:  dell3_run.sh ~/work/log-gas-lean cmd "bash scripts/pipeline.sh"
# Config: edit pipeline.conf (sourced below). Everything else is derived.
set -u
cd "$(dirname "$0")/.."
ROOT=$PWD
source scripts/pipeline.conf
export PATH="$HOME/.local/bin:$PATH"; [ -f ~/.elan/env ] && source ~/.elan/env
ulimit -n $(ulimit -Hn) 2>/dev/null
DATE=$(date +%F); NOW=$(date +%Y%m%d_%H%M%S)
mkdir -p logs/$NOW state advice notes/flags reports
RUN=logs/$NOW; SUMMARY=$RUN/summary.txt; : > $SUMMARY
log(){ echo "$(date +%T) $*" | tee -a $SUMMARY; }

# --- 0. shared-machine courtesy -------------------------------------------
LOAD=$(cut -d' ' -f1 /proc/loadavg | cut -d. -f1)
if [ "$LOAD" -gt "$LOAD_HALVE_ABOVE" ]; then MAX_WORKERS=$((MAX_WORKERS/2)); log "load $LOAD: workers halved to $MAX_WORKERS"; fi

# --- 1. sync and baseline build --------------------------------------------
git checkout -q main && git pull -q --ff-only
[ -d .lake/packages/mathlib/.lake/build ] || lake exe cache get >/dev/null
lake build 2>&1 | tail -3 | tee -a $SUMMARY
git worktree prune

# --- 2. open lemmas ---------------------------------------------------------
python3 scripts/open_lemmas.py LogGas/*.lean > $RUN/open.tsv
NOPEN=$(wc -l < $RUN/open.tsv); log "open lemmas: $NOPEN"
[ -f state/nights.tsv ] || : > state/nights.tsv

# --- cost accounting helpers ------------------------------------------------
COST_FILE=$RUN/cost.txt; : > $COST_FILE
cost_of(){ python3 -c 'import json,sys
try:
  d=json.load(open(sys.argv[1])); print(d.get("total_cost_usd",0))
except Exception: print(0)' "$1"; }
cost_total(){ awk '{s+=$1} END{printf "%.2f", s}' $COST_FILE; }
over_cap(){ awk -v c="$(cost_total)" -v cap="$NIGHT_COST_CAP_USD" 'BEGIN{exit !(c>cap)}'; }

# --- 3. workers, one per open lemma, bounded concurrency --------------------
run_worker(){ # file module lemma
  local file=$1 mod=$2 lem=$3 wt=wt/$3 br=wip/$3
  git worktree add -q -B $br $wt main 2>/dev/null || return
  local prompt; prompt=$(sed -e "s|{LEMMA_FILE}|$file|g" -e "s|{LEMMA_NAME}|$lem|g" \
                          -e "s|{MODULE}|$mod|g" -e "s|{MAX_ATTEMPTS}|$MAX_ATTEMPTS|g" prompts/worker.md)
  ( cd $wt && ln -sfn $ROOT/.lake .lake 2>/dev/null
    timeout ${WORKER_TIMEOUT}s claude -p --model $MODEL_WORKER --max-turns $MAX_TURNS \
      --dangerously-skip-permissions --output-format json "$prompt" > $ROOT/$RUN/$lem.json 2> $ROOT/$RUN/$lem.err
    python3 -c 'import json,sys; d=json.load(open(sys.argv[1])); print(d.get("result",""))' $ROOT/$RUN/$lem.json > $ROOT/$RUN/$lem.out 2>/dev/null )
  cost_of $RUN/$lem.json >> $COST_FILE
  grep -o 'STATUS=[a-z]* GOALS=[0-9]* ATTEMPTS=[0-9]*' $RUN/$lem.out | tail -1 | sed "s/^/$lem /" >> $RUN/status.txt \
    || echo "$lem STATUS=unknown GOALS=? ATTEMPTS=?" >> $RUN/status.txt
}
: > $RUN/status.txt
n=0
while IFS=$'\t' read -r file mod lem cnt; do
  over_cap && { log "cost cap reached, no more workers"; break; }
  run_worker "$file" "$mod" "$lem" &
  n=$((n+1)); [ $((n % MAX_WORKERS)) -eq 0 ] && wait
done < $RUN/open.tsv
wait
log "workers done; cost so far \$$(cost_total)"

# --- 4. merge progress into main --------------------------------------------
while read -r lem st rest; do
  br=wip/$lem
  git rev-parse -q --verify $br >/dev/null || continue
  [ "$(git rev-list --count main..$br)" -eq 0 ] && { git worktree remove -f wt/$lem; git branch -qD $br; continue; }
  if git merge -q --no-edit $br 2>/dev/null && lake build 2>&1 | grep -q "Build completed"; then
    log "merged $lem ($st)"
  else
    git merge --abort 2>/dev/null; git reset -q --hard main; log "merge failed for $lem, left on $br"
  fi
  git worktree remove -f wt/$lem 2>/dev/null
done < $RUN/status.txt

# --- 5. nights-open bookkeeping and advisor (minimal) -----------------------
python3 - "$RUN/status.txt" state/nights.tsv <<'EOF'
import sys
st={l.split()[0]:l.split()[1] for l in open(sys.argv[1]) if l.strip()}
old={}
for l in open(sys.argv[2]):
    p=l.split()
    if len(p)>=2: old[p[0]]=int(p[1])
new={lem:(old.get(lem,0)+1) for lem,s in st.items() if s!='STATUS=closed'}
open(sys.argv[2],'w').write('\n'.join(f"{k}\t{v}" for k,v in new.items())+'\n')
EOF
ADV=0
while IFS=$'\t' read -r lem nights; do
  [ "$nights" -lt "$ADVISOR_AFTER_NIGHTS" ] && continue
  [ "$ADV" -ge "$ADVISOR_MAX_PER_NIGHT" ] && break
  ls advice/$lem-* 2>/dev/null | tail -1 | grep -q "$(date -d "-$ADVISOR_COOLDOWN_DAYS days" +%F 2>/dev/null)" && continue
  line=$(grep -P "\t$lem\t" $RUN/open.tsv | head -1); file=$(cut -f1 <<<"$line")
  tex=$(ls notes/*.tex | tr '\n' ' ')
  alog=$(ls -t logs/*/$lem.out 2>/dev/null | head -3 | tr '\n' ' ')
  prompt=$(sed -e "s|{LEMMA_FILE}|$file|g" -e "s|{LEMMA_NAME}|$lem|g" -e "s|{TEX_FILES}|$tex|g" -e "s|{ATTEMPT_LOG}|$alog|g" prompts/advisor.md)
  claude -p --model $MODEL_ADVISOR --max-turns 20 --dangerously-skip-permissions --output-format json "$prompt" > $RUN/adv-$lem.json 2>/dev/null
  python3 -c 'import json,sys; print(json.load(open(sys.argv[1])).get("result",""))' $RUN/adv-$lem.json > advice/$lem-$DATE.md
  cost_of $RUN/adv-$lem.json >> $COST_FILE; ADV=$((ADV+1))
  if grep -q '^VERDICT=strategy' advice/$lem-$DATE.md; then
    printf '\n## %s (advisor %s)\n%s\n' "$lem" "$DATE" "$(sed 1d advice/$lem-$DATE.md)" >> notes/hints.md
  elif grep -q '^VERDICT=statement' advice/$lem-$DATE.md; then
    cp advice/$lem-$DATE.md notes/flags/$lem-statement.md
  fi
  log "advisor consulted for $lem"
done < state/nights.tsv

# --- 6. report ---------------------------------------------------------------
glog=$(git log --since="30 hours ago" --oneline | head -40 | tr '\n' ';')
prompt=$(sed -e "s|{RUN_SUMMARY}|$SUMMARY|g" -e "s|{STATUS_LINES}|$RUN/status.txt|g" -e "s|{ADVISOR_DIR}|advice|g" \
             -e "s|{GIT_LOG}|$glog|g" -e "s|{DATE}|$DATE|g" prompts/reporter.md)
echo "cost_usd_tonight=$(cost_total) advisor_calls=$ADV open_before=$NOPEN" >> $SUMMARY
claude -p --model $MODEL_REPORTER --max-turns 10 --dangerously-skip-permissions --output-format json "$prompt" > $RUN/report.json 2>/dev/null
python3 -c 'import json,sys; print(json.load(open(sys.argv[1])).get("result",""))' $RUN/report.json > reports/$DATE.md
grep -A1 '^## Tracker row' reports/$DATE.md | tail -1 >> state/tracker.md

# --- 7. publish ----------------------------------------------------------------
git add -A && git commit -qm "nightly $DATE: open=$NOPEN cost=\$$(cost_total) adv=$ADV" && git push -q
log "done"
