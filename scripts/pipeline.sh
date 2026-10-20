#!/bin/bash
# pipeline.sh — one nightly formalization run. Run from the repo root on dell3,
# normally via:  dell3_run.sh ~/work/log-gas-lean cmd "bash scripts/pipeline.sh"
# Config: edit pipeline.conf (sourced below). Everything else is derived.
# Exit status: 0 normal night; 1 the run was aborted (baseline build broken, or the
# model was unavailable for every worker) — nothing was proved, a stub report is written.
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
NOPEN=0; ADV=0
COST_FILE=$RUN/cost.txt; : > $COST_FILE
cost_of(){ python3 -c 'import json,sys
try:
  d=json.load(open(sys.argv[1])); print(d.get("total_cost_usd",0) or 0)
except Exception: print(0)' "$1"; }
cost_total(){ awk '{s+=$1} END{printf "%.2f", s}' $COST_FILE; }
over_cap(){ awk -v c="$(cost_total)" -v cap="$NIGHT_COST_CAP_USD" 'BEGIN{exit !(c>cap)}'; }
result_of(){ python3 -c 'import json,sys
try: print(json.load(open(sys.argv[1])).get("result",""))
except Exception: pass' "$1"; }
phases(){ cut -f1 $RUN/open.tsv 2>/dev/null | sed 's|LogGas/||;s|\.lean||' | sort -u | paste -sd, -; }
tracker_row(){ # closed attempts
  [ -s state/tracker.md ] || printf '| Date | Phase | Open lemmas | Closed tonight | Attempts | Advisor calls | Cost (USD) |\n|---|---|---|---|---|---|---|\n' > state/tracker.md
  echo "| $DATE | $(phases) | $NOPEN | $1 | $2 | $ADV | $(cost_total) |" >> state/tracker.md
}
abort_run(){ # reason
  log "ABORT: $1"
  printf '# Report %s\n\nRun aborted: %s\n\nNothing was proved or merged. Open lemmas: %s. Details: %s on dell3.\n' \
    "$DATE" "$1" "$NOPEN" "$RUN/summary.txt" > reports/$DATE.md
  tracker_row 0 0
  git add -A && git commit -qm "nightly $DATE: ABORTED ($1)" && git push -q
  exit 1
}

# --- 0. shared-machine courtesy -------------------------------------------
LOAD=$(cut -d' ' -f1 /proc/loadavg | cut -d. -f1)
if [ "$LOAD" -gt "$LOAD_HALVE_ABOVE" ]; then MAX_WORKERS=$((MAX_WORKERS/2)); log "load $LOAD: workers halved to $MAX_WORKERS"; fi

# --- 1. sync, clear leftovers from earlier runs, baseline build ---------------
git checkout -q main && git pull -q --ff-only
# A worktree or wip/ branch left behind makes `git worktree add` fail for that lemma, so
# the worker would silently never run (this is what happened on 2026-10-19). Clear them
# all; a branch that still holds unmerged commits is renamed failed/<lemma>-<run> and kept.
rm -rf wt; git worktree prune
for br in $(git for-each-ref --format='%(refname:short)' refs/heads/wip/); do
  if [ "$(git rev-list --count main..$br)" -gt 0 ]; then
    git branch -qm $br failed/${br#wip/}-$NOW; log "kept unmerged $br as failed/${br#wip/}-$NOW"
  else git branch -qD $br; fi
done
[ -d .lake/packages/mathlib/.lake/build ] || lake exe cache get >/dev/null
lake build > $RUN/build.log 2>&1; tail -3 $RUN/build.log | tee -a $SUMMARY
grep -q "Build completed successfully" $RUN/build.log || abort_run "baseline lake build failed on main"

# --- 2. open lemmas ---------------------------------------------------------
python3 scripts/open_lemmas.py LogGas/*.lean > $RUN/open.tsv
NOPEN=$(wc -l < $RUN/open.tsv | tr -d ' '); log "open lemmas: $NOPEN"
[ -f state/nights.tsv ] || : > state/nights.tsv

# --- 3. workers, one per open lemma, bounded concurrency --------------------
# Per lemma, the subshell leaves $RUN/<lemma>.rc = ok | timeout | unavailable.
run_worker(){ # file module lemma
  local file=$1 mod=$2 lem=$3 wt=wt/$3 br=wip/$3
  if ! git worktree add -q -B $br $wt main 2> $RUN/$lem.wt.err; then
    echo "$lem STATUS=failed GOALS=? ATTEMPTS=0" >> $RUN/status.txt
    log "$lem: git worktree add failed: $(head -1 $RUN/$lem.wt.err)"; return
  fi
  local prompt; prompt=$(sed -e "s|{LEMMA_FILE}|$file|g" -e "s|{LEMMA_NAME}|$lem|g" \
                          -e "s|{MODULE}|$mod|g" -e "s|{MAX_ATTEMPTS}|$MAX_ATTEMPTS|g" prompts/worker.md)
  ( cd $wt && ln -sfn $ROOT/.lake .lake 2>/dev/null
    echo unavailable > $ROOT/$RUN/$lem.rc
    for model in $MODEL_WORKER $MODEL_WORKER_FALLBACK; do
      timeout ${WORKER_TIMEOUT}s claude -p --model $model --max-turns $MAX_TURNS \
        --dangerously-skip-permissions --output-format json "$prompt" > $ROOT/$RUN/$lem.json 2> $ROOT/$RUN/$lem.err
      rc=$?
      if [ $rc -eq 124 ]; then echo timeout > $ROOT/$RUN/$lem.rc; echo "$lem model=$model timeout" >> $ROOT/$RUN/models.txt; break; fi
      if python3 $ROOT/scripts/quota_error.py $ROOT/$RUN/$lem.json $ROOT/$RUN/$lem.err; then
        echo "$(date +%T) $lem: $model unavailable: $(result_of $ROOT/$RUN/$lem.json | head -c 120 | tr '\n' ' ')" >> $ROOT/$SUMMARY
        continue
      fi
      echo ok > $ROOT/$RUN/$lem.rc; echo "$lem model=$model" >> $ROOT/$RUN/models.txt; break
    done
    result_of $ROOT/$RUN/$lem.json > $ROOT/$RUN/$lem.out )
  cost_of $RUN/$lem.json >> $COST_FILE
  local st; st=$(grep -o 'STATUS=[a-z]* GOALS=[0-9?]* ATTEMPTS=[0-9?]*' $RUN/$lem.out 2>/dev/null | tail -1)
  case "$(cat $RUN/$lem.rc 2>/dev/null)" in
    ok)      echo "$lem ${st:-STATUS=unknown GOALS=? ATTEMPTS=?}" >> $RUN/status.txt ;;
    timeout) echo "$lem ${st:-STATUS=timeout GOALS=? ATTEMPTS=?}" >> $RUN/status.txt ;;
    *)       echo "$lem STATUS=failed GOALS=? ATTEMPTS=0" >> $RUN/status.txt; touch $RUN/unavailable ;;
  esac
}
: > $RUN/status.txt; : > $RUN/models.txt
n=0
while IFS=$'\t' read -r file mod lem cnt; do
  over_cap && { log "cost cap reached, no more workers"; break; }
  if [ -e $RUN/unavailable ] && [ ! -s $RUN/models.txt ]; then
    log "model unavailable for every worker so far; not starting more"; break
  fi
  run_worker "$file" "$mod" "$lem" &
  n=$((n+1)); [ $((n % MAX_WORKERS)) -eq 0 ] && wait
done < $RUN/open.tsv
wait
log "workers done: $(grep -c . $RUN/status.txt) status lines, $(grep -c 'STATUS=closed' $RUN/status.txt) closed, $(grep -c 'STATUS=failed' $RUN/status.txt) failed; cost so far \$$(cost_total)"
[ "$NOPEN" -gt 0 ] && [ ! -s $RUN/models.txt ] && abort_run "model unavailable for every worker (quota/session limit); first message: $(grep -m1 unavailable: $SUMMARY | sed 's/.*unavailable: //')"

# --- 4. merge progress into main --------------------------------------------
while read -r lem st rest; do
  br=wip/$lem
  git rev-parse -q --verify $br >/dev/null || continue
  if [ "$(git rev-list --count main..$br)" -eq 0 ]; then git worktree remove -f wt/$lem 2>/dev/null; git branch -qD $br; continue; fi
  base=$(git rev-parse HEAD)
  if git merge -q --no-edit $br 2>/dev/null && lake build 2>&1 | grep -q "Build completed successfully"; then
    log "merged $lem ($st)"; git worktree remove -f wt/$lem 2>/dev/null; git branch -qD $br
  else
    git merge --abort 2>/dev/null; git reset -q --hard $base
    git worktree remove -f wt/$lem 2>/dev/null; log "merge failed for $lem, left on $br"
  fi
done < $RUN/status.txt

# --- 5. nights-open bookkeeping and advisor ---------------------------------
# A lemma's count grows only on a night a worker really tried it (not failed/no worker).
python3 - "$RUN/status.txt" "$RUN/open.tsv" state/nights.tsv <<'PY'
import sys
st={l.split()[0]:l.split()[1] for l in open(sys.argv[1]) if l.strip()}
opened=[l.split('\t')[2] for l in open(sys.argv[2]) if l.strip()]
old={}
for l in open(sys.argv[3]):
    p=l.split()
    if len(p)>=2: old[p[0]]=int(p[1])
new={}
for lem in opened:
    s=st.get(lem)
    if s=='STATUS=closed': continue
    tried = s is not None and s!='STATUS=failed'
    new[lem]=old.get(lem,0)+(1 if tried else 0)
open(sys.argv[3],'w').write(''.join(f"{k}\t{v}\n" for k,v in new.items()))
PY
CUTOFF=$(date -d "-$ADVISOR_COOLDOWN_DAYS days" +%F)
while IFS=$'\t' read -r lem nights; do
  [ -n "$lem" ] && [ -n "$nights" ] || continue
  [ "$nights" -lt "$ADVISOR_AFTER_NIGHTS" ] && continue
  [ "$ADV" -ge "$ADVISOR_MAX_PER_NIGHT" ] && break
  last=$(ls advice/$lem-????-??-??.md 2>/dev/null | sed 's/.*-\([0-9-]\{10\}\)\.md$/\1/' | sort | tail -1)
  [ -n "$last" ] && [[ "$last" > "$CUTOFF" ]] && continue
  line=$(grep -P "\t$lem\t" $RUN/open.tsv | head -1); file=$(cut -f1 <<<"$line")
  tex=$(ls notes/*.tex | tr '\n' ' ')
  alog=$(ls -t logs/*/$lem.out 2>/dev/null | head -3 | tr '\n' ' ')
  prompt=$(sed -e "s|{LEMMA_FILE}|$file|g" -e "s|{LEMMA_NAME}|$lem|g" -e "s|{TEX_FILES}|$tex|g" -e "s|{ATTEMPT_LOG}|$alog|g" prompts/advisor.md)
  claude -p --model $MODEL_ADVISOR --max-turns 20 --dangerously-skip-permissions --output-format json "$prompt" > $RUN/adv-$lem.json 2>/dev/null
  if python3 scripts/quota_error.py $RUN/adv-$lem.json; then log "advisor unavailable for $lem; skipping advisor"; break; fi
  result_of $RUN/adv-$lem.json > advice/$lem-$DATE.md
  cost_of $RUN/adv-$lem.json >> $COST_FILE; ADV=$((ADV+1))
  if grep -q '^VERDICT=strategy' advice/$lem-$DATE.md; then
    printf '\n## %s (advisor %s)\n%s\n' "$lem" "$DATE" "$(sed 1d advice/$lem-$DATE.md)" >> notes/hints.md
  elif grep -q '^VERDICT=statement' advice/$lem-$DATE.md; then
    cp advice/$lem-$DATE.md notes/flags/$lem-statement.md
  fi
  log "advisor consulted for $lem"
done < state/nights.tsv

# --- 6. report ---------------------------------------------------------------
CLOSED=$(grep -c 'STATUS=closed' $RUN/status.txt)
ATT=$(grep -o 'ATTEMPTS=[0-9]*' $RUN/status.txt | cut -d= -f2 | awk '{s+=$1} END{print s+0}')
glog=$(git log --since="30 hours ago" --oneline | head -40 | tr '\n' ';')
echo "cost_usd_tonight=$(cost_total) advisor_calls=$ADV open_before=$NOPEN closed=$CLOSED attempts=$ATT" >> $SUMMARY
prompt=$(sed -e "s|{RUN_SUMMARY}|$SUMMARY|g" -e "s|{STATUS_LINES}|$RUN/status.txt|g" -e "s|{OPEN_LIST}|$RUN/open.tsv|g" \
             -e "s|{NIGHTS_FILE}|state/nights.tsv|g" -e "s|{ADVISOR_DIR}|advice|g" \
             -e "s|{GIT_LOG}|$glog|g" -e "s|{DATE}|$DATE|g" prompts/reporter.md)
claude -p --model $MODEL_REPORTER --max-turns 10 --dangerously-skip-permissions --output-format json "$prompt" > $RUN/report.json 2>/dev/null
if python3 scripts/quota_error.py $RUN/report.json; then
  log "reporter unavailable; writing stub report"
  { printf '# Report %s\n\nReporter model unavailable; machine summary follows.\n\n```\n' "$DATE"; cat $SUMMARY; printf '```\n\n## Status lines\n```\n'; cat $RUN/status.txt; printf '```\n'; } > reports/$DATE.md
else
  result_of $RUN/report.json > reports/$DATE.md
fi
tracker_row "$CLOSED" "$ATT"

# --- 7. publish ----------------------------------------------------------------
git add -A && git commit -qm "nightly $DATE: open=$NOPEN closed=$CLOSED cost=\$$(cost_total) adv=$ADV" && git push -q
log "done"
