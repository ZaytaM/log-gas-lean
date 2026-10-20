#!/bin/bash
# Run on Dell3. The controller and supervisor survive SSH disconnects.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD
export PATH="$HOME/.local/bin:$PATH"
if [ -f "$HOME/.elan/env" ]; then source "$HOME/.elan/env"; fi
mkdir -p state/runtime logs/service
SESSION=loggas-service
case "${1:-status}" in
  start)
    if [ "${2:-}" = --automatic ]; then
      [ -e state/runtime/stop ] && exit 0
      if [ -f state/runtime/queue.sqlite3 ]; then
        completed=$(python3 -c 'import sqlite3; c=sqlite3.connect("state/runtime/queue.sqlite3"); r=c.execute("SELECT value FROM meta WHERE key=?",("service_state",)).fetchone(); print(r[0] if r else "")')
        [ "$completed" = complete ] && exit 0
      fi
    else
      rm -f state/runtime/stop
    fi
    if tmux has-session -t "=$SESSION" 2>/dev/null; then
      echo 'Persistent Lean service is already running.'
      exit 0
    fi
    if pgrep -u "$(id -u)" -f '^bash scripts/pipeline.sh$' >/dev/null; then
      echo 'A legacy pipeline is active; leaving it alone.'
      exit 1
    fi
    printf -v launch 'exec bash %q supervise' "$ROOT/scripts/service.sh"
    tmux new-session -d -s "$SESSION" "$launch"
    echo 'Started persistent Lean service (tmux: loggas-service).'
    ;;
  supervise)
    exec >> "$ROOT/logs/service/controller.log" 2>&1
    while [ ! -e state/runtime/stop ]; do
      set +e
      python3 scripts/persistent.py run
      rc=$?
      set -e
      [ "$rc" -eq 0 ] && exit 0
      printf '%s controller exited %s; retrying in 5 minutes\n' "$(date -Is)" "$rc"
      sleep 300
    done
    ;;
  stop) python3 scripts/persistent.py stop ;;
  status) python3 scripts/persistent.py status ;;
  retry-blocked) python3 scripts/persistent.py retry-blocked ;;
  *) echo 'Usage: service.sh start|stop|status|retry-blocked'; exit 2 ;;
esac
