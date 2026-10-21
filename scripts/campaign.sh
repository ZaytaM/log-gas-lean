#!/bin/bash
# One durable construction campaign; one publisher, no recursive model launches.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD
export PATH="$HOME/.local/bin:$PATH"
if [ -f "$HOME/.elan/env" ]; then source "$HOME/.elan/env"; fi
mkdir -p state/runtime/campaign logs/campaign
SESSION=loggas-main-campaign
case "${1:-status}" in
  start)
    if [ "${2:-}" = --automatic ]; then
      [ -e state/runtime/campaign/stop ] && exit 0
    else
      rm -f state/runtime/campaign/stop
    fi
    tmux has-session -t "=$SESSION" 2>/dev/null && exit 0
    if tmux has-session -t '=loggas-service' 2>/dev/null; then
      echo 'Stop the old proof-only service before starting the campaign.'; exit 1
    fi
    printf -v launch 'exec bash %q supervise' "$ROOT/scripts/campaign.sh"
    tmux new-session -d -s "$SESSION" "$launch"
    echo 'Started main theorem campaign.'
    ;;
  supervise)
    exec >> logs/campaign/controller.log 2>&1
    while [ ! -e state/runtime/campaign/stop ]; do
      set +e
      python3 scripts/campaign.py run
      rc=$?
      set -e
      [ "$rc" -eq 0 ] && exit 0
      printf '%s controller exit %s; preserving state, retry in 60 seconds\n' "$(date -Is)" "$rc"
      sleep 60
    done
    ;;
  install)
    current=$(mktemp)
    trap 'rm -f "$current" "$current.new"' EXIT
    crontab -l > "$current" 2>/dev/null || true
    cp "$current" "state/runtime/campaign/crontab-backup-$(date +%s)"
    sed '/# loggas-main-campaign$/d' "$current" > "$current.new"
    printf -v launch '/bin/bash %q start --automatic >> %q 2>&1' "$ROOT/scripts/campaign.sh" "$ROOT/logs/campaign/watchdog.log"
    printf '@reboot sleep 90 && %s # loggas-main-campaign\n' "$launch" >> "$current.new"
    printf '*/5 * * * * %s # loggas-main-campaign\n' "$launch" >> "$current.new"
    crontab "$current.new"
    bash scripts/campaign.sh start
    ;;
  status|stop) python3 scripts/campaign.py "$1" ;;
  *) echo 'Usage: campaign.sh start|install|stop|status'; exit 2 ;;
esac
