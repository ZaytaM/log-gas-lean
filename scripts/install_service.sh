#!/bin/bash
# Install an idempotent per-user reboot/watchdog entry on Dell3, preserving other jobs.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD
mkdir -p state/runtime logs/service
current=$(mktemp)
trap 'rm -f "$current" "$current.new"' EXIT
crontab -l > "$current" 2>/dev/null || true
cp "$current" "state/runtime/crontab-backup-$(date +%Y%m%d%H%M%S)"
sed '/# loggas-persistent$/d' "$current" > "$current.new"
printf -v launch '/bin/bash %q start --automatic >> %q 2>&1' "$ROOT/scripts/service.sh" "$ROOT/logs/service/watchdog.log"
printf '@reboot sleep 90 && %s # loggas-persistent\n' "$launch" >> "$current.new"
printf '*/5 * * * * %s # loggas-persistent\n' "$launch" >> "$current.new"
crontab "$current.new"
if [ "${1:-}" != --no-start ]; then bash scripts/service.sh start; fi
echo 'Installed reboot recovery and five-minute watchdog; existing cron jobs retained.'
