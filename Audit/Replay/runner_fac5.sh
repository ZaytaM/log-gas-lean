#!/bin/bash
# Independent-kernel replay of the log-gas formalization on fac5 (Audit/Replay/DESIGN.md).
# Usage: bash runner_fac5.sh <run-name> <project-commit> [github-url]
# Everything lives under /tmp/loggas-replay-<run>/ (fac5 local disk); nothing under ~ is used or trusted.
set -euo pipefail
RUN=${1:?run name}; COMMIT=${2:?project commit}; URL=${3:-https://github.com/ZaytaM/log-gas-lean.git}
TOOLCHAIN=leanprover/lean4:v4.36.0-rc1
EXPORT_TAG=v4.36.0-rc1
NANODA_URL=https://github.com/ammkrn/nanoda_lib
P=/tmp/loggas-replay-$RUN; L=$P/log; mkdir -p "$L"
HERE=$(cd "$(dirname "$0")" && pwd)
export ELAN_HOME=$P/elan RUSTUP_HOME=$P/rustup CARGO_HOME=$P/cargo
export PATH=$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH
export HOME_ORIG=$HOME
rec() { python3 - "$P/receipt.json" "$@" <<'EOF'
import json, sys, pathlib
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text()) if p.exists() else {}
k, v = sys.argv[2], sys.argv[3]
try: v = json.loads(v)
except Exception: pass
d[k] = v; p.write_text(json.dumps(d, indent=2, sort_keys=True))
EOF
}
step() { echo "=== $(date -u +%FT%TZ) $*" | tee -a "$L/runner.log"; }
guard() { # stop if the shared host is short of memory or /tmp of disk
  local freemb=$(free -m | awk '/^Mem:/{print $7}'); local tmpgb=$(df -BG /tmp | awk 'NR==2{gsub("G","",$4); print $4}')
  [ "$freemb" -ge 4096 ] || { echo "free RAM ${freemb}MB < 4GB; stopping"; exit 3; }
  [ "$tmpgb" -ge 6 ] || { echo "/tmp free ${tmpgb}GB < 6GB; stopping"; exit 3; }
}
sha() { shasum -a 256 "$1" | cut -d" " -f1; }

step "0 preflight on $(hostname)"; guard
rec run "$RUN"; rec host "$(hostname)"; rec started_utc "$(date -u +%FT%TZ)"; rec project_commit "$COMMIT"; rec project_url "$URL"
uptime | tee "$L/uptime.txt"; nproc | tee "$L/nproc.txt"

step "1 toolchain into $ELAN_HOME"
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$P/elan-init.sh"
sh "$P/elan-init.sh" -y --no-modify-path --default-toolchain none > "$L/elan-init.log" 2>&1
elan toolchain install "$TOOLCHAIN" > "$L/elan-toolchain.log" 2>&1
TC=$(elan which lean --toolchain "$TOOLCHAIN" | xargs dirname)
"$TC/lean" --version | tee "$L/lean-version.txt"
rec toolchain "$TOOLCHAIN"; rec lean_version "$(cat "$L/lean-version.txt")"
rec lean_sha256 "$(sha "$TC/lean")"; rec lake_sha256 "$(sha "$TC/lake")"; rec leanchecker_sha256 "$(sha "$TC/leanchecker")"

step "2 rust + nanoda_lib"
curl -sSf https://sh.rustup.rs -o "$P/rustup-init.sh"
sh "$P/rustup-init.sh" -y --no-modify-path --profile minimal > "$L/rustup-init.log" 2>&1
git clone -q "$NANODA_URL" "$P/nanoda_lib"; NANODA_COMMIT=$(git -C "$P/nanoda_lib" rev-parse HEAD)
(cd "$P/nanoda_lib" && nice -n 19 cargo build --release -j 4 > "$L/nanoda-build.log" 2>&1)
NANODA=$P/nanoda_lib/target/release/nanoda_bin; [ -x "$NANODA" ]
rec nanoda_commit "$NANODA_COMMIT"; rec nanoda_sha256 "$(sha "$NANODA")"; rec rustc_version "$(rustc --version)"

step "3 lean4export $EXPORT_TAG"
git clone -q --branch "$EXPORT_TAG" https://github.com/leanprover/lean4export "$P/lean4export"
(cd "$P/lean4export" && nice -n 19 lake build > "$L/lean4export-build.log" 2>&1)
EXPORT=$P/lean4export/.lake/build/bin/lean4export; [ -x "$EXPORT" ]
rec lean4export_commit "$(git -C "$P/lean4export" rev-parse HEAD)"; rec lean4export_sha256 "$(sha "$EXPORT")"

step "4 project clone at $COMMIT"; guard
git clone -q "$URL" "$P/project"; (cd "$P/project" && git checkout -q "$COMMIT")
cd "$P/project"
[ "$(cat lean-toolchain)" = "$TOOLCHAIN" ] || { echo "lean-toolchain mismatch: $(cat lean-toolchain)"; exit 4; }
cmp -s lake-manifest.json verification/dependency-lock.json || { echo "manifest != dependency lock"; exit 4; }
shasum -a 256 -c Audit/frozen_statements.sha256 | tee "$L/frozen-check.txt"
shasum -a 256 -c Audit/manuscript.sha256 | tee "$L/manuscript-check.txt"
rec frozen_statements_ok true
nice -n 19 lake exe cache get > "$L/cache-get.log" 2>&1 || echo "cache get reported problems (see log); continuing with build"
guard
nice -n 19 lake build -j 4 PaperChallenge Challenge PaperSolution Solution > "$L/build.log" 2>&1
grep -c "declaration uses 'sorry'" "$L/build.log" | { read n; rec sorry_warnings "$n"; [ "$n" = 0 ]; }
tail -1 "$L/build.log" | tee -a "$L/runner.log"; rec build_tail "$(tail -1 "$L/build.log")"
rec mathlib_rev "$(python3 -c "import json;print([p['rev'] for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='mathlib'][0])")"

step "5 export"; guard
nice -n 19 lake env "$EXPORT" PaperChallenge Challenge > "$P/challenge.ndjson" 2> "$L/export-challenge.err"
nice -n 19 lake env "$EXPORT" PaperSolution Solution > "$P/solution.ndjson" 2> "$L/export-solution.err"
rec challenge_export_bytes "$(stat -c %s "$P/challenge.ndjson")"; rec challenge_export_sha256 "$(sha "$P/challenge.ndjson")"
rec solution_export_bytes "$(stat -c %s "$P/solution.ndjson")"; rec solution_export_sha256 "$(sha "$P/solution.ndjson")"
head -1 "$P/solution.ndjson" | tee "$L/export-meta.txt"

step "6 compare challenge vs solution exports"
set +e
python3 "$HERE/compare_exports.py" "$P/challenge.ndjson" "$P/solution.ndjson" \
  --target LogGasPaper.main:LogGasPaper.PaperTheorem --target LogGasPaper.kernel_exists:LogGasPaper.LogKernelExists \
  --target LogGasChallenge.principal:LogGasChallenge.principalStatement --target LogGasChallenge.bulk:LogGasChallenge.bulkStatement \
  --permitted-axioms propext Classical.choice Quot.sound --report "$L/compare-report.json" > "$L/compare.log" 2>&1
CMP=$?; set -e; rec compare_exit "$CMP"; tail -5 "$L/compare.log"

step "7 nanoda replay of the solution export"; guard
sed "s#EXPORT_FILE#$P/solution.ndjson#" "$HERE/nanoda_config.json" > "$P/nanoda_config.json"
set +e; nice -n 19 "$NANODA" "$P/nanoda_config.json" > "$L/nanoda.log" 2>&1; NAN=$?; set -e
rec nanoda_exit "$NAN"; rec nanoda_last_line "$(tail -1 "$L/nanoda.log")"; tail -3 "$L/nanoda.log"

step "8 leanchecker (Lean's own kernel, fresh env)"
set +e; nice -n 19 lake env leanchecker --fresh PaperSolution > "$L/leanchecker-paper.log" 2>&1; LC1=$?
nice -n 19 lake env leanchecker --fresh Solution > "$L/leanchecker-solution.log" 2>&1; LC2=$?; set -e
rec leanchecker_exit "[$LC1, $LC2]"

step "9 verdict"
rec finished_utc "$(date -u +%FT%TZ)"
if [ "$CMP" = 0 ] && [ "$NAN" = 0 ] && grep -q "no errors" "$L/nanoda.log"; then rec status ACCEPTED; else rec status NOT_ACCEPTED; fi
cp "$P/receipt.json" "$P/receipt-$RUN.json"; cat "$P/receipt-$RUN.json"
echo "receipt: $P/receipt-$RUN.json ; logs: $L ; copy both into Audit/Replay/ and commit from a trusted checkout"
