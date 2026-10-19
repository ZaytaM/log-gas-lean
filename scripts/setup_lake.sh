#!/bin/bash
# setup_lake.sh — run ONCE on dell3 from the repo root. Makes this repo a Lake project
# with Mathlib, reusing the toolchain and Mathlib version already downloaded for
# ~/lean-work/leanproj, so no new multi-GB download is needed.
set -e
cd "$(dirname "$0")/.."
export PATH="$HOME/.local/bin:$PATH"; source ~/.elan/env
ulimit -n $(ulimit -Hn)
SRC=~/lean-work/leanproj
cp $SRC/lean-toolchain .
cp $SRC/lake-manifest.json .
cat > lakefile.toml <<'EOF'
name = "LogGas"
defaultTargets = ["LogGas"]

[[require]]
name = "mathlib"
scope = "leanprover-community"

[[lean_lib]]
name = "LogGas"
EOF
sed -i 's/"name": "leanproj"/"name": "LogGas"/' lake-manifest.json
cat > LogGas.lean <<'EOF'
import LogGas.Warmup
EOF
cat > LogGas/Warmup.lean <<'EOF'
import Mathlib
-- Phase 0 skeleton placeholder; scripts/orchestrate.sh notes/phase0.md rewrites this file.
namespace LogGas.Warmup
end LogGas.Warmup
EOF
# share the already-built Mathlib instead of rebuilding: symlink the package dir
mkdir -p .lake/packages
[ -e .lake/packages/mathlib ] || ln -s $SRC/.lake/packages/mathlib .lake/packages/mathlib
for p in batteries aesop Qq proofwidgets importGraph LeanSearchClient plausible Cli; do
  [ -e .lake/packages/$p ] || [ -e $SRC/.lake/packages/$p ] && ln -sfn $SRC/.lake/packages/$p .lake/packages/$p
done
lake build 2>&1 | tail -3
git add -A && git commit -qm "lake project setup" && git push -q
echo "Lake project ready."
