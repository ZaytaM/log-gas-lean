#!/bin/bash
# Assemble a self-contained fidelity-review package (snapshot + evidence) from the current commit.
# Usage: bash scripts/make_review_package.sh [outdir]   (default: review-package-<commit>)
# The package is what a fresh-context reviewer receives; see Audit/reviews/REVIEW_INSTRUCTIONS.md.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.local/bin:$PATH"; [ -f "$HOME/.elan/env" ] && source "$HOME/.elan/env"
[ -z "$(git status --porcelain)" ] || { echo "working tree not clean"; exit 1; }
commit=$(git rev-parse --short HEAD)
out=${1:-review-package-$commit}
rm -rf "$out"; mkdir -p "$out/snapshot" "$out/evidence" "$out/output"
git archive HEAD | tar -x -C "$out/snapshot"
git rev-parse HEAD > "$out/evidence/COMMIT.txt"
python3 - "$out/evidence/freeze.json" <<'EOF'
import sys, json; sys.path.insert(0, 'scripts')
from verify import freeze
json.dump(freeze(), open(sys.argv[1], 'w'), indent=2)
EOF
cp Audit/manuscript.sha256 "$out/evidence/"
cp Audit/statement_types.txt "$out/evidence/statement_types.txt"
latest=$(ls -d logs/verification/*/ | sort | tail -1)
cp "$latest/report.md" "$out/evidence/final-verification.md" 2>/dev/null || true
cp logs/campaign/final-verification.log "$out/evidence/final-verification.log" 2>/dev/null || true
cat > "$out/evidence/print_axioms.lean" <<'EOF'
import PaperSolution
import Solution
#print axioms LogGasPaper.main
#print axioms LogGasPaper.kernel_exists
#print axioms LogGasChallenge.principal
#print axioms LogGasChallenge.bulk
#print axioms LogGas.Main.theorem11
#print axioms LogGas.Bulk.lemma41
#print axioms LogGas.Singular.lemma51
#print axioms LogGas.BadEvent.bad_gibbs_bound
#print axioms LogGas.Decoupling.exp_bound
#print axioms LogGas.Grouped.grouped_exp_bound
#print axioms LogGas.Paper.paper_main
#print axioms LogGas.Paper.kernel_exists
#print axioms LogGas.Cutoff.cutoff_of_isLogKernel
#print axioms LogGas.Physical.singular_instance
#print axioms LogGas.Physical.log_exp_integrable
EOF
lake env lean "$out/evidence/print_axioms.lean" > "$out/evidence/print_axioms.txt"
cp Audit/reviews/REVIEW_INSTRUCTIONS.md "$out/INSTRUCTIONS.md"
(cd "$out" && find . -type f ! -name package.sha256 -print0 | sort -z | xargs -0 shasum -a 256 > package.sha256)
tar -czf "$out.tar.gz" "$out"
echo "package: $out.tar.gz ($(du -h "$out.tar.gz" | cut -f1)); commit $commit"
