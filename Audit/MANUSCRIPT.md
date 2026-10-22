# Manuscript of record

Two documents are relevant, and they play different roles. Both are committed under `manuscript/`
with their SHA-256 recorded here (`shasum -a 256 -c Audit/manuscript.sha256`).

## A. What was formalized: the short draft

`manuscript/attractive_log_gas_short_draft.tex` / `.pdf` — *An entropy bound for the attractive
logarithmic gas*, M. G. Delgadino, R. Gvalani, M. Rosenzweig; 11 pp., dated 2026-10-05 (file
mtime), 789 lines.

* SHA-256 tex: `17683a036cc51de7317c3587795c2731884daa3e54f2b668e1a0cade1de83ad5`
* SHA-256 pdf: `2ba6ba8ec0d31f8d3727ce3741252909c8c85c536fd14de03961bc8f483c2b2b`

The project's `notes/sec*.tex` and `notes/appendixA.tex` are verbatim excerpts of this file (every
label used by the formalization — `thm:principal`, `lem:physical-local-count-bound`,
`lem:canonical-array-exponential`, `app:continuous-proof`, … — resolves in it; see
`tex_numbering.txt`). `verification/contracts.json` records the SHA-256 of each excerpt.

**Provenance caveat (from the short draft's own README, 2026-09-28):** "Theorem statements are
copied from the manuscript; the explanatory prose is Claude's paraphrase of the proofs and has
not been checked by the authors." The *proof route* formalized here (Sections 2–6 and
Appendix A of the short draft: cutoff split, bad event, Appendix-A cell projection, singular
part, canonical arrays) is therefore a paraphrase of the canonical paper's argument. The Lean
kernel checks that this route proves the stated theorem; the paraphrase's agreement with the
canonical proof is not part of the certificate and is not needed for it.

## B. Statement of record: the canonical manuscript

`manuscript/attractive_log_gas_I.tex` / `.pdf` — *Attractive log gas I* (canonical promotion
2026-09-18, 8663 lines).

* SHA-256 tex: `860c5be06d891e3146a7bad556952d268cbce4112389049c711f1f4db0f12b92`
* SHA-256 pdf: recorded in `manuscript.sha256`

Its Theorem `thm:principal` (line 448) is the paper's principal theorem. Part A(i), line 455:
"For every β₀ < β_gm, there is C = C(d, β₀) < ∞ such that sup_{N≥2} sup_{0≤β≤β₀} Z_{N,β} ≤ C"
(`eq:principal-order-one`, line 460). Here β_gm is the global-minimization threshold,
`eq:global-minimization-threshold` (line 418), and the paper notes (line 1328–1340) that for every
b < β_gm the macroscopic inequality `eq:strict-subcritical-macroscopic-inequality`
(line 1335) holds: H(μ | μ_unif) ≥ −b I_μ for every finite-entropy probability μ, where
−2 I_{ρ μ_unif} = ∬ g(x−y)(ρ(x)−1)(ρ(y)−1) (`eq:energy-operator-form`).

## C. How the two statements relate

The short draft's Theorem (line 163) is: *under (1.3) with constant B, for every 0 ≤ β₀ < B there
is C(d, B, β₀) with sup Z ≤ C.* This is what `LogGasPaper.PaperTheorem` formalizes
(`LogHLS g B` is the short draft's (1.3), equivalently the canonical (1.3) with b = B).

The canonical Part A(i) follows: given β₀ < β_gm choose B with β₀ < B < β_gm (and B ≤ 2d, since
β_gm ≤ β_coll = 2d by `eq:threshold-hierarchy-intro`); the canonical (1.3) gives `LogHLS g B`;
apply `PaperTheorem`. The value of β_gm (and hence that the theorem is not vacuous) is the
Beckner–Onofri input `thm:beckner-onofri-input`, which is **not** part of this formalization
(layer 4, to be imported).

## Files

```
manuscript/attractive_log_gas_short_draft.tex
manuscript/attractive_log_gas_short_draft.pdf
manuscript/attractive_log_gas_I.tex
manuscript/attractive_log_gas_I.pdf
Audit/manuscript.sha256
```
