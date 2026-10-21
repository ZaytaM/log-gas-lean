# Coverage of this audit

"Exhaustive" = every line read and every displayed claim checked. "Statement" = declaration
statement/fields read and compared with the source; proof body not read line by line.
"Sampled" = proof body read in part. Nothing here is claimed beyond what is listed.

## Source (`notes/`) — exhaustive

| File | Lines | Coverage |
| --- | --- | --- |
| `00-preamble-macros.tex` | 124 | exhaustive (macros `\g`, `\Hr`, `\muunif`, `\d`, …) |
| `sec1-setting.tex` | 108 | exhaustive: (1.1)–(1.6), Thm 1.1, boxes, events, adjacency, figure caption |
| `sec2-cutoff.tex` | 46 | exhaustive; (2.1)–(2.4) re-derived (normalization constant checked) |
| `sec3-badevent.tex` | 39 | exhaustive; (3.1)–(3.3) re-derived |
| `sec4-bulk.tex` | 28 | exhaustive; Lemma 4.1 and (4.3) |
| `sec5-singular.tex` | 116 | exhaustive; Lemma 5.1 Steps 1–3 and Conclusion re-derived |
| `sec6-lemma61.tex` | 126 | exhaustive; (6.1)–(6.14) re-derived incl. counting |
| `appendixA.tex` | 180 | exhaustive; (A.1)–(A.11) re-derived; TikZ figure read only for content |
| `hypotheses.md`, `hints.md`, `phase0..5.md`, `flags/Decoupling-Hyp-h_bdd.md` | — | exhaustive |

## Specification and verification material — exhaustive

`Challenge.lean` (84 lines), `Solution.lean` (85), `verification/contracts.json`,
`verification/README.md`, `verification/reviews/mathematical-fidelity.md`,
`verification/reviews/lean-verification.md`, `reports/verification-2026-10-21.md`,
`reports/persistent.md`. Read in part: `VerificationAudit.lean` (first 80 lines: the audit
command), `reports/advisor-2026-10-21.md` (first 80 lines). Not read: the JSON receipts,
`reports/2026-10-19.md`, `reports/2026-10-20.md`, `scripts/`, `prompts/`, `state/`.

## Lean declarations (`LogGas/`)

Repository-wide grep confirmed that the advertised-but-missing names (`histogram_box`,
`empEnergy_split`, `empEnergy_le`, `dual_log_hls`, `empPair_cellFun`, `ell_hist`,
`coarse_particle_factor`, `coarse_exp_bound`, `rJ_bound`, `W_le`, `W_le_coarse`, `lemma41`,
`theorem11`, `bulk_hypothesis`, `parameter_choice`, `Torus.grid`, `singular_instance`,
`log_exp_integrable`, `LogGasChallenge.principal`, `LogGasChallenge.bulk`) occur only in comments or
docstrings, or nowhere; that `h_bdd` is gone; and that `exists_bound_S` is unreferenced.

| File | Lines | Coverage |
| --- | --- | --- |
| `Warmup.lean` | 165 | **exhaustive** (both theorems, proofs) |
| `Bulk.lean` | 402 | **exhaustive** (every declaration and proof; docstring compared with content) |
| `BadEvent.lean` | 707 | statements of all 16 declarations; proofs of `rough_bound`, `Z_mono`, `bad_probability`, `bad_gibbs_bound` read; `mgf_occupancy`, `chernoff_binomial` beginnings sampled; `integrable_exp_sum/W`, `holder_indicator`, `integral_exp_mul_le_rpow` statement only |
| `Decoupling.lean` | 1401 | definitions and `Hyp` exhaustive; statements of all D1–D7 declarations; `moment_bound`, `exp_bound` proofs exhaustive; `split_identity`, `random_split`, `vanishing_word`, `holder_group(_at)`, `word_moment`, `count_reduction`, `count_small`, `count_large`, `count_bound` sampled (first lines) |
| `Grouped.lean` | 980 | `greedy_edge_coloring` proof exhaustive; `exists_bound_S`, `block_exp_bound`, `block_factor` statements; `grouped_exp_bound` statement + its integrability sub-proof (first ~35 lines); `restrict`, `reindex`, `S_reindex`, `blocks_indep`, `class_mgf`, `class_bound`, `holder_classes`, `class_decomposition` names only |
| `Singular.lean` | 2767 | header, `SingularKernel`, `Sub`, `BoxKernel`, `labelKer`, `QJ/QJx/QJy`, `aker`, `hker`, `goodEvent`, `GoodLabel`, `labelMeasure`, `piN` exhaustive; statements of `aker_abs_le`, `aker_integral_le_right`, `moment_of_exp`, `aker_moment`, `hyp_aker`, `aker_exp_bound`, `log_moment`, `s_moment`, `box_ker_moment`, `hker_moment`, `label_decomposition`, `occupancy_decomposition`, `hyp_labels`, `S_labelKer_ae`, `label_exp_bound_of_boxKernel`, `hker_boxKernel`, `hyp_hker_labels`, `hker_trunc_boxKernel`, `label_exp_bound_trunc`, `holder_split`, `singular_holder`; proofs of `label_exp_bound` (truncation + Fatou) and `lemma51` exhaustive; centering lemmas, `hker_local`, `pi_eq_sum_labels`, `goodEvent_ae_iff`, `hker_trunc_tendsto` bodies **not** read |

Conclusion-bearing chain traced end to end: `lemma51` → `singular_holder`, `aker_exp_bound`,
`label_decomposition`, `label_exp_bound` → `label_exp_bound_trunc` →
`label_exp_bound_of_boxKernel` → `grouped_exp_bound` → `exp_bound` → `moment_bound`
(statements at every link; bodies as listed). `bad_gibbs_bound` → `holder_indicator`,
`Z_mono`, `rough_bound` → `Warmup.*`, `bad_probability` → `chernoff_binomial` (statements; bodies
as listed).

Correctness of unread proof bodies rests on the recorded fresh build, axiom scan of all
declarations, and `leanchecker` replay (2026-10-21), which I did not rerun (UNCH G2/G3).

## Mathematical comparisons required by the task — all addressed

Fixed vs supplied `g` (C2, E1, E11); H1-only vs H1/H2 (C1, `PAPER_THEOREM.md` §4); energy
integrability domain (C3, F4); torus/grid/adjacency/volume/cutoff instances (A4–A6, C5, E3–E5);
a.e. vs pointwise and representatives (A9, F5); unbounded kernel vs truncations, `h_bdd` repair,
integrable powers, a.e. centering/moments, limits (B8, B10, D1, Singular trace above);
Appendix A step inventory (E6); final Hölder split, inherited bulk hypotheses, parameter choice,
bad-event exponent, singular estimate, assembly (E7–E10, C8); constants and finite-`N` endpoints
(B1–B9); assumptions supplying unformalized upstream conclusions (C1, C3–C7).

## My own artefact

`PaperStatement.lean`: compiled (exit 0, no warnings) against the pinned Mathlib with direct
`lean`; `#print axioms` = `propext, Classical.choice, Quot.sound`. See `COMPILE_LOG.md`.
