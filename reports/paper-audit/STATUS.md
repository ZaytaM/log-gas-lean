# Paper theorem and proof-fidelity audit — STATUS

Model: `claude-opus-5-5` (single direct session, no subagents, no Git mutations).
State: IN PROGRESS (audit not finished). Proof is NOT complete.

## Progress log
- Read all seven source sections (`notes/00-preamble-macros.tex`, `sec1`–`sec6`, `appendixA.tex`),
  `notes/hypotheses.md`, `notes/hints.md`, `notes/phase0..5.md`, `notes/flags/*`,
  `Challenge.lean`, `Solution.lean`.
- First finding (checkpoint): `Solution.lean` re-declares the `Challenge.lean` definitions
  verbatim and contains NO inhabitant of `principalStatement` or `bulkStatement`.
  Neither the paper theorem nor the conditional H1/H2 target nor Lemma 4.1 is proved.

## Next
- Read `verification/`, reviews, final verification report, `LogGas/*.lean`.
- Read `verification/contracts.json`, both reviews, `reports/verification-2026-10-21.md`,
  `verification/README.md`, `VerificationAudit.lean` (header).
- Read Warmup (full), BadEvent (statements + B2/B3/B5/B6 proofs), Decoupling (Hyp, D1–D7
  statements, D6/D7 proofs), Grouped (G1 proof, G3 statement + integrability part),
  Singular (SingularKernel, BoxKernel, labelKer, hker_boxKernel, label_exp_bound, lemma51 proofs).
- Checkpoint finding: lemma51 is genuine for the *abstract* SingularKernel interface;
  the untruncated kernel is handled by truncation + Fatou (`label_exp_bound`), the truncated
  Bochner bound is backed by boundedness. No H2→SingularKernel instance exists.
- Read `LogGas/Bulk.lean` in full (402 lines). Checkpoint finding: the module docstring
  (lines 21–31) advertises `histogram_box`, `empEnergy_split`, `empEnergy_le`, `dual_log_hls`,
  `empPair_cellFun`, `coarse_particle_factor`, `coarse_exp_bound`, `rJ_bound`, `W_le`, `lemma41`;
  NONE of these is declared anywhere (grep-verified). Actual content: `gibbs_identity`,
  `posDef_add_smul_one`, `square_completion`, `exists_sqrt_inv`, `stdGauss`,
  `gaussian_mgf_linear`, `gaussian_quadratic_integral`, `iid_exp_sum`, definitions, `KHyp`.
  No `LogGas/Main.lean`, `LogGas/Torus.lean`, `LogGas/Physical.lean`.
