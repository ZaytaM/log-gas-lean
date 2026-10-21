# Paper theorem and proof-fidelity audit — STATUS

Model: `claude-opus-5-5` (single direct session on Dell3; no subagents, no other models, no Git
mutations). **Review state: FINISHED.** **Proof state: NOT complete.**

## Deliverables (all in `reports/paper-audit/`)

| File | Content |
| --- | --- |
| `PAPER_THEOREM.md` | Theorem 1.1 in full notation; H1 vs project H2; quantifier order; domain remark |
| `PaperStatement.lean` | standalone Mathlib-only specification `LogGasPaper.PaperTheorem` (+ `LogKernelExists`, `LogHLSWithDomain`, per-kernel variant); not a proof |
| `COMPILE_LOG.md` | exact commands and outputs (attempt 1 failed in a trivial lemma; attempt 2 exit 0; axioms clean) |
| `DEVIATIONS.md` | classified deviation table (A rep, B harmless, C strengthened, D weakened, E absent/missing, F source gaps, G unchecked, H overstated repo claims) |
| `COVERAGE.md` | what I read exhaustively vs sampled |

## Commands run and results

* `LEAN_PATH=<pinned package build dirs> lean reports/paper-audit/PaperStatement.lean` → exit 0, no
  output (27 s). The first attempt failed (exit 1) only because I used the wrong `intro` order in
  my own trivial lemma `PaperTheorem.perKernel`.
* Scratch copy with `#print axioms` in `.lake/paper-audit-scratch/` → exit 0; all four checked
  constants depend on `[propext, Classical.choice, Quot.sound]` only.
* `grep` over `*.lean` for the advertised Bulk/Main/Torus/Physical names and the
  `principal`/`bulk` inhabitants → no declarations (only docstrings/comments).
* I did not run any `lake` command, rebuild LogGas or rerun `leanchecker`; I relied on the recorded
  2026-10-21 fresh build, axiom scan and replay.

## Proof-readiness verdict

**Not proof-ready. Neither the paper's theorem nor the project's conditional target is proved.**

1. `Solution.lean` has no inhabitant of `principalStatement` or `bulkStatement`; `LogGas/Main.lean`
   does not exist.
2. **Proved and faithful at the abstract-interface level:** Lemma 6.1 one-block (`exp_bound`) and
   grouped (`grouped_exp_bound`) forms; §3 (`rough_bound`, `Z_mono`, `bad_probability`,
   `bad_gibbs_bound`); Lemma 5.1 (`lemma51`, with the untruncated log-singular kernel handled by
   truncation plus Fatou, no bounded-kernel premise). Their conclusions are genuine. Most export
   Bochner bounds without integrability (D1); this is harmless because the proofs establish it.
3. **Lemma 4.1 / Appendix A is absent.** `Bulk.lean` contains only ingredients (a Gibbs identity, a
   regularized matrix square completion, Gaussian integrals, i.i.d. factorization) plus
   definitions and `KHyp`. Its docstring lists ten A1–A8 declarations that do not exist. The
   planned regularized route is mathematically sound (I checked it).
4. **Everything concrete is absent:** the paper's kernel `g`, the §2 cutoff (assumed as H2), the
   torus grid/adjacency/ball-volume instance, the H2 → `SingularKernel` bridge with
   representatives, `A_b < ∞`, the transfer of H1 to `b_r`, the Hölder split, the parameter
   choice (including `D(δ‖1/M) → ∞`), and the assembly.
5. **Scope:** a proof of `principalStatement` would still only give the H1+H2 conditional
   statement for an arbitrary supplied `g`, with an extra energy-integrability premise and `C`
   chosen after `g`. Getting from there to the paper's H1-only theorem for the Fourier-normalized
   kernel also needs the §2 construction, the `L log L` domain lemma, and L¹ Fourier uniqueness on
   `𝕋^d`. That last one is not in this Mathlib, which has only the L² basis.
   `PaperStatement.lean` is the target such a bridge should reach.
6. **Paper:** I re-derived every display. The source argument is correct; the gaps are minor and
   fillable (F1–F6), e.g. extending the bulk log-HLS from `L²` densities to all finite-entropy
   densities by mollification.

## Remaining work (proof project, outside this audit)

In dependency order: PGRID (torus boxes) → PEXP, PSING (H2 → interfaces, a.e. representatives)
→ App. A (E6: A1, A2, A3 dual, A4, A5, A6 with continuity and refining grids, A7, A8 `lemma41`) →
`bulkStatement` → M2 (H1 transfer with truncation) → M1, M3 → M4 `principal` → kernel
construction, §2 cutoff, domain lemma, Fourier uniqueness → `PaperTheorem`.

**Next executable action:** implement `LogGas.Bulk` A1 (`ν_N(A_a) = 0`, i.e. the empirical mass
`n_a/N` of `A_a` equals `∫_{A_a} hist`) and A4 (the `ell`/`empPair` pairing identities) on the
existing definitions. Then do A3 `dual_log_hls` from `gibbs_identity`, `KHyp.entropy` and a
completed square. None of these needs a torus instance.

The audit itself is complete; `DONE.txt` contains `REVIEW_COMPLETE`. Audit completion is not proof
completion.
