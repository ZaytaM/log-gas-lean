# Statement map

Manuscript of record: see `MANUSCRIPT.md` (short draft `attractive_log_gas_short_draft.tex`, SHA-256
`17683a03…`; canonical `attractive_log_gas_I.tex`, SHA-256 `860c5be0…`). Line numbers "SD" refer to
the short draft, "C" to the canonical manuscript, "notes" to the excerpts under `notes/`.
Lean file:line refer to the freeze commit (`FREEZE.md`).

Legend: **REVIEW** = encoding choice the fidelity reviewer must judge; **NOTE** = recorded choice
that does not change content; **IMPORT** = depends on the layer-4 import.

## Block 1: the frozen statement layer (`PaperChallenge.lean`, namespace `LogGasPaper`)

| ID | TeX | Lean (file:line) | Encoding | Flag |
|---|---|---|---|---|
| P1 | §1 "𝕋^d = ℝ^d/ℤ^d", μ_unif (SD 134; C 160–165) | `Torus` :46, `uniform` :49 | `Fin d → AddCircle 1`; `Measure.pi` of `haarAddCircle` (mass one). Mathlib's metric on this type is the **sup** metric; the paper's `|x|` is Euclidean, so `radius` :56 is defined separately as the Euclidean norm of the representative in `(-1/2,1/2]^d`. | REVIEW (metric) |
| P2 | Fourier convention f̂(k) = ∫ f e^{-2πik·x} dμ (SD 142; C 1290) | `negCharacter` :60, `fourierCoeff` :64, `latticeNorm` :68 | complex-valued Bochner integral of `f · e^{-2πi k·x}`; `latticeNorm` is the Euclidean norm of k ∈ ℤ^d | NOTE |
| P3 | (1.1) kernel normalization, `eq:kernel-normalization` (SD 140; C 1296) | `cd` :72, `kernelCoeff` :76, `IsLogKernel` :80 | g is *characterized*, not constructed: `Measurable g ∧ Integrable g ∧ ∀ k, fourierCoeff g k = kernelCoeff d k`, with `kernelCoeff d 0 = 0`, `kernelCoeff d k = c_d/(2π|k|)^d`. Any two such g agree a.e. (L¹ Fourier uniqueness, proved in `LogGas/FourierUnique.lean`), and the theorem's conclusion only sees g a.e. | REVIEW (characterization vs. construction) |
| P4 | existence of g (C: `subsec:functional-domains`) | `LogKernelExists` :85 | `∀ d ≥ 2, ∃ g, IsLogKernel d g`; **proved** (`LogGasPaper.kernel_exists`) | — |
| P5 | g(x) = −log\|x\| + O_d(1) (SD 140; C `eq:kernel-local-form` 165) | `LogAsymptotic` :89 | recorded in a.e. form; **not a premise and not a conclusion** of `PaperTheorem` | NOTE |
| P6 | finite-entropy probability density (SD 156; C 1328) | `FiniteEntropyDensity` :93, `relEntropy` :98 | measurable, a.e. ≥ 0, integrable, ∫ρ = 1, ρ log ρ integrable; H = ∫ ρ log ρ dμ (real Bochner) | NOTE |
| P7 | (1.3) log-HLS, `eq:strict-subcritical-macroscopic-inequality` (SD 158; C 1335) | `logEnergy` :102, `LogHLS` :106 | `(B/2) · ∬ g(x−y)(ρ(x)−1)(ρ(y)−1) ≤ relEntropy ρ` for all finite-entropy ρ, with a **Bochner** double integral on μ⊗μ: if the integrand is not integrable Lean's value is 0 and the inequality is trivially true. So `LogHLS g B` is *weaker than or equal to* the paper's (1.3); the theorem assuming it is correspondingly *stronger*. `LogHLSWithDomain` :110 is the domain-explicit variant, not used by `PaperTheorem`. Canonical form: H(μ\|μ_unif) ≥ −b I_μ with −2 I_{ρμ} = ∬ g(x−y)(ρ−1)(ρ−1) (C `eq:energy-operator-form`), so b = B. | REVIEW (totalized integral) |
| P8 | (1.2) W_N, Z_{N,β}, `eq:homogeneous-partition-function` (SD 148; C 174) | `offDiagEnergy` :122, `partitionFunction` :126 | W_N = (1/N) Σ_{i≠j} g(x_i − x_j) over ordered pairs; Z = ∫⁻ ofReal(exp((β/2) W_N)) dμ^{⊗N} in `ℝ≥0∞`: divergence is `⊤`, never 0. Canonical writes β/(2N) Σ_{i≠j}; identical (C `eq:normalization-pair-sum-crosswalk`). | NOTE |
| P9 | **Theorem 1.1**, `thm:principal` (SD 163–169; C 448–460 Part A(i)) | `PaperTheorem` :134 | `∀ d ≥ 2, ∀ B ∈ (0, 2d], ∀ β₀ ∈ [0, B), ∃ C : ℝ≥0, ∀ g, IsLogKernel d g → LogHLS g B → ∀ N ≥ 2, ∀ β ∈ [0, β₀], partitionFunction g N β ≤ C`. Constant before g, N, β (paper: C = C(d, B, β₀)). Extra premise B ≤ 2d is harmless: β_gm ≤ 2d (C `eq:threshold-hierarchy-intro`). Relation to canonical Part A(i): `MANUSCRIPT.md` §C. | REVIEW (quantifier order, B ≤ 2d) |
| P10 | per-representative form | `PaperTheoremPerKernel` :142, `PaperTheorem.perKernel` :147 | weaker variant, proved from P9 trivially; not a target | NOTE |

## Block 1b: the conditional H1/H2 target (`Challenge.lean`, namespace `LogGasChallenge`)

| ID | TeX | Lean | Encoding | Flag |
|---|---|---|---|---|
| Q1 | §1–§2 with H1 (1.3) and H2 (`notes/hypotheses.md`) as hypotheses | `principalStatement` :63 | ∀ d, g, B, β₀: premises `Integrable g`, `∫ g = 0`, a.e. even, `logHLS g B` (with explicit domain), `cutoff g` (H2) → ∃ C, ∀ N ≥ 2, β ≤ β₀, `partition g N β ≤ C`. C is chosen **after** g here (audit C2); this is the intermediate target, superseded by P9. | NOTE (superseded) |
| Q2 | Lemma 4.1 `lem:continuous-entropy-partition` (SD 336) for the torus | `bulkStatement` :72 | continuous symmetric K with PSD form dominated by H1 → uniform partition bound | NOTE |

## Block 2: milestone statements of the proof (types frozen via `statement_types.txt`)

| ID | TeX | Lean (file:line) | Meaning / encoding | Flag |
|---|---|---|---|---|
| D7 | Lemma 6.1 `lem:canonical-array-exponential` (SD 484), `eq:canonical-array-exponential` (SD 504) | `LogGas/Decoupling.lean:1296` `exp_bound` | independent canonical arrays with a.e. centering, factorial moment bounds (`Hyp`); ∫ exp(θ S/m) ≤ 2/(1 − (C_u κ\|θ\|)²), C_u = 16 (paper: universal constant) | NOTE (explicit constants) |
| G3 | `eq:canonical-grouped-exponential` (SD 511) | `LogGas/Grouped.lean:796` `grouped_exp_bound` | grouped version with adjacency graph of degree ≤ K−1 and vanishing non-adjacent kernels; bound (8/3)^M | NOTE |
| B6 | §3 `eq:physical-bad-gibbs-bound` (SD 327) | `LogGas/BadEvent.lean:641` `bad_gibbs_bound` | bad-event Gibbs mass ≤ M^{1/s'} exp(N(log A/s − D(δ‖1/M)/s')); exponential slice integrability `hK_int`, `hKA` as premises (discharged by PEXP) | NOTE |
| S8 | Lemma 5.1 `lem:physical-local-count-bound` (SD 366) | `LogGas/Singular.lean:2638` `lemma51` | abstract singular-kernel interface `SingularKernel`; existence of δ₀, r₀; good-event bound (8/3)^{(M+1)/2}; instantiated by PSING | REVIEW (interface fields `ball_vol`, `s_local` on the sup metric, audit A4/C5) |
| A1 | App. A (A.1) (SD 617) | `LogGas/BulkHist.lean:49` `histogram_box` | ∫_{A_a} hist = n_a/N | — |
| A2 | App. A (A.2)–(A.4) | `LogGas/BulkSplit.lean:209,254` `empEnergy_split`, `empEnergy_le` | **regularized** Gram form Σ_ε = Σ + εI instead of the paper's projection P_M and null directions (audit A10, F2/F3); extra additive ε M² | REVIEW (proof deviation, same conclusion) |
| A3 | (A.5) `eq:dual-log-hls` (SD 719) | `LogGas/BulkDual.lean:147` `dual_log_hls` | log ∫ e^{Th} ≤ energy(h,h)/(2B) under `KHyp` (bounded K, symmetric, centered, PSD, entropy inequality on bounded densities) | NOTE (`KHyp.bdd` instead of continuity, audit C7) |
| A4 | (A.6) | `LogGas/Milestones.lean:36` `ell_hist` | ⟨hist, T·⟩ pairing = c·ℓ | — |
| A5 | (A.7) `eq:coarse-partition-estimate` (SD 741) | `LogGas/BulkCoarse.lean:92` `coarse_exp_bound` | Gaussian coarse bound (1 − t/B)^{−M/2} with integrability asserted | — |
| A6 | (A.9) `eq:continuous-small-remainder` (SD 755) | `LogGas/Milestones.lean:44` `rJ_bound` | continuity ⇒ remainder r_J uniformly small on the torus grid | — |
| A7 | (A.10) `eq:diagonal-correction-bound` (SD 763) | `LogGas/BulkSplit.lean:313` `W_le_coarse` | W ≤ N·coarse + M² + W(r_J) + 5 C_K | NOTE (explicit 5‖K‖_∞) |
| A8 | Lemma 4.1 `lem:continuous-entropy-partition` (SD 336) | `LogGas/BulkLemma41.lean:53` `lemma41` | abstract E, probability μ_E, `KHyp` + refining grids (`hgrid`) → ∃ C uniform in N, β ≤ β₀ < B, with integrability | — |
| M1 | (2.4) `eq:physical-cutoff-holder` (SD 287) | `LogGas/MainHolder.lean:19` `holder_split` | Hölder split of the lintegral over an event | — |
| M2 | §2 l.21 b_r satisfies Lemma 4.1 hypotheses | `LogGas/MainBulkHyp.lean:18` `bulk_hypothesis` | from bounded-density H1 (`boundedH1`), continuity, evenness, mean zero, positivity and form domination on bounded tests ⇒ `KHyp` (audit C8/F1 avoided: only bounded densities needed) | NOTE |
| M3 | §3 and §5 parameter choice (SD 305–330, 453–470) | `LogGas/Milestones.lean:94` `parameter_choice` | bad-event lintegral ≤ C(J) uniformly in N, β ≤ β₀ < 2d | — |
| M4 | Theorem 1.1 conditional form (SD 163) | `LogGas/MainTheorem.lean:32` `theorem11` | `boundedH1 g B` + `cutoff g` (H2) ⇒ ∃ C, partition ≤ C | — |
| PGRID | (1.5) `eq:common-box-partition` (SD 178) | `LogGas/TorusGrid.lean:104` `grid` (def), `adj` | J^d equal-volume cells of the torus as `Boxes`; periodic adjacency of degree ≤ 3^d − 1 | REVIEW (sup-metric cells vs. paper cubes — identical sets) |
| PSING | §2 (2.1)–(2.2) `eq:compact-positive-log-split` (SD 254) → §5 interface | `LogGas/PhysicalSing.lean:78` `singular_instance` | a.e. hypotheses on s (support in radius r, ≤ log₊(r/\|x\|), mass ≤ C_c r^d) ⇒ a `SingularKernel` with a symmetrized a.e. representative | REVIEW (a.e.→pointwise bridge, audit A9) |
| PEXP | §3 A_b < ∞ for b < 2d | `LogGas/Milestones.lean:56` `log_exp_integrable` | exp(α log₊(r/\|z\|)) ∈ L¹ for α < d | — |
| H2 | §2 construction (SD 245–290) | `LogGas/Cutoff*.lean`, `LogGas.Cutoff.cutoff_of_isLogKernel` | H2 is **proved** for every `IsLogKernel` kernel (was an assumption in `notes/hypotheses.md`) | NOTE |
| KERNEL | (1.1) existence | `LogGas/KernelExists.lean:101` `kernel_exists` | constructs g with the prescribed Fourier coefficients | — |
| PAPER | Theorem 1.1 | `LogGas/PaperMain.lean:25` `paper_main` : `paperTheorem` | `LogGas.Paper.paperTheorem` is a verbatim copy of `LogGasPaper.PaperTheorem` over the library's copies of the challenge definitions (`LogGas.Torus.T/unif/radius`, `LogGas.Fourier.IsLogKernel`, `LogGas.Spec.partition/paperLogHLS`); `PaperSolution.lean:152` `main := paper_main` type-checks against the frozen `PaperTheorem` (verify gate `paper-proof-contracts`) | — |

## Block 3: hypotheses

| ID | Status |
|---|---|
| H1 (1.3) | hypothesis of `PaperTheorem` (`LogHLS g B`), as in the paper. Satisfiability for some B > 0 (and the value β_gm) is the Beckner–Onofri input, `thm:beckner-onofri-input` of the canonical manuscript: **IMPORT** (layer 4). |
| H2 (§2 cutoff) | no longer a hypothesis; proved (`cutoff_of_isLogKernel`). |

## Open statements

None: every declaration above is proved with axioms `propext`, `Classical.choice`, `Quot.sound`
(evidence `logs/verification/20261022T042658Z/`). The open item is not a statement but the
satisfiability of H1 (Block 3).
