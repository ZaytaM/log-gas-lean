# Deviations between the paper and the formal development

Reviewer: Claude Opus 5.5 (`claude-opus-5-5`), single direct session, 2026-10-21.
Paper side: `notes/*.tex`. Formal side: `Challenge.lean`, `Solution.lean`, `LogGas/*.lean`,
`verification/contracts.json`, and my standalone `PaperStatement.lean`.
I traced the *definitions the conclusions depend on*, not names or docstrings. Coverage is in
`COVERAGE.md`.

**Bottom line.** Nothing in the repository proves the paper's Theorem 1.1, the conditional
H1/H2 target `LogGasChallenge.principalStatement`, or Lemma 4.1 (`bulkStatement`).
`Solution.lean` contains only re-declared definitions; there are no inhabitants `principal` /
`bulk`. Proved and faithful: Lemma 6.1 (one-block and grouped), the §3 bad-event estimates, and
Lemma 5.1, each **for abstract interfaces**, plus some Appendix A ingredients. Absent: the
Appendix A bulk proof itself (Lemma 4.1), the §2 cutoff construction, every concrete torus/grid
/kernel instance, and the final assembly.

Classification key: **REP** representation change · **HARM** harmless proof/constant change ·
**STR** strengthened hypothesis / new assumption · **WEAK** weakened conclusion ·
**ABS** absent construction · **MISS** missing proof step · **GAP** genuine source gap ·
**UNCH** unchecked.

## A. Representation changes

| ID | Source | Formal | Exact difference | Class | Consequence | Required fix |
| --- | --- | --- | --- | --- | --- | --- |
| A1 | §1 l.127 `μ_unif` on `ℝ^d/ℤ^d` | `Challenge.Torus`, `uniform` | `Fin d → AddCircle 1`, `Measure.pi haarAddCircle` | REP | Faithful: period one, total mass one | none |
| A2 | §1 (1.2) `W_N`, `Z_{N,β}` | `Challenge.energy/weight/partition` | `(1/N)∑_i∑_{j∈univ.erase i} g(x_i−x_j)`; `lintegral` of `ofReal(exp((β/2)W))` over `Measure.pi` | REP | Faithful: ordered off-diagonal pairs, `1/N`, `β/2`, attractive sign; divergence is `⊤`, not `0` | none |
| A3 | §1 l.160 `sup_N sup_β Z ≤ C` | `principalStatement` | `∃ C : ℝ≥0, ∀ N ≥ 2, ∀ β ∈ [0,β₀], partition ≤ C` | REP | Faithful order for `N, β`; but `C` comes **after** `g` (see C2) | see C2 |
| A4 | §2 l.21; H2 "dist" | `Challenge.radius` vs `Singular.SingularKernel` (`dist z 0` of `E`) | Challenge uses the Euclidean torus radius; the abstract interface uses `E`'s metric. On `Fin d → AddCircle 1` Mathlib's metric is the **sup** (ℓ∞) metric | REP | The Euclidean H2 facts imply the sup-metric fields (`dist_∞ ≤ radius`), with `V = 2^d` for `ball_vol`; direction is harmless but must be proved | prove in the PSING bridge |
| A5 | §1 (1.5) boxes `J^{-1}(a+[0,1)^d)` | `BadEvent.Boxes` | any measurable partition into `M` sets of measure `1/M`; no geometry, no relation `M = J^d` | REP | Lemmas are more general; concrete grid never built (E3) | PGRID |
| A6 | §1 l.186 periodic adjacency | `Singular.lemma51` args `G`, `hdeg`; field `s_local` | adjacency = arbitrary `SimpleGraph (Fin M)` with degree `≤ 3^d−1`; locality is an assumed field | REP+STR | see C5 | PGRID/PSING |
| A7 | §2 (2.3) multinomial occupancy sum | `Singular.label_decomposition`, `occupancy_decomposition` | label vectors with weight `M^{-N}`; multinomial form also proved | REP | Faithful | none |
| A8 | §6 random index set `I` | `Decoupling.split_identity` etc. | `𝔼_I` = exact average over all `2^m` subsets | REP | Faithful | none |
| A9 | §2 kernels as functions; `s_r(0)=+∞` | `Challenge.cutoff` (a.e.) vs `SingularKernel` (pointwise `s_nonneg`, `s_even`, `s_supp`, `s_local`; a.e. `s_log`) | a.e. identities in the target vs pointwise in the interface; `s` real-valued | REP | Permissible: `X_i−X_j` is uniform, so only a.e. class matters; a representative (truncate to the a.e. bounds, zero outside radius `r`, symmetrize) keeps `g = b + s − c` a.e. and `c` unchanged. Evenness of `s` is only a.e. (from a.e. evenness of `g`, evenness of `b`, neg-invariance) | construct the representative in PSING; never specialize an a.e. fact at a point |
| A10 | App. A (A.2)–(A.7) projection `P_M`, `q_M ≤ M−1` | `Bulk` docstring l.33–41; `square_completion`, `gramReg`, `coarse` | planned regularization `Σ_ε = Σ+ε1`, `ε = 1/N`, exponent `M/2`, extra additive `M²` | REP/HARM (plan) | I checked the planned inequality chain (`2c·ℓ − cᵀΣc ≤ ℓᵀΣ_ε⁻¹ℓ + ε|c|²`, `|c|² ≤ M²`, Gaussian with `LᵀΣ_εL = 1`, `(Lg)ᵀΣ(Lg) ≤ |g|²`) — it is sound and avoids GAP F2 | execute it (E6) |

## B. Harmless proof / constant changes

| ID | Source | Formal | Exact difference | Class | Consequence | Fix |
| --- | --- | --- | --- | --- | --- | --- |
| B1 | §6 (6.3) universal `C_u` | `Decoupling.Cu := 16` | explicit; proof gives `(32e²)^k ≤ 16^{2k}` | HARM | none | none |
| B2 | §5 (5.5)–(5.6) | `aker_abs_le` (`4Cc`), `kappa Cc r = (8Cc+1)/log(1/r)`, `aker_exp_bound` (`r₁ = exp(−(8max(Cc,0)+1)·4t₀C_u)`) | explicit constants | HARM | none | none |
| B3 | §5 (5.8), (5.10) `κ_*`, `δ₀` | `kappaStar Cc V = 2max(V,1)max(3Cc,1)`; `δ₀ = 1/(16·3^d·C_u·κ_*·t₀)` | explicit; same condition `8KC_uκ_*t₀δ₀ ≤ 1/2` | HARM | `κ_*` independent of `J` as in paper | none |
| B4 | Lemma 5.1 "`J₀ ≥ 3`" | `lemma51` "`∃ r₀`, `K.r ≤ r₀`" | scale threshold instead of grid threshold; `M r^d ≤ 1` field links them | HARM | equivalent once `r = 1/(2J)`, `M = J^d` | PGRID |
| B5 | §3 (3.1) `= A_b^{N−1}`, `A_b ≥ 1` | `Warmup.prod_bound_indep`, `BadEvent.rough_bound` | `≤ A` for a.e. slice; `A ≥ 1` assumed (the paper proves it by Jensen; `one_le_integral_exp` exists) | HARM | none | none |
| B6 | §3 (3.2) | `chernoff_binomial`, `bad_probability` | requires `1/M < δ < 1`; bad event `δN < n_a` | HARM | paper has `0<δ<1` | none |
| B7 | §6 coloring "2K−1 colors" | `Grouped.greedy_edge_coloring` | same count (greedy needs only `2K−3`) | HARM | none | none |
| B8 | §6 (6.1)–(6.2) | `Decoupling.Hyp.h_int` | joint `|h_ij|^p` integrability for **all** ordered `(i,j)` | HARM | derivable by Tonelli from the moment bounds for `i<j`; unused kernels can be `0` | none |
| B9 | §3 N≥1 trivially | `prod_bound_indep`, `rough_bound`, `bad_gibbs_bound` need `2 ≤ N` | endpoint | HARM | theorem is for `N ≥ 2` | none |
| B10 | §6 grouped hypothesis "kernels between remaining pairs vanish" | `grouped_exp_bound` `hvan : ∀ x y, h i j x y = 0` | pointwise on all of `E×E` | HARM | discharged by `Singular.labelKer` (box indicators × kernel), which equals the kernel a.e. (`S_labelKer_ae`) | none |

## C. Strengthened hypotheses and new assumptions supplying upstream conclusions

| ID | Source | Formal | Exact difference | Class | Consequence | Required fix |
| --- | --- | --- | --- | --- | --- | --- |
| C1 | §2 (whole section) proves the cutoff | `notes/hypotheses.md` H2; `Challenge.cutoff g` premise of `principalStatement` | the entire §2 construction is **assumed** | STR (authorized) | conditional target ≠ paper theorem; paper's only premise is H1 | construct `χ, φ, s_r, b_r` for the paper's `g` and prove `cutoff g` (E2) |
| C2 | §1 (1.1) fixed `g`; `C = C(d,B,β₀)` | `principalStatement : ∀ d g B β₀, … → ∃ C` | `g` arbitrary measurable function; `C` chosen after `g` | STR/REP | a proof would not mention the paper's kernel; `C` may depend on `g` (harmless for one fixed `g`, but the identification is missing) | prove `IsLogKernel d g → (premises of principalStatement)` and move `C` before `g` via L¹ Fourier uniqueness + a.e.-invariance (cf. `PaperStatement.lean`) |
| C3 | §1 (1.3) | `Challenge.logHLS` | adds `Integrable (g(z₁−z₂)(ρ z₁−1)(ρ z₂−1))` for every finite-entropy `ρ` | STR (true domain fact) | strictly stronger premise unless one proves finite log energy for `L log L` densities (true: Young/exp-integrability, see `PAPER_THEOREM.md` §2) | prove the domain lemma for the paper's `g`; or use the conservative totalized form (`PaperStatement.LogHLS`) |
| C4 | §1 (1.1) consequences | `principalStatement` premises `Integrable g`, `∫g = 0`, `∀ᵐ x, g(−x) = g x` | stated as premises | STR (derivable) | for the paper's `g`: `∫g = ĝ(0) = 0` directly; evenness needs Fourier uniqueness or the H2 construction | prove from `IsLogKernel` |
| C5 | §1 l.185–187, §5 (5.8) torus geometry | `SingularKernel` fields `ball_vol`, `Mr`, `s_local`, `V_nonneg`; `lemma51` premise `hdeg`; `Boxes` | grid separation, `M r^d ≤ 1`, small-ball volume, degree `3^d−1` are **inputs** | STR (supplies PGRID conclusions) | `lemma51` is an implication from these facts | PGRID + PSING |
| C6 | §3 `A_b < ∞` for `b < 2d` | `rough_bound`, `Z_mono`, `bad_gibbs_bound` premises `hK_int`, `hKA`, `hA` | exponential slice integrability assumed | STR (supplies PEXP) | bad-event estimate is conditional on it | prove from H2 (`b` bounded, `s ≤ log_+(r/|x|)`, so `e^{(b/2)g} ≤ C·max(1,(r/|x|)^{b/2})`, integrable iff `b<2d`; translation invariance gives every slice; `A ≥ 1` by `one_le_integral_exp`) |
| C7 | Lemma 4.1 `K ∈ C(𝕋^d×𝕋^d)` | `Bulk.KHyp` | `bdd` (assumed boundedness) instead of continuity; no continuity field; `pos` on bounded `f`; `entropy` only for **bounded** densities | STR (bdd) / weaker (entropy) | a future `lemma41 (KHyp …)` would still need continuity + grid refinement for A6 | add continuity and refining grids when stating A6/A8 |
| C8 | §2 l.21 `b_r` satisfies (1.3) | `Challenge.cutoff` last field | domination `b`-form ≤ `g`-form only for **bounded** `f` | weaker than paper's Fourier ordering | transferring H1 to `b` for all finite-entropy densities (needed by `bulkStatement`) requires truncation `ρ_n = min(ρ,n)/∫min(ρ,n)` and limits | M2 (`Main.bulk_hypothesis`) |
| C9 | §2 l.20 "both centered parts PSD" | `Challenge.cutoff` `positive (s − c)` | assumed separately from domination | HARM (redundant) | given integrability, equivalent to the domination field; unused by the proof | none |

## D. Weakened conclusions

No weakening of quantifiers or bounds was found in the proved Lemmas 5.1/6.1/§3 statements; the only issue is the form below. (`principalStatement`'s `C`-after-`g` is listed as C2.)

| ID | Source | Formal | Exact difference | Class | Consequence | Required fix |
| --- | --- | --- | --- | --- | --- | --- |
| D1 | (3.1), (6.3), (6.4), (5.7), (5.10) | `prod_bound_indep`, `rough_bound`, `Z_mono`, `bad_gibbs_bound`, `exp_bound`, `grouped_exp_bound`, `block_*`, `aker_exp_bound`, `label_exp_bound_of_boxKernel` | conclusions are **Bochner** bounds `∫ exp(…) ≤ c`, which in Lean do not assert integrability (non-integrable ⇒ value `0`) | WEAK (form) | Each proof I read establishes integrability internally (`block_*` via `exp_bound`, not read in full) (`integrable_exp_W`; the cosh-series argument in `exp_bound`; local `E` in `grouped_exp_bound`; boundedness for `aker`/truncations), so the bounds are genuine, but the exported statements lose that fact. `lemma51` does export `Integrable ∧ bound`; `label_exp_bound` gives a `lintegral` bound | assembly must re-derive or export integrability; `BadEvent.integrable_exp_W` is available |

## E. Absent constructions and missing proof steps

| ID | Source | Formal (expected) | Status (verified by reading/grep) | Class | Consequence |
| --- | --- | --- | --- | --- | --- |
| E1 | §1 (1.1) kernel `g` | — | not constructed or characterized anywhere in `LogGas/`, `Challenge`, `Solution`; `PaperStatement.lean` characterizes it by Fourier coefficients only; `LogKernelExists` unproved | ABS | no formal object is "the paper's kernel" |
| E2 | §2 (2.1)–(2.2) | — | `χ`, `φ = χ*χ`, `s_r`, `c_r`, Fourier positivity `0 ≤ ŝ̃_r ≤ ĝ`, support, `0 ≤ φ ≤ φ(0)` ⇒ log bound, `c_r = O(r^d)`, smoothness of `b_r`: all absent (assumed as H2) | ABS | H2 unproved |
| E3 | §1 (1.5), adjacency, ball volume | `LogGas.Torus.grid` (PGRID) | absent; no `LogGas/Torus.lean` | ABS | `Boxes`, `G`, `hdeg`, `ball_vol`, `Mr`, `s_local` never instantiated |
| E4 | H2 → §5 interface | `LogGas.Physical.singular_instance` (PSING) | absent | ABS | `lemma51` never applied to an H2 kernel |
| E5 | §3 `A_b` | `LogGas.Physical.log_exp_integrable` (PEXP) | absent | ABS | `bad_gibbs_bound` never applied |
| E6 | App. A Steps 1–3, (A.1)–(A.11); Lemma 4.1 | `Bulk.histogram_box`, `empEnergy_split`, `empEnergy_le`, `dual_log_hls`, `empPair_cellFun`/`ell_hist`, `coarse_particle_factor`, `coarse_exp_bound`, `rJ_bound`, `W_le`/`W_le_coarse`, `lemma41` | **none declared**, although the `Bulk.lean` module docstring (l.21–31) lists them as its statements. Present: `gibbs_identity` (Gibbs identity only, not the dual inequality), `posDef_add_smul_one`, `square_completion` (matrix inequality only), `exists_sqrt_inv`, `stdGauss`, `gaussian_mgf_linear`, `gaussian_quadratic_integral`, `iid_exp_sum`, definitions `energy`, `T`, `cellFun`, `gram`, `gramReg`, `rJ`, `histCoef`, `hist`, `empEnergy`, `empPair`, `ell`, `coarse`, and `KHyp`. Missing mathematics: `ν_N(A_a)=0`; `⟨f_L,Tμ_N⟩ = c·ℓ`, `⟨f_L,Tf_L⟩ = cᵀΣc`; `⟨ν_N,Tν_N⟩ = ⟨μ_N,T_{r_J}μ_N⟩` (uses that `K−r_J` is cell-constant in one variable and `r_J` has zero box averages); the dual log-HLS `log∫e^{Th} ≤ ⟨h,Th⟩/(2B)` (Gibbs density + H1 + completing the square, `∫Th = 0` from centering/symmetry); Tonelli exchange of Gaussian and particle integrals; `‖r_J‖_∞ ≤ 4ω_K(√d/J) → 0` (uniform continuity + cell diameter); diagonal correction `5‖K‖_∞`; Hölder with `p,q`; D7 for `r_J` with `κ = ‖r_J‖_∞`, `θ = qβ`. The Gaussian lemmas and `KHyp` are **not** Lemma 4.1 | ABS/MISS | bulk factor of (2.4) unbounded formally; `bulkStatement` unproved |
| E7 | §2 l.21, §4 l.107 | `Main.bulk_hypothesis` (M2) | absent | MISS | `b_r` not shown to satisfy Lemma 4.1 hypotheses (continuity of `(x,y) ↦ b(x−y)`, symmetry, centering via translation invariance, PSD, H1 transfer per C8) |
| E8 | §2 (2.4) | `Main.holder_split` (M1) | absent. (`Singular.holder_split` exists but is the two-factor Hölder of (5.4), a different statement) | MISS | no formal good/bad split of `Z_{N,β}`; needs `W_N(g) = W_N(b_r)+W_N(s̃_r)` a.s. from the a.e. decomposition |
| E9 | §3 l.85, §5 "Conclusion" | `Main.parameter_choice` (M3) | absent; in particular no lemma `relEnt δ (1/M) → ∞` as `M → ∞` (D(δ‖M⁻¹) ≥ δ log(δM) + (1−δ)log(1−δ)), no choice of `s` with `sβ₀ < 2d`, no simultaneous choice `J ≥ J₀`, `J^{-d} < δ < 1`, exponent `< 0`, all independent of `N` | MISS | — |
| E10 | Thm 1.1 | `Main.theorem11` (M4); `LogGasChallenge.principal`, `LogGasChallenge.bulk` | absent; no `LogGas/Main.lean`; `Solution.lean` has no theorem at all | ABS | **no main result is proved** |
| E11 | paper statement | bridge `principalStatement ⇒ PaperTheorem` | absent (needs E1, E2, C3 domain lemma, C4, L¹ Fourier uniqueness — not in this Mathlib, which has only the L² Hilbert basis `mFourierBasis`) | ABS | even a proof of the conditional target would not yet certify the paper |

## F. Genuine source gaps (paper)

All are minor and fillable; none threatens the theorem.

| ID | Source | Gap | Fix |
| --- | --- | --- | --- |
| F1 | §2 l.21 "energy form bounded by that of g, so (1.3) with the same B" | Fourier comparison `b̂_r ≤ ĝ` gives form domination for `L²` (or smooth) densities, but (1.3) quantifies over all finite-entropy densities, not necessarily in `L²` | mollify `ρ`: entropy does not increase (Jensen), `b_r`-energy is continuous in `L¹` since `b_r` is bounded continuous |
| F2 | App. A l.81 "positivity extends from densities by approximation" | `⟨ν_N,Tν_N⟩ ≥ 0`-type use for the singular measure `ν_N` needs an approximation with continuity of `K` | mollify `ν_N`; or avoid it as in the project's regularized plan (A10) |
| F3 | App. A l.87 null directions | "take the minimizer modulo them" informal | regularization (A10) or quotient by the null space |
| F4 | §1 (1.3) | domain of the double integral left implicit | `PAPER_THEOREM.md` §2 (finite log energy for `L log L`) |
| F5 | §2 (2.4), §3 | `g = b_r + s̃_r` used at pair differences; only a.e. equality available (`s_r(0) = +∞`, `g` an `L²` class) | `X_i − X_j` is uniform for `i ≠ j`; state everything a.e. |
| F6 | Thm 1.1 `C(d,B,β₀)` | the proof also depends on the cutoff profile `χ` | fix `χ = χ_d` once per `d`; then the dependence is only on `(d,B,β₀)` |

Checked and **not** gaps: (1.1)/(2.2) normalization consistency (`c_d/(2π)^d = 1/|S^{d−1}|`);
`c_r = ‖φ‖₁r^d/(dφ(0))`; (3.1)–(3.3) (Jensen, conditional product, Chernoff, Hölder,
`A_b^{N−1} ≤ A_b^N`); (5.2)–(5.11) (centering of `a_r`, `h_r`; `∫|a_r| ≤ 4c_r`; moment-from-exponential;
`∫_{B_r}(log(r/|z|))^p = |B_r|p!/d^p`; locality of `h_r`; `u = 2t`); §6 counting
(`A ≤ 2^{4k}` for `m<2k`; `A B_k ≤ (4e²)^k m^{2k}`), grouped Hölder; App. A completed square,
(A.5)–(A.7) Gaussian identity, `‖r_J‖ ≤ 4ω` (even `2ω`), diagonal correction `≤ 5‖K‖_∞`, (A.11).

## G. Unchecked items

| ID | Item | Why unchecked |
| --- | --- | --- |
| G1 | Non-vacuity: some `g` and `B > 0` satisfy the Challenge premises (H1 for the torus log kernel) | literature fact (log-HLS on `𝕋^d`) outside the excerpt; no Lean witness exists (also noted by the fidelity review) |
| G2 | Line-by-line correctness of proof bodies I only sampled (see `COVERAGE.md`) | accepted on the strength of the recorded fresh build, axiom scan and `leanchecker` replay (`reports/verification-2026-10-21.md`); my audit targets statement fidelity |
| G3 | Fresh rebuild / `leanchecker` of `LogGas` in this session | not rerun (task forbids touching proof state; I compiled only my standalone file) |
| G4 | That `SingularKernel`/`Boxes` are instantiable on the actual torus with sup metric | argued informally (A4, A9), unproved |
| G5 | External Comparator | never run (recorded as unperformed) |
| G6 | `LogKernelExists`, and that `PaperTheorem` is equivalent to the paper rather than only implying it | needs E1 and L¹ uniqueness |

## H. Repository claims that overstate the state

* `LogGas/Bulk.lean` module docstring lists A1–A8 declarations that do not exist (E6).
* `verification/contracts.json` node A5 text "proved rather than assumed" describes a planned,
  absent declaration; names also disagree with the docstring (`ell_hist`/`W_le_coarse` vs
  `empPair_cellFun`/`W_le`).
* `notes/flags/Decoupling-Hyp-h_bdd.md` "No admitted proof bodies remain … 189 declarations"
  is accurate but concerns only declarations that exist; it is not coverage. The verification
  report and both reviews already say this correctly.
