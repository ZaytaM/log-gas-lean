import Mathlib

/-!
# Phase 1 — Lemma 6.1 (`lem:canonical-array-exponential`), one-block bound (6.3)

Source: `notes/sec6-lemma61.tex`.  Phase notes: `notes/phase1.md`.

Setting.  `(Ω, μ)` is a probability space, `Y : Fin m → Ω → E` are independent with laws
`ν i`, and `h : Fin m → Fin m → E → E → ℝ` are bounded measurable kernels, used only for
`i < j`.  The transpose convention `h_{ji}(y,x) = h_{ij}(x,y)` of the paper is implemented
by `ext`.  Essential suprema of the paper are replaced by pointwise bounds (phase notes).

The Bernoulli(1/2) index set `I` "independent of `Y`" is modelled by the exact average
`(∑ I : Finset (Fin m), ·) / 2 ^ m` over all subsets: `𝔼_I[F(I)] = 2^{-m} ∑_I F(I)`.

Standing hypotheses of the lemma are collected in the `Prop`-structure `Hyp`; the standing
hypotheses H1/H2 of `notes/hypotheses.md` are not needed in this phase.

Statements (phase notes D1–D7):
* D1 `split_identity`   — eq. `eq:array-split-identity` (6.5)
* D2 `random_split`     — eq. `eq:array-random-split` (6.6)
* D3 `vanishing_word`   — vanishing of monomials with a label of multiplicity one
* D4 `holder_group`, `word_moment` — eqs. `eq:array-holder-group` (6.9),
  `eq:array-word-moment` (6.10); `count_reduction` — eq. `eq:array-count-reduction` (6.11)
* D5 `count_small`, `count_large`, `count_bound` — eq. `eq:array-combinatorial-bound` (6.12)
* D6 `moment_bound`     — first half of eq. `eq:canonical-array-exponential` (6.3)
* D7 `exp_bound`        — second half of (6.3), via eq. `eq:array-exponential-series` (6.13)

The universal constant is fixed as `Cu = 16` (the proof produces `(32 e²)^k ≤ 16^{2k}`).
-/

set_option autoImplicit false
-- The probability-measure instances below are section variables; some elementary lemmas
-- do not use them, which would otherwise trigger this linter.
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal Nat

namespace LogGas.Decoupling

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-! ### Definitions -/

section Defs

variable {m : ℕ}

/-- Extension of the kernels `h i j`, `i < j`, to all ordered pairs by the transpose
convention `h_{ji}(y,x) = h_{ij}(x,y)`; the diagonal is zero ("zero kernels are allowed"). -/
def ext (h : Fin m → Fin m → E → E → ℝ) (i j : Fin m) (x y : E) : ℝ :=
  if i < j then h i j x y else if j < i then h j i y x else 0

/-- `S = ∑_{i<j} h_{ij}(Y_i, Y_j)`. -/
def S (h : Fin m → Fin m → E → E → ℝ) (Y : Fin m → Ω → E) (ω : Ω) : ℝ :=
  ∑ i, ∑ j ∈ Ioi i, h i j (Y i ω) (Y j ω)

/-- `D_I = ∑_{i ∈ I, j ∉ I} h_{ij}(Y_i, Y_j)` with the extended kernels. -/
def D (h : Fin m → Fin m → E → E → ℝ) (Y : Fin m → Ω → E) (I : Finset (Fin m)) (ω : Ω) : ℝ :=
  ∑ i ∈ I, ∑ j ∈ Iᶜ, ext h i j (Y i ω) (Y j ω)

/-- Multiplicity `a_ℓ = #{v : w v = ℓ}` of the label `ℓ` in the word `w`
(eq. `eq:row-multiplicity`). -/
def mult {n : ℕ} (w : Fin n → Fin m) (ℓ : Fin m) : ℕ :=
  (univ.filter (fun v => w v = ℓ)).card

/-- The monomial `T = ∏_v h_{i_v j_v}(Y_{i_v}, Y_{j_v})` indexed by a row word `row` and a
column word `col`. -/
def word (h : Fin m → Fin m → E → E → ℝ) (Y : Fin m → Ω → E) {n : ℕ}
    (row col : Fin n → Fin m) (ω : Ω) : ℝ :=
  ∏ v, ext h (row v) (col v) (Y (row v) ω) (Y (col v) ω)

/-- `A`: the number of multiplicity vectors `(a_ℓ)_{ℓ ≤ m}` with `∑ a_ℓ = 2k` and no entry
equal to `1` (entries are bounded by `2k`, so we range over `Fin m → Fin (2k+1)`). -/
def A (m k : ℕ) : ℕ :=
  (univ.filter (fun a : Fin m → Fin (2 * k + 1) =>
    ∑ ℓ, (a ℓ : ℕ) = 2 * k ∧ ∀ ℓ, (a ℓ : ℕ) ≠ 1)).card

/-- `B_k`: the number of words of length `2k` on `m` labels in which no label occurs exactly
once. -/
def B (m k : ℕ) : ℕ :=
  (univ.filter (fun w : Fin (2 * k) → Fin m => ∀ ℓ, mult w ℓ ≠ 1)).card

/-- The universal constant `C_u` of Lemma 6.1, fixed as `16`. -/
def Cu : ℝ := 16

/-- Standing hypotheses of Lemma 6.1 (`lem:canonical-array-exponential`):
independence of the `Y i` with laws `ν i`, measurable bounded kernels, centering
(eq. `eq:canonical-array-centering`, 6.1) and the factorial moment bounds
(eq. `eq:canonical-array-kernel-moments`, 6.2), with essential suprema replaced by pointwise
bounds. -/
structure Hyp (μ : Measure Ω) (ν : Fin m → Measure E) (Y : Fin m → Ω → E)
    (h : Fin m → Fin m → E → E → ℝ) (κ : ℝ) : Prop where
  κ_pos : 0 < κ
  Y_meas : ∀ i, Measurable (Y i)
  Y_indep : iIndepFun Y μ
  Y_law : ∀ i, μ.map (Y i) = ν i
  h_meas : ∀ i j, Measurable (Function.uncurry (h i j))
  h_bdd : ∀ i j, ∃ C : ℝ, ∀ x y, |h i j x y| ≤ C
  /-- (6.1), first variable. -/
  centered_left : ∀ i j, i < j → ∀ y, ∫ x, h i j x y ∂(ν i) = 0
  /-- (6.1), second variable. -/
  centered_right : ∀ i j, i < j → ∀ x, ∫ y, h i j x y ∂(ν j) = 0
  /-- (6.2), first variable. -/
  moment_left : ∀ i j, i < j → ∀ p : ℕ, 1 ≤ p → ∀ y,
    ∫ x, |h i j x y| ^ p ∂(ν i) ≤ 2 * κ ^ p * (p.factorial : ℝ)
  /-- (6.2), second variable. -/
  moment_right : ∀ i j, i < j → ∀ p : ℕ, 1 ≤ p → ∀ x,
    ∫ y, |h i j x y| ^ p ∂(ν j) ≤ 2 * κ ^ p * (p.factorial : ℝ)

end Defs

/-! ### Lemmas -/

variable {m : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Fin m → Measure E}
  [∀ i, IsProbabilityMeasure (ν i)] {Y : Fin m → Ω → E}
  {h : Fin m → Fin m → E → E → ℝ} {κ : ℝ}

-- SKETCH: unfold `ext`, `split_ifs`, and discharge the impossible branches with
-- `lt_asymm` / `lt_irrefl` (or `omega` after `Fin.lt_def`).
omit [MeasurableSpace E] in
/-- The transpose convention `h_{ji}(y,x) = h_{ij}(x,y)` holds for the extended kernel. -/
theorem ext_symm (h : Fin m → Fin m → E → E → ℝ) (i j : Fin m) (x y : E) :
    ext h j i y x = ext h i j x y := by
  unfold ext; split_ifs <;> first | rfl | exact absurd ‹_› (lt_asymm ‹_›)

-- SKETCH: case split `i < j` / `j < i` / `i = j`.  First case is `H.centered_left`;
-- second is `H.centered_right j i` with the roles of `x, y` swapped (definitional after
-- `unfold ext`, `if_neg`, `if_pos`); third case integrates the zero function
-- (`integral_zero`).
/-- Eq. `eq:canonical-array-centering` (6.1) for the extended kernel: the first-variable
average of `ext h i j · y` under `ν i` vanishes for every `y`. -/
theorem ext_centered (H : Hyp μ ν Y h κ) (i j : Fin m) (y : E) :
    ∫ x, ext h i j x y ∂(ν i) = 0 := by
  unfold ext; split_ifs <;>
    first | exact H.centered_left _ _ ‹_› y | exact H.centered_right _ _ ‹_› y | simp

-- SKETCH: same case split as `ext_centered`; the diagonal case gives `∫ 0 = 0 ≤ 2κ^p p!`
-- using `H.κ_pos` (`pow_pos`, `Nat.cast_pos.2 (Nat.factorial_pos p)`).  Off-diagonal
-- cases are `H.moment_left` and `H.moment_right`.
/-- Eq. `eq:canonical-array-kernel-moments` (6.2) for the extended kernel, first variable. -/
theorem ext_moment (H : Hyp μ ν Y h κ) (i j : Fin m) (p : ℕ) (hp : 1 ≤ p) (y : E) :
    ∫ x, |ext h i j x y| ^ p ∂(ν i) ≤ 2 * κ ^ p * (p.factorial : ℝ) := by
  unfold ext; split_ifs <;> first | exact H.moment_left _ _ ‹_› p hp y | exact H.moment_right _ _ ‹_› p hp y | (have := H.κ_pos; simp [Nat.pos_iff_ne_zero.1 hp]; positivity)

-- SKETCH (D1): rewrite `D h Y I ω` as `∑ i, ∑ j, (if i ∈ I ∧ j ∉ I then ext h i j .. else 0)`
-- (`Finset.sum_filter`, `Finset.mem_compl`), swap the sum over `I` inside
-- (`Finset.sum_comm`), and count: for `i ≠ j` exactly `2^(m-2)` subsets contain `i` but
-- not `j` (`Finset.card_powerset`-style counting, or `Fintype.card_subtype` with the
-- bijection `I ↦ I \ {i,j}`), while the diagonal contributes `0` (`ext h i i = 0`).  Then
-- pair `(i,j)` with `(j,i)` via `ext_symm` and `Finset.sum_sigma`/`Finset.sum_Ioi_add_sum_Iio`
-- style splitting to recover `2 * 2^(m-2) * S = 2^m * (S / 2)`.
/-- Eq. `eq:array-split-identity` (6.5): averaging `D_I` over all `2^m` index sets `I`
gives `S/2`, for every fixed sample `ω`. -/
theorem split_identity (h : Fin m → Fin m → E → E → ℝ) (Y : Fin m → Ω → E) (ω : Ω) :
    (∑ I : Finset (Fin m), D h Y I ω) / 2 ^ m = S h Y ω / 2 := by
  sorry

-- SKETCH (D2): pointwise, `S ω = 2 * avg_I D_I ω` by `split_identity`, so
-- `|S ω|^(2k) = 2^(2k) * |avg_I D_I ω|^(2k) ≤ 2^(2k) * avg_I |D_I ω|^(2k)` by Jensen for the
-- convex function `x ↦ |x|^(2k)` (`(even_two_mul k).convexOn_pow` after `Even.pow_abs`,
-- with `ConvexOn.map_sum_le` and the uniform weights `2⁻¹^m`, `Finset.card_univ`,
-- `Fintype.card_finset`).  Integrate with `integral_mono`, `integral_finset_sum`,
-- `integral_const_mul`, `integral_div`; integrability from `H.h_meas`, `H.h_bdd`, `H.Y_meas`
-- via `Integrable.of_bound` (all integrands are bounded measurable, `μ` finite).
/-- Eq. `eq:array-random-split` (6.6): `𝔼|S|^{2k} ≤ 2^{2k} 𝔼_I 𝔼|D_I|^{2k}`. -/
theorem random_split (H : Hyp μ ν Y h κ) (k : ℕ) :
    ∫ ω, |S h Y ω| ^ (2 * k) ∂μ
      ≤ 2 ^ (2 * k) * ((∑ I : Finset (Fin m), ∫ ω, |D h Y I ω| ^ (2 * k) ∂μ) / 2 ^ m) := by
  sorry

-- SKETCH (D3): by `ext_symm` (transposing `row ↔ col`) it suffices to treat a row label
-- `ℓ` with `mult row ℓ = 1`, i.e. `row v₀ = ℓ` for a unique `v₀` (`Finset.card_eq_one`).
-- Since rows lie in `I` and columns in `Iᶜ`, `ℓ` is not a column label, so
-- `word = ext h ℓ (col v₀) (Y ℓ) (Y (col v₀)) * R` with `R` a bounded measurable function of
-- `(Y j)_{j ≠ ℓ}` (`Finset.prod_erase_mul`).  `Y ℓ` is independent of `(Y j)_{j ≠ ℓ}`
-- (`H.Y_indep.indepFun_finset {ℓ} {ℓ}ᶜ`), so the law of the pair is the product measure
-- (`indepFun_iff_map_prod_eq_prod_map_map`, `H.Y_law`); rewrite with `integral_map` and
-- `integral_prod` (Fubini), and the inner `ν ℓ`-integral vanishes by `ext_centered`.
/-- Vanishing monomials: if some label occurs exactly once in the row word or in the column
word of a term of the expansion of `D_I^{2k}`, its expectation is `0` (uses (6.1) and
independence). -/
theorem vanishing_word (H : Hyp μ ν Y h κ) {n : ℕ} (I : Finset (Fin m))
    (row col : Fin n → Fin m) (hrow : ∀ v, row v ∈ I) (hcol : ∀ v, col v ∉ I)
    (hone : (∃ ℓ, mult row ℓ = 1) ∨ (∃ ℓ, mult col ℓ = 1)) :
    ∫ ω, word h Y row col ω ∂μ = 0 := by
  sorry

-- SKETCH (6.9): with `a = mult row ℓ ≥ 1`, Hölder with `a` equal exponents `1/a`:
-- `|∫ ∏_v f_v| ≤ ∫ ∏_v |f_v| ≤ ∏_v (∫ |f_v|^a)^(1/a)` (`abs_integral_le_integral_abs`,
-- `ENNReal.lintegral_prod_norm_pow_le` with `p v = 1/a`, `∑ p v = 1`, translated to Bochner
-- integrals via `ofReal_integral_eq_lintegral_ofReal` for the nonnegative bounded
-- integrands).  Each factor is `≤ (2 κ^a a!)^(1/a)` by `ext_moment`; the product of `a`
-- such factors is `2 κ^a a!` (`Real.rpow_natCast`, `Finset.prod_const`, `Real.rpow_mul`).
/-- Eq. `eq:array-holder-group` (6.9): for a row label `ℓ` of multiplicity `a_ℓ ≥ 1`
and frozen column values `y`,
`|Φ_ℓ(y)| = |𝔼 ∏_{v : i_v = ℓ} h_{ℓ j_v}(Y_ℓ, y_{j_v})| ≤ 2 κ^{a_ℓ} a_ℓ!`. -/
theorem holder_group (H : Hyp μ ν Y h κ) {n : ℕ} (ℓ : Fin m) (row col : Fin n → Fin m)
    (hℓ : 1 ≤ mult row ℓ) (y : Fin m → E) :
    |∫ x, ∏ v ∈ univ.filter (fun v => row v = ℓ), ext h ℓ (col v) x (y (col v)) ∂(ν ℓ)|
      ≤ 2 * κ ^ (mult row ℓ) * ((mult row ℓ).factorial : ℝ) := by
  classical
  have hmeas : ∀ v, Measurable fun x => ext h ℓ (col v) x (y (col v)) := by
    intro v; unfold ext; split_ifs
    · exact (H.h_meas _ _).comp (measurable_id.prodMk measurable_const)
    · exact (H.h_meas _ _).comp (measurable_const.prodMk measurable_id)
    · exact measurable_const
  have hbdd : ∀ i j : Fin m, ∃ C : ℝ, ∀ x y, |ext h i j x y| ≤ C := by
    intro i j; unfold ext; split_ifs
    · exact H.h_bdd _ _
    · obtain ⟨C, hC⟩ := H.h_bdd j i
      exact ⟨C, fun x y => hC y x⟩
    · exact ⟨0, by simp⟩
  set s := univ.filter (fun v => row v = ℓ) with hsdef
  set a := mult row ℓ with ha
  have hs : s.card = a := rfl
  have ha1 : 1 ≤ a := hℓ
  set F : Fin n → E → ℝ := fun v x => |ext h ℓ (col v) x (y (col v))| with hF
  have hFm : ∀ v, Measurable (F v) := fun v => (hmeas v).abs
  have hF0 : ∀ v x, 0 ≤ F v x := fun v x => abs_nonneg _
  have hFint : ∀ v, Integrable (fun x => F v x ^ a) (ν ℓ) := by
    intro v
    obtain ⟨C, hC⟩ := hbdd ℓ (col v)
    refine Integrable.of_bound ((hFm v).pow_const a).aestronglyMeasurable (C ^ a)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (hF0 v x) a)]
    exact pow_le_pow_left₀ (hF0 v x) (hC _ _) a
  have key : ∫⁻ x, ENNReal.ofReal (∏ v ∈ s, F v x) ∂(ν ℓ)
      ≤ ENNReal.ofReal (2 * κ ^ a * (a.factorial : ℝ)) := by
    have hp : ∑ v ∈ s, (1 / (a : ℝ)) = 1 := by
      rw [Finset.sum_const, hs, nsmul_eq_mul]
      have : (a : ℝ) ≠ 0 := by positivity
      field_simp
    calc ∫⁻ x, ENNReal.ofReal (∏ v ∈ s, F v x) ∂(ν ℓ)
        = ∫⁻ x, ∏ v ∈ s, (ENNReal.ofReal (F v x) ^ (a : ℝ)) ^ (1 / (a : ℝ)) ∂(ν ℓ) := by
          congr 1; ext x
          rw [ENNReal.ofReal_prod_of_nonneg (fun v _ => hF0 v x)]
          refine Finset.prod_congr rfl fun v _ => ?_
          rw [← ENNReal.rpow_mul]
          have : (a : ℝ) ≠ 0 := by positivity
          rw [mul_one_div_cancel this, ENNReal.rpow_one]
      _ ≤ ∏ v ∈ s, (∫⁻ x, ENNReal.ofReal (F v x) ^ (a : ℝ) ∂(ν ℓ)) ^ (1 / (a : ℝ)) := by
          refine ENNReal.lintegral_prod_norm_pow_le s (fun v _ => ?_) hp (fun v _ => by positivity)
          exact ((hFm v).ennreal_ofReal.pow_const _).aemeasurable
      _ ≤ ∏ v ∈ s, (ENNReal.ofReal (2 * κ ^ a * (a.factorial : ℝ))) ^ (1 / (a : ℝ)) := by
          refine Finset.prod_le_prod' fun v _ => ?_
          refine ENNReal.rpow_le_rpow ?_ (by positivity)
          calc ∫⁻ x, ENNReal.ofReal (F v x) ^ (a : ℝ) ∂(ν ℓ)
              = ∫⁻ x, ENNReal.ofReal (F v x ^ a) ∂(ν ℓ) := by
                congr 1; ext x
                rw [ENNReal.ofReal_pow (hF0 v x), ← ENNReal.rpow_natCast]
            _ = ENNReal.ofReal (∫ x, F v x ^ a ∂(ν ℓ)) :=
                (ofReal_integral_eq_lintegral_ofReal (hFint v)
                  (ae_of_all _ fun x => pow_nonneg (hF0 v x) a)).symm
            _ ≤ _ := ENNReal.ofReal_le_ofReal (ext_moment H ℓ (col v) a ha1 (y (col v)))
      _ = ENNReal.ofReal (2 * κ ^ a * (a.factorial : ℝ)) := by
          rw [Finset.prod_const, hs, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          have : (a : ℝ) ≠ 0 := by positivity
          rw [one_div_mul_cancel this, ENNReal.rpow_one]
  calc |∫ x, ∏ v ∈ s, ext h ℓ (col v) x (y (col v)) ∂(ν ℓ)|
      ≤ ∫ x, |∏ v ∈ s, ext h ℓ (col v) x (y (col v))| ∂(ν ℓ) := abs_integral_le_integral_abs
    _ = ∫ x, ∏ v ∈ s, F v x ∂(ν ℓ) := by simp [hF, Finset.abs_prod]
    _ = (∫⁻ x, ENNReal.ofReal (∏ v ∈ s, F v x) ∂(ν ℓ)).toReal :=
        integral_eq_lintegral_of_nonneg_ae
          (ae_of_all _ fun x => Finset.prod_nonneg fun v _ => hF0 v x)
          (Finset.measurable_prod s fun v _ => hFm v).aestronglyMeasurable
    _ ≤ (ENNReal.ofReal (2 * κ ^ a * (a.factorial : ℝ))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top key
    _ = 2 * κ ^ a * (a.factorial : ℝ) :=
        ENNReal.toReal_ofReal (by have := H.κ_pos; positivity)

-- SKETCH (D4, 6.10): condition on the column block.  `(Y i)_{i ∈ I}` and `(Y j)_{j ∈ Iᶜ}`
-- are independent (`H.Y_indep.indepFun_finset I Iᶜ disjoint_compl_right`), so by
-- `indepFun_iff_map_prod_eq_prod_map_map`, `integral_map`, `integral_prod` the expectation
-- is `∫ (∫ word dP_I) dP_{Iᶜ}`; the row-block law `P_I` is `Measure.pi (fun i : I => ν i)`
-- (`iIndepFun_iff_map_fun_eq_pi_map` applied to `H.Y_indep.precomp Subtype.val_injective`).
-- Group the product by row label (`Finset.prod_fiberwise univ row`) and factor the
-- `Measure.pi`-integral (`integral_fintype_prod_eq_prod`); this is (6.8).  Bound each
-- active factor by `holder_group`, inactive labels (`a_ℓ = 0`) give `1`.  Finally
-- `∏_{active} 2 = 2^#active ≤ 2^k` since every active `a_ℓ ≥ 2` and `∑ a_ℓ = 2k`
-- (`Finset.sum_fiberwise`, `Finset.card_nsmul_le_sum`), and `∏_ℓ κ^{a_ℓ} = κ^{2k}`
-- (`Finset.prod_pow_eq_pow_sum`); `abs_integral_le_integral_abs`, `integral_mono`.
/-- Eq. `eq:array-word-moment` (6.10): for a surviving row word (no multiplicity equal to
one), `|𝔼 ∏_{v=1}^{2k} h_{i_v j_v}(Y_{i_v}, Y_{j_v})| ≤ 2^k κ^{2k} ∏_ℓ a_ℓ!`. -/
theorem word_moment (H : Hyp μ ν Y h κ) (k : ℕ) (I : Finset (Fin m))
    (row col : Fin (2 * k) → Fin m) (hrow : ∀ v, row v ∈ I) (hcol : ∀ v, col v ∉ I)
    (hsurv : ∀ ℓ, mult row ℓ ≠ 1) :
    |∫ ω, word h Y row col ω ∂μ|
      ≤ 2 ^ k * κ ^ (2 * k) * ∏ ℓ, ((mult row ℓ).factorial : ℝ) := by
  sorry

-- SKETCH: group the words by their multiplicity vector `w ↦ mult w` (`Finset.sum_fiberwise`
-- / `Finset.sum_comp`).  The fibre over `a` has `Nat.multinomial univ a = (2k)! / ∏ a_ℓ!`
-- elements (`Nat.multinomial_spec`; the count of words with prescribed fibre sizes is
-- obtained by induction on `m` with `Finset.card_eq_of_equiv`, or via `Sym`/`Multiset`
-- `Multiset.card_filter`), so each fibre contributes exactly `(2k)!`.  The multiplicity
-- vectors that occur are exactly those counted by `A m k` (entries `≤ 2k`, sum `2k`, no `1`),
-- and `Finset.card_le_card_of_injOn` for the map into `Fin m → Fin (2k+1)`.
/-- Counting step inside eq. `eq:array-count-reduction` (6.11): "there are
`(2k)!/∏ a_ℓ!` row words with given multiplicities, so the factorials cancel":
`∑_{surviving row words} ∏_ℓ a_ℓ! ≤ (2k)! · A`. -/
theorem sum_factorial_mult (m k : ℕ) :
    ∑ w ∈ (univ : Finset (Fin (2 * k) → Fin m)).filter (fun w => ∀ ℓ, mult w ℓ ≠ 1),
        ∏ ℓ, ((mult w ℓ).factorial : ℝ)
      ≤ ((2 * k).factorial : ℝ) * A m k := by
  sorry

-- SKETCH (6.11): `|D_I|^(2k) = D_I^(2k)` (`pow_abs_two_mul`); expand
-- `D_I = ∑_{p ∈ I ×ˢ Iᶜ} f p` to the `2k`-th power as a sum over words
-- `Fin (2k) → I ×ˢ Iᶜ` (`Finset.sum_pow'`, `Finset.prod_univ_sum`), i.e. over pairs
-- `(row, col)` with `row v ∈ I`, `col v ∉ I`; so `∫ D_I^(2k) = ∑_{(row,col)} ∫ word`
-- (`integral_finset_sum`, integrability by boundedness).  Terms with a multiplicity-one
-- label vanish (`vanishing_word`); the others are bounded by `word_moment`
-- (`Finset.abs_sum_le_sum_abs`).  Sum over surviving `col` first (at most `B m k` of them,
-- `Finset.card_le_card` since columns in `Iᶜ` are a subset of all surviving words), then
-- over surviving `row` with `sum_factorial_mult`.
/-- Eq. `eq:array-count-reduction` (6.11): `𝔼|D_I|^{2k} ≤ 2^k κ^{2k} (2k)! A B_k`. -/
theorem count_reduction (H : Hyp μ ν Y h κ) (k : ℕ) (I : Finset (Fin m)) :
    ∫ ω, |D h Y I ω| ^ (2 * k) ∂μ
      ≤ 2 ^ k * κ ^ (2 * k) * ((2 * k).factorial : ℝ) * (A m k * B m k : ℕ) := by
  sorry

-- SKETCH (D5, case m < 2k): `A ≤ #{weak compositions of 2k into m parts}
-- = (2k+m-1).choose (m-1) ≤ 2^(2k+m-1) ≤ 2^(4k)` (`Nat.choose_le_two_pow`,
-- `Nat.pow_le_pow_right`; the composition count via `Finset.card_le_card_of_injOn` into
-- `Finset.Nat.antidiagonalTuple m (2k)` and `Finset.Nat.card_antidiagonalTuple` /
-- `Nat.card_multichoose`), and `B ≤ #(Fin (2k) → Fin m) = m^(2k)` (`Finset.card_filter_le`,
-- `Fintype.card_fun`, `Fintype.card_fin`).  Cast with `Nat.cast_le`, `Nat.cast_mul`.
/-- Eq. `eq:array-combinatorial-bound` (6.12), small-`m` case: if `m < 2k` then
`A B_k ≤ 2^{4k} m^{2k}`. -/
theorem count_small (m k : ℕ) (hmk : m < 2 * k) :
    ((A m k * B m k : ℕ) : ℝ) ≤ 2 ^ (4 * k) * (m : ℝ) ^ (2 * k) := by
  sorry

-- SKETCH (D5, case m ≥ 2k): the active labels of a surviving vector/word form a set `T` of
-- size `n ≤ k`; there are `∑_{n ≤ k} m.choose n ≤ (e m / k)^k` such sets
-- (`Nat.choose_le_pow_div`, `Nat.factorial`-bound `k^k / k! ≤ e^k` from
-- `Real.pow_div_factorial_le_exp` or `Real.add_one_le_exp` iterated).  Given `T`, a positive
-- multiplicity vector on `T` summing to `2k` is a composition of `2k` into `n` parts:
-- at most `(2k-1).choose (n-1) ≤ 2^(2k) = 4^k` (`Nat.choose_le_two_pow`); and a word with
-- label set `T` is a function `Fin (2k) → T`: at most `n^(2k) ≤ k^(2k)`.  Multiply:
-- `A ≤ 4^k (em/k)^k`, `B ≤ k^(2k) (em/k)^k`, so `A B ≤ (4e²)^k m^(2k)`.
/-- Eq. `eq:array-combinatorial-bound` (6.12), large-`m` case: if `m ≥ 2k` then
`A ≤ 4^k (em/k)^k`, `B_k ≤ k^{2k} (em/k)^k`, hence `A B_k ≤ (4e²)^k m^{2k}`. -/
theorem count_large (m k : ℕ) (hmk : 2 * k ≤ m) :
    ((A m k * B m k : ℕ) : ℝ) ≤ (4 * Real.exp 1 ^ 2) ^ k * (m : ℝ) ^ (2 * k) := by
  sorry

-- SKETCH (D5): `rcases lt_or_ge m (2 * k)`; in the first case use `count_small` and
-- `2^(4k) = 16^k ≤ (4 e²)^k` (`pow_le_pow_left₀`, `Real.exp_one_gt_d9`, `nlinarith`);
-- in the second, `count_large`.
/-- Eq. `eq:array-combinatorial-bound` (6.12), unified: `A B_k ≤ (4e²)^k m^{2k}` for all
`m, k`. -/
theorem count_bound (m k : ℕ) :
    ((A m k * B m k : ℕ) : ℝ) ≤ (4 * Real.exp 1 ^ 2) ^ k * (m : ℝ) ^ (2 * k) := by
  sorry

-- SKETCH (D6): chain `random_split`, `count_reduction` (for every `I`; `Finset.sum_le_sum`,
-- `Finset.sum_const`, `Fintype.card_finset`, `Finset.card_univ`, cancel `2^m`), and
-- `count_bound`: `𝔼|S|^(2k) ≤ 2^(2k) 2^k κ^(2k) (2k)! (4e²)^k m^(2k) = (32 e²)^k (κ m)^(2k) (2k)!`.
-- Conclude with `32 e² ≤ 256 = Cu^2` (`Real.exp_one_lt_d9`, `nlinarith`), `pow_mul`,
-- `mul_pow`, `pow_le_pow_left₀`.
/-- First half of eq. `eq:canonical-array-exponential` (6.3), the even-moment bound:
`𝔼|S|^{2k} ≤ (C_u κ m)^{2k} (2k)!` for every `k ≥ 1`. -/
theorem moment_bound (H : Hyp μ ν Y h κ) (k : ℕ) (hk : 1 ≤ k) :
    ∫ ω, |S h Y ω| ^ (2 * k) ∂μ ≤ (Cu * κ * m) ^ (2 * k) * ((2 * k).factorial : ℝ) := by
  sorry

-- SKETCH (D7, 6.13): pointwise `exp x ≤ 2 cosh x` (`Real.cosh_eq`, `Real.exp_pos`) and
-- `cosh x = ∑' k, x^(2k)/(2k)!` (`Real.hasSum_cosh`), so with `x = θ S/m`,
-- `exp (θ S/m) ≤ 2 ∑' k, |θ|^(2k) |S|^(2k) / (m^(2k) (2k)!)` (`pow_abs_two_mul`).
-- Interchange sum and integral for the nonnegative series (Tonelli: `lintegral_tsum`, or
-- `integral_tsum` with summability of the `L¹` norms), bound term `k ≥ 1` by `moment_bound`
-- (`div_le_iff₀`, `m ≥ 1`) and term `k = 0` by `integral_const`/`measure_univ`, to get
-- `≤ 2 ∑' k, (Cu κ |θ|)^(2k) = 2 / (1 - (Cu κ |θ|)^2)` (`tsum_geometric_of_lt_one` with
-- ratio `(Cu κ |θ|)^2 < 1`, `pow_mul`, `one_div`).
/-- Second half of eq. `eq:canonical-array-exponential` (6.3), via
eq. `eq:array-exponential-series` (6.13): `𝔼 e^{θ S/m} ≤ 2/(1-(C_u κ |θ|)^2)` whenever
`C_u κ |θ| < 1`. -/
theorem exp_bound (H : Hyp μ ν Y h κ) (hm : 1 ≤ m) (θ : ℝ) (hθ : Cu * κ * |θ| < 1) :
    ∫ ω, Real.exp (θ * S h Y ω / m) ∂μ ≤ 2 / (1 - (Cu * κ * |θ|) ^ 2) := by
  sorry

end LogGas.Decoupling
