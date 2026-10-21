import LogGas.Grouped
import LogGas.BadEvent

/-!
# Phase 3 — Lemma 5.1 (`lem:physical-local-count-bound`), the singular part

Source: `notes/sec5-singular.tex`, with the boxes of `notes/sec1-setting.tex` and the cutoff
hypotheses H2 of `notes/hypotheses.md`.  Phase notes: `notes/phase3.md`.

Setting (abstract, no Fourier analysis).  `E` is a measurable abelian group with a
pseudo-metric (the torus `T^d`), `μE` a translation- and reflection-invariant probability
measure (normalized Lebesgue measure).  A grid `bx : Boxes μE M` of `M = J^d` boxes
`A_a` of measure `1/M` (from `LogGas.BadEvent`), with uniform box measures
`ν_a = boxMeasure bx a` and box averaging `QJ`.  Adjacency of boxes is a simple graph
`G : SimpleGraph (Fin M)` with degrees `≤ 3^d - 1`.  The singular kernel `s_r` and its mean
`c_r` are carried by the structure `SingularKernel`, which collects exactly the properties of
H2 used here (nonnegative, even, supported in the `r`-ball, `s_r ≤ (log(r/dist))_+`,
`c_r ≤ C r^d`, `M r^d ≤ 1`, vanishing between distinct non-adjacent boxes) together with the
volume bound `μE(B(0,ρ)) ≤ V ρ^d` for `ρ ≤ r` (a property of `T^d`, discharged in Phase 5).

Statements (phase notes S1–S8):
* S1 `stilde_split`, `particle_sum_splitting`, the centering lemmas `hker_box_centered_*`,
  `hker_centered_*`, `aker_centered_*` — eqs. (5.2)–(5.3);
* S2 `holder_split`, `singular_holder` — eq. (5.4);
* S3 `aker_abs_le`, `aker_integral_le_*`, `aker_moment` — eqs. (5.5)–(5.6);
* S4 `aker_exp_bound` — eq. (5.7);
* S5 `log_moment`, `s_moment`, `box_ker_moment`, `hker_moment` — eq. (5.8);
* S6 `pi_eq_sum_labels`, `label_decomposition`, `occupancy_decomposition` — eqs. (2.3)/(5.9);
* S7 `hyp_labels`, `label_exp_bound_of_boxKernel`, `label_exp_bound_trunc`,
  `label_exp_bound` — eqs. (5.10)–(5.11);
* S8 `lemma51` — eq. (5.1).

The decoupling interface accepts integrable absolute powers and almost-everywhere
centering/moment bounds. The logarithmically singular kernel is passed directly through
`hker_boxKernel`; bounded truncations remain useful auxiliary approximations.
The occupancy decomposition (5.9) is first proved at the level of label vectors
`L : Fin N → Fin M` with weights `M^{-N}` (`label_decomposition`); the paper's multinomial
form is `occupancy_decomposition`.

The standing hypothesis H1 is not needed in this phase; H2 enters only through
`SingularKernel`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Finset Function Filter Topology
open scoped BigOperators ENNReal NNReal

namespace LogGas.Singular

open LogGas.Decoupling LogGas.Grouped LogGas.BadEvent

variable {E : Type*} [MeasurableSpace E] [AddCommGroup E] [MeasurableAdd₂ E] [MeasurableNeg E]
  [PseudoMetricSpace E] [OpensMeasurableSpace E]
variable {μE : Measure E} [IsProbabilityMeasure μE] [μE.IsAddLeftInvariant] [μE.IsNegInvariant]
variable {M : ℕ}

/-! ### Boxes, box measures and box averaging -/

section Boxes

/-- The uniform probability measure `ν_a = M 1_{A_a} μ` on the box `A_a`
(`notes/sec1-setting.tex`, after eq. `eq:common-box-partition`). -/
noncomputable def boxMeasure (bx : Boxes μE M) (a : Fin M) : Measure E :=
  (M : ℝ≥0) • μE.restrict (bx.A a)

-- SKETCH: `(M • μE.restrict A) univ = M * μE A` (`Measure.smul_apply`, `Measure.restrict_apply_univ`,
-- `ENNReal.smul_def`), `bx.vol a` gives `μE A = M⁻¹`, and `M ≠ 0` from `Fin.pos a`
-- (`Nat.cast_ne_zero`), so `ENNReal.mul_inv_cancel` (with `M ≠ ⊤` by `ENNReal.natCast_ne_top`)
-- gives `1`.
/-- `ν_a` is a probability measure. -/
instance isProbabilityMeasure_boxMeasure (bx : Boxes μE M) (a : Fin M) :
    IsProbabilityMeasure (boxMeasure bx a) := by
  sorry

-- SKETCH: unfold `boxMeasure`; `Measure.restrict_le_self` and `Measure.smul_le_smul_left`
-- (`ENNReal.smul_def`, `Measure.le_iff`).
/-- `ν_a ≤ M μ`. -/
theorem boxMeasure_le (bx : Boxes μE M) (a : Fin M) : boxMeasure bx a ≤ (M : ℝ≥0∞) • μE := by
  sorry

-- SKETCH: `ae_smul_measure` (the `ℝ≥0`-smul is `ENNReal.smul_def`) and `ae_restrict_mem (bx.meas a)`.
/-- `ν_a`-almost every point lies in `A_a`. -/
theorem ae_mem_boxMeasure (bx : Boxes μE M) (a : Fin M) : ∀ᵐ x ∂(boxMeasure bx a), x ∈ bx.A a := by
  unfold boxMeasure
  exact Measure.ae_smul_measure (ae_restrict_mem (bx.meas a)) _

-- SKETCH: `μE = μE.restrict univ = μE.restrict (⋃ a, A a)` (`bx.cover`,
-- `Measure.restrict_univ`), then `Measure.restrict_iUnion bx.disj bx.meas` and
-- `Measure.sum_fintype`; finally `M⁻¹ • (M • ν) = ν` (`Finset.smul_sum`, `smul_smul`,
-- `ENNReal.inv_mul_cancel`, `one_smul`) using `Measure.ext`.
/-- `μ = M⁻¹ ∑_a ν_a`: the uniform measure is the average of the box measures. -/
theorem μE_eq_sum_boxMeasure (bx : Boxes μE M) :
    μE = (M : ℝ≥0∞)⁻¹ • ∑ a, boxMeasure bx a := by
  sorry

/-- Box averaging `Q_J`: `(Q_J u)|_{A_a} = ∫ u dν_a`
(`notes/sec1-setting.tex`, after eq. `eq:common-box-partition`). -/
noncomputable def QJ (bx : Boxes μE M) (f : E → ℝ) (x : E) : ℝ :=
  ∑ a, (bx.A a).indicator (fun _ => ∫ y, f y ∂(boxMeasure bx a)) x

/-- `Q_{J,x}`: box averaging of a two-variable kernel in the first variable. -/
noncomputable def QJx (bx : Boxes μE M) (K : E → E → ℝ) (x y : E) : ℝ :=
  QJ bx (fun x' => K x' y) x

/-- `Q_{J,y}`: box averaging of a two-variable kernel in the second variable. -/
noncomputable def QJy (bx : Boxes μE M) (K : E → E → ℝ) (x y : E) : ℝ :=
  QJ bx (fun y' => K x y') y

-- SKETCH: `Finset.sum_eq_single a`: for `b ≠ a` the point `x ∈ A a` is not in `A b`
-- (`bx.disj`, `Set.disjoint_left`), so `Set.indicator_of_notMem`; at `a`,
-- `Set.indicator_of_mem`.
/-- On the box `A_a`, `Q_J f` is the constant `∫ f dν_a`. -/
theorem QJ_apply_of_mem (bx : Boxes μE M) (f : E → ℝ) {a : Fin M} {x : E} (hx : x ∈ bx.A a) :
    QJ bx f x = ∫ y, f y ∂(boxMeasure bx a) := by
  unfold QJ
  rw [Finset.sum_eq_single a]
  · exact Set.indicator_of_mem hx _
  · intro b _ hb
    refine Set.indicator_of_notMem ?_ _
    intro hxb
    exact Set.disjoint_left.mp (bx.disj hb) hxb hx
  · simp

-- SKETCH: `Finset.measurable_sum`, each summand `measurable_const.indicator (bx.meas a)`.
/-- `Q_J f` is measurable (it is a finite sum of indicators of boxes times constants). -/
theorem measurable_QJ (bx : Boxes μE M) (f : E → ℝ) : Measurable (QJ bx f) := by
  sorry

-- SKETCH: `QJx bx K x y = ∑ a, (A a).indicator 1 x * ∫ x', K x' y ∂ν_a`; the map
-- `y ↦ ∫ x', K x' y ∂ν_a` is measurable by `StronglyMeasurable.integral_prod_left`
-- (`hK.stronglyMeasurable`, `SFinite (boxMeasure bx a)` from the probability instance), then
-- `Measurable.mul` with the indicator composed with `measurable_fst`, `measurable_snd`, and
-- `Finset.measurable_sum`.
/-- Measurability of `Q_{J,x} K` as a function of both variables. -/
theorem measurable_QJx (bx : Boxes μE M) (K : E → E → ℝ) (hK : Measurable (uncurry K)) :
    Measurable (uncurry (QJx bx K)) := by
  sorry

-- SKETCH: as `measurable_QJx` with `StronglyMeasurable.integral_prod_right` and the roles
-- of `measurable_fst`/`measurable_snd` exchanged.
/-- Measurability of `Q_{J,y} K` as a function of both variables. -/
theorem measurable_QJy (bx : Boxes μE M) (K : E → E → ℝ) (hK : Measurable (uncurry K)) :
    Measurable (uncurry (QJy bx K)) := by
  sorry

-- SKETCH: `QJ bx f = fun _ => ∫ f ∂ν_a` on `A a` (`QJ_apply_of_mem`), and `ν_a`-a.e. `x ∈ A a`
-- (`ae_mem_boxMeasure`); so `integral_congr_ae` turns the left side into `∫ (∫ f ∂ν_a) ∂ν_a`,
-- and `integral_const`, `measure_univ`, `one_smul` finish.
/-- `Q_J` is a projection: `∫ Q_J f dν_a = ∫ f dν_a`. -/
theorem integral_QJ_box (bx : Boxes μE M) (f : E → ℝ) (a : Fin M) :
    ∫ x, QJ bx f x ∂(boxMeasure bx a) = ∫ x, f x ∂(boxMeasure bx a) := by
  sorry

-- SKETCH: write `∫ g ∂μE = M⁻¹ ∑ a, ∫ g ∂ν_a` for `g = QJ bx f` and `g = f` using
-- `μE_eq_sum_boxMeasure`, `integral_smul_measure`, `integral_finset_sum_measure`
-- (integrability on each `ν_a` from `boxMeasure_le`: `Integrable.smul_measure`,
-- `Integrable.mono_measure`; `QJ bx f` is bounded hence integrable), then `integral_QJ_box`
-- termwise.
/-- `Q_J` preserves the `μ`-integral: `∫ Q_J f dμ = ∫ f dμ`. -/
theorem integral_QJ (bx : Boxes μE M) (f : E → ℝ) (hf : Integrable f μE) :
    ∫ x, QJ bx f x ∂μE = ∫ x, f x ∂μE := by
  sorry

-- SKETCH: `Finset.sum_nonneg`, `Set.indicator_nonneg`, `integral_nonneg`.
/-- Box averages of a nonnegative function are nonnegative. -/
theorem QJ_nonneg (bx : Boxes μE M) (f : E → ℝ) (hf : ∀ x, 0 ≤ f x) (x : E) : 0 ≤ QJ bx f x := by
  unfold QJ
  refine Finset.sum_nonneg fun a _ => Set.indicator_nonneg (fun _ _ => ?_) x
  exact integral_nonneg hf

-- SKETCH: pick the box `a` with `x ∈ A a` (`bx.cover`, `Set.mem_iUnion`); `QJ_apply_of_mem`;
-- `∫ f ∂ν_a = M * ∫ f ∂(μE.restrict (A a))` (`integral_smul_measure`, `ENNReal.toReal`) and
-- `setIntegral_le_integral hf_int (ae_of_all _ hf)`.
/-- "Every box average of the nonnegative kernel `s_r` is at most `M c_r`":
`Q_J f ≤ M ∫ f dμ` for `f ≥ 0`. -/
theorem QJ_le (bx : Boxes μE M) (f : E → ℝ) (hf : ∀ x, 0 ≤ f x) (hf_int : Integrable f μE)
    (x : E) : QJ bx f x ≤ M * ∫ y, f y ∂μE := by
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (bx.cover ▸ Set.mem_univ x)
  have hQ : QJ bx f x = ∫ y, f y ∂(boxMeasure bx a) := by
    unfold QJ
    rw [Finset.sum_eq_single a]
    · simp [Set.indicator_of_mem ha]
    · intro b _ hb
      exact Set.indicator_of_notMem
        (fun hxb => Set.disjoint_left.1 (bx.disj hb) hxb ha) _
    · simp
  rw [hQ, boxMeasure, ENNReal.smul_def, integral_smul_measure]
  simp only [ENNReal.coe_natCast, ENNReal.toReal_natCast, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (setIntegral_le_integral hf_int (Filter.Eventually.of_forall hf)) (Nat.cast_nonneg M)

end Boxes

/-! ### The singular kernel (hypothesis H2) and the split (5.2) -/

/-- The translation-invariant kernel `(x, y) ↦ s(x - y)` of a function of one variable
(`notes/sec1-setting.tex`, eq. `eq:homogeneous-partition-function`). -/
def ker (s : E → ℝ) (x y : E) : ℝ := s (x - y)

/-- The averaging part `a_r = Q_{J,x}s_r + Q_{J,y}s_r - Q_{J,x}Q_{J,y}s_r - c_r` of
eq. `eq:physical-local-centering` (5.2). -/
noncomputable def aker (bx : Boxes μE M) (s : E → ℝ) (c : ℝ) (x y : E) : ℝ :=
  QJx bx (ker s) x y + QJy bx (ker s) x y - QJx bx (QJy bx (ker s)) x y - c

/-- The doubly centered part `h_r = (I - Q_{J,x})(I - Q_{J,y}) s_r` of
eq. `eq:physical-local-centering` (5.2). -/
noncomputable def hker (bx : Boxes μE M) (s : E → ℝ) (x y : E) : ℝ :=
  ker s x y - QJx bx (ker s) x y - QJy bx (ker s) x y + QJx bx (QJy bx (ker s)) x y

/-- The truncation `s ∧ R` of a kernel (used to apply Lemma 6.1, which was formalized for
bounded kernels, to the singular kernel). -/
def trunc (R : ℝ) (s : E → ℝ) (z : E) : ℝ := min (s z) R

/-- The data of the singular cutoff kernel `s_r` at scale `r`, i.e. the part of hypothesis H2
(`notes/hypotheses.md`, eqs. 2.1–2.2) used in Section 5, together with the adjacency structure
of the boxes and the volume bound for small balls of `E = T^d`.  The constants `C = Cc`,
`V` and the dimension `d` are parameters so that "universal" constants may depend on them. -/
structure SingularKernel (μE : Measure E) {M : ℕ} (bx : Boxes μE M) (G : SimpleGraph (Fin M))
    (d : ℕ) (Cc V : ℝ) where
  /-- The raw singular kernel `s_r`. -/
  s : E → ℝ
  /-- Its mean `c_r = ∫ s_r dμ`. -/
  c : ℝ
  /-- The cutoff scale `r = 1/(2J)`. -/
  r : ℝ
  r_pos : 0 < r
  r_lt_one : r < 1
  V_nonneg : 0 ≤ V
  s_meas : Measurable s
  s_int : Integrable s μE
  s_nonneg : ∀ z, 0 ≤ s z
  /-- `s_r` is radial, in particular even. -/
  s_even : ∀ z, s (-z) = s z
  /-- `s_r(z) = 0` for `dist(z, 0) > r`. -/
  s_supp : ∀ z, r < dist z 0 → s z = 0
  /-- `s_r(z) ≤ (log(r / dist(z, 0)))_+` (used for eq. (5.8)); almost everywhere, since the
  paper's `s_r` is `+∞` at the origin. -/
  s_log : ∀ᵐ z ∂μE, s z ≤ max 0 (Real.log (r / dist z 0))
  c_def : ∫ z, s z ∂μE = c
  /-- `c_r ≤ C r^d`. -/
  c_le : c ≤ Cc * r ^ d
  /-- `M r^d = 2^{-d} ≤ 1`. -/
  Mr : (M : ℝ) * r ^ d ≤ 1
  /-- Volume of small balls in `T^d`: `μ(B(0, ρ)) ≤ V ρ^d` for `ρ ≤ r`. -/
  ball_vol : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → μE (Metric.ball (0 : E) ρ) ≤ ENNReal.ofReal (V * ρ ^ d)
  /-- Only particles in the same or in adjacent boxes interact through `s_r`
  (`notes/sec1-setting.tex`, after eq. `eq:physical-neighbor-events`). -/
  s_local : ∀ a b, a ≠ b → ¬ G.Adj a b → ∀ x ∈ bx.A a, ∀ y ∈ bx.A b, s (x - y) = 0

namespace SingularKernel

variable {bx : Boxes μE M} {G : SimpleGraph (Fin M)} {d : ℕ} {Cc V : ℝ}

/-- The centered singular kernel `s̃_r = s_r - c_r` (eq. `eq:compact-positive-log-split`). -/
def stilde (K : SingularKernel μE bx G d Cc V) (z : E) : ℝ := K.s z - K.c

/-- A measurable even function `0 ≤ s' ≤ s_r`: `s_r` itself and its truncations `s_r ∧ R`.
All kernel estimates of Section 5 are proved for such `s'` at once. -/
structure Sub (K : SingularKernel μE bx G d Cc V) (s' : E → ℝ) : Prop where
  meas : Measurable s'
  even : ∀ z, s' (-z) = s' z
  nonneg : ∀ z, 0 ≤ s' z
  le : ∀ z, s' z ≤ K.s z

/-- `s_r` is a sub-kernel of itself. -/
theorem Sub.self (K : SingularKernel μE bx G d Cc V) : K.Sub K.s :=
  ⟨K.s_meas, K.s_even, K.s_nonneg, fun _ => le_rfl⟩

-- SKETCH: `K.s_meas.min measurable_const`, `simp [trunc, K.s_even]`, `le_min (K.s_nonneg z) hR`,
-- `min_le_left`.
/-- Truncations `s_r ∧ R`, `R ≥ 0`, are sub-kernels. -/
theorem Sub.trunc (K : SingularKernel μE bx G d Cc V) {R : ℝ} (hR : 0 ≤ R) : K.Sub (trunc R K.s) := by
  refine ⟨K.s_meas.min measurable_const, fun z => ?_, fun z => ?_, fun z => min_le_left _ _⟩
  · show min (K.s (-z)) R = min (K.s z) R
    rw [K.s_even]
  · exact le_min (K.s_nonneg z) hR

-- SKETCH: `K.c_def ▸ integral_nonneg K.s_nonneg`.
/-- `0 ≤ c_r`. -/
theorem c_nonneg (K : SingularKernel μE bx G d Cc V) : 0 ≤ K.c := by
  exact K.c_def ▸ MeasureTheory.integral_nonneg K.s_nonneg

-- SKETCH: `0 ≤ c ≤ Cc * r^d` with `r^d > 0` (`pow_pos K.r_pos`), so `0 ≤ Cc`
-- (`nonneg_of_mul_nonneg_left` / `pos_of_mul_pos`-style, or `by_contra` + `nlinarith`).
/-- `0 ≤ C` (the constant of `c_r ≤ C r^d`). -/
theorem Cc_nonneg (K : SingularKernel μE bx G d Cc V) : 0 ≤ Cc := by
  have hc : 0 ≤ K.c := K.c_def ▸ MeasureTheory.integral_nonneg K.s_nonneg
  have hr : 0 < K.r ^ d := pow_pos K.r_pos d
  have h := K.c_le
  by_contra hneg
  have hneg := not_le.mp hneg
  nlinarith [mul_neg_of_neg_of_pos hneg hr]

-- SKETCH: `M * c ≤ M * (Cc * r^d) = Cc * (M * r^d) ≤ Cc` by `K.c_le`, `K.Mr`, `Cc_nonneg`
-- (`mul_le_mul_of_nonneg_left`, `nlinarith`).
/-- "`M c_r ≤ C`": the bound on box averages of `s_r` is uniform in `J`. -/
theorem Mc_le (K : SingularKernel μE bx G d Cc V) : (M : ℝ) * K.c ≤ Cc := by
  have h0 : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
  have hC := Cc_nonneg K
  calc (M : ℝ) * K.c ≤ M * (Cc * K.r ^ d) := mul_le_mul_of_nonneg_left K.c_le h0
    _ = Cc * (M * K.r ^ d) := by ring
    _ ≤ Cc * 1 := mul_le_mul_of_nonneg_left K.Mr hC
    _ = Cc := mul_one _

-- SKETCH: `Integrable.mono' K.s_int` with `‖s' z‖ = s' z ≤ K.s z` (`Real.norm_of_nonneg`),
-- measurability from `hs'.meas`.
/-- Sub-kernels are integrable. -/
theorem Sub.integrable (K : SingularKernel μE bx G d Cc V) {s' : E → ℝ} (hs' : K.Sub s') :
    Integrable s' μE := by
  refine K.s_int.mono' hs'.meas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (hs'.nonneg z)]
  exact hs'.le z

-- SKETCH: `integral_sub_right_eq_self`.
omit [PseudoMetricSpace E] [OpensMeasurableSpace E] [μE.IsNegInvariant] in
/-- Translation invariance: `∫ s'(x - y) dμ(x) = ∫ s' dμ`. -/
theorem integral_ker_left (s' : E → ℝ) (y : E) : ∫ x, s' (x - y) ∂μE = ∫ z, s' z ∂μE :=
  integral_sub_right_eq_self s' y

-- SKETCH: `integral_sub_left_eq_self`.
omit [PseudoMetricSpace E] [OpensMeasurableSpace E] in
/-- Reflection and translation invariance: `∫ s'(x - y) dμ(y) = ∫ s' dμ`. -/
theorem integral_ker_right (s' : E → ℝ) (x : E) : ∫ y, s' (x - y) ∂μE = ∫ z, s' z ∂μE :=
  integral_sub_left_eq_self s' μE x

-- SKETCH: `Integrable.mono_measure` along `boxMeasure_le` after `Integrable.smul_measure`
-- (`ENNReal.natCast_ne_top`); the `μE`-integrability of `x ↦ s'(x - y)` is
-- `(hs'.integrable).comp_sub_right y` (`Integrable.comp_sub_right`).
/-- `x ↦ s'(x - y)` is `ν_a`-integrable. -/
theorem integrable_ker_box_left (K : SingularKernel μE bx G d Cc V) {s' : E → ℝ} (hs' : K.Sub s')
    (a : Fin M) (y : E) : Integrable (fun x => s' (x - y)) (boxMeasure bx a) := by
  have hi : Integrable s' μE :=
    K.s_int.mono' hs'.meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (hs'.nonneg z)]; exact hs'.le z)
  unfold boxMeasure
  exact ((hi.comp_sub_right y).integrableOn (s := bx.A a)).smul_measure ENNReal.coe_ne_top

-- SKETCH: as `integrable_ker_box_left` with `Integrable.comp_sub_left`.
/-- `y ↦ s'(x - y)` is `ν_b`-integrable. -/
theorem integrable_ker_box_right (K : SingularKernel μE bx G d Cc V) {s' : E → ℝ} (hs' : K.Sub s')
    (b : Fin M) (x : E) : Integrable (fun y => s' (x - y)) (boxMeasure bx b) := by
  sorry

end SingularKernel

section Split

variable {bx : Boxes μE M} {G : SimpleGraph (Fin M)} {d : ℕ} {Cc V : ℝ}

-- SKETCH: `ker s` uncurried is `s ∘ (fun p => p.1 - p.2)`: `hs.comp measurable_sub`; then
-- `measurable_QJx`, `measurable_QJy` (twice) and `Measurable.add/sub/const`.
/-- `a_r` is measurable in both variables. -/
theorem measurable_aker (s : E → ℝ) (hs : Measurable s) (c : ℝ) :
    Measurable (uncurry (aker bx s c)) := by
  sorry

-- SKETCH: as `measurable_aker`.
/-- `h_r` is measurable in both variables. -/
theorem measurable_hker (s : E → ℝ) (hs : Measurable s) : Measurable (uncurry (hker bx s)) := by
  sorry

/-- Eq. `eq:physical-local-centering` (5.2): `s̃_r = a_r + h_r`. -/
theorem stilde_split (K : SingularKernel μE bx G d Cc V) (x y : E) :
    ker K.stilde x y = aker bx K.s K.c x y + hker bx K.s x y := by
  simp only [ker, SingularKernel.stilde, aker, hker]; ring

-- SKETCH: `QJx bx (ker s') y x = ∫ s'(x' - x) dν_{b(y)}(x')` and
-- `QJy bx (ker s') x y = ∫ s'(x - y') dν_{b(y)}(y')`, both read on the box containing `y`
-- (`QJ_apply_of_mem`, `bx.cover`); they agree termwise by `hs'.even` (`neg_sub`).
-- Equivalently, unfold `QJ` and use `Finset.sum_congr` with `integral_congr_ae` on each box.
/-- `(Q_{J,x} s_r)(y, x) = (Q_{J,y} s_r)(x, y)` for even `s_r`. -/
theorem QJx_ker_swap (K : SingularKernel μE bx G d Cc V) {s' : E → ℝ} (hs' : K.Sub s') (x y : E) :
    QJx bx (ker s') y x = QJy bx (ker s') x y := by
  unfold QJx QJy ker
  congr 1
  funext z
  rw [← neg_sub, hs'.even]

-- SKETCH: both sides are the double average `∬ s'(x' - y') dν_{b(x)}(x') dν_{b(y)}(y')`
-- in the two orders (`QJ_apply_of_mem` twice), equal by Fubini `integral_integral_swap`
-- (integrability on `ν_a.prod ν_b` from `Integrable.mono'` with the nonnegative bound
-- `s'(x' - y') ≤ K.s (x' - y')`, whose double integral is `≤ M c` by Tonelli and
-- `integral_ker_left`) and by `hs'.even`.
/-- `(Q_{J,x}Q_{J,y} s_r)(y, x) = (Q_{J,x}Q_{J,y} s_r)(x, y)` for even `s_r`. -/
theorem QJxQJy_ker_swap (K : SingularKernel μE bx G d Cc V) {s' : E → ℝ} (hs' : K.Sub s')
    (x y : E) : QJx bx (QJy bx (ker s')) y x = QJx bx (QJy bx (ker s')) x y := by
  sorry

-- SKETCH: unfold `aker`; `QJx_ker_swap`, `QJxQJy_ker_swap` and `add_comm`.
/-- `a_r` is a symmetric kernel. -/
theorem aker_symm (K : SingularKernel μE bx G d Cc V) (x y : E) :
    aker bx K.s K.c x y = aker bx K.s K.c y x := by
  sorry

-- SKETCH: unfold `hker`, `ker`; `hs'.even` (`neg_sub`), `QJx_ker_swap`, `QJxQJy_ker_swap`.
/-- `h_r` is a symmetric kernel (for every sub-kernel `s'`). -/
theorem hker_symm (K : SingularKernel μE bx G d Cc V) {s' : E → ℝ} (hs' : K.Sub s') (x y : E) :
    hker bx s' x y = hker bx s' y x := by
  sorry

-- SKETCH: `hker = (ker - QJx ker) - (QJy ker - QJx (QJy ker))` and
-- `QJx bx K' x y = QJ bx (K' · y) x`; by `integral_sub` and `integral_QJ_box` both brackets
-- integrate to `0` against `ν_a` (integrability: `integrable_ker_box_left`, and `QJ` of an
-- integrable function is bounded).
/-- Eq. (5.2), "`h_r` has zero average in each variable over every box", first variable:
`∫ h_r(x, y) dν_a(x) = 0` for every `a` and `y`. -/
theorem hker_box_centered_left (K : SingularKernel μE bx G d Cc V) {s' : E → ℝ} (hs' : K.Sub s')
    (a : Fin M) (y : E) : ∫ x, hker bx s' x y ∂(boxMeasure bx a) = 0 := by
  sorry

-- SKETCH: `hker = (ker - QJy ker) - QJx (ker - QJy ker)` (pointwise, `QJx` is linear:
-- `QJ` of a difference is the difference of `QJ`s by `integral_sub`).  The first term
-- integrates to `0` against `ν_b` in `y` by `integral_QJ_box`.  For the second,
-- `QJx bx K' x y = ∑ a, 1_{A a}(x) ∫ K'(x', y) dν_a(x')`; integrate in `y` and swap with the
-- `ν_a`-integral (`integral_integral_swap`, integrability from the bound by `K.s` as in
-- `QJxQJy_ker_swap`), the inner `∫ (ker - QJy ker)(x', y) dν_b(y)` vanishes.
/-- Eq. (5.2), box centering in the second variable: `∫ h_r(x, y) dν_b(y) = 0`. -/
theorem hker_box_centered_right (K : SingularKernel μE bx G d Cc V) {s' : E → ℝ} (hs' : K.Sub s')
    (b : Fin M) (x : E) : ∫ y, hker bx s' x y ∂(boxMeasure bx b) = 0 := by
  sorry

-- SKETCH: `μE_eq_sum_boxMeasure`, `integral_smul_measure`, `integral_finset_sum_measure`
-- (integrability of `hker · y` on each `ν_a` from `integrable_ker_box_left` and boundedness of
-- the averaged terms), then `hker_box_centered_left` termwise and `Finset.sum_const_zero`.
/-- Eq. (5.2), "`h_r` has zero average in each variable under `μ`", first variable. -/
theorem hker_centered_left (K : SingularKernel μE bx G d Cc V) {s' : E → ℝ} (hs' : K.Sub s')
    (y : E) : ∫ x, hker bx s' x y ∂μE = 0 := by
  sorry

-- SKETCH: as `hker_centered_left`, from `hker_box_centered_right`.
/-- Eq. (5.2), centering of `h_r` under `μ` in the second variable. -/
theorem hker_centered_right (K : SingularKernel μE bx G d Cc V) {s' : E → ℝ} (hs' : K.Sub s')
    (x : E) : ∫ y, hker bx s' x y ∂μE = 0 := by
  sorry

-- SKETCH: the four terms of `aker · y` integrate under `μE` to `c, c, c, c`:
-- `∫ QJx (ker s) (·, y) dμE = ∫ s(x - y) dμE(x) = c` (`integral_QJ`, `integral_ker_left`,
-- `K.c_def`); `∫ QJy (ker s) (x, y) dμE(x) = ∫ (∫ s(x - y') dμE(x)) dν_{b(y)}(y') = c`
-- (`QJ_apply_of_mem`, `integral_integral_swap`, `integral_ker_left`, `integral_const`);
-- `∫ QJx (QJy (ker s)) (·, y) dμE = ∫ QJy (ker s) (·, y) dμE = c` (`integral_QJ`).
-- Then `integral_add`, `integral_sub`, `integral_const` and `c + c - c - c = 0`.
/-- Eq. (5.2), "`a_r` has zero average in each variable under `μ`", first variable. -/
theorem aker_centered_left (K : SingularKernel μE bx G d Cc V) (y : E) :
    ∫ x, aker bx K.s K.c x y ∂μE = 0 := by
  sorry

-- SKETCH: `aker_symm` and `aker_centered_left`.
/-- Eq. (5.2), centering of `a_r` under `μ` in the second variable. -/
theorem aker_centered_right (K : SingularKernel μE bx G d Cc V) (x : E) :
    ∫ y, aker bx K.s K.c x y ∂μE = 0 := by
  sorry

-- SKETCH: `s'(x - y) = 0` from `K.s_local` and `0 ≤ s' ≤ K.s` (`le_antisymm`).  The three
-- averaged terms vanish because `ν_a`-a.e. `x' ∈ A a` (`ae_mem_boxMeasure`) and then
-- `s'(x' - y) = 0` (`integral_eq_zero_of_ae`); for the double average apply this twice
-- (`QJ_apply_of_mem` on the boxes of `x` and `y`).
/-- "Box averaging preserves this property": `h_r(x, y) = 0` when `x`, `y` lie in distinct
non-adjacent boxes. -/
theorem hker_local (K : SingularKernel μE bx G d Cc V) {s' : E → ℝ} (hs' : K.Sub s') {a b : Fin M}
    (hab : a ≠ b) (hadj : ¬ G.Adj a b) {x y : E} (hx : x ∈ bx.A a) (hy : y ∈ bx.A b) :
    hker bx s' x y = 0 := by
  sorry

end Split

/-! ### The particle sums `W_N` and `S` -/

section W

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}

omit [MeasurableAdd₂ E] [MeasurableNeg E] [PseudoMetricSpace E] [OpensMeasurableSpace E] in
/-- `W_N` is additive in the kernel. -/
theorem W_add (K₁ K₂ : E → E → ℝ) (X : Fin N → Ω → E) (ω : Ω) :
    W (fun x y => K₁ x y + K₂ x y) X ω = W K₁ X ω + W K₂ X ω := by
  simp only [W, Finset.sum_add_distrib, mul_add]

-- SKETCH: `W K X ω = (1/N) ∑ i, ∑ j ∈ univ.erase i, K (X i) (X j)`; split
-- `univ.erase i = Ioi i ∪ Iio i` (`Finset.Ioi_union_Iio`-style via `Finset.filter`), use
-- `hK` on the `Iio` part and `Finset.sum_comm` / `Finset.sum_sigma'` to identify it with the
-- `Ioi` part (the pairs `(i, j)` with `j < i` are the pairs `(j, i)` with `i < j`).  Then
-- `S`, `two_mul`, `mul_div_assoc`, `one_div`.
omit [MeasurableAdd₂ E] [MeasurableNeg E] [PseudoMetricSpace E] [OpensMeasurableSpace E] in
/-- "`W_N(h_r) = 2 N^{-1} ∑_{i<j} h_r(X_i, X_j)`" (eq. (5.3)): for a symmetric kernel,
`W_N(K) = 2 S / N` with `S` of `LogGas.Decoupling`. -/
theorem W_eq_S (K : E → E → ℝ) (hK : ∀ x y, K x y = K y x) (X : Fin N → Ω → E) (ω : Ω) :
    W K X ω = 2 * S (fun _ _ => K) X ω / N := by
  have hsplit : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, K (X i ω) (X j ω)
      = ∑ j ∈ Finset.Ioi i, K (X i ω) (X j ω) + ∑ j ∈ Finset.Iio i, K (X i ω) (X j ω) := by
    intro i
    have : Finset.univ.erase i = Finset.Ioi i ∪ Finset.Iio i := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Ioi,
        Finset.mem_Iio]
      constructor
      · intro h; exact (lt_or_gt_of_ne h).symm
      · rintro (h | h)
        · exact h.ne'
        · exact h.ne
    rw [this, Finset.sum_union]
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_Ioi, Finset.mem_Iio] at h1 h2
    exact lt_asymm h1 h2
  have hcomm : ∑ i : Fin N, ∑ j ∈ Finset.Iio i, K (X i ω) (X j ω)
      = ∑ i : Fin N, ∑ j ∈ Finset.Ioi i, K (X i ω) (X j ω) := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.Ioi j)]
    · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => hK _ _
    · intro i j
      simp
  unfold W S
  simp only [hsplit, Finset.sum_add_distrib, hcomm]
  ring

-- SKETCH: `Finset.measurable_sum` twice and `hK.comp ((hX i).prodMk (hX j))`, then
-- `Measurable.const_mul`.
omit [MeasurableAdd₂ E] [MeasurableNeg E] [PseudoMetricSpace E] [OpensMeasurableSpace E] in
/-- `W_N(K)` is measurable for a measurable kernel and measurable particles. -/
theorem measurable_W (K : E → E → ℝ) (hK : Measurable (uncurry K)) (X : Fin N → Ω → E)
    (hX : ∀ i, Measurable (X i)) : Measurable (W K X) := by
  sorry

variable {bx : Boxes μE M} {G : SimpleGraph (Fin M)} {d : ℕ} {Cc V : ℝ}

-- SKETCH: `W_add` after rewriting the kernel with `stilde_split` (`funext`), then `mul_add`.
/-- Eq. `eq:physical-particle-sum-splitting` (5.3):
`(t/2) W_N(s̃_r) = (t/2) W_N(a_r) + (t/2) W_N(h_r)`. -/
theorem particle_sum_splitting (K : SingularKernel μE bx G d Cc V) (X : Fin N → Ω → E) (t : ℝ)
    (ω : Ω) :
    (t / 2) * W (ker K.stilde) X ω
      = (t / 2) * W (aker bx K.s K.c) X ω + (t / 2) * W (hker bx K.s) X ω := by
  sorry

end W

/-! ### S2: Cauchy–Schwarz (5.4) -/

section Holder

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}

-- SKETCH: `ENNReal.lintegral_mul_le_Lp_mul_Lq μ` with the conjugate pair `p = q = 2`
-- (`Real.HolderConjugate` built by `⟨by norm_num, by norm_num⟩`),
-- `f = ofReal (exp (F/2))`, `g = A.indicator (ofReal (exp (G/2)))`; the integrand is
-- `f * g` (`Set.indicator_mul_left`, `← ENNReal.ofReal_mul`, `← Real.exp_add`, `add_div`), and
-- `f ^ 2 = ofReal (exp F)`, `g ^ 2 = A.indicator (ofReal (exp G))` (`ENNReal.ofReal_rpow_of_nonneg`,
-- `← Real.exp_mul`, `Set.indicator_pow`-style via `Set.indicator_apply`); measurability by
-- `Real.measurable_exp`, `ENNReal.measurable_ofReal`, `Measurable.indicator`.
/-- Cauchy–Schwarz with an indicator (abstract form of eq. `eq:physical-local-holder` (5.4)):
`∫ 1_A e^{(F+G)/2} ≤ (∫ e^F)^{1/2} (∫ 1_A e^G)^{1/2}`, as Lebesgue integrals. -/
theorem holder_split (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A) (F G : Ω → ℝ)
    (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Real.exp ((F ω + G ω) / 2))) ω ∂μ
      ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (F ω)) ∂μ) ^ (1 / 2 : ℝ)
        * (∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Real.exp (G ω))) ω ∂μ) ^ (1 / 2 : ℝ) := by
  sorry

variable {bx : Boxes μE M} {G : SimpleGraph (Fin M)} {d : ℕ} {Cc V : ℝ}

-- SKETCH: rewrite the exponent with `particle_sum_splitting` as `(t W(a_r) + t W(h_r)) / 2`
-- (`mul_div_assoc`, `add_div`) and apply `holder_split` with `F = t W(a_r)`, `G = t W(h_r)`;
-- measurability from `measurable_W`, `measurable_aker K.s_meas`, `measurable_hker K.s_meas`.
/-- Eq. `eq:physical-local-holder` (5.4):
`𝔼[1_𝓐 e^{(t/2)W_N(s̃_r)}] ≤ (𝔼 e^{tW_N(a_r)})^{1/2} (𝔼[1_𝓐 e^{tW_N(h_r)}])^{1/2}`. -/
theorem singular_holder (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (K : SingularKernel μE bx G d Cc V) (X : Fin N → Ω → E) (hX : ∀ i, Measurable (X i)) (t : ℝ) :
    ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Real.exp ((t / 2) * W (ker K.stilde) X ω))) ω ∂μ
      ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (t * W (aker bx K.s K.c) X ω)) ∂μ) ^ (1 / 2 : ℝ)
        * (∫⁻ ω, A.indicator
            (fun ω => ENNReal.ofReal (Real.exp (t * W (hker bx K.s) X ω))) ω ∂μ) ^ (1 / 2 : ℝ) := by
  sorry

end Holder

/-! ### S3: the averaging term is perturbative, (5.5)–(5.6) -/

section Averaging

variable {bx : Boxes μE M} {G : SimpleGraph (Fin M)} {d : ℕ} {Cc V : ℝ}

-- SKETCH: each of `QJx (ker s) x y`, `QJy (ker s) x y`, `QJx (QJy (ker s)) x y` lies in
-- `[0, M c]`: `QJ_nonneg`, `QJ_le` with `integral_ker_left` / `integral_ker_right` and
-- `K.c_def` (for the double average, bound `QJy (ker s) (·, y) ≤ M c` pointwise first, or
-- use `QJ_le` with `∫ QJy (ker s) (x', y) dμE(x') = c` from `aker_centered_left`'s
-- computation).  Then `M c ≤ Cc` (`Mc_le`), `c ≤ Cc` (`K.c_le`, `r^d ≤ 1`), and
-- `abs_le.2 ⟨_, _⟩` with `linarith`.
/-- Eq. `eq:physical-average-smallness` (5.5), first bound: `‖a_r‖_∞ ≤ C` (here `4C`). -/
theorem aker_abs_le (K : SingularKernel μE bx G d Cc V) (x y : E) :
    |aker bx K.s K.c x y| ≤ 4 * Cc := by
  sorry

-- SKETCH: `|a_r| ≤ QJx + QJy + QJxQJy + c` (all terms nonnegative, `abs_sub`, `abs_add`),
-- and "each averaging term has integral `c_r` in either variable": in the variable `y`,
-- `∫ QJx (ker s) (x, y) dμE(y) = ∫ (∫ s(x' - y) dμE(y)) dν_{b(x)}(x') = c` (Fubini,
-- `integral_ker_right`), `∫ QJy (ker s) (x, y) dμE(y) = ∫ s(x - y) dμE(y) = c` (`integral_QJ`),
-- `∫ QJx (QJy (ker s)) (x, ·) dμE = c` likewise, `∫ c dμE = c`; so `≤ 4 c`
-- (`integral_mono`, `integral_add`).
/-- Eq. `eq:physical-average-smallness` (5.5), second bound: `∫ |a_r(x, y)| dμ(y) ≤ 4 c_r`. -/
theorem aker_integral_le_right (K : SingularKernel μE bx G d Cc V) (x : E) :
    ∫ y, |aker bx K.s K.c x y| ∂μE ≤ 4 * K.c := by
  classical
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (bx.cover ▸ Set.mem_univ x)
  have hMpos : (0:ℝ) < M := Nat.cast_pos.2 (Fin.pos a)
  have hM0 : (M:ℝ) ≠ 0 := hMpos.ne'
  have hν : ∀ (b : Fin M) (f : E → ℝ),
      ∫ z, f z ∂(boxMeasure bx b) = M * ∫ z in bx.A b, f z ∂μE := by
    intro b f
    rw [boxMeasure, ENNReal.smul_def, integral_smul_measure]
    simp only [ENNReal.coe_natCast, ENNReal.toReal_natCast, smul_eq_mul]
  have hvol : ∀ b : Fin M, (μE.restrict (bx.A b)).real Set.univ = 1 / M := by
    intro b
    rw [Measure.real, Measure.restrict_apply_univ, bx.vol]
    simp
  have hP : ∀ g : E → ℝ, Integrable g μE →
      Integrable (QJ bx g) μE ∧ ∫ y, QJ bx g y ∂μE = ∫ y, g y ∂μE := by
    intro g hg
    refine ⟨?_, ?_⟩
    · unfold QJ
      exact integrable_finsetSum _ fun b _ => (integrable_const _).indicator (bx.meas b)
    · unfold QJ
      rw [integral_finsetSum _ (fun b _ => (integrable_const _).indicator (bx.meas b))]
      have : ∀ b, ∫ y, (bx.A b).indicator (fun _ => ∫ z, g z ∂(boxMeasure bx b)) y ∂μE
          = ∫ z in bx.A b, g z ∂μE := by
        intro b
        rw [integral_indicator_const _ (bx.meas b), Boxes.real_vol, hν, smul_eq_mul]
        field_simp
      simp_rw [this]
      rw [← integral_iUnion_fintype bx.meas bx.disj (fun b => hg.integrableOn), bx.cover,
        setIntegral_univ]
  have hS2 : Integrable (fun p : E × E => K.s (p.1 - p.2)) (μE.prod μE) := by
    have := Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
      (integrable_const (1:ℝ) (μ := μE)) K.s_int (μ := μE) (ν := μE)
    simpa using this
  have hS3 : ∀ A B : Set E,
      Integrable (fun p : E × E => K.s (p.1 - p.2)) ((μE.restrict A).prod (μE.restrict B)) :=
    fun A B => hS2.mono_measure (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
  have hS4 : ∀ A : Set E,
      Integrable (fun p : E × E => K.s (p.1 - p.2)) ((μE.restrict A).prod μE) :=
    fun A => hS2.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hT1 : ∀ y, QJx bx (ker K.s) x y = M * ∫ x' in bx.A a, K.s (x' - y) ∂μE := by
    intro y
    unfold QJx
    rw [QJ_apply_of_mem bx _ ha, hν]
    rfl
  have hT1int : Integrable (fun y => QJx bx (ker K.s) x y) μE ∧
      ∫ y, QJx bx (ker K.s) x y ∂μE = K.c := by
    have hi : Integrable (fun y => ∫ x' in bx.A a, K.s (x' - y) ∂μE) μE :=
      (hS4 (bx.A a)).integral_prod_right
    simp_rw [hT1]
    refine ⟨hi.const_mul _, ?_⟩
    rw [integral_const_mul]
    have hsw := integral_integral_swap (μ := μE.restrict (bx.A a)) (ν := μE)
      (f := fun x' y => K.s (x' - y)) (hS4 _)
    rw [← hsw]
    simp_rw [SingularKernel.integral_ker_right K.s, K.c_def]
    rw [integral_const, smul_eq_mul, hvol]
    field_simp
  have hT2 : ∀ y, QJy bx (ker K.s) x y = QJ bx (fun y' => K.s (x - y')) y := fun y => rfl
  have hT2int : Integrable (fun y => QJy bx (ker K.s) x y) μE ∧
      ∫ y, QJy bx (ker K.s) x y ∂μE = K.c := by
    obtain ⟨h1, h2⟩ := hP _ (K.s_int.comp_sub_left x)
    simp_rw [hT2]
    refine ⟨h1, ?_⟩
    rw [h2, SingularKernel.integral_ker_right K.s, K.c_def]
  have hT3 : ∀ y, QJx bx (QJy bx (ker K.s)) x y
      = QJ bx (fun y' => QJx bx (ker K.s) x y') y := by
    intro y
    obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (bx.cover ▸ Set.mem_univ y)
    have e1 : QJx bx (QJy bx (ker K.s)) x y
        = M * ∫ x'' in bx.A a, M * ∫ y' in bx.A b, K.s (x'' - y') ∂μE ∂μE := by
      unfold QJx
      rw [QJ_apply_of_mem bx _ ha, hν]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun x'' => ?_)
      show QJ bx (fun y' => ker K.s x'' y') y = _
      rw [QJ_apply_of_mem bx _ hb, hν]
      rfl
    have e2 : QJ bx (fun y' => QJx bx (ker K.s) x y') y
        = M * ∫ y' in bx.A b, M * ∫ x'' in bx.A a, K.s (x'' - y') ∂μE ∂μE := by
      rw [QJ_apply_of_mem bx _ hb, hν]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun y' => ?_)
      exact hT1 y'
    rw [e1, e2]
    simp only [integral_const_mul]
    rw [integral_integral_swap (μ := μE.restrict (bx.A a)) (ν := μE.restrict (bx.A b))
      (f := fun x'' y' => K.s (x'' - y')) (hS3 _ _)]
  have hT3int : Integrable (fun y => QJx bx (QJy bx (ker K.s)) x y) μE ∧
      ∫ y, QJx bx (QJy bx (ker K.s)) x y ∂μE = K.c := by
    obtain ⟨h1, h2⟩ := hP _ hT1int.1
    simp_rw [hT3]
    exact ⟨h1, h2.trans hT1int.2⟩
  have hnn : ∀ y, 0 ≤ QJx bx (ker K.s) x y := fun y =>
    QJ_nonneg bx _ (fun z => K.s_nonneg _) x
  have hnn2 : ∀ y, 0 ≤ QJy bx (ker K.s) x y := fun y =>
    QJ_nonneg bx _ (fun z => K.s_nonneg _) y
  have hnn2' : ∀ x' y, 0 ≤ QJy bx (ker K.s) x' y := fun x' y =>
    QJ_nonneg bx _ (fun z => K.s_nonneg _) y
  have hnn3 : ∀ y, 0 ≤ QJx bx (QJy bx (ker K.s)) x y := fun y =>
    QJ_nonneg bx (fun x' => QJy bx (ker K.s) x' y) (fun z => hnn2' z y) x
  have hint : Integrable (fun y => QJx bx (ker K.s) x y + QJy bx (ker K.s) x y
      + QJx bx (QJy bx (ker K.s)) x y + K.c) μE :=
    ((hT1int.1.add hT2int.1).add hT3int.1).add (integrable_const _)
  calc ∫ y, |aker bx K.s K.c x y| ∂μE
      ≤ ∫ y, (QJx bx (ker K.s) x y + QJy bx (ker K.s) x y
        + QJx bx (QJy bx (ker K.s)) x y + K.c) ∂μE := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _) hint
          (Filter.Eventually.of_forall fun y => ?_)
        have := K.c_nonneg
        have h1 := hnn y
        have h2 := hnn2 y
        have h3 := hnn3 y
        unfold aker
        rw [abs_le]
        constructor <;> linarith
    _ = 4 * K.c := by
        have h12 : Integrable (fun y => QJx bx (ker K.s) x y + QJy bx (ker K.s) x y) μE :=
          hT1int.1.add hT2int.1
        have h123 : Integrable (fun y => QJx bx (ker K.s) x y + QJy bx (ker K.s) x y
            + QJx bx (QJy bx (ker K.s)) x y) μE := h12.add hT3int.1
        rw [integral_add h123 (integrable_const _), integral_add h12 hT3int.1,
          integral_add hT1int.1 hT2int.1, hT1int.2, hT2int.2, hT3int.2, integral_const]
        simp
        ring

-- SKETCH: `aker_symm` and `aker_integral_le_right`.
/-- Eq. (5.5), second bound in the other variable: `∫ |a_r(x, y)| dμ(x) ≤ 4 c_r`. -/
theorem aker_integral_le_left (K : SingularKernel μE bx G d Cc V) (y : E) :
    ∫ x, |aker bx K.s K.c x y| ∂μE ≤ 4 * K.c := by
  sorry

-- SKETCH: pointwise, with `u = |f x| / κ ≥ 0`: `u^p / p! = u * (u^(p-1) / p!) ≤ u * (u^(p-1)/(p-1)!)
-- ≤ u * exp u` (`Real.pow_div_factorial_le_exp`, `Nat.factorial_succ`, `Nat.succ_pred_eq_of_pos`),
-- so `|f x|^p ≤ κ^p p! * (|f x| / κ) * exp (C / κ)` (`Real.exp_le_exp`, `hC`, `div_le_div_of_nonneg_right`).
-- Integrate (`integral_mono`; integrability of `|f|^p` by `Integrable.of_bound` on the finite
-- measure with `|f|^p ≤ C^p`), `integral_const_mul`, `hε`, and `ε * exp (C/κ) / κ ≤ 1` from `hsmall`.
/-- The exponential-moment device of Step 2 of the proof of Lemma 5.1: if `|f| ≤ C`,
`∫ |f| ≤ ε` and `ε e^{C/κ} ≤ κ`, then `∫ |f|^p ≤ κ^p p!` for every `p ≥ 1`. -/
theorem moment_of_exp {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (f : α → ℝ) (hf : Measurable f) (C κ ε : ℝ) (hκ : 0 < κ) (hC : ∀ x, |f x| ≤ C)
    (hε : ∫ x, |f x| ∂ν ≤ ε) (hsmall : ε * Real.exp (C / κ) ≤ κ) (p : ℕ) (hp : 1 ≤ p) :
    ∫ x, |f x| ^ p ∂ν ≤ κ ^ p * p.factorial := by
  sorry

/-- The decay rate `κ(r) = C'/log(1/r)` of eq. `eq:physical-average-factorial` (5.6), with
`C' = 8 C + 1`. -/
noncomputable def kappa (Cc r : ℝ) : ℝ := (8 * Cc + 1) / Real.log (1 / r)

-- SKETCH: `div_pos` with `Real.log_pos` (`one_lt_one_div hr hr1`).
/-- `κ(r) > 0` for `0 < r < 1`. -/
theorem kappa_pos (Cc : ℝ) (hCc : 0 ≤ Cc) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 0 < kappa Cc r := by
  sorry

-- SKETCH: `Real.log (1/r) ≥ (8 Cc + 1)/ε` from `hr'` (`Real.log_le_log`, `Real.log_exp`,
-- `one_div`, `Real.log_inv`), then `div_le_iff₀` and `div_le_iff₀` again.
/-- `κ(r) ≤ ε` as soon as `r ≤ exp(-(8C+1)/ε)`. -/
theorem kappa_le_of_le (Cc : ℝ) (hCc : 0 ≤ Cc) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hr' : r ≤ Real.exp (-((8 * Cc + 1) / ε))) : kappa Cc r ≤ ε := by
  sorry

-- SKETCH: `Real.tendsto_log_atTop.comp` with `tendsto_one_div_nhdsWithin_Ioi`-style
-- (`tendsto_inv_nhdsGT_zero`), then `Tendsto.div_atTop tendsto_const_nhds`.
/-- `κ(r) → 0` as `r ↓ 0` (eq. (5.6)). -/
theorem kappa_tendsto_zero (Cc : ℝ) : Tendsto (fun r => kappa Cc r) (𝓝[>] 0) (𝓝 0) := by
  sorry

-- SKETCH: `moment_of_exp` with `C = 4 Cc` (`aker_abs_le`), `ε = 4 c` (`aker_integral_le_*`),
-- `κ = kappa Cc r`, measurability from `measurable_aker`.  Smallness: with `L = log (1/r) > 0`,
-- `exp (4 Cc / κ) = exp (4 Cc L / (8 Cc + 1)) ≤ exp (L / 2) = r ^ (-1/2)` (`Real.exp_log`,
-- `Real.rpow_neg`, `Real.sqrt_eq_rpow`), `4 c ≤ 4 Cc r^d ≤ 4 Cc r` (`K.c_le`, `d ≥ 1`, `r < 1`),
-- and `√r · L ≤ 2` from `Real.log_le_sub_one_of_pos` applied to `1/√r`; hence
-- `4 c exp (4Cc/κ) ≤ 8 Cc / L ≤ (8 Cc + 1) / L = κ`.  Finally `κ^p p! ≤ 2 κ^p p!`.
/-- Eq. `eq:physical-average-factorial` (5.6): for every `p ≥ 1`,
`sup_x ∫ |a_r(x,y)|^p dμ(y) ≤ 2 κ(r)^p p!` and `sup_y ∫ |a_r(x,y)|^p dμ(x) ≤ 2 κ(r)^p p!`,
with `κ(r) = (8C+1)/log(1/r)` (valid for all `0 < r < 1`). -/
theorem aker_moment (K : SingularKernel μE bx G d Cc V) (hd : 1 ≤ d) (p : ℕ) (hp : 1 ≤ p) :
    (∀ x, ∫ y, |aker bx K.s K.c x y| ^ p ∂μE ≤ 2 * kappa Cc K.r ^ p * p.factorial) ∧
    (∀ y, ∫ x, |aker bx K.s K.c x y| ^ p ∂μE ≤ 2 * kappa Cc K.r ^ p * p.factorial) := by
  sorry

end Averaging

/-! ### S4: the averaging exponential, (5.7) -/

section AveragingExp

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
variable {bx : Boxes μE M} {G : SimpleGraph (Fin M)} {d : ℕ} {Cc V : ℝ}

-- SKETCH: fields: `hκ`; `hX_meas`; `hX_indep`; `hX_law`; `measurable_aker K.s_meas`;
-- `⟨4 * Cc, fun x y => aker_abs_le K x y⟩`; `aker_centered_left`, `aker_centered_right`
-- (ignoring `i < j`); `(hmom p hp).2`, `(hmom p hp).1`.
/-- The kernels `h_{ij} = a_r` (all `i < j`), under the i.i.d. law `μ`, satisfy the hypotheses
of Lemma 6.1 with the constant `κ` of eq. (5.6). -/
theorem hyp_aker (μ : Measure Ω) [IsProbabilityMeasure μ] (K : SingularKernel μE bx G d Cc V)
    (X : Fin N → Ω → E) (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X μ)
    (hX_law : ∀ i, μ.map (X i) = μE) (κ : ℝ) (hκ : 0 < κ)
    (hmom : ∀ p : ℕ, 1 ≤ p →
      (∀ x, ∫ y, |aker bx K.s K.c x y| ^ p ∂μE ≤ 2 * κ ^ p * p.factorial) ∧
      (∀ y, ∫ x, |aker bx K.s K.c x y| ^ p ∂μE ≤ 2 * κ ^ p * p.factorial)) :
    Hyp μ (fun _ => μE) X (fun _ _ => aker bx K.s K.c) κ := by
  sorry

-- SKETCH: take `r1 := Real.exp (-((8 * Cc + 1) * (4 * t0 * Cu)))` (so `kappa_le_of_le` gives
-- `κ(r) ≤ 1 / (4 t0 Cu)` for `r ≤ r1`, hence `2 t Cu κ(r) ≤ 1/2`; this is the choice of `J_0`).
-- For such `K`: `hyp_aker` with `aker_moment K hd`; `W_eq_S` with `aker_symm` turns
-- `t * W(a_r)` into `(2t) * S / N`; `LogGas.Decoupling.exp_bound` with `θ = 2t`
-- (`Cu κ |2t| ≤ 1/2 < 1`, `abs_of_nonneg`); and `2 / (1 - x^2) ≤ 8/3` for `0 ≤ x ≤ 1/2`
-- (`div_le_div_of_nonneg_left`, `nlinarith`, `norm_num`).
/-- Eq. `eq:physical-average-exponential-bound` (5.7): there is `r_1 > 0` (i.e. `J_0`) such
that for every singular kernel at scale `r ≤ r_1`, every `N ≥ 1` and `0 ≤ t ≤ t_0`,
`𝔼 e^{t W_N(a_r)} ≤ 2/(1 - (2 t C_u κ(r))^2) ≤ 8/3`. -/
theorem aker_exp_bound (d : ℕ) (hd : 1 ≤ d) (Cc V : ℝ) (t0 : ℝ) (ht0 : 0 < t0) :
    ∃ r1 : ℝ, 0 < r1 ∧
      ∀ {M : ℕ} (bx : Boxes μE M) (G : SimpleGraph (Fin M))
        (K : SingularKernel μE bx G d Cc V), K.r ≤ r1 →
        ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ},
          1 ≤ N → ∀ (X : Fin N → Ω → E), (∀ i, Measurable (X i)) → iIndepFun X μ →
          (∀ i, μ.map (X i) = μE) → ∀ t : ℝ, 0 ≤ t → t ≤ t0 →
          ∫ ω, Real.exp (t * W (aker bx K.s K.c) X ω) ∂μ ≤ 8 / 3 := by
  sorry

end AveragingExp

/-! ### S5: factorial moments of the singular part under box measures, (5.8) -/

section SingularMoments

variable {bx : Boxes μE M} {G : SimpleGraph (Fin M)} {d : ℕ} {Cc V : ℝ}

-- SKETCH: layer cake `lintegral_rpow_eq_lintegral_meas_lt_mul` (with `p : ℝ` via
-- `Real.rpow_natCast`) for `g z = max 0 (log (r / dist z 0))`, measurable by
-- `(continuous_id.dist continuous_const).measurable`, `Real.measurable_log`, `measurable_const.max`.
-- For `u > 0`: `{z | u < g z} ⊆ Metric.ball 0 (r * exp (-u))` (`Real.lt_log_iff_exp_lt`,
-- `lt_div_iff₀`, `Metric.mem_ball`), so `μE {u < g} ≤ ofReal (V r^d exp (-d u))` by
-- `K.ball_vol` (`Real.exp_neg`, `mul_pow`, `Real.exp_nat_mul`).  Then
-- `∫_0^∞ p u^(p-1) V r^d e^{-du} du = V r^d p Γ(p) / d^p` via `integral_rpow_mul_exp_neg_mul_Ioi`
-- and `Real.Gamma_nat_eq_factorial`; convert with `ofReal_integral_eq_lintegral_ofReal`.
/-- The layer-cake computation behind eq. `eq:physical-singular-factorial` (5.8):
`∫ (log(r/dist(z,0)))_+^p dμ ≤ |B_r| p!/d^p` with `|B_r| ≤ V r^d`. -/
theorem log_moment (K : SingularKernel μE bx G d Cc V) (hd : 1 ≤ d) (p : ℕ) (hp : 1 ≤ p) :
    ∫⁻ z, ENNReal.ofReal (max 0 (Real.log (K.r / dist z 0)) ^ p) ∂μE
      ≤ ENNReal.ofReal (V * K.r ^ d * p.factorial / d ^ p) := by
  sorry

-- SKETCH: `lintegral_mono_ae` with `K.s_log`, `hs'.le`, `hs'.nonneg` and
-- `pow_le_pow_left₀` (`ENNReal.ofReal_le_ofReal`), then `log_moment`.
/-- "`M ∫ s_r^p dμ ≤ M |B_r| p!/d^p`" (eq. (5.8)), the `∫ s_r^p dμ` part, for every sub-kernel. -/
theorem s_moment (K : SingularKernel μE bx G d Cc V) (hd : 1 ≤ d) {s' : E → ℝ} (hs' : K.Sub s')
    (p : ℕ) (hp : 1 ≤ p) :
    ∫⁻ z, ENNReal.ofReal (s' z ^ p) ∂μE ≤ ENNReal.ofReal (V * K.r ^ d * p.factorial / d ^ p) := by
  sorry

-- SKETCH: `lintegral_mono' (boxMeasure_le bx a)`, `lintegral_smul_measure`,
-- `lintegral_sub_right_eq_self` (resp. `lintegral_sub_left_eq_self`), `s_moment`, and
-- `M * (V r^d p!/d^p) ≤ V p!/d^p` from `K.Mr`, `K.V_nonneg` (`ENNReal.ofReal_mul`,
-- `ENNReal.ofReal_le_ofReal`, `mul_le_of_le_one_left`-style with `nlinarith`).
/-- "`M ∫ s_r^p dμ ≤ C^p p!`" (eq. (5.8)): moments of `s'(x - y)` under a box measure in
either variable are bounded by `V p!/d^p`. -/
theorem box_ker_moment (K : SingularKernel μE bx G d Cc V) (hd : 1 ≤ d) {s' : E → ℝ}
    (hs' : K.Sub s') (a : Fin M) (p : ℕ) (hp : 1 ≤ p) :
    (∀ y, ∫⁻ x, ENNReal.ofReal (s' (x - y) ^ p) ∂(boxMeasure bx a)
        ≤ ENNReal.ofReal (V * p.factorial / d ^ p)) ∧
    (∀ x, ∫⁻ y, ENNReal.ofReal (s' (x - y) ^ p) ∂(boxMeasure bx a)
        ≤ ENNReal.ofReal (V * p.factorial / d ^ p)) := by
  sorry

-- SKETCH: "the averages subtracted to form `h_r` are bounded by `M c_r ≤ C`": each of
-- `QJx (ker s')`, `QJy (ker s')`, `QJx (QJy (ker s'))` lies in `[0, M c]` (`QJ_nonneg`, `QJ_le`
-- with `integral_ker_left`/`integral_ker_right`, `hs'.le`, `integral_mono`, `K.c_def`), and
-- `M c ≤ Cc` (`Mc_le`); then `abs_le`, `linarith` with `hs'.nonneg`.
/-- `|h_r(x, y)| ≤ s_r(x - y) + 3C`: the averaged terms are bounded by `M c_r ≤ C`. -/
theorem hker_abs_le (K : SingularKernel μE bx G d Cc V) {s' : E → ℝ} (hs' : K.Sub s') (x y : E) :
    |hker bx s' x y| ≤ s' (x - y) + 3 * Cc := by
  sorry

/-- The universal constant `κ_*` of eq. `eq:physical-singular-factorial` (5.8), depending only
on `d`-independent data `C`, `V`: `κ_* = 2 max(V,1) max(3C,1)`. -/
noncomputable def kappaStar (Cc V : ℝ) : ℝ := 2 * max V 1 * max (3 * Cc) 1

-- SKETCH: `positivity` / `mul_pos` with `lt_max_of_lt_right one_pos`.
/-- `κ_* > 0`. -/
theorem kappaStar_pos (Cc V : ℝ) : 0 < kappaStar Cc V := by
  sorry

-- SKETCH: `|h|^p ≤ (s' + 3Cc)^p ≤ 2^(p-1) (s'^p + (3Cc)^p)` (`hker_abs_le`, `pow_le_pow_left₀`,
-- `add_pow_le_pow_mul_pow_of_sq_le_sq` or `inner_le_nnorm_mul_nnorm`-free convexity:
-- `(convexOn_pow p).2` with weights `1/2`), integrate with `lintegral_mono`, `lintegral_add_left`,
-- `lintegral_const`, `box_ker_moment`; then `2^(p-1) (V p!/d^p + (3Cc)^p) ≤ 2 κ_*^p p!` using
-- `d^p ≥ 1`, `V ≤ max V 1 ≤ (max V 1)^p`, `(3Cc)^p ≤ (max (3Cc) 1)^p`, `1 ≤ p!`, `mul_pow`.
/-- Eq. `eq:physical-singular-factorial` (5.8): under the box-uniform measures, for every
`p ≥ 1`, `sup_y ∫ |h_r(x,y)|^p dν_a(x) ≤ 2 κ_*^p p!` and `sup_x ∫ |h_r(x,y)|^p dν_a(y) ≤ 2 κ_*^p p!`,
with `κ_*` independent of `J` (stated for every sub-kernel `s'`, in particular for `s_r` and
its truncations). -/
theorem hker_moment (K : SingularKernel μE bx G d Cc V) (hd : 1 ≤ d) {s' : E → ℝ}
    (hs' : K.Sub s') (a : Fin M) (p : ℕ) (hp : 1 ≤ p) :
    (∀ y, ∫⁻ x, ENNReal.ofReal (|hker bx s' x y| ^ p) ∂(boxMeasure bx a)
        ≤ ENNReal.ofReal (2 * kappaStar Cc V ^ p * p.factorial)) ∧
    (∀ x, ∫⁻ y, ENNReal.ofReal (|hker bx s' x y| ^ p) ∂(boxMeasure bx a)
        ≤ ENNReal.ofReal (2 * kappaStar Cc V ^ p * p.factorial)) := by
  sorry

/-- Finite nonnegative moments imply genuine Bochner integrability, including for `s_r`.
This avoids the convention that the integral of a nonintegrable function is zero. -/
theorem hker_integrable_pow_left (K : SingularKernel μE bx G d Cc V) (hd : 1 ≤ d)
    {s' : E → ℝ} (hs' : K.Sub s') (a : Fin M) (p : ℕ) (hp : 1 ≤ p) (y : E) :
    Integrable (fun x => |hker bx s' x y| ^ p) (boxMeasure bx a) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (((measurable_hker s' hs'.meas).comp (measurable_id.prodMk measurable_const)).abs.pow_const p).aestronglyMeasurable
    (ae_of_all _ fun x => pow_nonneg (abs_nonneg _) p)).mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((hker_moment K hd hs' a p hp).1 y)

theorem hker_integrable_pow_right (K : SingularKernel μE bx G d Cc V) (hd : 1 ≤ d)
    {s' : E → ℝ} (hs' : K.Sub s') (b : Fin M) (p : ℕ) (hp : 1 ≤ p) (x : E) :
    Integrable (fun y => |hker bx s' x y| ^ p) (boxMeasure bx b) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (((measurable_hker s' hs'.meas).comp (measurable_const.prodMk measurable_id)).abs.pow_const p).aestronglyMeasurable
    (ae_of_all _ fun y => pow_nonneg (abs_nonneg _) p)).mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((hker_moment K hd hs' b p hp).2 x)

/-- Eq. (5.8) as Bochner moments, without truncation or boundedness assumptions. -/
theorem hker_moment_integral (K : SingularKernel μE bx G d Cc V) (hd : 1 ≤ d)
    {s' : E → ℝ} (hs' : K.Sub s') (a : Fin M) (p : ℕ) (hp : 1 ≤ p) :
    (∀ y, ∫ x, |hker bx s' x y| ^ p ∂boxMeasure bx a
      ≤ 2 * kappaStar Cc V ^ p * p.factorial) ∧
    (∀ x, ∫ y, |hker bx s' x y| ^ p ∂boxMeasure bx a
      ≤ 2 * kappaStar Cc V ^ p * p.factorial) := by
  constructor
  · intro y
    exact (ENNReal.ofReal_le_ofReal_iff (by have := kappaStar_pos Cc V; positivity)).mp
      ((ofReal_integral_eq_lintegral_ofReal (hker_integrable_pow_left K hd hs' a p hp y)
        (ae_of_all _ fun x => pow_nonneg (abs_nonneg _) p)).trans_le
        ((hker_moment K hd hs' a p hp).1 y))
  · intro x
    exact (ENNReal.ofReal_le_ofReal_iff (by have := kappaStar_pos Cc V; positivity)).mp
      ((ofReal_integral_eq_lintegral_ofReal (hker_integrable_pow_right K hd hs' a p hp x)
        (ae_of_all _ fun y => pow_nonneg (abs_nonneg _) p)).trans_le
        ((hker_moment K hd hs' a p hp).2 x))

/-- Joint moments are integrable by Fubini and the uniform slice moment bound. -/
theorem hker_integrable_pow_prod (K : SingularKernel μE bx G d Cc V) (hd : 1 ≤ d)
    {s' : E → ℝ} (hs' : K.Sub s') (a b : Fin M) (p : ℕ) (hp : 1 ≤ p) :
    Integrable (fun z : E × E => |hker bx s' z.1 z.2| ^ p)
      ((boxMeasure bx a).prod (boxMeasure bx b)) := by
  apply (integrable_prod_iff' ((measurable_hker s' hs'.meas).abs.pow_const p).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (hker_integrable_pow_left K hd hs' a p hp), ?_⟩
  apply Integrable.of_bound
    ((show StronglyMeasurable (uncurry (fun x y => ‖|hker bx s' x y| ^ p‖)) from
      ((measurable_hker s' hs'.meas).abs.pow_const p).stronglyMeasurable.norm).integral_prod_left.aestronglyMeasurable)
    (2 * kappaStar Cc V ^ p * p.factorial)
  filter_upwards [] with y
  change ‖∫ x, ‖|hker bx s' x y| ^ p‖ ∂boxMeasure bx a‖ ≤ _
  have heq : ∀ x : E, ‖|hker bx s' x y| ^ p‖ = |hker bx s' x y| ^ p :=
    fun x => Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) p)
  simp_rw [heq]
  rw [Real.norm_of_nonneg (integral_nonneg fun x => pow_nonneg (abs_nonneg _) p)]
  exact (hker_moment_integral K hd hs' a p hp).1 y

-- SKETCH: `hker bx (trunc R K.s)` is bounded by `R + 3 Cc` (`hker_abs_le`, `min_le_right`),
-- so `|h|^p` is integrable on the probability measure `ν_a` (`Integrable.of_bound`), and
-- `ofReal_integral_eq_lintegral_ofReal` + `ENNReal.ofReal_le_ofReal_iff` transfer `hker_moment`.
/-- Eq. (5.8) for the truncated kernels `h_r^R`, as Bochner integrals (the form required by
`LogGas.Decoupling.Hyp`). -/
theorem hker_moment_trunc (K : SingularKernel μE bx G d Cc V) (hd : 1 ≤ d) {R : ℝ} (hR : 0 ≤ R)
    (a : Fin M) (p : ℕ) (hp : 1 ≤ p) :
    (∀ y, ∫ x, |hker bx (trunc R K.s) x y| ^ p ∂(boxMeasure bx a)
        ≤ 2 * kappaStar Cc V ^ p * p.factorial) ∧
    (∀ x, ∫ y, |hker bx (trunc R K.s) x y| ^ p ∂(boxMeasure bx a)
        ≤ 2 * kappaStar Cc V ^ p * p.factorial) := by
  exact hker_moment_integral K hd (SingularKernel.Sub.trunc K hR) a p hp

end SingularMoments

/-! ### S6: the occupancy decomposition, (2.3)/(5.9) -/

section Occupancy

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}

/-- The coordinate variables `Y_i(x) = x_i` on the product space `Fin N → E`. -/
abbrev coord (N : ℕ) (i : Fin N) (x : Fin N → E) : E := x i

/-- The occupancy `n_a(L) = #{i : L_i = a}` of a label vector. -/
def labelCount (L : Fin N → Fin M) (a : Fin M) : ℕ := (univ.filter (fun i => L i = a)).card

/-- A good label vector: `max_a n_a ≤ δ N` (the condition of `𝓐_{N,J,δ}`,
eq. `eq:physical-neighbor-events`). -/
def GoodLabel (L : Fin N → Fin M) (δ : ℝ) : Prop := ∀ a, (labelCount L a : ℝ) ≤ δ * N

/-- The law `𝔼_n` of eq. `eq:partition-occupancy-sum` (2.3), indexed by the label vector `L`:
independent particles, particle `i` distributed according to `ν_{L_i}`. -/
noncomputable def labelMeasure (bx : Boxes μE M) (L : Fin N → Fin M) : Measure (Fin N → E) :=
  Measure.pi (fun i => boxMeasure bx (L i))

/-- `𝔼_n` is a probability measure. -/
instance isProbabilityMeasure_labelMeasure (bx : Boxes μE M) (L : Fin N → Fin M) :
    IsProbabilityMeasure (labelMeasure bx L) := by
  unfold labelMeasure; infer_instance

/-- The multinomial weight `π_N(n) = N!/(M^N ∏_a n_a!)` of eq. `eq:partition-occupancy-sum`
(2.3). -/
noncomputable def piN (M N : ℕ) (n : Fin M → ℕ) : ℝ≥0∞ :=
  (Nat.multinomial univ n : ℝ≥0∞) / (M : ℝ≥0∞) ^ N

/-- The good event `𝓐_{N,J,δ} = {n_a ≤ δ N for every a}` (eq. `eq:physical-neighbor-events`). -/
def goodEvent (X : Fin N → Ω → E) (bx : Boxes μE M) (δ : ℝ) : Set Ω :=
  {ω | ∀ a, (occupancy X (bx.A a) ω : ℝ) ≤ δ * N}

omit [MeasurableAdd₂ E] [MeasurableNeg E] [PseudoMetricSpace E] [OpensMeasurableSpace E]
  [IsProbabilityMeasure μE] [μE.IsAddLeftInvariant] [μE.IsNegInvariant] in
/-- `𝓐_{N,J,δ}` is the complement of the bad event `𝓑_{N,J,δ}` of `LogGas.BadEvent`. -/
theorem goodEvent_eq_compl (X : Fin N → Ω → E) (bx : Boxes μE M) (δ : ℝ) :
    goodEvent X bx δ = (badEvent X bx δ)ᶜ := by
  ext ω; simp [goodEvent, badEvent, not_lt]

omit [MeasurableAdd₂ E] [MeasurableNeg E] [PseudoMetricSpace E] [OpensMeasurableSpace E]
  [IsProbabilityMeasure μE] [μE.IsAddLeftInvariant] [μE.IsNegInvariant] in
/-- The good event is measurable. -/
theorem measurableSet_goodEvent (X : Fin N → Ω → E) (hX : ∀ i, Measurable (X i))
    (bx : Boxes μE M) (δ : ℝ) : MeasurableSet (goodEvent X bx δ) := by
  rw [goodEvent_eq_compl]; exact (measurableSet_badEvent X hX bx δ).compl

omit [MeasurableAdd₂ E] [MeasurableNeg E] [PseudoMetricSpace E] [OpensMeasurableSpace E]
  [IsProbabilityMeasure μE] [μE.IsAddLeftInvariant] [μE.IsNegInvariant] in
/-- The good event is the preimage of the good set of the product space under
`ω ↦ (X_i(ω))_i`. -/
theorem goodEvent_preimage (X : Fin N → Ω → E) (bx : Boxes μE M) (δ : ℝ) :
    goodEvent X bx δ = (fun ω i => X i ω) ⁻¹' goodEvent (coord N) bx δ :=
  rfl

-- SKETCH: `Measure.pi_eq`: for a box `Set.pi univ t`, the left side is `∏ i, μE (t i)`
-- (`Measure.pi_pi`); write `μE = M⁻¹ • ∑ a, ν_a` (`μE_eq_sum_boxMeasure`), so
-- `∏ i, M⁻¹ ∑ a, ν_a (t i) = M^{-N} ∑ L, ∏ i, ν_{L i} (t i)` (`Finset.prod_univ_sum`,
-- `Finset.prod_mul_distrib`, `Finset.prod_const`, `ENNReal.inv_pow`), which is the right side
-- evaluated on the box (`Measure.smul_apply`, `Measure.coe_finset_sum`, `Finset.sum_apply`,
-- `Measure.pi_pi`).
/-- The retagging identity behind eq. `eq:partition-occupancy-sum` (2.3), before grouping by
occupancies: the i.i.d. law `μ^{⊗N}` is the average over all label vectors of `𝔼_L`,
`μ^{⊗N} = M^{-N} ∑_L ⨂_i ν_{L_i}`. -/
theorem pi_eq_sum_labels (bx : Boxes μE M) :
    (Measure.pi (fun _ : Fin N => μE)) = ((M : ℝ≥0∞) ^ N)⁻¹ • ∑ L : Fin N → Fin M, labelMeasure bx L := by
  sorry

-- SKETCH: `Measure.ae_pi_le_pi` (`Filter.pi`, `Filter.mem_pi`): a.e. for `Measure.pi` is implied
-- by a.e. in each coordinate (`ae_all_iff` over the finite index set), and `ae_mem_boxMeasure`
-- for each `i`.  Concretely: `(Measure.ae_pi_le_pi) (Filter.pi_mem_pi …)` or
-- `MeasureTheory.Measure.ae_pi_eval`-style lemmas (`ae_eval_ne`, `Measure.pi_map_eval`).
/-- Under `𝔼_L`, almost surely particle `i` lies in the box `A_{L_i}`. -/
theorem ae_labels_mem (bx : Boxes μE M) (L : Fin N → Fin M) :
    ∀ᵐ x ∂(labelMeasure bx L), ∀ i, x i ∈ bx.A (L i) := by
  sorry

-- SKETCH: on the a.e. set of `ae_labels_mem`, `(bx.A a).indicator 1 (x i) = if L i = a then 1 else 0`
-- (`bx.disj`, `Set.disjoint_left`, `Set.indicator_apply`), so `occupancy (coord N) (A a) x =
-- labelCount L a` (`occupancy`, `labelCount`, `Finset.card_filter`, `Finset.sum_boole`), and the
-- two conditions coincide (`goodEvent`, `GoodLabel`).
/-- Under `𝔼_L` the good event is almost surely the deterministic condition
"`L` is a good label vector". -/
theorem goodEvent_ae_iff (bx : Boxes μE M) (L : Fin N → Fin M) (δ : ℝ) :
    ∀ᵐ x ∂(labelMeasure bx L), x ∈ goodEvent (coord N) bx δ ↔ GoodLabel L δ := by
  sorry

-- SKETCH: `goodEvent_preimage` and `lintegral_map` (`measurableSet_goodEvent`,
-- `Measurable.indicator`, `measurable_pi_lambda`) move the integral to `μ.map (fun ω i => X i ω)
-- = Measure.pi (fun _ => μE)` (`iIndepFun_iff_map_fun_eq_pi_map`, `hX_law`); `pi_eq_sum_labels`,
-- `lintegral_smul_measure`, `lintegral_finset_sum_measure`.  On each `labelMeasure bx L`,
-- `goodEvent_ae_iff` and `lintegral_congr_ae` replace the indicator by the constant
-- `if GoodLabel L δ then 1 else 0` (`Set.indicator_apply`, `lintegral_const_mul`, `mul_zero`,
-- `lintegral_zero`).
open scoped Classical in
/-- Eq. `eq:physical-good-occupancy-sum` (5.9), label-vector form: for measurable `F ≥ 0`,
`𝔼[1_𝓐 F(X)] = ∑_{L good} M^{-N} 𝔼_L[F]`. -/
theorem label_decomposition (μ : Measure Ω) [IsProbabilityMeasure μ] (bx : Boxes μE M) (δ : ℝ)
    (X : Fin N → Ω → E) (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X μ)
    (hX_law : ∀ i, μ.map (X i) = μE) (F : (Fin N → E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, (goodEvent X bx δ).indicator (fun ω => F (fun i => X i ω)) ω ∂μ
      = ∑ L : Fin N → Fin M,
          if GoodLabel L δ then ((M : ℝ≥0∞) ^ N)⁻¹ * ∫⁻ x, F x ∂(labelMeasure bx L) else 0 := by
  sorry

-- SKETCH: start from `label_decomposition` and group the label vectors by their occupancy
-- `labelCount L` (`Finset.sum_fiberwise_of_maps_to` into `Finset.Nat.antidiagonalTuple M N`,
-- using `∑ a, labelCount L a = N` by `Finset.card_eq_sum_card_fiberwise`).  For `L` with
-- `labelCount L = n`, there is `σ : Equiv.Perm (Fin N)` with `L = retag n ∘ σ`
-- (`Fintype.card_eq`-bijections between the fibres `{i | L i = a}` and `{i | retag n i = a}`,
-- glued over `a`), and `labelMeasure bx L = (labelMeasure bx (retag n)).map (· ∘ σ)`
-- (`Measure.pi_map_piCongrLeft` / `MeasurePreserving.piCongrLeft`), so `lintegral_map` and
-- `hsymm` give equal integrals.  The fibre over `n` has `Nat.multinomial univ n` elements
-- (`Nat.multinomial_spec`; count words with prescribed multiplicities as in
-- `LogGas.Decoupling.sum_factorial_mult`), whence the weight `π_N(n)` (`piN`, `Finset.sum_const`,
-- `nsmul_eq_mul`, `ENNReal.div_eq_inv_mul`).  Good labels correspond to good `n` (`GoodLabel`).
/-- Eq. `eq:partition-occupancy-sum` (2.3) restricted to the good event, i.e.
eq. `eq:physical-good-occupancy-sum` (5.9):
`𝔼[1_𝓐 F] = ∑_{n : ∑ n_a = N, max n_a ≤ δN} π_N(n) 𝔼_n[F]` for symmetric measurable `F ≥ 0`,
where `𝔼_n` retags the particles in any fixed order `retag n` with occupancies `n`.
(Not used downstream: `label_decomposition` suffices for Lemma 5.1.) -/
theorem occupancy_decomposition (μ : Measure Ω) [IsProbabilityMeasure μ] (bx : Boxes μE M) (δ : ℝ)
    (X : Fin N → Ω → E) (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X μ)
    (hX_law : ∀ i, μ.map (X i) = μE) (F : (Fin N → E) → ℝ≥0∞) (hF : Measurable F)
    (hsymm : ∀ σ : Equiv.Perm (Fin N), ∀ x, F (x ∘ σ) = F x)
    (retag : (Fin M → ℕ) → Fin N → Fin M)
    (hretag : ∀ n ∈ Finset.Nat.antidiagonalTuple M N, ∀ a, labelCount (retag n) a = n a) :
    ∫⁻ ω, (goodEvent X bx δ).indicator (fun ω => F (fun i => X i ω)) ω ∂μ
      = ∑ n ∈ (Finset.Nat.antidiagonalTuple M N).filter (fun n => ∀ a, (n a : ℝ) ≤ δ * N),
          piN M N n * ∫⁻ x, F x ∂(labelMeasure bx (retag n)) := by
  sorry

end Occupancy

/-! ### S7: few particles make the singular term perturbative, (5.10)–(5.11) -/

section Grouped

variable {N : ℕ}
variable {bx : Boxes μE M} {G : SimpleGraph (Fin M)} {d : ℕ} {Cc V : ℝ}

/-- The hypotheses of Lemma 6.1 for a single symmetric kernel with finite moments under the box measures,
together with locality: exactly what Step 3 of the proof of Lemma 5.1 verifies for `h_r`
(centering (6.1) under every `ν_a`, moments (6.2) with `κ`, vanishing between distinct
non-adjacent boxes). -/
structure BoxKernel (bx : Boxes μE M) (G : SimpleGraph (Fin M)) (h : E → E → ℝ) (κ : ℝ) :
    Prop where
  κ_pos : 0 < κ
  meas : Measurable (uncurry h)
  integrable_pow : ∀ a b (p : ℕ), 1 ≤ p →
    Integrable (fun z : E × E => |h z.1 z.2| ^ p)
      ((boxMeasure bx a).prod (boxMeasure bx b))
  symm : ∀ x y, h x y = h y x
  centered_left : ∀ a b, ∀ᵐ y ∂boxMeasure bx b, ∫ x, h x y ∂(boxMeasure bx a) = 0
  centered_right : ∀ a b, ∀ᵐ x ∂boxMeasure bx a, ∫ y, h x y ∂(boxMeasure bx b) = 0
  moment_left : ∀ a b (p : ℕ), 1 ≤ p → ∀ᵐ y ∂boxMeasure bx b,
    ∫ x, |h x y| ^ p ∂(boxMeasure bx a) ≤ 2 * κ ^ p * p.factorial
  moment_right : ∀ a b (p : ℕ), 1 ≤ p → ∀ᵐ x ∂boxMeasure bx a,
    ∫ y, |h x y| ^ p ∂(boxMeasure bx b) ≤ 2 * κ ^ p * p.factorial
  local_ : ∀ a b, a ≠ b → ¬ G.Adj a b → ∀ x ∈ bx.A a, ∀ y ∈ bx.A b, h x y = 0

/-- The kernels `h_{ij}` fed to Lemma 6.1 under `𝔼_L`: `h` localized to the boxes of the labels
of `i` and `j`, `h_{ij}(x, y) = 1_{A_{L_i}}(x) 1_{A_{L_j}}(y) h(x, y)`; this equals `h` almost
surely and vanishes identically between distinct non-adjacent groups. -/
noncomputable def labelKer (bx : Boxes μE M) (L : Fin N → Fin M) (h : E → E → ℝ) (i j : Fin N)
    (x y : E) : ℝ :=
  (bx.A (L i)).indicator 1 x * (bx.A (L j)).indicator 1 y * h x y

-- SKETCH: `κ_pos := H.κ_pos`; `Y_meas i := measurable_pi_apply i`; `Y_indep` via
-- `iIndepFun_iff_map_fun_eq_pi_map`: `map (fun x i => x i) = map id = labelMeasure`, and
-- `map (eval i) (Measure.pi ν) = ν i` (`Measure.pi_map_eval`, `measure_univ`, `Finset.prod_const_one`);
-- `Y_law` the same; `h_meas` from `H.meas` and indicators; `h_int` by restricting the joint moment integral to the measurable box rectangle; centering: pull the constant `1_{A_{L j}}(y)` out
-- (`integral_const_mul`) and `∫ 1_{A_{L i}} h(·, y) dν_{L i} = ∫ h(·, y) dν_{L i} = 0`
-- (`integral_congr_ae` with `ae_mem_boxMeasure`, `H.centered_left`); moments likewise
-- (`|1_A x * 1_B y * h| ^ p ≤ |h| ^ p`, `integral_mono`, `H.moment_left`).
/-- Eq. (5.10), first part: under `𝔼_L` the coordinates are independent with laws `ν_{L_i}`,
and the localized kernels satisfy (6.1)–(6.2) with constant `κ`. -/
theorem hyp_labels {h : E → E → ℝ} {κ : ℝ} (H : BoxKernel bx G h κ) (L : Fin N → Fin M) :
    Hyp (labelMeasure bx L) (fun i => boxMeasure bx (L i)) (coord N) (labelKer bx L h) κ := by
  classical
  refine { κ_pos := H.κ_pos
           Y_meas := fun i => measurable_pi_apply i
           Y_indep := iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
           Y_law := fun i => (measurePreserving_eval (fun i => boxMeasure bx (L i)) i).map_eq
           h_meas := ?_
           h_int := ?_
           centered_left := ?_
           centered_right := ?_
           moment_left := ?_
           moment_right := ?_ }
  · intro i j
    exact (((measurable_const.indicator (bx.meas (L i))).comp measurable_fst).mul
      ((measurable_const.indicator (bx.meas (L j))).comp measurable_snd)).mul H.meas
  · intro i j p hp
    convert (H.integrable_pow (L i) (L j) p hp).indicator
      ((bx.meas (L i)).prod (bx.meas (L j))) using 1
    funext z
    by_cases hx : z.1 ∈ bx.A (L i) <;> by_cases hy : z.2 ∈ bx.A (L j) <;>
      simp [labelKer, Set.indicator, hx, hy, zero_pow (by omega : p ≠ 0)]
  · intro i j _
    filter_upwards [H.centered_left (L i) (L j), ae_mem_boxMeasure bx (L j)] with y hc hy
    rw [← hc]
    apply integral_congr_ae
    filter_upwards [ae_mem_boxMeasure bx (L i)] with x hx
    simp [labelKer, hx, hy]
  · intro i j _
    filter_upwards [H.centered_right (L i) (L j), ae_mem_boxMeasure bx (L i)] with x hc hx
    rw [← hc]
    apply integral_congr_ae
    filter_upwards [ae_mem_boxMeasure bx (L j)] with y hy
    simp [labelKer, hx, hy]
  · intro i j _ p hp
    filter_upwards [H.moment_left (L i) (L j) p hp, ae_mem_boxMeasure bx (L j)] with y hm hy
    have heq : (fun x => |labelKer bx L h i j x y| ^ p) =ᵐ[boxMeasure bx (L i)]
        (fun x => |h x y| ^ p) := by
      filter_upwards [ae_mem_boxMeasure bx (L i)] with x hx
      simp [labelKer, hx, hy]
    rwa [integral_congr_ae heq]
  · intro i j _ p hp
    filter_upwards [H.moment_right (L i) (L j) p hp, ae_mem_boxMeasure bx (L i)] with x hm hx
    have heq : (fun y => |labelKer bx L h i j x y| ^ p) =ᵐ[boxMeasure bx (L j)]
        (fun y => |h x y| ^ p) := by
      filter_upwards [ae_mem_boxMeasure bx (L j)] with y hy
      simp [labelKer, hx, hy]
    rwa [integral_congr_ae heq]


-- SKETCH: on the a.e. set of `ae_labels_mem`, every indicator equals `1`
-- (`Set.indicator_of_mem`, `one_mul`), so the double sums defining `S` agree termwise
-- (`Filter.Eventually.mono`, `Finset.sum_congr`).
/-- Under `𝔼_L`, `S` for the localized kernels coincides a.s. with `S` for `h`. -/
theorem S_labelKer_ae (bx : Boxes μE M) (L : Fin N → Fin M) (h : E → E → ℝ) :
    ∀ᵐ x ∂(labelMeasure bx L), S (labelKer bx L h) (coord N) x = S (fun _ _ => h) (coord N) x := by
  sorry

-- SKETCH: `W_eq_S` with `H.symm` turns `t * W h` into `(2t) * S / N`; replace `S (fun _ _ => h)`
-- by `S (labelKer bx L h)` a.e. (`S_labelKer_ae`, `integral_congr_ae`); apply
-- `LogGas.Grouped.grouped_exp_bound (hyp_labels H L) hN L (⌊δ N⌋₊) _ G (3^d) _ hdeg _ (2t) _`:
-- `hsize` from `hL` and `Nat.le_floor` (`labelCount`); `hvan` from `H.local_` (the indicators
-- force `x ∈ A (L i)`, `y ∈ A (L j)`, else the product is `0`: `Set.indicator_apply`, `split_ifs`);
-- `hu`: `4 * 3^d * Cu * κ * |2t| * ⌊δN⌋₊ / N ≤ 8 * 3^d * Cu * κ * t * δ ≤ 1/2`
-- (`abs_of_nonneg`, `Nat.floor_le`, `div_le_iff₀`, `nlinarith`).
/-- Eq. `eq:physical-local-effective-coupling` (5.10): for a good label vector and
`8 K C_u κ t δ ≤ 1/2` with `K = 3^d`, the grouped bound (6.4) gives
`𝔼_L[e^{t W_N(h)}] ≤ (8/3)^M` for every box kernel `h` with finite moments. -/
theorem label_exp_bound_of_boxKernel [DecidableRel G.Adj] (hdeg : ∀ a, G.degree a ≤ 3 ^ d - 1)
    {h : E → E → ℝ} {κ : ℝ} (H : BoxKernel bx G h κ) (hN : 1 ≤ N) (L : Fin N → Fin M) (δ : ℝ)
    (hL : GoodLabel L δ) (t : ℝ) (ht : 0 ≤ t) (hδ : 8 * 3 ^ d * Cu * κ * t * δ ≤ 1 / 2) :
    ∫ x, Real.exp (t * W h (coord N) x) ∂(labelMeasure bx L) ≤ (8 / 3) ^ M := by
  sorry

/-- The singular centered kernel and all its sub-kernels satisfy the generalized interface.
No boundedness assumption is needed. -/
theorem hker_boxKernel (K : SingularKernel μE bx G d Cc V) (hd : 1 ≤ d)
    {s' : E → ℝ} (hs' : K.Sub s') : BoxKernel bx G (hker bx s') (kappaStar Cc V) := by
  refine { κ_pos := kappaStar_pos Cc V
           meas := measurable_hker s' hs'.meas
           integrable_pow := fun a b p hp => hker_integrable_pow_prod K hd hs' a b p hp
           symm := hker_symm K hs'
           centered_left := fun a b => ae_of_all _ (hker_box_centered_left K hs' a)
           centered_right := fun a b => ae_of_all _ (hker_box_centered_right K hs' b)
           moment_left := fun a b p hp => ae_of_all _ (hker_moment_integral K hd hs' a p hp).1
           moment_right := fun a b p hp => ae_of_all _ (hker_moment_integral K hd hs' b p hp).2
           local_ := ?_ }
  intro a b hab hadj x hx y hy
  exact hker_local K hs' hab hadj hx hy

/-- Direct application of the generalized decoupling hypotheses to the logarithmically
singular kernel under a label law. All integrability fields are discharged by (5.8). -/
theorem hyp_hker_labels (K : SingularKernel μE bx G d Cc V) (hd : 1 ≤ d) (L : Fin N → Fin M) :
    Hyp (labelMeasure bx L) (fun i => boxMeasure bx (L i)) (coord N)
      (labelKer bx L (hker bx K.s)) (kappaStar Cc V) := by
  exact hyp_labels (hker_boxKernel K hd (SingularKernel.Sub.self K)) L

-- SKETCH: `kappaStar_pos`; `measurable_hker (K.s_meas.min measurable_const)`;
-- `⟨R + 3 * Cc, …⟩` from `hker_abs_le` and `min_le_right`; `hker_symm`,
-- `hker_box_centered_left/right`, `hker_moment_trunc`, `hker_local`, all with `K.Sub.trunc hR`.
/-- Step 3 of the proof of Lemma 5.1 for the truncated kernels: `h_r^R` is a bounded box kernel
with the universal constant `κ_*` of eq. (5.8). -/
theorem hker_trunc_boxKernel (K : SingularKernel μE bx G d Cc V) (hd : 1 ≤ d) {R : ℝ}
    (hR : 0 ≤ R) : BoxKernel bx G (hker bx (trunc R K.s)) (kappaStar Cc V) := by
  exact hker_boxKernel K hd (SingularKernel.Sub.trunc K hR)

-- SKETCH: `label_exp_bound_of_boxKernel hdeg (hker_trunc_boxKernel K hd hR) hN L δ hL t ht hδ`.
/-- Eqs. (5.10)–(5.11) for the truncated kernels: `𝔼_L[e^{t W_N(h_r^R)}] ≤ (8/3)^M` for every
good label vector, uniformly in `R`, `N`, `L`. -/
theorem label_exp_bound_trunc [DecidableRel G.Adj] (hdeg : ∀ a, G.degree a ≤ 3 ^ d - 1)
    (K : SingularKernel μE bx G d Cc V) (hd : 1 ≤ d) {R : ℝ} (hR : 0 ≤ R) (hN : 1 ≤ N)
    (L : Fin N → Fin M) (δ : ℝ) (hL : GoodLabel L δ) (t : ℝ) (ht : 0 ≤ t)
    (hδ : 8 * 3 ^ d * Cu * kappaStar Cc V * t * δ ≤ 1 / 2) :
    ∫ x, Real.exp (t * W (hker bx (trunc R K.s)) (coord N) x) ∂(labelMeasure bx L) ≤ (8 / 3) ^ M := by
  sorry

-- SKETCH: `trunc n K.s z → K.s z` (eventually constant: `min_eq_left` once `K.s z ≤ n`,
-- `tendsto_atTop_of_eventually_const` / `Filter.EventuallyEq.tendsto`).  The box averages
-- converge by dominated convergence `tendsto_integral_of_dominated_convergence` with the bound
-- `K.s (x' - y)` (`integrable_ker_box_left`, `min_le_left`), and the double average by the same
-- with bound `x' ↦ ∫ K.s (x' - y') dν_b(y')` (integrable by Tonelli as in `QJxQJy_ker_swap`);
-- finally `Tendsto.sub`, `Tendsto.add` over the four terms of `hker`, and `QJ` is a finite sum
-- of indicators times these integrals (`tendsto_finset_sum`).
/-- `h_r^R → h_r` pointwise as the truncation level `R = n → ∞`. -/
theorem hker_trunc_tendsto (K : SingularKernel μE bx G d Cc V) (x y : E) :
    Tendsto (fun n : ℕ => hker bx (trunc n K.s) x y) atTop (𝓝 (hker bx K.s x y)) := by
  sorry

-- Use `hker_boxKernel K hd K.Sub.self` and the grouped bound directly.
-- Establish exponential integrability using the positive moment series before converting
-- the Bochner bound to a lintegral bound. An upper bound on a Bochner integral alone does
-- not establish integrability. Truncation/Fatou remains an alternative derivation.
/-- Eq. `eq:physical-centered-local-bound` (5.11) for a fixed good label vector:
`𝔼_L[e^{t W_N(h_r)}] ≤ (8/3)^M`, using the integrable-moment box-kernel interface. -/
theorem label_exp_bound [DecidableRel G.Adj] (hdeg : ∀ a, G.degree a ≤ 3 ^ d - 1)
    (K : SingularKernel μE bx G d Cc V) (hd : 1 ≤ d) (hN : 1 ≤ N) (L : Fin N → Fin M) (δ : ℝ)
    (hL : GoodLabel L δ) (t : ℝ) (ht : 0 ≤ t)
    (hδ : 8 * 3 ^ d * Cu * kappaStar Cc V * t * δ ≤ 1 / 2) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (t * W (hker bx K.s) (coord N) x)) ∂(labelMeasure bx L)
      ≤ ENNReal.ofReal ((8 / 3) ^ M) := by
  sorry

end Grouped

/-! ### S8: Lemma 5.1 -/

section Main

-- SKETCH: `δ0 := 1 / (16 * 3^d * Cu * kappaStar Cc V * t0)` (so `8 K Cu κ_* t δ ≤ 1/2` for
-- `t ≤ t0`, `δ ≤ δ0`) and `r0 := r1` from `aker_exp_bound d hd Cc V t0 ht0`.  Fix the data.
-- Work with `ℓ := ∫⁻ 1_𝓐 ofReal (exp ((t/2) W(s̃_r)))`: by `singular_holder`
-- (`measurableSet_goodEvent`, `K.s_meas`) it is `≤ a^{1/2} b^{1/2}`.  `a ≤ ofReal (8/3)` from
-- `aker_exp_bound` via `ofReal_integral_eq_lintegral_ofReal` (bounded integrand).
-- `b = ∑ L, if GoodLabel L δ then M^{-N} ∫⁻ ofReal (exp (t W(h_r))) ∂𝔼_L else 0` by
-- `label_decomposition` with `F x := ofReal (exp (t * W (hker bx K.s) (coord N) x))`
-- (`goodEvent_preimage`; measurability `measurable_W`, `measurable_hker`), each term
-- `≤ M^{-N} ofReal ((8/3)^M)` by `label_exp_bound`, and `∑_L M^{-N} = 1`
-- (`Finset.card_univ`, `Fintype.card_fun`, `Fintype.card_fin`, `ENNReal.inv_pow`,
-- `ENNReal.mul_inv_cancel`); so `b ≤ ofReal ((8/3)^M)`.  Hence
-- `ℓ ≤ ofReal (8/3)^{1/2} ofReal ((8/3)^M)^{1/2} = ofReal ((8/3)^((M+1)/2))`
-- (`ENNReal.ofReal_rpow_of_nonneg`, `ENNReal.ofReal_mul`, `Real.rpow_natCast`,
-- `Real.rpow_add`, `Real.rpow_mul`).  Finally `ℓ < ⊤` gives integrability of the nonnegative
-- measurable integrand (`Integrable`, `hasFiniteIntegral_iff_ofReal`) and
-- `integral_eq_lintegral_of_nonneg_ae`, `ENNReal.toReal_le_of_le_ofReal` give the bound.
/-- Lemma 5.1 (`lem:physical-local-count-bound`), eq. `eq:physical-local-count-conclusion`
(5.1): for every `t_0 > 0` there are `δ_0 > 0` and `r_0 > 0` (i.e. `J_0`) such that for every
grid with `≤ 3^d - 1` neighbours per box, every singular kernel at scale `r ≤ r_0`, every
`0 < δ ≤ δ_0`, every `N ≥ 1`, i.i.d. particles with law `μ`, and every `0 ≤ t ≤ t_0`,
`𝔼[1_{𝓐_{N,J,δ}} e^{(t/2) W_N(s̃_r)}] ≤ (8/3)^{(M+1)/2}` (and the integrand is integrable).
The constants depend on `d`, `C`, `V`, `t_0` only; in particular not on `N`. -/
theorem lemma51 (d : ℕ) (hd : 1 ≤ d) (Cc V : ℝ) (t0 : ℝ) (ht0 : 0 < t0) :
    ∃ δ0 r0 : ℝ, 0 < δ0 ∧ 0 < r0 ∧
      ∀ {M : ℕ} (bx : Boxes μE M) (G : SimpleGraph (Fin M)) [DecidableRel G.Adj],
        (∀ a, G.degree a ≤ 3 ^ d - 1) →
        ∀ (K : SingularKernel μE bx G d Cc V), K.r ≤ r0 →
        ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
        ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ},
          1 ≤ N → ∀ (X : Fin N → Ω → E), (∀ i, Measurable (X i)) → iIndepFun X μ →
          (∀ i, μ.map (X i) = μE) → ∀ t : ℝ, 0 ≤ t → t ≤ t0 →
          Integrable (fun ω => (goodEvent X bx δ).indicator
            (fun ω => Real.exp ((t / 2) * W (fun x y => K.stilde (x - y)) X ω)) ω) μ ∧
          ∫ ω, (goodEvent X bx δ).indicator
              (fun ω => Real.exp ((t / 2) * W (fun x y => K.stilde (x - y)) X ω)) ω ∂μ
            ≤ (8 / 3 : ℝ) ^ (((M : ℝ) + 1) / 2) := by
  sorry

end Main

end LogGas.Singular
