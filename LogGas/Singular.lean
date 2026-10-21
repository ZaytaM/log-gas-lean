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
  refine ⟨?_⟩
  have hM : (M : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.1 a.pos)
  simp only [boxMeasure, Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_natCast, smul_eq_mul,
    Measure.restrict_apply_univ, bx.vol a]
  exact ENNReal.mul_inv_cancel hM (ENNReal.natCast_ne_top M)

-- SKETCH: unfold `boxMeasure`; `Measure.restrict_le_self` and `Measure.smul_le_smul_left`
-- (`ENNReal.smul_def`, `Measure.le_iff`).
/-- `ν_a ≤ M μ`. -/
theorem boxMeasure_le (bx : Boxes μE M) (a : Fin M) : boxMeasure bx a ≤ (M : ℝ≥0∞) • μE := by
  refine Measure.le_iff'.2 fun s => ?_
  simp only [boxMeasure, Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_natCast, smul_eq_mul]
  exact mul_le_mul_right (Measure.restrict_apply_le _ _) _

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
  have h : μE = ∑ a, μE.restrict (bx.A a) := by
    have := Measure.restrict_iUnion (μ := μE) bx.disj bx.meas
    rw [bx.cover, Measure.restrict_univ] at this
    rw [Measure.sum_fintype] at this
    exact this
  have hM : (M : ℝ≥0∞) ≠ 0 := by
    rintro h0
    have hM0 : M = 0 := by exact_mod_cast h0
    subst hM0
    simp at h
    exact (IsProbabilityMeasure.ne_zero μE) h
  have hb : ∀ a, boxMeasure bx a = (M : ℝ≥0∞) • μE.restrict (bx.A a) := by
    intro a
    simp only [boxMeasure, ENNReal.smul_def, ENNReal.coe_natCast]
  simp only [hb, ← Finset.smul_sum, smul_smul, ENNReal.inv_mul_cancel hM (ENNReal.natCast_ne_top M),
    one_smul]
  exact h

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
  unfold QJ
  exact Finset.measurable_sum _ fun a _ => measurable_const.indicator (bx.meas a)

-- SKETCH: `QJx bx K x y = ∑ a, (A a).indicator 1 x * ∫ x', K x' y ∂ν_a`; the map
-- `y ↦ ∫ x', K x' y ∂ν_a` is measurable by `StronglyMeasurable.integral_prod_left`
-- (`hK.stronglyMeasurable`, `SFinite (boxMeasure bx a)` from the probability instance), then
-- `Measurable.mul` with the indicator composed with `measurable_fst`, `measurable_snd`, and
-- `Finset.measurable_sum`.
/-- Measurability of `Q_{J,x} K` as a function of both variables. -/
theorem measurable_QJx (bx : Boxes μE M) (K : E → E → ℝ) (hK : Measurable (uncurry K)) :
    Measurable (uncurry (QJx bx K)) := by
  unfold QJx QJ
  simp only [uncurry]
  refine Finset.measurable_sum _ fun a _ => ?_
  have h1 : Measurable fun y : E => ∫ x', K x' y ∂(boxMeasure bx a) :=
    (StronglyMeasurable.integral_prod_right (f := fun y x' => K x' y) (ν := boxMeasure bx a)
      (hK.comp measurable_swap).stronglyMeasurable).measurable
  exact Measurable.indicator (h1.comp measurable_snd) (measurable_fst (bx.meas a))

-- SKETCH: as `measurable_QJx` with `StronglyMeasurable.integral_prod_right` and the roles
-- of `measurable_fst`/`measurable_snd` exchanged.
/-- Measurability of `Q_{J,y} K` as a function of both variables. -/
theorem measurable_QJy (bx : Boxes μE M) (K : E → E → ℝ) (hK : Measurable (uncurry K)) :
    Measurable (uncurry (QJy bx K)) := by
  unfold QJy QJ
  have : (uncurry fun x y => ∑ a, (bx.A a).indicator
      (fun _ => ∫ y', K x y' ∂(boxMeasure bx a)) y) = fun p => ∑ a, (Prod.snd ⁻¹' bx.A a).indicator
      (fun p : E × E => ∫ y', K p.1 y' ∂(boxMeasure bx a)) p := by
    ext ⟨x, y⟩
    simp only [uncurry_apply_pair, Set.indicator, Set.mem_preimage]
    rfl
  rw [this]
  refine Finset.measurable_sum _ fun a _ => ?_
  have h := (hK.stronglyMeasurable.integral_prod_right' (ν := boxMeasure bx a)).measurable
  exact Measurable.indicator (h.comp measurable_fst) (measurable_snd (bx.meas a))

-- SKETCH: `QJ bx f = fun _ => ∫ f ∂ν_a` on `A a` (`QJ_apply_of_mem`), and `ν_a`-a.e. `x ∈ A a`
-- (`ae_mem_boxMeasure`); so `integral_congr_ae` turns the left side into `∫ (∫ f ∂ν_a) ∂ν_a`,
-- and `integral_const`, `measure_univ`, `one_smul` finish.
/-- `Q_J` is a projection: `∫ Q_J f dν_a = ∫ f dν_a`. -/
theorem integral_QJ_box (bx : Boxes μE M) (f : E → ℝ) (a : Fin M) :
    ∫ x, QJ bx f x ∂(boxMeasure bx a) = ∫ x, f x ∂(boxMeasure bx a) := by
  have h : ∀ᵐ x ∂(boxMeasure bx a), QJ bx f x = ∫ y, f y ∂(boxMeasure bx a) := by
    filter_upwards [ae_mem_boxMeasure bx a] with x hx
    exact QJ_apply_of_mem bx f hx
  rw [integral_congr_ae h, integral_const]
  simp

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
  have h : Integrable (fun y => s' (x - y)) μE := (Sub.integrable K hs').comp_sub_left x
  exact (h.smul_measure (ENNReal.natCast_ne_top M)).mono_measure (boxMeasure_le bx b)

end SingularKernel

section Split

variable {bx : Boxes μE M} {G : SimpleGraph (Fin M)} {d : ℕ} {Cc V : ℝ}

-- SKETCH: `ker s` uncurried is `s ∘ (fun p => p.1 - p.2)`: `hs.comp measurable_sub`; then
-- `measurable_QJx`, `measurable_QJy` (twice) and `Measurable.add/sub/const`.
/-- `a_r` is measurable in both variables. -/
theorem measurable_aker (s : E → ℝ) (hs : Measurable s) (c : ℝ) :
    Measurable (uncurry (aker bx s c)) := by
  have hk : Measurable (uncurry (ker s)) := hs.comp measurable_sub
  have h1 := measurable_QJx bx (ker s) hk
  have h2 := measurable_QJy bx (ker s) hk
  have h3 := measurable_QJx bx (QJy bx (ker s)) h2
  exact (h1.add h2).sub h3 |>.sub_const c

-- SKETCH: as `measurable_aker`.
/-- `h_r` is measurable in both variables. -/
theorem measurable_hker (s : E → ℝ) (hs : Measurable s) : Measurable (uncurry (hker bx s)) := by
  have hk : Measurable (uncurry (ker s)) := hs.comp measurable_sub
  have h1 := measurable_QJx bx (ker s) hk
  have h2 := measurable_QJy bx (ker s) hk
  have h3 := measurable_QJx bx (QJy bx (ker s)) h2
  have : uncurry (hker bx s) = fun p => uncurry (ker s) p - uncurry (QJx bx (ker s)) p
      - uncurry (QJy bx (ker s)) p + uncurry (QJx bx (QJy bx (ker s))) p := rfl
  rw [this]
  exact ((hk.sub h1).sub h2).add h3

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
  have hI : Integrable s' μE :=
    K.s_int.mono' hs'.meas.aestronglyMeasurable (ae_of_all _ (fun z => by
      rw [Real.norm_of_nonneg (hs'.nonneg z)]; exact hs'.le z))
  have hP : Integrable (fun p : E × E => s' (p.1 - p.2)) (μE.prod μE) := by
    have h1 : Integrable (fun q : E × E => s' q.1) (μE.prod μE) := hI.comp_fst μE
    exact ((measurePreserving_sub_prod μE μE).integrable_comp
      (g := fun q : E × E => s' q.1) h1.aestronglyMeasurable).2 h1
  have hFub : ∀ a b : Fin M, Integrable (fun p : E × E => s' (p.1 - p.2))
      ((boxMeasure bx a).prod (boxMeasure bx b)) := by
    intro a b
    have hle : (boxMeasure bx a).prod (boxMeasure bx b) ≤
        ((M : ℝ≥0∞) * M) • μE.prod μE := by
      calc (boxMeasure bx a).prod (boxMeasure bx b)
          ≤ ((M : ℝ≥0∞) • μE).prod ((M : ℝ≥0∞) • μE) :=
            Measure.prod_mono (boxMeasure_le bx a) (boxMeasure_le bx b)
        _ = ((M : ℝ≥0∞) * M) • μE.prod μE := by
            rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    exact (hP.smul_measure (by simp [ENNReal.mul_eq_top])).mono_measure hle
  obtain ⟨a, ha⟩ : ∃ a, x ∈ bx.A a := by
    have := bx.cover ▸ Set.mem_univ x
    simpa using this
  obtain ⟨b, hb⟩ : ∃ b, y ∈ bx.A b := by
    have := bx.cover ▸ Set.mem_univ y
    simpa using this
  have e1 : QJx bx (QJy bx (ker s')) y x
      = ∫ x', ∫ y', s' (x' - y') ∂(boxMeasure bx a) ∂(boxMeasure bx b) := by
    unfold QJx
    rw [QJ_apply_of_mem bx _ hb]
    refine integral_congr_ae (ae_of_all _ (fun x' => ?_))
    simp only [QJy]
    rw [QJ_apply_of_mem bx _ ha]; rfl
  have e2 : QJx bx (QJy bx (ker s')) x y
      = ∫ x', ∫ y', s' (x' - y') ∂(boxMeasure bx b) ∂(boxMeasure bx a) := by
    unfold QJx
    rw [QJ_apply_of_mem bx _ ha]
    refine integral_congr_ae (ae_of_all _ (fun x' => ?_))
    simp only [QJy]
    rw [QJ_apply_of_mem bx _ hb]; rfl
  rw [e1, e2]
  rw [integral_integral_swap (f := fun x' y' => s' (x' - y')) (hFub b a)]
  refine integral_congr_ae (ae_of_all _ (fun y' => integral_congr_ae (ae_of_all _ (fun x' => ?_))))
  simp only
  rw [← hs'.even (x' - y'), neg_sub]

-- SKETCH: unfold `aker`; `QJx_ker_swap`, `QJxQJy_ker_swap` and `add_comm`.
/-- `a_r` is a symmetric kernel. -/
theorem aker_symm (K : SingularKernel μE bx G d Cc V) (x y : E) :
    aker bx K.s K.c x y = aker bx K.s K.c y x := by
  have h1 := QJx_ker_swap K (SingularKernel.Sub.self K) x y
  have h2 := QJx_ker_swap K (SingularKernel.Sub.self K) y x
  have h3 := QJxQJy_ker_swap K (SingularKernel.Sub.self K) x y
  unfold aker
  rw [h1, ← h2, h3]
  ring

-- SKETCH: unfold `hker`, `ker`; `hs'.even` (`neg_sub`), `QJx_ker_swap`, `QJxQJy_ker_swap`.
/-- `h_r` is a symmetric kernel (for every sub-kernel `s'`). -/
theorem hker_symm (K : SingularKernel μE bx G d Cc V) {s' : E → ℝ} (hs' : K.Sub s') (x y : E) :
    hker bx s' x y = hker bx s' y x := by
  have h1 := QJx_ker_swap K hs' x y
  have h2 := QJx_ker_swap K hs' y x
  have h3 := QJxQJy_ker_swap K hs' x y
  unfold hker
  have h0 : ker s' y x = ker s' x y := by
    simp only [ker]; rw [← neg_sub, hs'.even]
  rw [h0, h3, ← h1]
  rw [QJx_ker_swap K hs' y x] at *
  linarith

-- SKETCH: `hker = (ker - QJx ker) - (QJy ker - QJx (QJy ker))` and
-- `QJx bx K' x y = QJ bx (K' · y) x`; by `integral_sub` and `integral_QJ_box` both brackets
-- integrate to `0` against `ν_a` (integrability: `integrable_ker_box_left`, and `QJ` of an
-- integrable function is bounded).
/-- Eq. (5.2), "`h_r` has zero average in each variable over every box", first variable:
`∫ h_r(x, y) dν_a(x) = 0` for every `a` and `y`. -/
theorem hker_box_centered_left (K : SingularKernel μE bx G d Cc V) {s' : E → ℝ} (hs' : K.Sub s')
    (a : Fin M) (y : E) : ∫ x, hker bx s' x y ∂(boxMeasure bx a) = 0 := by
  have hμ : Integrable (fun p : E × E => s' (p.1 - p.2)) (μE.prod μE) := by
    have hm : Measurable (fun p : E × E => s' (p.1 - p.2)) := hs'.meas.comp measurable_sub
    refine (integrable_prod_iff hm.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun x => (SingularKernel.Sub.integrable K hs').comp_sub_left x
    · have : (fun x => ∫ y, ‖s' (x - y)‖ ∂μE) = fun _ => ∫ z, ‖s' z‖ ∂μE := by
        funext x
        exact integral_sub_left_eq_self (fun z => ‖s' z‖) μE x
      rw [this]
      exact integrable_const _
  have hprod : ∀ a b : Fin M,
      Integrable (fun p : E × E => s' (p.1 - p.2)) ((boxMeasure bx a).prod (boxMeasure bx b)) := by
    intro a b
    have hle : (boxMeasure bx a).prod (boxMeasure bx b) ≤
        ((M : ℝ≥0∞) • μE).prod ((M : ℝ≥0∞) • μE) :=
      Measure.prod_mono (boxMeasure_le bx a) (boxMeasure_le bx b)
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul] at hle
    exact ((hμ.smul_measure (c := (M : ℝ≥0∞) * M)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top M) (ENNReal.natCast_ne_top M))).mono_measure hle)
  have hg : ∀ a : Fin M, Integrable (fun x' => QJy bx (ker s') x' y) (boxMeasure bx a) := by
    intro a
    obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (bx.cover ▸ Set.mem_univ y)
    have : (fun x' => QJy bx (ker s') x' y) = fun x' => ∫ y', s' (x' - y') ∂(boxMeasure bx b) := by
      funext x'
      exact QJ_apply_of_mem bx _ hb
    rw [this]
    exact (hprod a b).integral_prod_left
  have hconst : ∀ (f : E → ℝ), Integrable (QJ bx f) (boxMeasure bx a) := by
    intro f
    unfold QJ
    refine integrable_finsetSum _ fun c _ => ?_
    exact (integrable_const _).indicator (bx.meas c)
  have hG : Integrable (fun x' => ker s' x' y - QJy bx (ker s') x' y) (boxMeasure bx a) :=
    (SingularKernel.integrable_ker_box_left K hs' a y).sub (hg a)
  have heq : (fun x => hker bx s' x y) = fun x =>
      (ker s' x y - QJy bx (ker s') x y) - QJ bx (fun x' => ker s' x' y - QJy bx (ker s') x' y) x := by
    funext x
    have h1 : QJ bx (fun x' => ker s' x' y - QJy bx (ker s') x' y) x
        = QJx bx (ker s') x y - QJx bx (QJy bx (ker s')) x y := by
      unfold QJx
      show _ = QJ bx (fun x' => ker s' x' y) x - QJ bx (fun x' => QJy bx (ker s') x' y) x
      unfold QJ
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hx : x ∈ bx.A c
      · simp only [Set.indicator_of_mem hx]
        exact integral_sub (SingularKernel.integrable_ker_box_left K hs' c y) (hg c)
      · simp [Set.indicator_of_notMem hx]
    unfold hker
    rw [h1]; ring
  have hQ : ∫ x, QJ bx (fun x' => ker s' x' y - QJy bx (ker s') x' y) x ∂(boxMeasure bx a)
      = ∫ x, (ker s' x y - QJy bx (ker s') x y) ∂(boxMeasure bx a) := by
    set g := fun x' => ker s' x' y - QJy bx (ker s') x' y with hgdef
    have hae : (QJ bx g) =ᵐ[boxMeasure bx a]
        fun _ => ∫ x', g x' ∂(boxMeasure bx a) := by
      filter_upwards [ae_mem_boxMeasure bx a] with x hx
      exact QJ_apply_of_mem bx g hx
    rw [integral_congr_ae hae, integral_const]
    simp
  rw [heq, integral_sub hG (hconst _), hQ, sub_self]

-- SKETCH: `hker = (ker - QJy ker) - QJx (ker - QJy ker)` (pointwise, `QJx` is linear:
-- `QJ` of a difference is the difference of `QJ`s by `integral_sub`).  The first term
-- integrates to `0` against `ν_b` in `y` by `integral_QJ_box`.  For the second,
-- `QJx bx K' x y = ∑ a, 1_{A a}(x) ∫ K'(x', y) dν_a(x')`; integrate in `y` and swap with the
-- `ν_a`-integral (`integral_integral_swap`, integrability from the bound by `K.s` as in
-- `QJxQJy_ker_swap`), the inner `∫ (ker - QJy ker)(x', y) dν_b(y)` vanishes.
/-- Eq. (5.2), box centering in the second variable: `∫ h_r(x, y) dν_b(y) = 0`. -/
theorem hker_box_centered_right (K : SingularKernel μE bx G d Cc V) {s' : E → ℝ} (hs' : K.Sub s')
    (b : Fin M) (x : E) : ∫ y, hker bx s' x y ∂(boxMeasure bx b) = 0 := by
  classical
  have hQB : ∀ (f : E → ℝ) (c : Fin M),
      ∫ z, QJ bx f z ∂(boxMeasure bx c) = ∫ z, f z ∂(boxMeasure bx c) := by
    intro f c
    have : ∀ᵐ z ∂(boxMeasure bx c), QJ bx f z = ∫ y, f y ∂(boxMeasure bx c) := by
      filter_upwards [ae_mem_boxMeasure bx c] with z hz
      exact QJ_apply_of_mem bx f hz
    rw [integral_congr_ae this]
    simp
  set F : E → E → ℝ := fun x' y => s' (x' - y) with hFdef
  have hFm : Measurable (uncurry F) := hs'.meas.comp measurable_sub
  have hFker : ker s' = F := rfl
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (bx.cover ▸ Set.mem_univ x)
  have hsi : Integrable s' μE := hs'.integrable K
  have hbox : ∀ (f : E → ℝ), (∀ z, 0 ≤ f z) → Integrable f μE → ∀ c : Fin M,
      ∫ z, f z ∂(boxMeasure bx c) ≤ M * ∫ z, f z ∂μE := by
    intro f hf hfi c
    rw [boxMeasure, ENNReal.smul_def, integral_smul_measure]
    simp only [ENNReal.coe_natCast, ENNReal.toReal_natCast, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hfi (Filter.Eventually.of_forall hf)) (Nat.cast_nonneg M)
  have hFint : ∀ x', Integrable (fun y => F x' y) μE := fun x' => by
    simpa [hFdef] using (hsi.comp_sub_left x')
  have hHm : Measurable (uncurry (QJy bx F)) := measurable_QJy bx F hFm
  have hHb : ∀ x' y, ‖QJy bx F x' y‖ ≤ M * ∫ z, s' z ∂μE := fun x' y => by
    have h0 : 0 ≤ QJy bx F x' y := QJ_nonneg bx _ (fun z => hs'.nonneg _) y
    rw [Real.norm_of_nonneg h0]
    have := QJ_le bx (fun y' => F x' y') (fun z => hs'.nonneg _) (hFint x') y
    have h2 : ∫ z, F x' z ∂μE = ∫ z, s' z ∂μE := SingularKernel.integral_ker_right s' x'
    unfold QJy
    exact this.trans (le_of_eq (by rw [← h2]))
  have hHint : Integrable (uncurry (QJy bx F)) ((boxMeasure bx a).prod (boxMeasure bx b)) :=
    Integrable.of_bound hHm.aestronglyMeasurable _ (Filter.Eventually.of_forall fun p => hHb p.1 p.2)
  have hFint2 : Integrable (uncurry F) ((boxMeasure bx a).prod (boxMeasure bx b)) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun x' => SingularKernel.integrable_ker_box_right K hs' b x', ?_⟩
    have hm : Measurable fun x' => ∫ y, ‖F x' y‖ ∂(boxMeasure bx b) := by
      have h : StronglyMeasurable (uncurry fun x' y => ‖F x' y‖) := hFm.norm.stronglyMeasurable
      exact (h.integral_prod_right (ν := boxMeasure bx b)).measurable
    refine Integrable.of_bound hm.aestronglyMeasurable (M * ∫ z, s' z ∂μE)
      (Filter.Eventually.of_forall fun x' => ?_)
    have h0 : 0 ≤ ∫ y, ‖F x' y‖ ∂(boxMeasure bx b) := integral_nonneg fun _ => norm_nonneg _
    simp only [Function.uncurry_apply_pair]
    rw [Real.norm_of_nonneg h0]
    have := hbox (fun y => F x' y) (fun z => hs'.nonneg _) (hFint x') b
    have h2 : ∫ z, F x' z ∂μE = ∫ z, s' z ∂μE := SingularKernel.integral_ker_right s' x'
    simp only [hFdef] at this ⊢
    simp only [Real.norm_of_nonneg (hs'.nonneg _)]
    exact this.trans (le_of_eq (by rw [SingularKernel.integral_ker_right s' x']))
  have hQx : ∀ (g : E → E → ℝ) y, QJx bx g x y = ∫ x', g x' y ∂(boxMeasure bx a) :=
    fun g y => QJ_apply_of_mem bx _ ha
  have hform : ∀ y, hker bx s' x y = F x y - (∫ x', F x' y ∂(boxMeasure bx a))
      - QJy bx F x y + ∫ x', QJy bx F x' y ∂(boxMeasure bx a) := by
    intro y
    unfold hker
    rw [hFker, hQx F y, hQx (QJy bx F) y]
  simp_rw [hform]
  have i1 : Integrable (fun y => F x y) (boxMeasure bx b) := SingularKernel.integrable_ker_box_right K hs' b x
  have i2 : Integrable (fun y => ∫ x', F x' y ∂(boxMeasure bx a)) (boxMeasure bx b) :=
    hFint2.integral_prod_right
  have i3 : Integrable (fun y => QJy bx F x y) (boxMeasure bx b) :=
    Integrable.of_bound (hHm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun y => hHb x y)
  have i4 : Integrable (fun y => ∫ x', QJy bx F x' y ∂(boxMeasure bx a)) (boxMeasure bx b) :=
    hHint.integral_prod_right
  have i12 : Integrable (fun y => F x y - ∫ x', F x' y ∂(boxMeasure bx a)) (boxMeasure bx b) :=
    i1.sub i2
  have i123 : Integrable (fun y => F x y - (∫ x', F x' y ∂(boxMeasure bx a)) - QJy bx F x y)
      (boxMeasure bx b) := i12.sub i3
  rw [integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2]
  have e3 : ∫ y, QJy bx F x y ∂(boxMeasure bx b) = ∫ y, F x y ∂(boxMeasure bx b) :=
    hQB (fun y' => F x y') b
  have e4 : ∫ y, ∫ x', QJy bx F x' y ∂(boxMeasure bx a) ∂(boxMeasure bx b)
      = ∫ y, ∫ x', F x' y ∂(boxMeasure bx a) ∂(boxMeasure bx b) := by
    rw [← integral_integral_swap hHint, ← integral_integral_swap hFint2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
    exact hQB (fun y' => F x' y') b
  rw [e3, e4]; ring

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
  classical
  have hs : Integrable K.s μE := K.s_int
  have hIQJ : ∀ f : E → ℝ, Integrable (QJ bx f) μE := by
    intro f
    unfold QJ
    exact integrable_finsetSum _ fun a _ => (integrable_const _).indicator (bx.meas a)
  have hQ : ∀ f : E → ℝ, Integrable f μE → ∫ x, QJ bx f x ∂μE = ∫ x, f x ∂μE := by
    intro f hf
    have hμ := μE_eq_sum_boxMeasure bx
    have hint : ∀ a, Integrable f (boxMeasure bx a) := fun a =>
      (hf.smul_measure (c := (M : ℝ≥0∞)) (ENNReal.natCast_ne_top M)).mono_measure
        (boxMeasure_le bx a)
    have hR : ∫ x, f x ∂μE = ((M : ℝ≥0∞)⁻¹).toReal • ∑ a, ∫ x, f x ∂(boxMeasure bx a) := by
      calc ∫ x, f x ∂μE = ∫ x, f x ∂((M : ℝ≥0∞)⁻¹ • ∑ a, boxMeasure bx a) := by rw [← hμ]
        _ = _ := by
          rw [integral_smul_measure, integral_finsetSum_measure (fun a _ => hint a)]
    have hL : ∫ x, QJ bx f x ∂μE
        = ((M : ℝ≥0∞)⁻¹).toReal • ∑ a, ∫ x, f x ∂(boxMeasure bx a) := by
      unfold QJ
      rw [integral_finsetSum _ fun a _ => (integrable_const _).indicator (bx.meas a),
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_indicator_const _ (bx.meas a)]
      simp [Measure.real, bx.vol a]
    rw [hL, hR]
  obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (bx.cover ▸ Set.mem_univ y)
  have hi1 : Integrable (fun x => ker K.s x y) μE := hs.comp_sub_right y
  have h1 : ∫ x, QJx bx (ker K.s) x y ∂μE = K.c := by
    unfold QJx
    rw [hQ _ hi1]
    simp only [ker]
    rw [SingularKernel.integral_ker_left, K.c_def]
  have hF : Integrable (Function.uncurry fun x y' => K.s (x - y'))
      (μE.prod (boxMeasure bx b)) := by
    have hm : AEStronglyMeasurable (Function.uncurry fun x y' => K.s (x - y'))
        (μE.prod (boxMeasure bx b)) :=
      (K.s_meas.comp measurable_sub).aestronglyMeasurable
    rw [integrable_prod_iff' hm]
    refine ⟨Filter.Eventually.of_forall fun y' => hs.comp_sub_right y', ?_⟩
    have : (fun y' => ∫ x, ‖Function.uncurry (fun x y' => K.s (x - y')) (x, y')‖ ∂μE)
        = fun _ => ∫ z, ‖K.s z‖ ∂μE := by
      funext y'
      exact SingularKernel.integral_ker_left (fun z => ‖K.s z‖) y'
    rw [this]
    exact integrable_const _
  have e2 : ∀ x, QJy bx (ker K.s) x y = ∫ y', K.s (x - y') ∂(boxMeasure bx b) := fun x =>
    QJ_apply_of_mem bx _ hb
  have hi2 : Integrable (fun x => QJy bx (ker K.s) x y) μE := by
    simp_rw [e2]
    exact hF.integral_prod_left
  have h2 : ∫ x, QJy bx (ker K.s) x y ∂μE = K.c := by
    simp_rw [e2]
    rw [integral_integral_swap hF]
    simp only [SingularKernel.integral_ker_left, K.c_def, integral_const, measure_univ,
      ENNReal.toReal_one, one_smul]
    simp [K.c_def]
  have h3 : ∫ x, QJx bx (QJy bx (ker K.s)) x y ∂μE = K.c := by
    unfold QJx
    rw [hQ _ hi2]
    exact h2
  have hI1 : Integrable (fun x => QJx bx (ker K.s) x y) μE := hIQJ _
  have hI3 : Integrable (fun x => QJx bx (QJy bx (ker K.s)) x y) μE := hIQJ _
  unfold aker
  have e : ∫ x, (QJx bx (ker K.s) x y + QJy bx (ker K.s) x y
        - QJx bx (QJy bx (ker K.s)) x y - K.c) ∂μE
      = (∫ x, QJx bx (ker K.s) x y ∂μE) + (∫ x, QJy bx (ker K.s) x y ∂μE)
        - (∫ x, QJx bx (QJy bx (ker K.s)) x y ∂μE) - K.c := by
    have hA : Integrable (fun x => QJx bx (ker K.s) x y + QJy bx (ker K.s) x y) μE :=
      hI1.add hi2
    have hB : Integrable (fun x => QJx bx (ker K.s) x y + QJy bx (ker K.s) x y
        - QJx bx (QJy bx (ker K.s)) x y) μE := hA.sub hI3
    rw [integral_sub hB (integrable_const _), integral_sub hA hI3, integral_add hI1 hi2]
    simp
  rw [e, h1, h2, h3]
  ring

-- SKETCH: `aker_symm` and `aker_centered_left`.
/-- Eq. (5.2), centering of `a_r` under `μ` in the second variable. -/
theorem aker_centered_right (K : SingularKernel μE bx G d Cc V) (x : E) :
    ∫ y, aker bx K.s K.c x y ∂μE = 0 := by
  have hsym : ∀ y, aker bx K.s K.c x y = aker bx K.s K.c y x := by
    intro y
    unfold aker
    rw [QJx_ker_swap K (SingularKernel.Sub.self K) x y,
      ← QJx_ker_swap K (SingularKernel.Sub.self K) y x,
      QJxQJy_ker_swap K (SingularKernel.Sub.self K) y x]
    ring
  simp_rw [hsym]
  exact aker_centered_left K x

-- SKETCH: `s'(x - y) = 0` from `K.s_local` and `0 ≤ s' ≤ K.s` (`le_antisymm`).  The three
-- averaged terms vanish because `ν_a`-a.e. `x' ∈ A a` (`ae_mem_boxMeasure`) and then
-- `s'(x' - y) = 0` (`integral_eq_zero_of_ae`); for the double average apply this twice
-- (`QJ_apply_of_mem` on the boxes of `x` and `y`).
/-- "Box averaging preserves this property": `h_r(x, y) = 0` when `x`, `y` lie in distinct
non-adjacent boxes. -/
theorem hker_local (K : SingularKernel μE bx G d Cc V) {s' : E → ℝ} (hs' : K.Sub s') {a b : Fin M}
    (hab : a ≠ b) (hadj : ¬ G.Adj a b) {x y : E} (hx : x ∈ bx.A a) (hy : y ∈ bx.A b) :
    hker bx s' x y = 0 := by
  have hz : ∀ x' ∈ bx.A a, ∀ y' ∈ bx.A b, s' (x' - y') = 0 := fun x' hx' y' hy' =>
    le_antisymm ((hs'.le _).trans (K.s_local a b hab hadj x' hx' y' hy').le) (hs'.nonneg _)
  have h2 : ∀ x' ∈ bx.A a, QJy bx (ker s') x' y = 0 := by
    intro x' hx'
    unfold QJy
    rw [QJ_apply_of_mem bx _ hy]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_mem_boxMeasure bx b] with y' hy'
    exact hz x' hx' y' hy'
  have h1 : QJx bx (ker s') x y = 0 := by
    unfold QJx
    rw [QJ_apply_of_mem bx _ hx]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_mem_boxMeasure bx a] with x' hx'
    exact hz x' hx' y hy
  have h3 : QJy bx (ker s') x y = 0 := h2 x hx
  have h4 : QJx bx (QJy bx (ker s')) x y = 0 := by
    unfold QJx
    rw [QJ_apply_of_mem bx _ hx]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_mem_boxMeasure bx a] with x' hx'
    exact h2 x' hx'
  have h0 : ker s' x y = 0 := hz x hx y hy
  unfold hker
  rw [h0, h1, h3, h4]; ring

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
  unfold W
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_) _
  exact hK.comp ((hX i).prodMk (hX j))

variable {bx : Boxes μE M} {G : SimpleGraph (Fin M)} {d : ℕ} {Cc V : ℝ}

-- SKETCH: `W_add` after rewriting the kernel with `stilde_split` (`funext`), then `mul_add`.
/-- Eq. `eq:physical-particle-sum-splitting` (5.3):
`(t/2) W_N(s̃_r) = (t/2) W_N(a_r) + (t/2) W_N(h_r)`. -/
theorem particle_sum_splitting (K : SingularKernel μE bx G d Cc V) (X : Fin N → Ω → E) (t : ℝ)
    (ω : Ω) :
    (t / 2) * W (ker K.stilde) X ω
      = (t / 2) * W (aker bx K.s K.c) X ω + (t / 2) * W (hker bx K.s) X ω := by
  have h : ker K.stilde = fun x y => aker bx K.s K.c x y + hker bx K.s x y := by
    funext x y; exact stilde_split K x y
  rw [h, W_add, mul_add]

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
  have hp : (2:ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  set f : Ω → ENNReal := fun ω => ENNReal.ofReal (Real.exp (F ω / 2)) with hf
  set g : Ω → ENNReal := fun ω => A.indicator (fun ω => ENNReal.ofReal (Real.exp (G ω / 2))) ω with hg
  have hfm : AEMeasurable f μ := (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hF.div_const 2))).aemeasurable
  have hgm : AEMeasurable g μ := (Measurable.indicator (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hG.div_const 2))) hA).aemeasurable
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hp hfm hgm
  have e1 : ∀ ω, A.indicator (fun ω => ENNReal.ofReal (Real.exp ((F ω + G ω) / 2))) ω = (f * g) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [hg, hf, Set.indicator_of_mem hω, Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; congr 2; ring
    · simp [hg, hω]
  have e2 : ∀ ω, (f ω) ^ (2:ℝ) = ENNReal.ofReal (Real.exp (F ω)) := by
    intro ω
    simp only [hf]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]; congr 2; ring
  have e3 : ∀ ω, (g ω) ^ (2:ℝ) = A.indicator (fun ω => ENNReal.ofReal (Real.exp (G ω))) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [hg, Set.indicator_of_mem hω]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]; congr 2; ring
    · simp [hg, hω]
  simp only [e1, e2, e3] at *
  simpa using h

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
  have hak : Measurable (uncurry (aker bx K.s K.c)) := by
    have hk : Measurable (uncurry (ker K.s)) := K.s_meas.comp measurable_sub
    have h1 := measurable_QJx bx (ker K.s) hk
    have h2 := measurable_QJy bx (ker K.s) hk
    have h3 := measurable_QJx bx (QJy bx (ker K.s)) h2
    have : uncurry (aker bx K.s K.c) = fun p => uncurry (QJx bx (ker K.s)) p
        + uncurry (QJy bx (ker K.s)) p - uncurry (QJx bx (QJy bx (ker K.s))) p - K.c := rfl
    rw [this]
    exact ((h1.add h2).sub h3).sub measurable_const
  have h := holder_split μ A hA (fun ω => t * W (aker bx K.s K.c) X ω)
    (fun ω => t * W (hker bx K.s) X ω)
    (measurable_W _ hak X hX |>.const_mul t)
    (measurable_W _ (measurable_hker K.s K.s_meas) X hX |>.const_mul t)
  have e : ∀ ω, (t / 2) * W (ker K.stilde) X ω
      = (t * W (aker bx K.s K.c) X ω + t * W (hker bx K.s) X ω) / 2 := by
    intro ω; rw [particle_sum_splitting]; ring
  simpa only [e] using h

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
  have hM := SingularKernel.Mc_le K
  have hc0 := SingularKernel.c_nonneg K
  have hC := SingularKernel.Cc_nonneg K
  have key : ∀ (f : E → ℝ) (B : ℝ) (x : E), (∀ z, 0 ≤ f z) → (∀ z, f z ≤ B) →
      QJ bx f x ≤ B := by
    intro f B x hf hB
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (bx.cover ▸ Set.mem_univ x)
    have hQ : QJ bx f x = ∫ y, f y ∂(boxMeasure bx a) := by
      unfold QJ
      rw [Finset.sum_eq_single a]
      · simp [Set.indicator_of_mem ha]
      · intro b _ hb
        exact Set.indicator_of_notMem
          (fun hxb => Set.disjoint_left.1 (bx.disj hb) hxb ha) _
      · simp
    rw [hQ]
    calc ∫ y, f y ∂(boxMeasure bx a) ≤ ∫ _y, B ∂(boxMeasure bx a) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall hf) (integrable_const B)
            (Filter.Eventually.of_forall hB)
      _ = B := by simp
  have hA : QJx bx (ker K.s) x y ≤ M * K.c := by
    unfold QJx
    have := QJ_le bx (fun x' => ker K.s x' y) (fun z => K.s_nonneg _)
      (K.s_int.comp_sub_right y) x
    simpa [ker, SingularKernel.integral_ker_left K.s y, K.c_def] using this
  have hBg : ∀ x y, QJy bx (ker K.s) x y ≤ M * K.c := by
    intro x y
    unfold QJy
    have := QJ_le bx (fun y' => ker K.s x y') (fun z => K.s_nonneg _)
      ((K.s_int.comp_sub_left x)) y
    simpa [ker, SingularKernel.integral_ker_right K.s x, K.c_def] using this
  have hB := hBg x y
  have hA0 : 0 ≤ QJx bx (ker K.s) x y := QJ_nonneg bx _ (fun z => K.s_nonneg _) x
  have hB0 : 0 ≤ QJy bx (ker K.s) x y := QJ_nonneg bx _ (fun z => K.s_nonneg _) y
  have hC0 : 0 ≤ QJx bx (QJy bx (ker K.s)) x y :=
    QJ_nonneg bx _ (fun z => QJ_nonneg bx _ (fun w => K.s_nonneg _) y) x
  have hC1 : QJx bx (QJy bx (ker K.s)) x y ≤ M * K.c := by
    unfold QJx
    exact key _ _ x (fun z => QJ_nonneg bx _ (fun w => K.s_nonneg _) y)
      (fun z => hBg z y)
  have hcC : K.c ≤ Cc := by
    have h1 : K.r ^ d ≤ 1 := pow_le_one₀ K.r_pos.le K.r_lt_one.le
    nlinarith [K.c_le]
  unfold aker
  rw [abs_le]
  constructor <;> linarith

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
  have hsym : ∀ x y, aker bx K.s K.c x y = aker bx K.s K.c y x := fun x y => by
    unfold aker
    have h1 := QJxQJy_ker_swap K (SingularKernel.Sub.self K) x y
    have h2 := QJx_ker_swap K (SingularKernel.Sub.self K) x y
    have h3 := QJx_ker_swap K (SingularKernel.Sub.self K) y x
    linarith
  have h := aker_integral_le_right K y
  simpa only [hsym _ y] using h

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
  have hpt : ∀ x, |f x| ^ p ≤ (κ ^ p * p.factorial * (Real.exp (C / κ) / κ)) * |f x| := by
    intro x
    set u := |f x| / κ with hu
    have hu0 : 0 ≤ u := div_nonneg (abs_nonneg _) hκ.le
    have hfx : |f x| = κ * u := by rw [hu]; field_simp
    have h1 : u ^ (p - 1) / (p - 1).factorial ≤ Real.exp u := Real.pow_div_factorial_le_exp u hu0 (p - 1)
    have h2 : Real.exp u ≤ Real.exp (C / κ) :=
      Real.exp_le_exp.2 (div_le_div_of_nonneg_right (hC x) hκ.le)
    have hfac : (p.factorial : ℝ) = p * (p - 1).factorial := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp [Nat.factorial_succ]
    have hf1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hfpos : (0 : ℝ) < (p - 1).factorial := by exact_mod_cast Nat.factorial_pos _
    have h3 : u ^ (p - 1) ≤ p.factorial * Real.exp (C / κ) := by
      rw [div_le_iff₀ hfpos] at h1
      rw [hfac]
      have := mul_le_mul_of_nonneg_right h2 hfpos.le
      nlinarith [mul_le_mul_of_nonneg_right hf1 (mul_nonneg (Real.exp_pos (C / κ)).le hfpos.le)]
    have hup : u ^ p = u * u ^ (p - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hκp : 0 < κ ^ p := pow_pos hκ p
    have : (κ * u) ^ p = κ ^ p * (u * u ^ (p - 1)) := by rw [mul_pow, hup]
    rw [hfx, this]
    have e : κ ^ p * p.factorial * (Real.exp (C / κ) / κ) * (κ * u)
        = κ ^ p * (u * (p.factorial * Real.exp (C / κ))) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hu0) hκp.le
  have hC0 : ∀ x, 0 ≤ C := fun x => (abs_nonneg _).trans (hC x)
  have hint1 : Integrable (fun x => |f x|) ν :=
    Integrable.of_bound (hf.abs.aestronglyMeasurable) C (Filter.Eventually.of_forall fun x => by simpa using hC x)
  have hint : Integrable (fun x => |f x| ^ p) ν :=
    Integrable.of_bound (hf.abs.pow_const p).aestronglyMeasurable (C ^ p)
      (Filter.Eventually.of_forall fun x => by
        simpa using pow_le_pow_left₀ (abs_nonneg _) (hC x) p)
  calc ∫ x, |f x| ^ p ∂ν ≤ ∫ x, (κ ^ p * p.factorial * (Real.exp (C / κ) / κ)) * |f x| ∂ν :=
        integral_mono hint (hint1.const_mul _) hpt
    _ = (κ ^ p * p.factorial * (Real.exp (C / κ) / κ)) * ∫ x, |f x| ∂ν := integral_const_mul _ _
    _ ≤ (κ ^ p * p.factorial * (Real.exp (C / κ) / κ)) * ε := by
        apply mul_le_mul_of_nonneg_left hε
        positivity
    _ = κ ^ p * p.factorial * (ε * Real.exp (C / κ) / κ) := by ring
    _ ≤ κ ^ p * p.factorial * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_one hκ]; exact hsmall
    _ = _ := mul_one _

/-- The decay rate `κ(r) = C'/log(1/r)` of eq. `eq:physical-average-factorial` (5.6), with
`C' = 8 C + 1`. -/
noncomputable def kappa (Cc r : ℝ) : ℝ := (8 * Cc + 1) / Real.log (1 / r)

-- SKETCH: `div_pos` with `Real.log_pos` (`one_lt_one_div hr hr1`).
/-- `κ(r) > 0` for `0 < r < 1`. -/
theorem kappa_pos (Cc : ℝ) (hCc : 0 ≤ Cc) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 0 < kappa Cc r := by
  unfold kappa
  exact div_pos (by linarith) (Real.log_pos (one_lt_one_div hr hr1))

-- SKETCH: `Real.log (1/r) ≥ (8 Cc + 1)/ε` from `hr'` (`Real.log_le_log`, `Real.log_exp`,
-- `one_div`, `Real.log_inv`), then `div_le_iff₀` and `div_le_iff₀` again.
/-- `κ(r) ≤ ε` as soon as `r ≤ exp(-(8C+1)/ε)`. -/
theorem kappa_le_of_le (Cc : ℝ) (hCc : 0 ≤ Cc) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hr' : r ≤ Real.exp (-((8 * Cc + 1) / ε))) : kappa Cc r ≤ ε := by
  have hC : 0 < 8 * Cc + 1 := by linarith
  have h1 : Real.log r ≤ -((8 * Cc + 1) / ε) := by
    have := Real.log_le_log hr hr'
    rwa [Real.log_exp] at this
  have h2 : (8 * Cc + 1) / ε ≤ Real.log (1 / r) := by
    rw [one_div, Real.log_inv]; linarith
  have h3 : 0 < Real.log (1 / r) := lt_of_lt_of_le (div_pos hC hε) h2
  unfold kappa
  rw [div_le_iff₀ h3]
  rw [div_le_iff₀ hε] at h2
  linarith

-- SKETCH: `Real.tendsto_log_atTop.comp` with `tendsto_one_div_nhdsWithin_Ioi`-style
-- (`tendsto_inv_nhdsGT_zero`), then `Tendsto.div_atTop tendsto_const_nhds`.
/-- `κ(r) → 0` as `r ↓ 0` (eq. (5.6)). -/
theorem kappa_tendsto_zero (Cc : ℝ) : Tendsto (fun r => kappa Cc r) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun r : ℝ => Real.log (1 / r)) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp ((tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).congr (fun x => (one_div x).symm))
  exact Tendsto.div_atTop tendsto_const_nhds h

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
  have hm := measurable_aker (bx := bx) K.s K.s_meas K.c
  refine { κ_pos := hκ, Y_meas := hX_meas, Y_indep := hX_indep, Y_law := hX_law,
           h_meas := fun _ _ => hm, h_int := ?_,
           centered_left := fun _ _ _ => ae_of_all _ (fun y => aker_centered_left K y),
           centered_right := fun _ _ _ => ae_of_all _ (fun x => aker_centered_right K x),
           moment_left := fun _ _ _ p hp => ae_of_all _ (fun y => (hmom p hp).2 y),
           moment_right := fun _ _ _ p hp => ae_of_all _ (fun x => (hmom p hp).1 x) }
  intro i j p hp
  refine Integrable.of_bound (C := (4 * Cc) ^ p)
    ((hm.norm.pow_const p).aestronglyMeasurable) (ae_of_all _ fun z => ?_)
  have h0 := aker_abs_le K z.1 z.2
  have : 0 ≤ |aker bx K.s K.c z.1 z.2| := abs_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ this h0 p

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
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  have hr := K.r_pos
  have hV := K.V_nonneg
  set g : E → ℝ := fun z => max 0 (Real.log (K.r / dist z 0)) with hg
  have gmeas : Measurable g :=
    measurable_const.max (Real.measurable_log.comp (measurable_const.div
      (continuous_id.dist continuous_const).measurable))
  have gnn : 0 ≤ᵐ[μE] g := Filter.Eventually.of_forall fun z => le_max_left _ _
  have key := lintegral_comp_eq_lintegral_meas_lt_mul μE gnn gmeas.aemeasurable
    (g := fun t : ℝ => ((q:ℝ) + 1) * t ^ q)
    (fun t _ => (by fun_prop : Continuous fun t : ℝ => ((q:ℝ) + 1) * t ^ q).intervalIntegrable _ _)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => by
      have : (0:ℝ) < t := ht
      positivity))
  have hint : ∀ z, ∫ t in (0:ℝ)..g z, ((q:ℝ) + 1) * t ^ q = g z ^ (q + 1) := by
    intro z
    rw [intervalIntegral.integral_const_mul, integral_pow]
    field_simp
    simp
  simp_rw [hint] at key
  rw [key]
  have hmeas : ∀ t : ℝ, 0 < t →
      μE {a | t < g a} ≤ ENNReal.ofReal (V * K.r ^ d * Real.exp (-(d * t))) := by
    intro t ht
    have hsub : {a | t < g a} ⊆ Metric.ball (0:E) (K.r * Real.exp (-t)) := by
      intro a ha
      simp only [Set.mem_setOf_eq, hg] at ha
      have h1 : t < Real.log (K.r / dist a 0) := by
        rcases lt_max_iff.mp ha with h | h
        · linarith
        · exact h
      rw [Metric.mem_ball]
      by_cases h0 : dist a 0 = 0
      · rw [h0, div_zero, Real.log_zero] at h1
        linarith
      · have hpos : 0 < dist a 0 := lt_of_le_of_ne dist_nonneg (Ne.symm h0)
        rw [Real.lt_log_iff_exp_lt (div_pos hr hpos), lt_div_iff₀ hpos] at h1
        rw [Real.exp_neg]
        rw [← div_eq_mul_inv, lt_div_iff₀ (Real.exp_pos t)]
        linarith
    refine (measure_mono hsub).trans ?_
    refine (K.ball_vol _ (by positivity) ?_).trans (le_of_eq ?_)
    · exact mul_le_of_le_one_right hr.le (Real.exp_le_one_iff.mpr (by linarith))
    · congr 1
      rw [mul_pow, ← Real.exp_nat_mul]
      ring_nf
  have hI : ∫ t in Set.Ioi (0:ℝ), t ^ q * Real.exp (-(d * t))
      = (q.factorial : ℝ) / (d:ℝ) ^ (q + 1) := by
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (q:ℝ) + 1) (r := d)
      (by positivity) hdpos
    simp only [add_sub_cancel_right, Real.rpow_natCast] at this
    rw [Real.Gamma_nat_eq_factorial, ← Nat.cast_succ, Real.rpow_natCast] at this
    rw [this, Nat.succ_eq_add_one, one_div, inv_pow]
    ring
  calc ∫⁻ t in Set.Ioi (0:ℝ), μE {a | t < g a} * ENNReal.ofReal (((q:ℝ) + 1) * t ^ q)
      ≤ ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (V * K.r ^ d * (((q:ℝ) + 1) *
          (t ^ q * Real.exp (-(d * t))))) := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        have ht' : (0:ℝ) < t := ht
        refine (mul_le_mul_left (hmeas t ht') _).trans (le_of_eq ?_)
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ = ENNReal.ofReal (∫ t in Set.Ioi (0:ℝ), V * K.r ^ d * (((q:ℝ) + 1) *
          (t ^ q * Real.exp (-(d * t))))) := by
        have hpos : 0 < ∫ t in Set.Ioi (0:ℝ), t ^ q * Real.exp (-(d * t)) := by
          rw [hI]; positivity
        have hi : IntegrableOn (fun t : ℝ => t ^ q * Real.exp (-(d * t))) (Set.Ioi 0) := by
          by_contra hn
          rw [integral_undef hn] at hpos
          exact lt_irrefl _ hpos
        symm
        refine ofReal_integral_eq_lintegral_ofReal ?_ ?_
        · exact (hi.const_mul ((q:ℝ) + 1)).const_mul (V * K.r ^ d)
        · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
          have : (0:ℝ) < t := ht
          positivity
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        rw [integral_const_mul, integral_const_mul, hI]
        rw [Nat.factorial_succ]
        push_cast
        ring

-- SKETCH: `lintegral_mono_ae` with `K.s_log`, `hs'.le`, `hs'.nonneg` and
-- `pow_le_pow_left₀` (`ENNReal.ofReal_le_ofReal`), then `log_moment`.
/-- "`M ∫ s_r^p dμ ≤ M |B_r| p!/d^p`" (eq. (5.8)), the `∫ s_r^p dμ` part, for every sub-kernel. -/
theorem s_moment (K : SingularKernel μE bx G d Cc V) (hd : 1 ≤ d) {s' : E → ℝ} (hs' : K.Sub s')
    (p : ℕ) (hp : 1 ≤ p) :
    ∫⁻ z, ENNReal.ofReal (s' z ^ p) ∂μE ≤ ENNReal.ofReal (V * K.r ^ d * p.factorial / d ^ p) := by
  refine le_trans (lintegral_mono_ae ?_) (log_moment K hd p hp)
  filter_upwards [K.s_log] with z hz
  exact ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (hs'.nonneg z) ((hs'.le z).trans hz) p)

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
  classical
  have hC := SingularKernel.Cc_nonneg K
  have hMc := SingularKernel.Mc_le K
  have hint := SingularKernel.Sub.integrable K hs'
  have hcc : ∫ z, s' z ∂μE ≤ K.c := by
    rw [← K.c_def]
    exact integral_mono hint K.s_int hs'.le
  have hM0 : (0:ℝ) ≤ M := Nat.cast_nonneg M
  have hMc' : (M : ℝ) * ∫ z, s' z ∂μE ≤ Cc :=
    (mul_le_mul_of_nonneg_left hcc hM0).trans hMc
  -- a bounded nonnegative function has box averages in `[0, Cc]`
  have key : ∀ g : E → ℝ, (∀ z, 0 ≤ g z) → (∀ z, g z ≤ Cc) → ∀ x, QJ bx g x ≤ Cc := by
    intro g hg0 hgC x
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (bx.cover ▸ Set.mem_univ x)
    have hMpos : (0:ℝ) < M := Nat.cast_pos.2 (Fin.pos a)
    rw [QJ_apply_of_mem bx g ha, boxMeasure, ENNReal.smul_def, integral_smul_measure]
    simp only [ENNReal.coe_natCast, ENNReal.toReal_natCast, smul_eq_mul]
    have hvol : (μE.restrict (bx.A a)).real Set.univ = 1 / M := by
      rw [Measure.real, Measure.restrict_apply_univ, bx.vol]
      simp
    have h1 : ∫ z in bx.A a, g z ∂μE ≤ ∫ _ in bx.A a, Cc ∂μE :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall hg0) (integrable_const _)
        (Filter.Eventually.of_forall hgC)
    rw [integral_const, smul_eq_mul, hvol] at h1
    calc (M : ℝ) * ∫ z in bx.A a, g z ∂μE ≤ M * (1 / M * Cc) :=
          mul_le_mul_of_nonneg_left h1 hM0
      _ = Cc := by field_simp
  have hT1 : ∀ x y, QJx bx (ker s') x y ≤ Cc := fun x y => by
    unfold QJx
    refine (QJ_le bx _ (fun z => hs'.nonneg _) (hint.comp_sub_right y) x).trans ?_
    simpa [ker, SingularKernel.integral_ker_left] using hMc'
  have hT2 : ∀ x y, QJy bx (ker s') x y ≤ Cc := fun x y => by
    unfold QJy
    refine (QJ_le bx _ (fun z => hs'.nonneg _) (hint.comp_sub_left x) y).trans ?_
    simpa [ker, SingularKernel.integral_ker_right] using hMc'
  have n1 : ∀ x y, 0 ≤ QJx bx (ker s') x y := fun x y =>
    QJ_nonneg bx _ (fun z => hs'.nonneg _) x
  have n2 : ∀ x y, 0 ≤ QJy bx (ker s') x y := fun x y =>
    QJ_nonneg bx _ (fun z => hs'.nonneg _) y
  have hT3 : QJx bx (QJy bx (ker s')) x y ≤ Cc := by
    unfold QJx
    exact key _ (fun z => n2 z y) (fun z => hT2 z y) x
  have n3 : 0 ≤ QJx bx (QJy bx (ker s')) x y :=
    QJ_nonneg bx _ (fun z => n2 z y) x
  have hs0 := hs'.nonneg (x - y)
  have a1 := hT1 x y
  have a2 := hT2 x y
  have a3 := n1 x y
  have a4 := n2 x y
  unfold hker
  rw [abs_le]
  have : ker s' x y = s' (x - y) := rfl
  constructor <;> linarith

/-- The universal constant `κ_*` of eq. `eq:physical-singular-factorial` (5.8), depending only
on `d`-independent data `C`, `V`: `κ_* = 2 max(V,1) max(3C,1)`. -/
noncomputable def kappaStar (Cc V : ℝ) : ℝ := 2 * max V 1 * max (3 * Cc) 1

-- SKETCH: `positivity` / `mul_pos` with `lt_max_of_lt_right one_pos`.
/-- `κ_* > 0`. -/
theorem kappaStar_pos (Cc V : ℝ) : 0 < kappaStar Cc V := by
  unfold kappaStar
  have h1 : (0:ℝ) < max V 1 := lt_max_of_lt_right one_pos
  have h2 : (0:ℝ) < max (3 * Cc) 1 := lt_max_of_lt_right one_pos
  positivity

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
  classical
  have h1 : ∀ s : Set E, MeasurableSet s → μE s = (M : ℝ≥0∞)⁻¹ * ∑ a, boxMeasure bx a s := by
    intro s hs
    have hM : (M : ℝ≥0∞) ≠ 0 := by
      have : 0 < M := by
        by_contra h0
        have h0' : M = 0 := by omega
        subst h0'
        have := bx.cover
        have hx : (Classical.arbitrary E) ∈ ⋃ a, bx.A a := by rw [this]; trivial
        obtain ⟨a, _⟩ := Set.mem_iUnion.1 hx
        exact a.elim0
      exact_mod_cast this.ne'
    have hMt : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top M
    have : ∀ a, boxMeasure bx a s = (M : ℝ≥0∞) * μE (s ∩ bx.A a) := by
      intro a
      simp [boxMeasure, Measure.restrict_apply hs, ENNReal.smul_def]
    simp_rw [this]
    rw [← Finset.mul_sum, ← mul_assoc, ENNReal.inv_mul_cancel hM hMt, one_mul]
    have hU : μE (⋃ a, s ∩ bx.A a) = ∑ a, μE (s ∩ bx.A a) :=
      (measure_iUnion
        (fun i j hij => (bx.disj hij).mono Set.inter_subset_right Set.inter_subset_right)
        (fun a => hs.inter (bx.meas a))).trans (tsum_fintype _)
    rw [← hU, ← Set.inter_iUnion, bx.cover, Set.inter_univ]
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  simp only [labelMeasure, Measure.pi_pi]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ : Fin N => (Finset.univ : Finset (Fin M)))
    (fun i a => boxMeasure bx a (s i))]
  simp_rw [h1 _ (hs _)]
  rw [Finset.prod_mul_distrib]
  simp [ENNReal.inv_pow, smul_eq_mul]

-- SKETCH: `Measure.ae_pi_le_pi` (`Filter.pi`, `Filter.mem_pi`): a.e. for `Measure.pi` is implied
-- by a.e. in each coordinate (`ae_all_iff` over the finite index set), and `ae_mem_boxMeasure`
-- for each `i`.  Concretely: `(Measure.ae_pi_le_pi) (Filter.pi_mem_pi …)` or
-- `MeasureTheory.Measure.ae_pi_eval`-style lemmas (`ae_eval_ne`, `Measure.pi_map_eval`).
/-- Under `𝔼_L`, almost surely particle `i` lies in the box `A_{L_i}`. -/
theorem ae_labels_mem (bx : Boxes μE M) (L : Fin N → Fin M) :
    ∀ᵐ x ∂(labelMeasure bx L), ∀ i, x i ∈ bx.A (L i) := by
  rw [ae_all_iff]
  intro i
  exact (MeasureTheory.Measure.quasiMeasurePreserving_eval (fun i => boxMeasure bx (L i)) i).ae
    (by
      unfold boxMeasure
      exact Measure.ae_smul_measure (ae_restrict_mem (bx.meas (L i))) _)

-- SKETCH: on the a.e. set of `ae_labels_mem`, `(bx.A a).indicator 1 (x i) = if L i = a then 1 else 0`
-- (`bx.disj`, `Set.disjoint_left`, `Set.indicator_apply`), so `occupancy (coord N) (A a) x =
-- labelCount L a` (`occupancy`, `labelCount`, `Finset.card_filter`, `Finset.sum_boole`), and the
-- two conditions coincide (`goodEvent`, `GoodLabel`).
/-- Under `𝔼_L` the good event is almost surely the deterministic condition
"`L` is a good label vector". -/
theorem goodEvent_ae_iff (bx : Boxes μE M) (L : Fin N → Fin M) (δ : ℝ) :
    ∀ᵐ x ∂(labelMeasure bx L), x ∈ goodEvent (coord N) bx δ ↔ GoodLabel L δ := by
  have h : ∀ᵐ x ∂(labelMeasure bx L), ∀ i, x i ∈ bx.A (L i) := by
    unfold labelMeasure
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval (fun i => boxMeasure bx (L i)) i).ae
      (ae_mem_boxMeasure bx (L i))
  filter_upwards [h] with x hx
  have key : ∀ a, occupancy (coord N) (bx.A a) x = labelCount L a := by
    intro a
    unfold occupancy labelCount
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : L i = a
    · subst hi; simp [coord, hx i]
    · have : x i ∉ bx.A a := fun hm =>
        Set.disjoint_left.1 (bx.disj hi) (hx i) hm
      simp [coord, this, hi]
  simp only [goodEvent, GoodLabel, Set.mem_setOf_eq, key]

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
  have hmem : ∀ᵐ x ∂(labelMeasure bx L), ∀ i, x i ∈ bx.A (L i) := by
    rw [ae_all_iff]
    intro i
    have h1 : ∀ᵐ y ∂(boxMeasure bx (L i)), y ∈ bx.A (L i) := by
      simp only [boxMeasure]
      rw [Measure.ae_smul_measure_iff (by simp [Fin.pos (L i) |>.ne'])]
      exact ae_restrict_mem (bx.meas _)
    exact (Measure.ae_pi_le_pi (Filter.tendsto_eval_pi _ i |>.eventually h1))
  filter_upwards [hmem] with x hx
  unfold S
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [labelKer, coord, hx i, hx j]

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
