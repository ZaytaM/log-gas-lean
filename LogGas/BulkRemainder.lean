import LogGas.Bulk

/-!
# Appendix A, step 3 — the remainder kernel `r_J` and its Lemma 6.1 bound

Source: `notes/appendixA.tex`, eqs. `eq:general-cell-centering` (A.8) and
`eq:continuous-small-remainder` (A.9); audit E6 A6/A7, D1.

For a bounded measurable kernel `K` and a grid `bx`, the remainder
`r_J = (I − Q_J)_x (I − Q_J)_y K` (`LogGas.Bulk.rJ`) satisfies:
* `measurable_rJ`, `rJ_symm`, `rJ_abs_le_bound` (`|r_J| ≤ 4 C_K`);
* `rJ_abs_le_osc`: (A.9), `|r_J| ≤ 4 ω₀` if `K` oscillates by at most `ω₀` on products of cells;
* `rJ_centered_left/right`: zero box averages in each variable;
* `rJ_exp_bound`: Lemma 6.1 (`LogGas.Decoupling.exp_bound`) applied to `h_{ij} = r_J`,
  `ν_i = μE`: `𝔼 exp((θ/2) W_N(r_J)) ≤ 8/3` once `Cu κ θ ≤ 1/2`.

`E` carries only a `MeasurableSpace` here, so the box-averaging facts of `LogGas.Singular`
(which assume group/metric instances) are reproved locally under the prefix `br`.
No deviation from the stated targets.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Finset Function Matrix
open scoped BigOperators ENNReal NNReal

namespace LogGas.Bulk

open LogGas.Decoupling LogGas.BadEvent LogGas.Singular

section Remainder

variable {E : Type*} [MeasurableSpace E] {μE : Measure E} [IsProbabilityMeasure μE] {M : ℕ}

/-! ### Local box-averaging facts (no group structure) -/

private instance br_prob (bx : Boxes μE M) (a : Fin M) :
    IsProbabilityMeasure (boxMeasure bx a) := by
  refine ⟨?_⟩
  have hM : (M : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.1 a.pos)
  simp only [boxMeasure, Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_natCast, smul_eq_mul,
    Measure.restrict_apply_univ, bx.vol a]
  exact ENNReal.mul_inv_cancel hM (ENNReal.natCast_ne_top M)

private theorem br_boxMeasure_le (bx : Boxes μE M) (a : Fin M) :
    boxMeasure bx a ≤ (M : ℝ≥0∞) • μE := by
  refine Measure.le_iff'.2 fun s => ?_
  simp only [boxMeasure, Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_natCast, smul_eq_mul]
  exact mul_le_mul_right (Measure.restrict_apply_le _ _) _

private theorem br_ae_mem (bx : Boxes μE M) (a : Fin M) : ∀ᵐ x ∂(boxMeasure bx a), x ∈ bx.A a := by
  unfold boxMeasure
  exact Measure.ae_smul_measure (ae_restrict_mem (bx.meas a)) _

private theorem br_μE_eq_sum (bx : Boxes μE M) :
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

private theorem br_QJ_apply (bx : Boxes μE M) (f : E → ℝ) {a : Fin M} {x : E}
    (hx : x ∈ bx.A a) : QJ bx f x = ∫ y, f y ∂(boxMeasure bx a) := by
  unfold QJ
  rw [Finset.sum_eq_single a]
  · exact Set.indicator_of_mem hx _
  · intro b _ hb
    refine Set.indicator_of_notMem ?_ _
    intro hxb
    exact Set.disjoint_left.mp (bx.disj hb) hxb hx
  · simp

private theorem br_measurable_QJ (bx : Boxes μE M) (f : E → ℝ) : Measurable (QJ bx f) := by
  unfold QJ
  exact Finset.measurable_sum _ fun a _ => measurable_const.indicator (bx.meas a)

private theorem br_measurable_QJx (bx : Boxes μE M) (K : E → E → ℝ)
    (hK : Measurable (uncurry K)) : Measurable (uncurry (QJx bx K)) := by
  unfold QJx QJ
  simp only [uncurry]
  refine Finset.measurable_sum _ fun a _ => ?_
  have h1 : Measurable fun y : E => ∫ x', K x' y ∂(boxMeasure bx a) :=
    (StronglyMeasurable.integral_prod_right (f := fun y x' => K x' y) (ν := boxMeasure bx a)
      (hK.comp measurable_swap).stronglyMeasurable).measurable
  exact Measurable.indicator (h1.comp measurable_snd) (measurable_fst (bx.meas a))

private theorem br_measurable_QJy (bx : Boxes μE M) (K : E → E → ℝ)
    (hK : Measurable (uncurry K)) : Measurable (uncurry (QJy bx K)) := by
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

private theorem br_integrable_of_bdd {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] {f : α → ℝ} (hf : Measurable f) (C : ℝ) (h : ∀ x, |f x| ≤ C) :
    Integrable f ν :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact h x)

private theorem br_integral_QJ (bx : Boxes μE M) (f : E → ℝ) (hf : Integrable f μE)
    (hQ : Integrable (QJ bx f) μE) : ∫ x, QJ bx f x ∂μE = ∫ x, f x ∂μE := by
  have hint : ∀ g : E → ℝ, Integrable g μE → ∀ a, Integrable g (boxMeasure bx a) := fun g hg a =>
    (hg.smul_measure (ENNReal.natCast_ne_top M)).mono_measure (br_boxMeasure_le bx a)
  have hbox : ∀ a, ∫ x, QJ bx f x ∂(boxMeasure bx a) = ∫ x, f x ∂(boxMeasure bx a) := by
    intro a
    have h : ∀ᵐ x ∂(boxMeasure bx a), QJ bx f x = ∫ y, f y ∂(boxMeasure bx a) := by
      filter_upwards [br_ae_mem bx a] with x hx
      exact br_QJ_apply bx f hx
    rw [integral_congr_ae h, integral_const]
    simp
  have hsum : ∀ g : E → ℝ, Integrable g μE →
      ∫ x, g x ∂μE = (M : ℝ)⁻¹ * ∑ a, ∫ x, g x ∂(boxMeasure bx a) := by
    intro g hg
    have h := congrArg (fun m : Measure E => ∫ x, g x ∂m) (br_μE_eq_sum bx)
    rw [h, integral_smul_measure, integral_finsetSum_measure (fun a _ => hint g hg a)]
    simp
  rw [hsum _ hQ, hsum _ hf]
  simp only [hbox]

private theorem br_QJ_abs_le (bx : Boxes μE M) (f : E → ℝ) (C : ℝ) (hf : ∀ y, |f y| ≤ C)
    (x : E) : |QJ bx f x| ≤ C := by
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (bx.cover ▸ Set.mem_univ x)
  rw [br_QJ_apply bx f ha]
  have := norm_integral_le_of_norm_le_const (μ := boxMeasure bx a) (f := f) (C := C)
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hf y)
  simpa using this

/-- Deviation of `f x` from its `ν_a`-average, controlled `ν_a`-almost everywhere. -/
private theorem br_dev_le (bx : Boxes μE M) (a : Fin M) (f : E → ℝ)
    (hfi : Integrable f (boxMeasure bx a)) (x : E) (ω : ℝ)
    (h : ∀ᵐ x' ∂boxMeasure bx a, |f x - f x'| ≤ ω) :
    |f x - ∫ x', f x' ∂boxMeasure bx a| ≤ ω := by
  have e : f x - ∫ x', f x' ∂boxMeasure bx a = ∫ x', (f x - f x') ∂boxMeasure bx a := by
    rw [integral_sub (integrable_const _) hfi]; simp
  rw [e]
  have := norm_integral_le_of_norm_le_const (μ := boxMeasure bx a) (f := fun x' => f x - f x')
    (C := ω) (h.mono fun x' hx' => by rw [Real.norm_eq_abs]; exact hx')
  simpa using this

private theorem br_meas_left {K : E → E → ℝ} (hK : Measurable (uncurry K)) (y : E) :
    Measurable (fun x => K x y) :=
  hK.comp (measurable_id.prodMk measurable_const)

private theorem br_meas_right {K : E → E → ℝ} (hK : Measurable (uncurry K)) (x : E) :
    Measurable (fun y => K x y) :=
  hK.comp (measurable_const.prodMk measurable_id)

/-- Box averaging in `x` commutes with box averaging in `y` (Fubini on `ν_a ⊗ ν_b`). -/
private theorem br_QJ_comm (bx : Boxes μE M) (K : E → E → ℝ) (hK : Measurable (uncurry K))
    (CK : ℝ) (hKb : ∀ x y, |K x y| ≤ CK) (x y : E) :
    QJx bx (QJy bx K) x y = QJy bx (QJx bx K) x y := by
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (bx.cover ▸ Set.mem_univ x)
  obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (bx.cover ▸ Set.mem_univ y)
  have hint : Integrable (uncurry K) ((boxMeasure bx a).prod (boxMeasure bx b)) :=
    br_integrable_of_bdd hK CK (fun p => hKb p.1 p.2)
  have h1 : ∀ x', QJy bx K x' y = ∫ y', K x' y' ∂(boxMeasure bx b) :=
    fun x' => br_QJ_apply bx (fun y' => K x' y') hb
  have h2 : ∀ y', QJx bx K x y' = ∫ x', K x' y' ∂(boxMeasure bx a) :=
    fun y' => br_QJ_apply bx (fun x' => K x' y') ha
  calc QJx bx (QJy bx K) x y = ∫ x', QJy bx K x' y ∂(boxMeasure bx a) :=
        br_QJ_apply bx (fun x' => QJy bx K x' y) ha
    _ = ∫ x', ∫ y', K x' y' ∂(boxMeasure bx b) ∂(boxMeasure bx a) := by
        rw [show (fun x' => QJy bx K x' y) = fun x' => ∫ y', K x' y' ∂(boxMeasure bx b)
          from funext h1]
    _ = ∫ y', ∫ x', K x' y' ∂(boxMeasure bx a) ∂(boxMeasure bx b) := integral_integral_swap hint
    _ = ∫ y', QJx bx K x y' ∂(boxMeasure bx b) := by
        rw [show (fun y' => QJx bx K x y') = fun y' => ∫ x', K x' y' ∂(boxMeasure bx a)
          from funext h2]
    _ = QJy bx (QJx bx K) x y := (br_QJ_apply bx (fun y' => QJx bx K x y') hb).symm

private theorem br_QJx_bound (bx : Boxes μE M) (K : E → E → ℝ) (CK : ℝ)
    (hKb : ∀ x y, |K x y| ≤ CK) (x y : E) : |QJx bx K x y| ≤ CK :=
  br_QJ_abs_le bx _ CK (fun x' => hKb x' y) x

private theorem br_QJy_bound (bx : Boxes μE M) (K : E → E → ℝ) (CK : ℝ)
    (hKb : ∀ x y, |K x y| ≤ CK) (x y : E) : |QJy bx K x y| ≤ CK :=
  br_QJ_abs_le bx _ CK (fun y' => hKb x y') y

/-! ### Targets (1)–(5) -/

variable {K : E → E → ℝ}

theorem measurable_rJ (bx : Boxes μE M) (hK : Measurable (uncurry K)) (CK : ℝ)
    (hKb : ∀ x y, |K x y| ≤ CK) : Measurable (uncurry (rJ bx K)) := by
  have hy := br_measurable_QJy bx K hK
  have hx := br_measurable_QJx bx K hK
  have hxy := br_measurable_QJx bx (QJy bx K) hy
  unfold rJ
  exact ((hK.sub hx).sub hy).add hxy

private theorem br_rJ_transpose (bx : Boxes μE M) (hK : Measurable (uncurry K)) (CK : ℝ)
    (hKb : ∀ x y, |K x y| ≤ CK) (x y : E) :
    rJ bx K x y = rJ bx (fun x y => K y x) y x := by
  have hc := br_QJ_comm bx K hK CK hKb x y
  have : rJ bx (fun x y => K y x) y x
      = K x y - QJy bx K x y - QJx bx K x y + QJy bx (QJx bx K) x y := rfl
  rw [this, ← hc]
  unfold rJ
  ring

theorem rJ_symm (bx : Boxes μE M) (hK : Measurable (uncurry K)) (CK : ℝ)
    (hKb : ∀ x y, |K x y| ≤ CK) (hKs : ∀ x y, K x y = K y x) :
    ∀ x y, rJ bx K x y = rJ bx K y x := by
  intro x y
  have hKt : (fun x y => K y x) = K := by
    funext a b; exact (hKs a b).symm
  have := br_rJ_transpose bx hK CK hKb x y
  rwa [hKt] at this

theorem rJ_abs_le_bound (bx : Boxes μE M) (CK : ℝ) (hKb : ∀ x y, |K x y| ≤ CK)
    (hK : Measurable (uncurry K)) : ∀ x y, |rJ bx K x y| ≤ 4 * CK := by
  intro x y
  have hxy : |QJx bx (QJy bx K) x y| ≤ CK :=
    br_QJ_abs_le bx _ CK (fun x' => br_QJy_bound bx K CK hKb x' y) x
  have h1 := hKb x y
  have h2 := br_QJx_bound bx K CK hKb x y
  have h3 := br_QJy_bound bx K CK hKb x y
  unfold rJ
  have := abs_le.1 h1; have := abs_le.1 h2; have := abs_le.1 h3; have := abs_le.1 hxy
  rw [abs_le]; constructor <;> linarith

theorem rJ_abs_le_osc (bx : Boxes μE M) (hK : Measurable (uncurry K)) (CK : ℝ)
    (hKb : ∀ x y, |K x y| ≤ CK) (ω₀ : ℝ)
    (hosc : ∀ a b, ∀ x ∈ bx.A a, ∀ x' ∈ bx.A a, ∀ y ∈ bx.A b, ∀ y' ∈ bx.A b,
      |K x y - K x' y'| ≤ ω₀) : ∀ x y, |rJ bx K x y| ≤ 4 * ω₀ := by
  intro x y
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (bx.cover ▸ Set.mem_univ x)
  obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (bx.cover ▸ Set.mem_univ y)
  have hω : 0 ≤ ω₀ := by
    have := hosc a b x ha x ha y hb y hb
    simpa using this
  have hKy := br_measurable_QJy bx K hK
  have e : rJ bx K x y = (K x y - QJ bx (fun x' => K x' y) x)
      - (QJy bx K x y - QJ bx (fun x' => QJy bx K x' y) x) := by
    unfold rJ QJx; ring
  have d1 : |K x y - QJ bx (fun x' => K x' y) x| ≤ ω₀ := by
    rw [br_QJ_apply bx _ ha]
    refine br_dev_le bx a (fun x' => K x' y)
      (br_integrable_of_bdd (br_meas_left hK y) CK (fun x' => hKb x' y)) x ω₀ ?_
    filter_upwards [br_ae_mem bx a] with x' hx'
    exact hosc a b x ha x' hx' y hb y hb
  have d2 : |QJy bx K x y - QJ bx (fun x' => QJy bx K x' y) x| ≤ ω₀ := by
    rw [br_QJ_apply bx _ ha]
    refine br_dev_le bx a (fun x' => QJy bx K x' y)
      (br_integrable_of_bdd (br_meas_left hKy y) CK (fun x' => br_QJy_bound bx K CK hKb x' y))
      x ω₀ ?_
    filter_upwards [br_ae_mem bx a] with x' hx'
    have e1 : QJy bx K x y = ∫ y', K x y' ∂(boxMeasure bx b) :=
      br_QJ_apply bx (fun y' => K x y') hb
    have e2 : QJy bx K x' y = ∫ y', K x' y' ∂(boxMeasure bx b) :=
      br_QJ_apply bx (fun y' => K x' y') hb
    have hi1 : Integrable (fun y' => K x y') (boxMeasure bx b) :=
      br_integrable_of_bdd (br_meas_right hK x) CK (fun y' => hKb x y')
    have hi2 : Integrable (fun y' => K x' y') (boxMeasure bx b) :=
      br_integrable_of_bdd (br_meas_right hK x') CK (fun y' => hKb x' y')
    show |QJy bx K x y - QJy bx K x' y| ≤ ω₀
    rw [e1, e2, ← integral_sub hi1 hi2]
    have := norm_integral_le_of_norm_le_const (μ := boxMeasure bx b)
      (f := fun y' => K x y' - K x' y') (C := ω₀)
      ((br_ae_mem bx b).mono fun y' hy' => by
        rw [Real.norm_eq_abs]; exact hosc a b x ha x' hx' y' hy' y' hy')
    simpa using this
  rw [e]
  have := abs_sub (K x y - QJ bx (fun x' => K x' y) x)
    (QJy bx K x y - QJ bx (fun x' => QJy bx K x' y) x)
  linarith

theorem rJ_centered_left (bx : Boxes μE M) (hK : Measurable (uncurry K)) (CK : ℝ)
    (hKb : ∀ x y, |K x y| ≤ CK) : ∀ y, ∫ x, rJ bx K x y ∂μE = 0 := by
  intro y
  have hKy := br_measurable_QJy bx K hK
  have hu : Integrable (fun x => K x y) μE :=
    br_integrable_of_bdd (br_meas_left hK y) CK (fun x => hKb x y)
  have hv : Integrable (fun x => QJy bx K x y) μE :=
    br_integrable_of_bdd (br_meas_left hKy y) CK (fun x => br_QJy_bound bx K CK hKb x y)
  have hQu : Integrable (QJ bx (fun x => K x y)) μE :=
    br_integrable_of_bdd (br_measurable_QJ bx _) CK (br_QJ_abs_le bx _ CK (fun x => hKb x y))
  have hQv : Integrable (QJ bx (fun x => QJy bx K x y)) μE :=
    br_integrable_of_bdd (br_measurable_QJ bx _) CK
      (br_QJ_abs_le bx _ CK (fun x => br_QJy_bound bx K CK hKb x y))
  have e : (fun x => rJ bx K x y) = fun x => (K x y - QJ bx (fun x' => K x' y) x)
      - (QJy bx K x y - QJ bx (fun x' => QJy bx K x' y) x) := by
    funext x; unfold rJ QJx; ring
  have i1 : ∫ x, ((K x y - QJ bx (fun x' => K x' y) x)
      - (QJy bx K x y - QJ bx (fun x' => QJy bx K x' y) x)) ∂μE
      = ∫ x, (K x y - QJ bx (fun x' => K x' y) x) ∂μE
        - ∫ x, (QJy bx K x y - QJ bx (fun x' => QJy bx K x' y) x) ∂μE :=
    integral_sub (hu.sub hQu) (hv.sub hQv)
  have i2 : ∫ x, (K x y - QJ bx (fun x' => K x' y) x) ∂μE
      = ∫ x, K x y ∂μE - ∫ x, QJ bx (fun x' => K x' y) x ∂μE := integral_sub hu hQu
  have i3 : ∫ x, (QJy bx K x y - QJ bx (fun x' => QJy bx K x' y) x) ∂μE
      = ∫ x, QJy bx K x y ∂μE - ∫ x, QJ bx (fun x' => QJy bx K x' y) x ∂μE := integral_sub hv hQv
  rw [e, i1, i2, i3, br_integral_QJ bx _ hu hQu, br_integral_QJ bx _ hv hQv]
  ring

theorem rJ_centered_right (bx : Boxes μE M) (hK : Measurable (uncurry K)) (CK : ℝ)
    (hKb : ∀ x y, |K x y| ≤ CK) : ∀ x, ∫ y, rJ bx K x y ∂μE = 0 := by
  intro x
  have hKt : Measurable (uncurry fun x y => K y x) := hK.comp measurable_swap
  have := rJ_centered_left bx hKt CK (fun x y => hKb y x) x
  rw [← this]
  exact integral_congr_ae (ae_of_all _ fun y => br_rJ_transpose bx hK CK hKb x y)

/-! ### Target (6): the exponential bound from Lemma 6.1 -/

private theorem br_W_eq_S {N : ℕ} {Ω : Type*} (K : E → E → ℝ) (hK : ∀ x y, K x y = K y x)
    (X : Fin N → Ω → E) (ω : Ω) :
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

theorem rJ_exp_bound (bx : Boxes μE M) (hK : Measurable (uncurry K)) (CK : ℝ)
    (hKb : ∀ x y, |K x y| ≤ CK) (hKs : ∀ x y, K x y = K y x)
    (κ : ℝ) (hκ : 0 < κ) (hrJ : ∀ x y, |rJ bx K x y| ≤ κ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 1 ≤ N) (X : Fin N → Ω → E) (hXm : ∀ i, Measurable (X i))
    (hXi : iIndepFun X μ) (hXl : ∀ i, μ.map (X i) = μE) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ : Cu * κ * θ ≤ 1 / 2) :
    Integrable (fun ω => Real.exp ((θ / 2) * W (rJ bx K) X ω)) μ ∧
      ∫ ω, Real.exp ((θ / 2) * W (rJ bx K) X ω) ∂μ ≤ 8 / 3 := by
  have hmeas := measurable_rJ bx hK CK hKb
  have hcl := rJ_centered_left bx hK CK hKb
  have hcr := rJ_centered_right bx hK CK hKb
  have hmom_bound : ∀ (p : ℕ), 1 ≤ p → ∀ (g : E → ℝ), (∀ z, |g z| ≤ κ) →
      ∫ z, |g z| ^ p ∂μE ≤ 2 * κ ^ p * (p.factorial : ℝ) := by
    intro p hp g hg
    have h1 : ∫ z, |g z| ^ p ∂μE ≤ κ ^ p := by
      have := norm_integral_le_of_norm_le_const (μ := μE) (f := fun z => |g z| ^ p) (C := κ ^ p)
        (ae_of_all _ fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hg z) p)
      exact (le_abs_self _).trans (by simpa using this)
    have h2 : (1 : ℝ) ≤ p.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero p)
    have h3 : 0 < κ ^ p := by positivity
    nlinarith
  have H : Hyp μ (fun _ : Fin N => μE) X (fun _ _ => rJ bx K) κ :=
    { κ_pos := hκ
      Y_meas := hXm
      Y_indep := hXi
      Y_law := hXl
      h_meas := fun _ _ => hmeas
      h_int := fun i j p hp =>
        br_integrable_of_bdd (((hmeas.comp measurable_id).abs).pow_const p) (κ ^ p)
          (fun z => by
            rw [abs_of_nonneg (by positivity)]
            exact pow_le_pow_left₀ (abs_nonneg _) (hrJ z.1 z.2) p)
      centered_left := fun i j _ => ae_of_all _ fun y => hcl y
      centered_right := fun i j _ => ae_of_all _ fun x => hcr x
      moment_left := fun i j _ p hp => ae_of_all _ fun y =>
        hmom_bound p hp (fun x => rJ bx K x y) (fun x => hrJ x y)
      moment_right := fun i j _ p hp => ae_of_all _ fun x =>
        hmom_bound p hp (fun y => rJ bx K x y) (fun y => hrJ x y) }
  have hrs : ∀ x y, rJ bx K x y = rJ bx K y x := rJ_symm bx hK CK hKb hKs
  have hWS : ∀ ω, (θ / 2) * W (rJ bx K) X ω = θ * S (fun _ _ => rJ bx K) X ω / N := by
    intro ω
    rw [br_W_eq_S (rJ bx K) hrs X ω]
    ring
  have hθ1 : Cu * κ * |θ| < 1 := by
    rw [abs_of_nonneg hθ0]; linarith
  have hbd := exp_bound H hN θ hθ1
  refine ⟨?_, ?_⟩
  · -- integrability: `W` is bounded and measurable
    have hWm : Measurable (W (rJ bx K) X) := by
      unfold W
      refine Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
        Finset.measurable_sum _ fun j _ => ?_) _
      exact hmeas.comp ((hXm i).prodMk (hXm j))
    set B : ℝ := (1 / (N : ℝ)) * ∑ i : Fin N, ∑ j ∈ univ.erase i, κ with hB
    have hWb : ∀ ω, |W (rJ bx K) X ω| ≤ B := by
      intro ω
      unfold W
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (N : ℝ))]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hrJ _ _)
    refine Integrable.of_bound (C := Real.exp (θ / 2 * B))
      ((Real.measurable_exp.comp (hWm.const_mul (θ / 2))).aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hWb ω)) (by positivity)
  · have e : ∫ ω, Real.exp ((θ / 2) * W (rJ bx K) X ω) ∂μ
        = ∫ ω, Real.exp (θ * S (fun _ _ => rJ bx K) X ω / N) ∂μ := by
      congr 1; funext ω; rw [hWS]
    rw [e]
    refine hbd.trans ?_
    have hCu : Cu = 16 := rfl
    have h0 : 0 ≤ Cu * κ * θ := by rw [hCu]; positivity
    rw [abs_of_nonneg hθ0]
    have hsq : (Cu * κ * θ) ^ 2 ≤ 1 / 4 := by nlinarith
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith

end Remainder

end LogGas.Bulk
