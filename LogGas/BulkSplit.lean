import LogGas.Bulk

/-!
# Appendix A energy split (regularized form)

Source: `notes/appendixA.tex` eqs. (A.2)–(A.4) and (A.10); regularization as planned in the
docstring of `LogGas.Bulk` (audit A10, F2, F3).

Statements (all deterministic in `ω`, for bounded measurable symmetric `K`):
* `histCoef_dot_le` — `|c|² ≤ M²` for the histogram coefficients `c`;
* `empEnergy_split` — `⟨μ_N,Kμ_N⟩ = 2⟨c,ℓ⟩ − ⟨c,Σc⟩ + ⟨μ_N, r_J μ_N⟩`;
* `empEnergy_le` — eq. (A.4), regularized: `empEnergy K ≤ coarse_ε + ε M² + empEnergy r_J`;
* `W_le_coarse` — eq. (A.10), regularized with `ε = 1/N`.

The box lemmas of `LogGas.Singular` require group/metric instances on `E`, which `LogGas.Bulk`
does not assume, so the small facts needed are reproved here with the prefix `bs_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Finset Function Matrix
open scoped BigOperators ENNReal

namespace LogGas.Bulk

open LogGas.Decoupling LogGas.BadEvent LogGas.Singular

section BulkSplit

variable {E : Type*} [MeasurableSpace E] {μE : Measure E} [IsProbabilityMeasure μE]
  {M N : ℕ} {Ω : Type*} {K : E → E → ℝ}

private theorem bs_prob (bx : Boxes μE M) (a : Fin M) :
    IsProbabilityMeasure (boxMeasure bx a) := by
  refine ⟨?_⟩
  have h := bx.vol a
  have hM : (M : ℝ≥0∞) ≠ 0 := by
    have := a.pos
    exact_mod_cast this.ne'
  simp only [boxMeasure, Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_natCast, smul_eq_mul,
    Measure.restrict_apply_univ, h]
  exact ENNReal.mul_inv_cancel hM (ENNReal.natCast_ne_top M)

private theorem bs_QJ_mem (bx : Boxes μE M) (f : E → ℝ) {a : Fin M} {x : E} (hx : x ∈ bx.A a) :
    QJ bx f x = ∫ y, f y ∂(boxMeasure bx a) := by
  unfold QJ
  rw [Finset.sum_eq_single a]
  · exact Set.indicator_of_mem hx _
  · intro b _ hb
    refine Set.indicator_of_notMem ?_ _
    intro hxb
    exact Set.disjoint_left.mp (bx.disj hb) hxb hx
  · simp

private theorem bs_exists_box (bx : Boxes μE M) (x : E) : ∃ a, x ∈ bx.A a := by
  have := bx.cover ▸ Set.mem_univ x
  simpa using this

/-- sum of box indicators is one. -/
private theorem bs_sum_ind (bx : Boxes μE M) (x : E) :
    ∑ a, (bx.A a).indicator (1 : E → ℝ) x = 1 := by
  obtain ⟨a, ha⟩ := bs_exists_box bx x
  rw [Finset.sum_eq_single a]
  · simp [ha]
  · intro b _ hb
    refine Set.indicator_of_notMem ?_ _
    intro hxb
    exact Set.disjoint_left.mp (bx.disj hb) hxb ha
  · simp

private theorem bs_occ_cast (X : Fin N → Ω → E) (A : Set E) (ω : Ω) :
    (occupancy X A ω : ℝ) = ∑ i, A.indicator (1 : E → ℝ) (X i ω) := by
  unfold occupancy
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : X i ω ∈ A <;> simp [h]

private theorem bs_occ_sum (bx : Boxes μE M) (X : Fin N → Ω → E) (ω : Ω) :
    ∑ a, (occupancy X (bx.A a) ω : ℝ) = N := by
  simp_rw [bs_occ_cast]
  rw [Finset.sum_comm]
  simp [bs_sum_ind]

theorem histCoef_dot_le (bx : Boxes μE M) (X : Fin N → Ω → E) (ω : Ω) (hN : 1 ≤ N) :
    histCoef X bx ω ⬝ᵥ histCoef X bx ω ≤ (M : ℝ) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum := bs_occ_sum bx X ω
  have hocc0 : ∀ a, (0 : ℝ) ≤ (occupancy X (bx.A a) ω : ℝ) := fun a => Nat.cast_nonneg _
  have hle : ∀ a, (occupancy X (bx.A a) ω : ℝ) ≤ N := by
    intro a
    rw [← hsum]
    exact Finset.single_le_sum (f := fun a => (occupancy X (bx.A a) ω : ℝ))
      (fun b _ => hocc0 b) (Finset.mem_univ a)
  have hc0 : ∀ a, 0 ≤ histCoef X bx ω a := fun a => by
    unfold histCoef; positivity
  have hcM : ∀ a, histCoef X bx ω a ≤ M := by
    intro a
    unfold histCoef
    rw [div_le_iff₀ hNpos]
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    nlinarith [hle a]
  have hcs : ∑ a, histCoef X bx ω a = M := by
    unfold histCoef
    rw [← Finset.sum_div, ← Finset.mul_sum, hsum]
    field_simp
  calc histCoef X bx ω ⬝ᵥ histCoef X bx ω = ∑ a, histCoef X bx ω a * histCoef X bx ω a := rfl
    _ ≤ ∑ a, histCoef X bx ω a * M :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hcM a) (hc0 a)
    _ = (M : ℝ) ^ 2 := by rw [← Finset.sum_mul, hcs]; ring

/-! ### Box averages of a two-variable kernel -/

private theorem bs_int_box (bx : Boxes μE M) (a : Fin M) (g : E → ℝ) :
    ∫ y, g y ∂(boxMeasure bx a) = (M : ℝ) * ∫ y, (bx.A a).indicator g y ∂μE := by
  unfold boxMeasure
  rw [integral_smul_nnreal_measure, integral_indicator (bx.meas a), NNReal.smul_def, smul_eq_mul]
  simp

private theorem bs_m_eq_T (bx : Boxes μE M) (K : E → E → ℝ) (a : Fin M) (x : E) :
    ∫ y, K x y ∂(boxMeasure bx a) = M * T μE K ((bx.A a).indicator 1) x := by
  rw [bs_int_box]
  unfold T
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases h : y ∈ bx.A a <;> simp [h]

/-- The `(a,b)` entry of the double box average. -/
private noncomputable def bsG (bx : Boxes μE M) (K : E → E → ℝ) (a b : Fin M) : ℝ :=
  ∫ x', ∫ y', K x' y' ∂(boxMeasure bx b) ∂(boxMeasure bx a)

private theorem bs_G_eq_gram (bx : Boxes μE M) (K : E → E → ℝ) (a b : Fin M) :
    bsG bx K a b = (M : ℝ) ^ 2 * gram μE K bx a b := by
  unfold bsG
  simp_rw [bs_m_eq_T]
  rw [integral_const_mul, bs_int_box]
  have : gram μE K bx a b = ∫ x, (bx.A a).indicator (T μE K ((bx.A b).indicator 1)) x ∂μE := by
    show energy μE K ((bx.A a).indicator 1) ((bx.A b).indicator 1) = _
    unfold energy T
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases h : x ∈ bx.A a
    · simp only [h, Set.indicator_of_mem]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp
    · simp [h]
  rw [this]; ring

private theorem bs_QJy_eq (bx : Boxes μE M) (K : E → E → ℝ) (x y : E) :
    QJy bx K x y = ∑ b, (bx.A b).indicator (1 : E → ℝ) y *
      (M * T μE K ((bx.A b).indicator 1) x) := by
  unfold QJy QJ
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [bs_m_eq_T]
  by_cases h : y ∈ bx.A b <;> simp [h]

private theorem bs_QJx_eq_QJy (bx : Boxes μE M) (K : E → E → ℝ) (hKs : ∀ x y, K x y = K y x)
    (x y : E) : QJx bx K x y = QJy bx K y x := by
  unfold QJx QJy
  congr 1
  funext z
  exact hKs _ _

private theorem bs_QJxQJy_eq (bx : Boxes μE M) (K : E → E → ℝ) (x y : E) :
    QJx bx (QJy bx K) x y = ∑ a, ∑ b, (bx.A a).indicator (1 : E → ℝ) x *
      (bx.A b).indicator (1 : E → ℝ) y * bsG bx K a b := by
  obtain ⟨b0, hb0⟩ := bs_exists_box bx y
  have h1 : ∀ x', QJy bx K x' y = ∫ y', K x' y' ∂(boxMeasure bx b0) := fun x' =>
    bs_QJ_mem bx _ hb0
  have h2 : ∀ a, ∫ x', QJy bx K x' y ∂(boxMeasure bx a) = bsG bx K a b0 := by
    intro a
    unfold bsG
    exact integral_congr_ae (Filter.Eventually.of_forall h1)
  unfold QJx QJ
  simp_rw [h2]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single b0]
  · simp [hb0]
    by_cases h : x ∈ bx.A a <;> simp [h]
  · intro b _ hb
    have : y ∉ bx.A b := fun hyb =>
      Set.disjoint_left.mp (bx.disj hb) hyb hb0
    simp [this]
  · simp

/-- Double indicator expansion of an empirical sum. -/
private theorem bs_emp_double (bx : Boxes μE M) (X : Fin N → Ω → E) (ω : Ω)
    (G : Fin M → Fin M → ℝ) :
    ∑ i, ∑ j, ∑ a, ∑ b, (bx.A a).indicator (1 : E → ℝ) (X i ω) *
      (bx.A b).indicator (1 : E → ℝ) (X j ω) * G a b
      = ∑ a, ∑ b, (occupancy X (bx.A a) ω : ℝ) * (occupancy X (bx.A b) ω : ℝ) * G a b := by
  simp_rw [bs_occ_cast]
  have h1 : ∀ i, ∑ j, ∑ a, ∑ b, (bx.A a).indicator (1 : E → ℝ) (X i ω) *
      (bx.A b).indicator (1 : E → ℝ) (X j ω) * G a b
      = ∑ a, ∑ b, ∑ j, (bx.A a).indicator (1 : E → ℝ) (X i ω) *
      (bx.A b).indicator (1 : E → ℝ) (X j ω) * G a b := by
    intro i
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]

theorem empEnergy_split (hK : Measurable (uncurry K)) (CK : ℝ) (hKb : ∀ x y, |K x y| ≤ CK)
    (hKs : ∀ x y, K x y = K y x) (bx : Boxes μE M) (X : Fin N → Ω → E) (ω : Ω) (hN : 1 ≤ N) :
    empEnergy K X ω = 2 * (histCoef X bx ω ⬝ᵥ ell μE K bx X ω)
      - histCoef X bx ω ⬝ᵥ (gram μE K bx *ᵥ histCoef X bx ω) + empEnergy (rJ bx K) X ω := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  -- the three correction sums
  have hy : empEnergy (QJy bx K) X ω = histCoef X bx ω ⬝ᵥ ell μE K bx X ω := by
    unfold empEnergy
    simp_rw [bs_QJy_eq]
    have : ∀ i, ∑ j, ∑ b, (bx.A b).indicator (1 : E → ℝ) (X j ω) *
        (M * T μE K ((bx.A b).indicator 1) (X i ω))
        = ∑ b, (occupancy X (bx.A b) ω : ℝ) * (M * T μE K ((bx.A b).indicator 1) (X i ω)) := by
      intro i
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [bs_occ_cast, Finset.sum_mul]
    simp_rw [this]
    rw [Finset.sum_comm]
    unfold dotProduct histCoef ell empPair
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [← Finset.mul_sum]
    field_simp
  have hx : empEnergy (QJx bx K) X ω = empEnergy (QJy bx K) X ω := by
    unfold empEnergy
    simp_rw [bs_QJx_eq_QJy bx K hKs]
    rw [Finset.sum_comm]
  have hxy : empEnergy (QJx bx (QJy bx K)) X ω
      = histCoef X bx ω ⬝ᵥ (gram μE K bx *ᵥ histCoef X bx ω) := by
    unfold empEnergy
    simp_rw [bs_QJxQJy_eq, bs_emp_double]
    simp only [Matrix.mulVec, dotProduct, histCoef]
    simp_rw [bs_G_eq_gram, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    field_simp
  have hr : empEnergy (rJ bx K) X ω = empEnergy K X ω - empEnergy (QJx bx K) X ω
      - empEnergy (QJy bx K) X ω + empEnergy (QJx bx (QJy bx K)) X ω := by
    unfold empEnergy rJ
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  rw [hr, hx, hy, hxy]
  ring

theorem empEnergy_le (hK : Measurable (uncurry K)) (CK : ℝ) (hKb : ∀ x y, |K x y| ≤ CK)
    (hKs : ∀ x y, K x y = K y x) (bx : Boxes μE M) (X : Fin N → Ω → E) (ω : Ω) (hN : 1 ≤ N)
    (hSig : (gram μE K bx).PosSemidef) (ε : ℝ) (hε : 0 < ε) :
    empEnergy K X ω ≤ coarse μE K bx ε X ω + ε * (M : ℝ) ^ 2 + empEnergy (rJ bx K) X ω := by
  rw [empEnergy_split hK CK hKb hKs bx X ω hN]
  have h1 := square_completion (gram μE K bx) hSig ε hε (ell μE K bx X ω) (histCoef X bx ω)
  have h2 := histCoef_dot_le bx X ω hN
  have h3 : ε * (histCoef X bx ω ⬝ᵥ histCoef X bx ω) ≤ ε * (M : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left h2 hε.le
  have h4 : coarse μE K bx ε X ω = ell μE K bx X ω ⬝ᵥ
      (gram μE K bx + ε • (1 : Matrix (Fin M) (Fin M) ℝ))⁻¹ *ᵥ ell μE K bx X ω := rfl
  rw [h4]
  linarith [dotProduct_comm (ell μE K bx X ω) (histCoef X bx ω)]

private theorem bs_QJ_bound (bx : Boxes μE M) (f : E → ℝ) (C : ℝ) (hf : ∀ y, |f y| ≤ C) (x : E) :
    |QJ bx f x| ≤ C := by
  obtain ⟨a, ha⟩ := bs_exists_box bx x
  have := bs_prob bx a
  rw [bs_QJ_mem bx f ha, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := boxMeasure bx a) (f := f) (C := C)
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hf y)
  simpa using this

private theorem bs_rJ_bound (bx : Boxes μE M) (CK : ℝ) (hKb : ∀ x y, |K x y| ≤ CK) (x y : E) :
    |rJ bx K x y| ≤ 4 * CK := by
  have h1 : |QJx bx K x y| ≤ CK := bs_QJ_bound bx _ CK (fun x' => hKb x' y) x
  have h2 : |QJy bx K x y| ≤ CK := bs_QJ_bound bx _ CK (fun y' => hKb x y') y
  have h3 : |QJx bx (QJy bx K) x y| ≤ CK :=
    bs_QJ_bound bx _ CK (fun x' => bs_QJ_bound bx _ CK (fun y' => hKb x' y') y) x
  have h0 := hKb x y
  unfold rJ
  rw [abs_le] at *
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

private theorem bs_W_eq (K : E → E → ℝ) (X : Fin N → Ω → E) (ω : Ω) (hN : 1 ≤ N) :
    W K X ω = N * empEnergy K X ω - (1 / (N : ℝ)) * ∑ i, K (X i ω) (X i ω) := by
  have hNne : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  unfold W empEnergy
  have : ∀ i, ∑ j ∈ univ.erase i, K (X i ω) (X j ω)
      = ∑ j, K (X i ω) (X j ω) - K (X i ω) (X i ω) := fun i =>
    Finset.sum_erase_eq_sub (Finset.mem_univ i)
  simp_rw [this, Finset.sum_sub_distrib]
  field_simp

private theorem bs_diag_bound (K : E → E → ℝ) (C : ℝ) (hb : ∀ x y, |K x y| ≤ C)
    (X : Fin N → Ω → E) (ω : Ω) (hN : 1 ≤ N) :
    |(1 / (N : ℝ)) * ∑ i, K (X i ω) (X i ω)| ≤ C := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
  have : |∑ i, K (X i ω) (X i ω)| ≤ N * C := by
    calc |∑ i, K (X i ω) (X i ω)| ≤ ∑ i, |K (X i ω) (X i ω)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, C := Finset.sum_le_sum fun i _ => hb _ _
      _ = N * C := by simp
  calc 1 / (N : ℝ) * |∑ i, K (X i ω) (X i ω)| ≤ 1 / (N : ℝ) * (N * C) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = C := by field_simp

theorem W_le_coarse (hK : Measurable (uncurry K)) (CK : ℝ) (hKb : ∀ x y, |K x y| ≤ CK)
    (hKs : ∀ x y, K x y = K y x) (bx : Boxes μE M) (X : Fin N → Ω → E) (ω : Ω) (hN : 1 ≤ N)
    (hSig : (gram μE K bx).PosSemidef) :
    W K X ω ≤ (N : ℝ) * coarse μE K bx (1 / N) X ω + (M : ℝ) ^ 2 + W (rJ bx K) X ω + 5 * CK := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hle := empEnergy_le hK CK hKb hKs bx X ω hN hSig (1 / N) (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hle hNpos.le
  have hd1 := bs_diag_bound K CK hKb X ω hN
  have hd2 := bs_diag_bound (rJ bx K) (4 * CK) (bs_rJ_bound bx CK hKb) X ω hN
  rw [bs_W_eq K X ω hN, bs_W_eq (rJ bx K) X ω hN]
  have hε : (N : ℝ) * (1 / N * (M : ℝ) ^ 2) = (M : ℝ) ^ 2 := by field_simp
  rw [abs_le] at hd1 hd2
  nlinarith [hd1.1, hd1.2, hd2.1, hd2.2, hmul, hε]

end BulkSplit

end LogGas.Bulk
