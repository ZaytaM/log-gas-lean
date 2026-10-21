import Mathlib

/-!
# Shared concrete torus base

Definitions here are copies (verbatim bodies) of those in `Challenge.lean` (`LogGas.Spec`,
`LogGas.Torus`) and `PaperChallenge.lean` (`LogGas.Fourier`; eq. (1.1) of `notes/sec1-setting.tex`),
with `Torus ↦ T` and `uniform ↦ unif`, so bridges close by unfolding.
The torus is `Fin d → AddCircle 1` with normalized Haar product measure.
-/

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LogGas.Torus

abbrev T (d : ℕ) := Fin d → AddCircle (1 : ℝ)

noncomputable def unif (d : ℕ) : Measure (T d) :=
  Measure.pi fun _ => AddCircle.haarAddCircle

instance (d : ℕ) : IsProbabilityMeasure (unif d) := by
  unfold unif; infer_instance

instance (d : ℕ) : (unif d).IsAddLeftInvariant := by
  unfold unif; infer_instance

instance (d : ℕ) : (unif d).IsNegInvariant := by
  unfold unif
  have : (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))).IsNegInvariant :=
    inferInstance
  infer_instance

instance (d : ℕ) : (unif d).IsAddRightInvariant := by
  unfold unif; infer_instance

noncomputable def radius {d : ℕ} (x : T d) : ℝ :=
  Real.sqrt (∑ i, dist (x i) 0 ^ 2)

theorem dist_zero_le_radius {d : ℕ} (x : T d) : dist x 0 ≤ radius x := by
  unfold radius
  refine (dist_pi_le_iff (Real.sqrt_nonneg _)).2 fun i => ?_
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (f := fun i => dist (x i) (0 : AddCircle (1 : ℝ)) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem radius_le_sqrt_mul {d : ℕ} (x : T d) : radius x ≤ Real.sqrt d * dist x 0 := by
  unfold radius
  have h : Real.sqrt d * dist x 0 = Real.sqrt (d * dist x 0 ^ 2) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq dist_nonneg]
  rw [h]
  apply Real.sqrt_le_sqrt
  calc ∑ i, dist (x i) (0 : AddCircle (1 : ℝ)) ^ 2 ≤ ∑ _i : Fin d, dist x 0 ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have : dist (x i) 0 ≤ dist x 0 := dist_le_pi_dist x 0 i
        exact pow_le_pow_left₀ dist_nonneg this 2
    _ = d * dist x 0 ^ 2 := by simp

theorem continuous_radius {d : ℕ} : Continuous (radius (d := d)) := by
  unfold radius
  fun_prop

private theorem torusbase_circle_ball (ρ : ℝ) (x : AddCircle (1 : ℝ)) :
    (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) (Metric.ball x ρ) ≤
      ENNReal.ofReal (2 * ρ) := by
  have h1 : (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) =
      volume := by
    have := AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))
    simp at this
    rw [this]
  rw [h1]
  calc volume (Metric.ball x ρ) ≤ volume (Metric.closedBall x ρ) :=
        measure_mono Metric.ball_subset_closedBall
    _ = ENNReal.ofReal (min 1 (2 * ρ)) := AddCircle.volume_closedBall 1 ρ
    _ ≤ ENNReal.ofReal (2 * ρ) := ENNReal.ofReal_le_ofReal (min_le_right _ _)

theorem ball_vol (d : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    unif d (Metric.ball (0 : T d) ρ) ≤ ENNReal.ofReal ((2 : ℝ) ^ d * ρ ^ d) := by
  unfold unif
  rw [Measure.pi_ball _ _ hρ]
  calc ∏ i : Fin d, (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ)))
        (Metric.ball ((0 : T d) i) ρ)
      ≤ ∏ _i : Fin d, ENNReal.ofReal (2 * ρ) :=
        by gcongr with i; exact torusbase_circle_ball ρ _
    _ = ENNReal.ofReal ((2 : ℝ) ^ d * ρ ^ d) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← ENNReal.ofReal_pow (by positivity), mul_pow]

theorem measurePreserving_sub (d : ℕ) :
    MeasurePreserving (fun z : T d × T d => z.1 - z.2) ((unif d).prod (unif d)) (unif d) :=
  (measurePreserving_fst (μ := unif d) (ν := unif d)).comp
    (measurePreserving_sub_prod (unif d) (unif d))

end LogGas.Torus

namespace LogGas.Fourier
open LogGas.Torus

noncomputable def negChar {d : ℕ} (k : Fin d → ℤ) (x : T d) : ℂ :=
  ∏ i, fourier (-(k i)) (x i)

noncomputable def coeff {d : ℕ} (f : T d → ℝ) (k : Fin d → ℤ) : ℂ :=
  ∫ x, negChar k x * (f x : ℂ) ∂unif d

noncomputable def latticeNorm {d : ℕ} (k : Fin d → ℤ) : ℝ :=
  Real.sqrt (∑ i, ((k i : ℤ) : ℝ) ^ 2)

noncomputable def cd (d : ℕ) : ℝ :=
  2 ^ (d - 1) * Real.pi ^ ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2)

noncomputable def kernelCoeff (d : ℕ) (k : Fin d → ℤ) : ℝ :=
  if k = 0 then 0 else cd d / (2 * Real.pi * latticeNorm k) ^ d

def IsLogKernel (d : ℕ) (g : T d → ℝ) : Prop :=
  Measurable g ∧ Integrable g (unif d) ∧
    ∀ k : Fin d → ℤ, coeff g k = (kernelCoeff d k : ℂ)

end LogGas.Fourier

namespace LogGas.Spec
open LogGas.Torus

noncomputable def energy {d : ℕ} (g : T d → ℝ) (N : ℕ) (x : Fin N → T d) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i, g (x i - x j)

noncomputable def weight {d : ℕ} (g : T d → ℝ) (N : ℕ) (β : ℝ)
    (x : Fin N → T d) : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((β / 2) * energy g N x))

noncomputable def partition {d : ℕ} (g : T d → ℝ) (N : ℕ) (β : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, weight g N β x ∂Measure.pi (fun _ => unif d)

noncomputable def entropy {d : ℕ} (ρ : T d → ℝ) : ℝ :=
  ∫ x, ρ x * Real.log (ρ x) ∂unif d

noncomputable def quadratic {d : ℕ} (K : T d → T d → ℝ)
    (f : T d → ℝ) : ℝ :=
  ∫ x, ∫ y, K x y * f x * f y ∂unif d ∂unif d

def density {d : ℕ} (ρ : T d → ℝ) : Prop :=
  Measurable ρ ∧ (∀ᵐ x ∂unif d, 0 ≤ ρ x) ∧ Integrable ρ (unif d) ∧
    (∫ x, ρ x ∂unif d) = 1 ∧ Integrable (fun x => ρ x * Real.log (ρ x)) (unif d)

def logHLS {d : ℕ} (g : T d → ℝ) (B : ℝ) : Prop :=
  ∀ ρ, density ρ →
    Integrable (fun z : T d × T d =>
      g (z.1 - z.2) * (ρ z.1 - 1) * (ρ z.2 - 1)) ((unif d).prod (unif d)) ∧
    (B / 2) * quadratic (fun x y => g (x - y)) (fun x => ρ x - 1) ≤ entropy ρ

def positive {d : ℕ} (g : T d → ℝ) : Prop :=
  ∀ f : T d → ℝ, Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    0 ≤ quadratic (fun x y => g (x - y)) f

def cutoff {d : ℕ} (g : T d → ℝ) : Prop :=
  ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ J : ℕ, 3 ≤ J →
    ∃ s b : T d → ℝ,
      Measurable s ∧ Integrable s (unif d) ∧ Continuous b ∧
      (∀ x, b (-x) = b x) ∧ (∫ x, b x ∂unif d) = 0 ∧
      (∀ᵐ x ∂unif d, g x = b x + (s x - ∫ z, s z ∂unif d)) ∧
      (∀ᵐ x ∂unif d, 0 ≤ s x) ∧
      (∀ᵐ x ∂unif d, (1 / (2 * (J : ℝ))) < radius x → s x = 0) ∧
      (∀ᵐ x ∂unif d, s x ≤ max 0 (Real.log ((1 / (2 * (J : ℝ))) / radius x))) ∧
      0 ≤ (∫ z, s z ∂unif d) ∧
      (∫ z, s z ∂unif d) ≤ Cc * (1 / (2 * (J : ℝ))) ^ d ∧
      positive b ∧ positive (fun x => s x - ∫ z, s z ∂unif d) ∧
      (∀ f : T d → ℝ, Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
        quadratic (fun x y => b (x - y)) f ≤ quadratic (fun x y => g (x - y)) f)

def principalStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ (g : T d → ℝ) (B β0 : ℝ),
    Measurable g → Integrable g (unif d) → (∫ x, g x ∂unif d) = 0 →
    (∀ᵐ x ∂unif d, g (-x) = g x) →
    0 < B → B ≤ 2 * d → 0 ≤ β0 → β0 < B → logHLS g B → cutoff g →
    ∃ C : ℝ≥0, ∀ N : ℕ, 2 ≤ N → ∀ β : ℝ, 0 ≤ β → β ≤ β0 →
      partition g N β ≤ (C : ℝ≥0∞)

def bulkStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ (K : T d → T d → ℝ) (B β0 : ℝ),
    Continuous (Function.uncurry K) → (∀ x y, K x y = K y x) →
    (∀ x, ∫ y, K x y ∂unif d = 0) →
    (∀ f : T d → ℝ, Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      0 ≤ quadratic K f) →
    0 < B → 0 ≤ β0 → β0 < B →
    (∀ ρ, density ρ → (B / 2) * quadratic K (fun x => ρ x - 1) ≤ entropy ρ) →
    ∃ C : ℝ≥0, ∀ N : ℕ, 1 ≤ N → ∀ β : ℝ, 0 ≤ β → β ≤ β0 →
      (∫⁻ x : Fin N → T d, ENNReal.ofReal (Real.exp ((β / 2) *
        ((1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i, K (x i) (x j))))
          ∂Measure.pi (fun _ => unif d)) ≤ (C : ℝ≥0∞)

end LogGas.Spec
