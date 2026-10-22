import LogGas.TorusBase

/-!
# Continuous real Fourier series with absolutely summable even coefficients

Bulk part `b_r` of `H2`, `notes/sec2-cutoff.tex` (2.1)-(2.2); audit E2.
Given an even real family `c` on `ℤᵈ` with `∑ |c k| < ∞`, we construct a continuous even
real function `b` on the torus with `coeff b k = c k` (and `coeff f 0` is the mean of `f`).
-/

set_option autoImplicit false
open MeasureTheory LogGas.Torus
open scoped BigOperators

namespace LogGas.Fourier

theorem coeff_zero_eq {d : ℕ} (f : T d → ℝ) :
    coeff f 0 = ((∫ x, f x ∂unif d : ℝ) : ℂ) := by
  unfold coeff
  have h1 : ∀ x : T d, negChar 0 x = 1 := fun x => by simp [negChar]
  simp_rw [h1, one_mul]
  exact integral_ofReal

private theorem fourierseries_negChar {d : ℕ} (k : Fin d → ℤ) (x : T d) :
    negChar k x = UnitAddTorus.mFourier (-k) x := rfl

private theorem fourierseries_orth {d : ℕ} (k m : Fin d → ℤ) :
    ∫ x, UnitAddTorus.mFourier (-k) x * UnitAddTorus.mFourier m x ∂unif d =
      if m = k then 1 else 0 := by
  have h := orthonormal_iff_ite.mp UnitAddTorus.orthonormal_mFourier k m
  simp only [ContinuousMap.inner_toLp, ← UnitAddTorus.mFourier_neg] at h
  have h2 : (∫ x, UnitAddTorus.mFourier (-k) x * UnitAddTorus.mFourier m x ∂unif d) =
      if k = m then 1 else 0 := by
    refine Eq.trans ?_ h
    congr 1
    ext x
    rw [UnitAddTorus.mFourier_neg, mul_comm]
  rw [h2]
  by_cases hk : m = k
  · subst hk; simp
  · simp [hk, Ne.symm hk]

private theorem fourierseries_norm {d : ℕ} (k : Fin d → ℤ) (x : T d) :
    ‖UnitAddTorus.mFourier k x‖ = 1 := by
  have := UnitAddTorus.mFourier_neg (d := Fin d) (n := k) (x := x)
  have h2 : UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) x = 1 := by
    rw [← UnitAddTorus.mFourier_add]; simp [UnitAddTorus.mFourier_zero]
  rw [this] at h2
  have : ‖UnitAddTorus.mFourier k x‖ ^ 2 = 1 := by
    have h3 := Complex.mul_conj' (UnitAddTorus.mFourier k x)
    rw [h2] at h3
    exact_mod_cast h3.symm
  nlinarith [norm_nonneg (UnitAddTorus.mFourier k x)]

theorem exists_continuous_of_summable {d : ℕ} (c : (Fin d → ℤ) → ℝ)
    (hc : Summable fun k => |c k|) (heven : ∀ k, c (-k) = c k) :
    ∃ b : T d → ℝ, Continuous b ∧ (∀ x, b (-x) = b x) ∧ ∀ k, coeff b k = (c k : ℂ) := by
  set u : (Fin d → ℤ) → T d → ℂ := fun k x => (c k : ℂ) * UnitAddTorus.mFourier k x with hu
  have hsum : ∀ x, Summable fun k => u k x := fun x =>
    Summable.of_norm (by simpa [hu, fourierseries_norm] using hc)
  set F : T d → ℂ := fun x => ∑' k, u k x with hF
  have hFcont : Continuous F := by
    refine continuous_tsum (u := fun k => |c k|) (fun k => ?_) hc (fun k x => ?_)
    · simp only [hu]; exact continuous_const.mul (UnitAddTorus.mFourier k).continuous
    · simp [hu, fourierseries_norm]
  have hconj : ∀ x, (starRingEnd ℂ) (F x) = F x := by
    intro x
    have h1 : (starRingEnd ℂ) (F x) = ∑' k, (starRingEnd ℂ) (u k x) :=
      Complex.conj_tsum _
    have h2 : ∀ k, (starRingEnd ℂ) (u k x) = u (-k) x := by
      intro k
      simp [hu, heven, UnitAddTorus.mFourier_neg]
    rw [h1]
    simp_rw [h2]
    exact (Equiv.tsum_eq (Equiv.neg (Fin d → ℤ)) (fun k => u k x))
  have hreal : ∀ x, ((F x).re : ℂ) = F x := fun x => Complex.conj_eq_iff_re.mp (hconj x)
  have hneg : ∀ x, F (-x) = F x := by
    intro x
    have : ∀ k, u k (-x) = u (-k) x := by
      intro k
      simp only [hu, heven]
      congr 1
      show UnitAddTorus.mFourier k (-x) = UnitAddTorus.mFourier (-k) x
      simp [UnitAddTorus.mFourier]
    simp_rw [hF, this]
    exact (Equiv.tsum_eq (Equiv.neg (Fin d → ℤ)) (fun k => u k x))
  refine ⟨fun x => (F x).re, Complex.continuous_re.comp hFcont, fun x => by simp [hneg], ?_⟩
  intro k
  have hcoeff : coeff (fun x => (F x).re) k = ∫ x, UnitAddTorus.mFourier (-k) x * F x ∂unif d := by
    unfold coeff
    congr 1
    ext x
    rw [hreal x]
    rfl
  have hG : ∀ n, Continuous fun x : T d => UnitAddTorus.mFourier (-k) x * u n x := fun n => by
    simp only [hu]
    exact (UnitAddTorus.mFourier (-k)).continuous.mul
      (continuous_const.mul (UnitAddTorus.mFourier n).continuous)
  have hHS := hasSum_integral_of_dominated_convergence (μ := unif d)
    (F := fun n x => UnitAddTorus.mFourier (-k) x * u n x)
    (f := fun x => UnitAddTorus.mFourier (-k) x * F x) (fun n _ => |c n|)
    (fun n => (hG n).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun x => by
      simp [hu, fourierseries_norm])
    (Filter.Eventually.of_forall fun x => hc)
    (integrable_const _)
    (Filter.Eventually.of_forall fun x => (hsum x).hasSum.mul_left _)
  have hterm : ∀ n, ∫ x, UnitAddTorus.mFourier (-k) x * u n x ∂unif d =
      (c n : ℂ) * (if n = k then 1 else 0) := by
    intro n
    have : ∀ x, UnitAddTorus.mFourier (-k) x * u n x =
        (c n : ℂ) * (UnitAddTorus.mFourier (-k) x * UnitAddTorus.mFourier n x) := by
      intro x; simp only [hu]; ring
    simp_rw [this]
    rw [integral_const_mul, fourierseries_orth]
  simp_rw [hterm] at hHS
  rw [hcoeff, ← hHS.tsum_eq]
  simp

end LogGas.Fourier
