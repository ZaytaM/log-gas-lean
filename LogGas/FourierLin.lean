import LogGas.TorusBase

/-!
# Linearity of torus Fourier coefficients and the null origin

Helper for `notes/sec2-cutoff.tex` (2.1)-(2.2): the kernel identity a.e. and positivity of
`s - ∫ s` (audit E2, C2).  Contains `integral_negChar`, `coeff_add`, `coeff_const`,
`coeff_sub_const`, `unif_singleton_zero`, `ae_radius_ne_zero`.
-/

set_option autoImplicit false
open MeasureTheory LogGas.Torus

namespace LogGas.Fourier

private theorem fourierlin_integral_fourier (n : ℤ) :
    ∫ t, fourier n t ∂(AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) =
      if n = 0 then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
    exact integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index h one_pos)

theorem integral_negChar {d : ℕ} (k : Fin d → ℤ) :
    ∫ x, negChar k x ∂unif d = if k = 0 then 1 else 0 := by
  unfold negChar unif
  rw [integral_fintype_prod_eq_prod (fun i (t : AddCircle (1 : ℝ)) => fourier (-(k i)) t)]
  simp_rw [fourierlin_integral_fourier]
  by_cases hk : k = 0
  · subst hk; simp
  · obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
      by_contra h; push Not at h; exact hk (funext h)
    rw [ite_eq_right_iff.2 (fun h => absurd h hk)]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

private theorem fourierlin_norm_negChar {d : ℕ} (k : Fin d → ℤ) (x : T d) :
    ‖negChar k x‖ = 1 := by
  unfold negChar
  simp [norm_prod]

private theorem fourierlin_cont {d : ℕ} (k : Fin d → ℤ) : Continuous (negChar k) := by
  unfold negChar
  fun_prop

private theorem fourierlin_integrable {d : ℕ} (f : T d → ℝ) (hf : Integrable f (unif d))
    (k : Fin d → ℤ) : Integrable (fun x => negChar k x * (f x : ℂ)) (unif d) := by
  have h1 : Integrable (fun x => (f x : ℂ)) (unif d) := hf.ofReal
  refine h1.bdd_mul (c := 1) (fourierlin_cont k).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => (fourierlin_norm_negChar k x).le

theorem coeff_add {d : ℕ} (f h : T d → ℝ) (hf : Integrable f (unif d))
    (hh : Integrable h (unif d)) (k : Fin d → ℤ) :
    coeff (fun x => f x + h x) k = coeff f k + coeff h k := by
  unfold coeff
  rw [← integral_add (fourierlin_integrable f hf k) (fourierlin_integrable h hh k)]
  congr 1; ext x; push_cast; ring

theorem coeff_const {d : ℕ} (c : ℝ) (k : Fin d → ℤ) :
    coeff (fun _ => c) k = if k = 0 then (c : ℂ) else 0 := by
  unfold coeff
  simp_rw [integral_mul_const, integral_negChar]
  split_ifs <;> simp

theorem coeff_sub_const {d : ℕ} (f : T d → ℝ) (hf : Integrable f (unif d)) (c : ℝ)
    (k : Fin d → ℤ) :
    coeff (fun x => f x - c) k = coeff f k - if k = 0 then (c : ℂ) else 0 := by
  have h := coeff_add f (fun _ => -c) hf (integrable_const _) k
  have h2 := coeff_const (d := d) (-c) k
  simp only [← sub_eq_add_neg] at h
  rw [h, h2]
  split_ifs <;> simp [sub_eq_add_neg]

theorem unif_singleton_zero {d : ℕ} (hd : 1 ≤ d) : unif d {0} = 0 := by
  have hd0 : d ≠ 0 := by omega
  have hc : Continuous (fun ρ : ℝ => (2 : ℝ) ^ d * ρ ^ d) := by fun_prop
  have hlim : Filter.Tendsto (fun ρ : ℝ => ENNReal.ofReal ((2 : ℝ) ^ d * ρ ^ d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 : Filter.Tendsto (fun ρ : ℝ => ENNReal.ofReal ((2 : ℝ) ^ d * ρ ^ d)) (nhds 0)
        (nhds (ENNReal.ofReal ((2 : ℝ) ^ d * 0 ^ d))) :=
      (ENNReal.continuous_ofReal.comp hc).tendsto 0
    simpa [zero_pow hd0] using h0.mono_left nhdsWithin_le_nhds
  refine le_antisymm (ge_of_tendsto hlim ?_) zero_le
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  have hsub : ({0} : Set (T d)) ⊆ Metric.ball 0 ρ := by
    intro x hx; simp only [Set.mem_singleton_iff] at hx; subst hx; simpa using hρ
  exact (measure_mono hsub).trans (ball_vol d ρ hρ)

theorem ae_radius_ne_zero {d : ℕ} (hd : 1 ≤ d) : ∀ᵐ x ∂unif d, radius x ≠ 0 := by
  have h := unif_singleton_zero hd
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) h
  simp only [ne_eq, not_not] at hx
  have : dist x 0 ≤ 0 := hx ▸ dist_zero_le_radius x
  exact dist_le_zero.1 this

end LogGas.Fourier
