import LogGas.CutoffCoef
import LogGas.FourierSeries
import LogGas.FourierForm
import LogGas.FourierUnique

/-!
# Section 2 — `H2` for the normalized log kernel

Source: `notes/sec2-cutoff.tex` (2.1)-(2.2) `eq:compact-positive-log-split`,
`eq:compact-split-fourier-order`; Challenge `cutoff`; audit E2, C2, C4, C8, C9, G6.

`cutoff_of_isLogKernel`: every representative `g` of the Fourier-normalized log kernel
(`IsLogKernel d g`, `2 ≤ d`) satisfies `LogGas.Spec.cutoff g`.  With `r = 1/(2J)`, `s = sT d r`,
`b` the continuous even function with Fourier coefficients `bcoef d r`, and
`Cc = ∫ φ / (d φ(0))`, the identity `g = b + (s - ∫ s)` holds a.e. by Fourier uniqueness.
-/

set_option autoImplicit false
open MeasureTheory LogGas.Torus LogGas.Fourier

namespace LogGas.Cutoff

private theorem cm_negChar_eq {d : ℕ} (k : Fin d → ℤ) (x : T d) :
    negChar k x = UnitAddTorus.mFourier (-k) x := rfl

private theorem cm_integral_negChar {d : ℕ} (k : Fin d → ℤ) (hk : k ≠ 0) :
    ∫ x, negChar k x ∂unif d = 0 := by
  have h := orthonormal_iff_ite.mp UnitAddTorus.orthonormal_mFourier k 0
  simp only [ContinuousMap.inner_toLp, ← UnitAddTorus.mFourier_neg] at h
  have h2 : (∫ x, negChar k x ∂unif d) = if k = 0 then 1 else 0 := by
    refine Eq.trans ?_ h
    congr 1
    ext x
    rw [cm_negChar_eq, UnitAddTorus.mFourier_neg, mul_comm]
    simp [UnitAddTorus.mFourier_zero]
  rw [h2, if_neg hk]

private theorem cm_coeff_const {d : ℕ} (c : ℝ) (k : Fin d → ℤ) :
    coeff (fun _ => c) k = if k = 0 then (c : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst hk
    rw [coeff_zero_eq]
    simp
  · rw [if_neg hk]
    unfold coeff
    rw [integral_mul_const, cm_integral_negChar k hk, zero_mul]

private theorem cm_int_mul {d : ℕ} (f : T d → ℝ) (hf : Integrable f (unif d))
    (k : Fin d → ℤ) : Integrable (fun x => negChar k x * (f x : ℂ)) (unif d) := by
  have hc : Continuous (negChar k) := by
    have : negChar k = UnitAddTorus.mFourier (-k) := funext fun x => rfl
    rw [this]; exact (UnitAddTorus.mFourier (-k)).continuous
  have hn : ∀ x, ‖negChar k x‖ ≤ 1 := fun x => by
    have h1 := UnitAddTorus.mFourier_neg (d := Fin d) (n := -k) (x := x)
    have h2 : UnitAddTorus.mFourier (-k) x * UnitAddTorus.mFourier (- -k) x = 1 := by
      rw [← UnitAddTorus.mFourier_add]; simp [UnitAddTorus.mFourier_zero]
    rw [cm_negChar_eq]
    have h3 : ‖UnitAddTorus.mFourier (-k) x‖ ^ 2 = 1 := by
      have h4 := Complex.mul_conj' (UnitAddTorus.mFourier (-k) x)
      rw [h1] at h2
      rw [h2] at h4
      exact_mod_cast h4.symm
    nlinarith [norm_nonneg (UnitAddTorus.mFourier (-k) x)]
  have hf' : Integrable (fun x => (f x : ℂ)) (unif d) := hf.ofReal
  have := hf'.mul_bdd (c := 1) hc.aestronglyMeasurable (Filter.Eventually.of_forall hn)
  simpa [mul_comm] using this

private theorem cm_coeff_add_sub {d : ℕ} (b s : T d → ℝ) (c : ℝ) (hb : Integrable b (unif d))
    (hs : Integrable s (unif d)) (k : Fin d → ℤ) :
    coeff (fun x => b x + (s x - c)) k =
      coeff b k + (coeff s k - (if k = 0 then (c : ℂ) else 0)) := by
  rw [← cm_coeff_const c k]
  unfold coeff
  have hc : Integrable (fun _ : T d => c) (unif d) := integrable_const _
  have e : ∀ x, negChar k x * (((b x + (s x - c) : ℝ)) : ℂ) =
      negChar k x * (b x : ℂ) + (negChar k x * (s x : ℂ) - negChar k x * (c : ℂ)) := by
    intro x; push_cast; ring
  simp_rw [e]
  rw [integral_add (cm_int_mul b hb k) (by exact (cm_int_mul s hs k).sub (cm_int_mul _ hc k)),
    integral_sub (cm_int_mul s hs k) (cm_int_mul _ hc k)]

private theorem cm_unif_zero (d : ℕ) (hd : 1 ≤ d) : unif d {(0 : T d)} = 0 := by
  have h : ∀ ρ : ℝ, 0 < ρ → unif d {(0 : T d)} ≤ ENNReal.ofReal ((2 : ℝ) ^ d * ρ ^ d) := fun ρ hρ =>
    (measure_mono (by simpa using Metric.mem_ball_self (x := (0 : T d)) hρ)).trans
      (ball_vol d ρ hρ)
  have ht : Filter.Tendsto (fun ρ : ℝ => ENNReal.ofReal ((2 : ℝ) ^ d * ρ ^ d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 : Filter.Tendsto (fun ρ : ℝ => (2 : ℝ) ^ d * ρ ^ d) (nhds 0) (nhds 0) := by
      have : Continuous (fun ρ : ℝ => (2 : ℝ) ^ d * ρ ^ d) := by fun_prop
      simpa [zero_pow (by omega : d ≠ 0)] using this.tendsto 0
    have := ENNReal.tendsto_ofReal (h0.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
    rwa [ENNReal.ofReal_zero] at this
  exact le_antisymm (ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ρ hρ => h ρ hρ))
    bot_le

private theorem cm_radius_ne {d : ℕ} (hd : 1 ≤ d) : ∀ᵐ x ∂unif d, radius x ≠ 0 := by
  have h0 : unif d {x : T d | ¬ radius x ≠ 0} = 0 := by
    have : {x : T d | ¬ radius x ≠ 0} ⊆ {(0 : T d)} := by
      intro x hx
      simp only [Set.mem_setOf_eq, not_not] at hx
      have := dist_zero_le_radius x
      rw [hx] at this
      exact Set.mem_singleton_iff.2 (dist_le_zero.mp this)
    exact measure_mono_null this (cm_unif_zero d hd)
  exact h0

theorem cutoff_of_isLogKernel {d : ℕ} (hd : 2 ≤ d) {g : T d → ℝ} (hg : IsLogKernel d g) :
    LogGas.Spec.cutoff g := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hgm, hgi, hgc⟩ := hg
  have hphi : 0 < (d : ℝ) * phi d 0 := mul_pos (by positivity) phi_zero_pos
  refine ⟨(∫ v, phi d v) / (d * phi d 0), div_nonneg (integral_nonneg phi_nonneg) hphi.le, ?_⟩
  intro J hJ
  have hJ' : (3 : ℝ) ≤ J := by exact_mod_cast hJ
  set r : ℝ := 1 / (2 * (J : ℝ)) with hrdef
  have hr : 0 < r := by rw [hrdef]; positivity
  have hr1 : r ≤ 1 := by
    rw [hrdef, div_le_one (by positivity)]; linarith
  obtain ⟨b, hbc, hbe, hbco⟩ := exists_continuous_of_summable (bcoef d r)
    (summable_bcoef hd1 hr) bcoef_even
  have hbi : Integrable b (unif d) := hbc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace b)
  have hsi : Integrable (sT d r) (unif d) := integrable_sT hd1 hr1
  have hsint : ∫ z, sT d r z ∂unif d = (∫ v, phi d v) / (d * phi d 0) * r ^ d := by
    rw [integral_sT hd1 hr1, integral_sR hd1 hr]; ring
  have hs0 : 0 ≤ ∫ z, sT d r z ∂unif d := integral_nonneg fun x => sT_nonneg x
  -- coefficients of s - ∫ s
  have hcs : ∀ k, coeff (fun x => sT d r x - ∫ z, sT d r z ∂unif d) k =
      ((if k = 0 then 0 else (phi d 0)⁻¹ *
        ∫ t in Set.Ioc 0 r, t ^ (d - 1) * phiHat d (t • kvec k) : ℝ) : ℂ) := by
    intro k
    have := cm_coeff_add_sub (fun _ => 0) (sT d r) (∫ z, sT d r z ∂unif d) (integrable_const _) hsi k
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl]
      have h1 : coeff (fun x => sT d r x - ∫ z, sT d r z ∂unif d) 0 =
          ((∫ x, (sT d r x - ∫ z, sT d r z ∂unif d) ∂unif d : ℝ) : ℂ) := coeff_zero_eq _
      rw [h1, integral_sub hsi (integrable_const _)]
      simp
    · rw [if_neg hk]
      have h2 := cm_coeff_const (d := d) (∫ z, sT d r z ∂unif d) k
      have h3 : coeff (fun x => sT d r x - ∫ z, sT d r z ∂unif d) k =
          coeff (sT d r) k - coeff (fun _ => ∫ z, sT d r z ∂unif d) k := by
        unfold coeff
        rw [← integral_sub (cm_int_mul _ hsi k) (cm_int_mul _ (integrable_const _) k)]
        congr 1; ext x; push_cast; ring
      rw [h3, h2, if_neg hk, sub_zero]
      exact coeff_sT hd1 hr hr1 k
  have hcs_nonneg : ∀ k, (coeff (fun x => sT d r x - ∫ z, sT d r z ∂unif d) k).im = 0 ∧
      0 ≤ (coeff (fun x => sT d r x - ∫ z, sT d r z ∂unif d) k).re := by
    intro k
    rw [hcs k, Complex.ofReal_im, Complex.ofReal_re]
    refine ⟨rfl, ?_⟩
    split_ifs
    · exact le_rfl
    · refine mul_nonneg (inv_nonneg.2 phi_zero_pos.le) (setIntegral_nonneg measurableSet_Ioc ?_)
      intro t ht
      exact mul_nonneg (pow_nonneg ht.1.le _) (phiHat_nonneg _)
  have hbk : ∀ k, (coeff b k).im = 0 ∧ (coeff b k).re = bcoef d r k := by
    intro k; rw [hbco k]; simp
  refine ⟨sT d r, b, measurable_sT, hsi, hbc, hbe, ?_, ?_, ?_, ?_, ?_, hs0, ?_, ?_, ?_, ?_⟩
  · have := hbco 0
    rw [coeff_zero_eq, bcoef_zero] at this
    exact_mod_cast this
  · have hae := ae_eq_of_coeff_eq g (fun x => b x + (sT d r x - ∫ z, sT d r z ∂unif d)) hgi
      (hbi.add (hsi.sub (integrable_const _))) (fun k => by
        rw [cm_coeff_add_sub b _ _ hbi hsi k, hgc k]
        by_cases hk : k = 0
        · subst hk
          rw [if_pos rfl, hbco 0, bcoef_zero, coeff_zero_eq, kernelCoeff]
          simp
        · rw [if_neg hk, sub_zero, hbco k, coeff_sT hd1 hr hr1 k]
          have := bcoef_add hd1 hr k hk
          rw [← this]; push_cast; rfl)
    exact hae
  · exact Filter.Eventually.of_forall fun x => sT_nonneg x
  · exact Filter.Eventually.of_forall fun x hx => sT_support x (by linarith)
  · filter_upwards [cm_radius_ne hd1] with x hx
    exact sT_le_log hr x hx
  · rw [hsint]
  · intro f hf ⟨C, hC⟩
    exact quadratic_nonneg_of_coeff b hbi (fun k => ⟨(hbk k).1, by rw [(hbk k).2]; exact bcoef_nonneg hr k⟩)
      f hf C hC
  · intro f hf ⟨C, hC⟩
    exact quadratic_nonneg_of_coeff _ (hsi.sub (integrable_const _)) hcs_nonneg f hf C hC
  · intro f hf ⟨C, hC⟩
    refine quadratic_mono_of_coeff b g hbi hgi (fun k => ⟨(hbk k).1, ?_, ?_⟩) f hf C hC
    · rw [hgc k]; simp
    · rw [(hbk k).2, hgc k, Complex.ofReal_re]
      by_cases hk : k = 0
      · subst hk; simp [bcoef_zero, kernelCoeff]
      · have := bcoef_add hd1 hr k hk
        have h0 : 0 ≤ (phi d 0)⁻¹ * ∫ t in Set.Ioc 0 r, t ^ (d - 1) * phiHat d (t • kvec k) :=
          mul_nonneg (inv_nonneg.2 phi_zero_pos.le) (setIntegral_nonneg measurableSet_Ioc fun t ht =>
            mul_nonneg (pow_nonneg ht.1.le _) (phiHat_nonneg _))
        linarith

end LogGas.Cutoff
