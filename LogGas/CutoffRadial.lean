import LogGas.CutoffFourier
import LogGas.TorusBase

/-!
# Section 2 — radial integral of `φ̂` and the kernel normalization

Source: `notes/sec2-cutoff.tex` (2.2), `notes/sec1-setting.tex` (1.1); audit E1, E2.

`radial_integral`: for `ξ ≠ 0`, `∫_0^∞ t^{d-1} φ̂(tξ) dt = φ(0) · Γ(d/2)/(2π^{d/2}) · ‖ξ‖^{-d}`
(and the integrand is integrable on `(0,∞)`), via polar coordinates and `∫ φ̂ = φ(0)`.
`kernelCoeff_eq`: `kernelCoeff d k = Γ(d/2)/(2π^{d/2}) · |k|^{-d}` for `k ≠ 0`
(that is, `c_d/(2π|k|)^d` with `c_d = 2^{d-1} π^{d/2} Γ(d/2)`).
-/

open MeasureTheory

namespace LogGas.Cutoff

/-- The radial profile of `φ̂`. -/
private noncomputable def crPsi (d : ℕ) (u : ℝ) : ℝ :=
  if h : 1 ≤ d then phiHat d (u • EuclideanSpace.single (⟨0, h⟩ : Fin d) (1 : ℝ)) else 0

private lemma cr_phiHat_eq {d : ℕ} (hd : 1 ≤ d) (x : V d) : phiHat d x = crPsi d ‖x‖ := by
  unfold crPsi
  rw [dif_pos hd]
  apply phiHat_radial
  rw [norm_smul]
  simp [EuclideanSpace.norm_eq, abs_of_nonneg (Real.sqrt_nonneg _)]

private lemma cr_polar {d : ℕ} (hd : 1 ≤ d) :
    IntegrableOn (fun u : ℝ => u ^ (d - 1) * crPsi d u) (Set.Ioi 0) ∧
    ∫ u in Set.Ioi (0 : ℝ), u ^ (d - 1) * crPsi d u
      = phi d 0 * (Real.Gamma ((d : ℝ) / 2) / (2 * Real.pi ^ ((d : ℝ) / 2))) := by
  haveI : Nontrivial (V d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  have hfr : Module.finrank ℝ (V d) = d := by simp
  have hint : Integrable (fun x : V d => crPsi d ‖x‖) volume := by
    have : (fun x : V d => crPsi d ‖x‖) = phiHat d := funext fun x => (cr_phiHat_eq hd x).symm
    rw [this]; exact phiHat_integrable
  have h1 := (integrable_fun_norm_addHaar (volume : Measure (V d)) (f := crPsi d)).1 hint
  have h2 := integral_fun_norm_addHaar (volume : Measure (V d)) (crPsi d)
  have hL : ∫ x : V d, crPsi d ‖x‖ = phi d 0 := by
    have : (fun x : V d => crPsi d ‖x‖) = phiHat d := funext fun x => (cr_phiHat_eq hd x).symm
    rw [this]; exact integral_phiHat
  rw [hfr] at h1 h2
  refine ⟨by simpa [smul_eq_mul] using h1, ?_⟩
  have hvol : (volume : Measure (V d)).real (Metric.ball 0 1)
      = Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1) := by
    rw [Measure.real, InnerProductSpace.volume_ball, hfr]
    simp only [ENNReal.ofReal_one, one_pow, one_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 1; ring
  rw [hL, hvol] at h2
  have hG : Real.Gamma ((d : ℝ) / 2 + 1) = ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2) :=
    Real.Gamma_add_one (by have : (0:ℝ) < d := by exact_mod_cast hd
                           positivity)
  have hGpos : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by
    have : (0:ℝ) < d := by exact_mod_cast hd
    positivity)
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hpi : 0 < Real.pi ^ ((d : ℝ) / 2) := by positivity
  simp only [smul_eq_mul, nsmul_eq_mul] at h2
  rw [hG] at h2
  field_simp at h2 ⊢
  linarith

theorem radial_integral {d : ℕ} (hd : 1 ≤ d) (ξ : V d) (hξ : ξ ≠ 0) :
    IntegrableOn (fun t : ℝ => t ^ (d - 1) * phiHat d (t • ξ)) (Set.Ioi 0) ∧
    ∫ t in Set.Ioi 0, t ^ (d - 1) * phiHat d (t • ξ)
      = phi d 0 * (Real.Gamma ((d : ℝ) / 2) / (2 * Real.pi ^ ((d : ℝ) / 2))) * ‖ξ‖ ^ (-(d : ℝ)) := by
  obtain ⟨hI, hv⟩ := cr_polar hd
  set a : ℝ := ‖ξ‖ with ha
  have hapos : 0 < a := norm_pos_iff.2 hξ
  have heq : ∀ t : ℝ, 0 < t → t ^ (d - 1) * phiHat d (t • ξ)
      = (a ^ (d - 1))⁻¹ * ((a * t) ^ (d - 1) * crPsi d (a * t)) := by
    intro t ht
    rw [cr_phiHat_eq hd, norm_smul, Real.norm_of_nonneg ht.le, mul_pow]
    field_simp
    rw [mul_comm t a]
  have hI' : IntegrableOn (fun t : ℝ => (a * t) ^ (d - 1) * crPsi d (a * t)) (Set.Ioi 0) := by
    rw [integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ => u ^ (d - 1) * crPsi d u) 0 hapos]
    simpa using hI
  refine ⟨?_, ?_⟩
  · have hc : IntegrableOn (fun t : ℝ => (a ^ (d - 1))⁻¹ * ((a * t) ^ (d - 1) * crPsi d (a * t)))
        (Set.Ioi 0) := Integrable.const_mul hI' _
    exact hc.congr_fun (fun t ht => (heq t ht).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => heq t ht), integral_const_mul,
      integral_comp_mul_left_Ioi (fun u : ℝ => u ^ (d - 1) * crPsi d u) 0 hapos]
    simp only [mul_zero, smul_eq_mul]
    rw [hv, Real.rpow_neg hapos.le, Real.rpow_natCast]
    have : a ^ d = a ^ (d - 1) * a := by
      rw [← pow_succ]; congr 1; omega
    rw [this]
    field_simp

theorem kernelCoeff_eq {d : ℕ} (hd : 1 ≤ d) (k : Fin d → ℤ) (hk : k ≠ 0) :
    LogGas.Fourier.kernelCoeff d k = Real.Gamma ((d : ℝ) / 2) / (2 * Real.pi ^ ((d : ℝ) / 2))
      * LogGas.Fourier.latticeNorm k ^ (-(d : ℝ)) := by
  have hn : 0 < LogGas.Fourier.latticeNorm k := by
    unfold LogGas.Fourier.latticeNorm
    apply Real.sqrt_pos.2
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hk
    have : (0:ℝ) < ((k i : ℤ) : ℝ) ^ 2 := by
      have : (k i : ℝ) ≠ 0 := by exact_mod_cast hi
      positivity
    exact lt_of_lt_of_le this
      (Finset.single_le_sum (f := fun j => ((k j : ℤ) : ℝ) ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i))
  unfold LogGas.Fourier.kernelCoeff LogGas.Fourier.cd
  rw [if_neg hk, Real.rpow_neg hn.le, Real.rpow_natCast, mul_pow, mul_pow]
  have h2 : (2:ℝ) ^ d = 2 ^ (d - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  have hpd : (Real.pi ^ ((d : ℝ) / 2)) ^ 2 = Real.pi ^ d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]; norm_num
  have hpi : 0 < Real.pi ^ ((d : ℝ) / 2) := by positivity
  rw [h2, ← hpd]
  field_simp

end LogGas.Cutoff
