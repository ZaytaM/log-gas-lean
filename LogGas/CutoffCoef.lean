import LogGas.CutoffRadial
import LogGas.CutoffTorus
import LogGas.KernelExists

/-!
# Section 2 — Fourier coefficients of the bulk part `b_r`

Source: `notes/sec2-cutoff.tex` (2.1)-(2.2) `eq:compact-split-fourier-order`; audit E2, C8, C9.

`bcoef d r k = φ(0)⁻¹ ∫_r^∞ t^{d-1} φ̂(t k) dt` for `k ≠ 0` (and `0` at `k = 0`).  We prove
`bcoef_zero`, nonnegativity, evenness, absolute summability, and the splitting
`bcoef k + φ(0)⁻¹ ∫_0^r t^{d-1} φ̂(t k) dt = kernelCoeff d k` for `k ≠ 0`.
-/

open MeasureTheory

namespace LogGas.Cutoff

/-- Fourier coefficients of the bulk part `b_r`. -/
noncomputable def bcoef (d : ℕ) (r : ℝ) (k : Fin d → ℤ) : ℝ :=
  if k = 0 then 0 else
    (phi d 0)⁻¹ * ∫ t in Set.Ioi r, t ^ (d - 1) * phiHat d (t • kvec k)

theorem bcoef_zero {d : ℕ} {r : ℝ} : bcoef d r 0 = 0 := by simp [bcoef]

theorem bcoef_nonneg {d : ℕ} {r : ℝ} (hr : 0 < r) (k : Fin d → ℤ) : 0 ≤ bcoef d r k := by
  unfold bcoef
  split_ifs
  · exact le_rfl
  · refine mul_nonneg (inv_nonneg.2 phi_zero_pos.le) (setIntegral_nonneg measurableSet_Ioi ?_)
    intro t ht
    exact mul_nonneg (pow_nonneg (hr.trans ht).le _) (phiHat_nonneg _)

theorem bcoef_even {d : ℕ} {r : ℝ} (k : Fin d → ℤ) : bcoef d r (-k) = bcoef d r k := by
  by_cases hk : k = 0
  · subst hk; simp
  · have hk' : -k ≠ 0 := neg_ne_zero.2 hk
    simp only [bcoef, hk, hk', ite_false]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    congr 1
    apply phiHat_radial
    rw [kvec_neg, smul_neg, norm_neg]

private lemma bc_kvec_ne {d : ℕ} {k : Fin d → ℤ} (hk : k ≠ 0) : kvec k ≠ 0 := by
  intro h
  apply hk
  funext i
  have h2 := congrFun (congrArg (WithLp.equiv 2 (Fin d → ℝ)) h) i
  simpa [kvec] using h2

theorem bcoef_add {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (k : Fin d → ℤ) (hk : k ≠ 0) :
    bcoef d r k + (phi d 0)⁻¹ * ∫ t in Set.Ioc 0 r, t ^ (d - 1) * phiHat d (t • kvec k)
      = LogGas.Fourier.kernelCoeff d k := by
  have hkv : kvec k ≠ 0 := bc_kvec_ne hk
  obtain ⟨hI, hv⟩ := radial_integral hd (kvec k) hkv
  have hsplit : ∫ t in Set.Ioi (0:ℝ), t ^ (d - 1) * phiHat d (t • kvec k) =
      (∫ t in Set.Ioc (0:ℝ) r, t ^ (d - 1) * phiHat d (t • kvec k)) +
      ∫ t in Set.Ioi r, t ^ (d - 1) * phiHat d (t • kvec k) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hr.le]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hI.mono_set Set.Ioc_subset_Ioi_self)
      (hI.mono_set (Set.Ioi_subset_Ioi hr.le))
  have hp : phi d 0 ≠ 0 := phi_zero_pos.ne'
  rw [kernelCoeff_eq hd k hk, bcoef, if_neg hk]
  rw [hsplit, norm_kvec] at hv
  have : (phi d 0)⁻¹ * ((∫ t in Set.Ioc (0:ℝ) r, t ^ (d - 1) * phiHat d (t • kvec k)) +
      ∫ t in Set.Ioi r, t ^ (d - 1) * phiHat d (t • kvec k)) =
      Real.Gamma ((d : ℝ) / 2) / (2 * Real.pi ^ ((d : ℝ) / 2)) *
        LogGas.Fourier.latticeNorm k ^ (-(d : ℝ)) := by
    rw [hv]; field_simp
  rw [← this]; ring

theorem summable_bcoef {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    Summable (fun k : Fin d → ℤ => |bcoef d r k|) := by
  obtain ⟨C, hC⟩ := phiHat_decay (d := d)
  have hC0 : 0 ≤ C := by
    have := hC 0
    have h2 : 0 ≤ C * (1 + ‖(0 : V d)‖) ^ (-((d : ℝ) + 2)) := (abs_nonneg _).trans this
    simpa using h2
  have hs := LogGas.Fourier.summable_latticeNorm_rpow d ((d : ℝ) + 2) (by linarith)
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    (hs.mul_left ((phi d 0)⁻¹ * C * (r ^ (-2 : ℝ) / 2)))
  by_cases hk : k = 0
  · subst hk; simp [bcoef_zero]
  · set a := LogGas.Fourier.latticeNorm k with ha
    have hapos : 0 < a := by
      rw [ha, ← norm_kvec]
      exact norm_pos_iff.2 (bc_kvec_ne hk)
    set g : ℝ → ℝ := fun t => C * a ^ (-((d : ℝ) + 2)) * t ^ (-3 : ℝ) with hg
    have hgi : IntegrableOn g (Set.Ioi r) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hr).const_mul _
    have hgint : ∫ t in Set.Ioi r, g t = C * a ^ (-((d : ℝ) + 2)) * (r ^ (-2 : ℝ) / 2) := by
      rw [hg, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hr]
      norm_num
    have hb : ‖∫ t in Set.Ioi r, t ^ (d - 1) * phiHat d (t • kvec k)‖ ≤
        ∫ t in Set.Ioi r, g t := by
      refine norm_integral_le_of_norm_le hgi ?_
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
      have ht0 : 0 < t := hr.trans ht
      have h1 := hC (t • kvec k)
      have hn : ‖t • kvec k‖ = t * a := by
        rw [norm_smul, norm_kvec, Real.norm_of_nonneg ht0.le]
      rw [hn] at h1
      have hta : 0 < t * a := mul_pos ht0 hapos
      have h2 : (1 + t * a) ^ (-((d : ℝ) + 2)) ≤ (t * a) ^ (-((d : ℝ) + 2)) :=
        Real.rpow_le_rpow_of_nonpos hta (by linarith) (by linarith)
      have h3 : |phiHat d (t • kvec k)| ≤ C * (t * a) ^ (-((d : ℝ) + 2)) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hC0)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht0.le _)]
      calc t ^ (d - 1) * |phiHat d (t • kvec k)|
          ≤ t ^ (d - 1) * (C * (t * a) ^ (-((d : ℝ) + 2))) :=
            mul_le_mul_of_nonneg_left h3 (pow_nonneg ht0.le _)
        _ = g t := by
            rw [hg]
            simp only
            rw [Real.mul_rpow ht0.le hapos.le]
            have : t ^ (d - 1) = t ^ (((d - 1 : ℕ) : ℝ)) := (Real.rpow_natCast t _).symm
            have e : (-3 : ℝ) = ((d - 1 : ℕ) : ℝ) + -((d : ℝ) + 2) := by
              rw [Nat.cast_sub hd]; push_cast; ring
            rw [this, e, Real.rpow_add ht0]
            ring
    have hpi : 0 < (phi d 0)⁻¹ := inv_pos.2 phi_zero_pos
    rw [bcoef, if_neg hk, abs_mul, abs_of_pos hpi]
    calc (phi d 0)⁻¹ * |∫ t in Set.Ioi r, t ^ (d - 1) * phiHat d (t • kvec k)|
        ≤ (phi d 0)⁻¹ * (C * a ^ (-((d : ℝ) + 2)) * (r ^ (-2 : ℝ) / 2)) := by
          apply mul_le_mul_of_nonneg_left _ hpi.le
          rw [← hgint]; exact hb
      _ = _ := by rw [if_neg hk]; ring

end LogGas.Cutoff
