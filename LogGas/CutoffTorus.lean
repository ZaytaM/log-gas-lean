import LogGas.CutoffSr
import LogGas.Periodize

/-!
# Section 2 — the periodic singular cutoff `s_r` on `𝕋^d`

Source: `notes/sec2-cutoff.tex` (2.1); audit E2, A4.

`sT d r x = sR d r (toV x)`.  Since `s_r` is supported in `‖v‖ < r/2 ≤ 1/2`, the periodization
is a single term.  We record measurability, positivity, support, the logarithmic bound,
integrability, the integral, and the Fourier coefficients
`coeff (sT d r) k = φ(0)⁻¹ ∫_0^r t^{d-1} φ̂(t k) dt`.
-/

open MeasureTheory LogGas.Torus

namespace LogGas.Cutoff

/-- The frequency vector of `k : Fin d → ℤ` in `ℝ^d`. -/
noncomputable def kvec {d : ℕ} (k : Fin d → ℤ) : V d :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => (k i : ℝ))

/-- The periodic singular cutoff. -/
noncomputable def sT (d : ℕ) (r : ℝ) (x : T d) : ℝ := sR d r (toV x)

theorem norm_kvec {d : ℕ} (k : Fin d → ℤ) : ‖kvec k‖ = LogGas.Fourier.latticeNorm k := by
  unfold kvec LogGas.Fourier.latticeNorm
  rw [EuclideanSpace.norm_eq]
  simp

theorem kvec_neg {d : ℕ} (k : Fin d → ℤ) : kvec (-k) = -kvec k := by
  unfold kvec
  ext i
  simp

theorem measurable_sT {d : ℕ} {r : ℝ} : Measurable (sT d r) :=
  (measurable_sR r).comp measurable_toV

theorem sT_nonneg {d : ℕ} {r : ℝ} (x : T d) : 0 ≤ sT d r x := sR_nonneg _ _

theorem sT_support {d : ℕ} {r : ℝ} (x : T d) (hx : r / 2 ≤ radius x) : sT d r x = 0 := by
  unfold sT
  exact sR_support _ (by rwa [← radius_eq_norm_toV])

theorem sT_le_log {d : ℕ} {r : ℝ} (hr : 0 < r) (x : T d) (hx : radius x ≠ 0) :
    sT d r x ≤ max 0 (Real.log (r / radius x)) := by
  have h : toV x ≠ 0 := by
    intro h0
    apply hx
    rw [radius_eq_norm_toV, h0, norm_zero]
  have := sR_le_log hr (toV x) h
  rwa [← radius_eq_norm_toV] at this

private theorem ct_supp {d : ℕ} {r : ℝ} (hr1 : r ≤ 1) :
    ∀ v : V d, (1/2 : ℝ) ≤ ‖v‖ → (sR d r v : ℂ) = 0 := by
  intro v hv
  rw [sR_support v (by linarith)]
  simp

theorem integrable_sT {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr1 : r ≤ 1) :
    Integrable (sT d r) (unif d) := by
  have h := integrable_comp_toV (fun v => (sR d r v : ℂ)) (ct_supp hr1)
    (integrable_sR hd r).ofReal
  unfold sT
  simpa using h.re

theorem integral_sT {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr1 : r ≤ 1) :
    ∫ x, sT d r x ∂unif d = ∫ v, sR d r v := by
  have h := integral_comp_toV (fun v => (sR d r v : ℂ)) (ct_supp hr1)
    (integrable_sR hd r).ofReal
  simp only [integral_complex_ofReal] at h
  exact_mod_cast h

theorem coeff_sT {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (k : Fin d → ℤ) :
    LogGas.Fourier.coeff (sT d r) k =
      (((phi d 0)⁻¹ * ∫ t in Set.Ioc 0 r, t ^ (d - 1) * phiHat d (t • kvec k) : ℝ) : ℂ) := by
  have h := coeff_comp_toV (sR d r) (fun v hv => sR_support v (by linarith))
    (integrable_sR hd r) k
  unfold sT
  rw [h]
  exact fourier_sR hd hr (kvec k)

end LogGas.Cutoff
