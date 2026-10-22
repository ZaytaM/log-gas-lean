import LogGas.TorusBase

/-!
# Existence of the Fourier-normalized log kernel

Proves `LogGas.Fourier.summable_latticeNorm_rpow` (summability of `|k|^{-s}` over `ℤ^d \ {0}`
for `s > d`) and `LogGas.Fourier.kernel_exists`, i.e. `∃ g, IsLogKernel d g`: the kernel with
Fourier coefficients `kernelCoeff d k` of eq. (1.1) (`eq:kernel-normalization`,
`notes/sec1-setting.tex`) exists (audit E1, G6).
-/

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace LogGas.Fourier
open LogGas.Torus

theorem summable_latticeNorm_rpow (d : ℕ) (s : ℝ) (hs : (d : ℝ) < s) :
    Summable (fun k : Fin d → ℤ => if k = 0 then (0 : ℝ) else latticeNorm k ^ (-s)) := by
  let bE : Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let L := Submodule.span ℤ (Set.range bE)
  have hli : LinearIndependent ℤ bE := bE.linearIndependent.restrict_scalars' ℤ
  let b : Module.Basis (Fin d) ℤ L := Module.Basis.span hli
  have hrank : Module.finrank ℤ L = d := by
    rw [ZLattice.rank ℝ L]; simp
  have hsum := ZLattice.summable_norm_rpow L (-s) (by rw [hrank]; linarith)
  have hcoord : ∀ (z : L) (i : Fin d),
      ((b.equivFun z i : ℤ) : ℝ) = (z : EuclideanSpace ℝ (Fin d)) i := by
    intro z i
    have h : (z : EuclideanSpace ℝ (Fin d)) = ∑ j, (b.equivFun z j) • bE j := by
      conv_lhs => rw [← b.sum_equivFun z]
      simp only [Submodule.coe_sum, Submodule.coe_smul, Module.Basis.span_apply]
      exact Finset.sum_congr rfl fun x _ => by rw [Module.Basis.span_apply hli x]
    have h2 := congrArg (fun w : EuclideanSpace ℝ (Fin d) => w i) h
    simpa [bE, Pi.single_apply] using h2.symm
  have hnorm : ∀ z : L, ‖(z : EuclideanSpace ℝ (Fin d))‖ = latticeNorm (b.equivFun z) := by
    intro z
    rw [EuclideanSpace.norm_eq, latticeNorm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcoord, Real.norm_eq_abs, sq_abs]
  have key : (fun k : Fin d → ℤ => if k = 0 then (0 : ℝ) else latticeNorm k ^ (-s)) ∘
      b.equivFun = fun z : L => ‖z‖ ^ (-s) := by
    funext z
    show (if b.equivFun z = 0 then (0 : ℝ) else latticeNorm (b.equivFun z) ^ (-s)) =
      ‖(z : EuclideanSpace ℝ (Fin d))‖ ^ (-s)
    rw [hnorm]
    by_cases hz : b.equivFun z = 0
    · have : z = 0 := by simpa using hz
      subst this
      have hs0 : -s ≠ 0 := by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        intro h; linarith
      simp [latticeNorm, Real.zero_rpow hs0]
    · simp only [hz, ↓reduceIte]
  rw [← b.equivFun.toEquiv.summable_iff]
  have := key ▸ hsum
  exact this

/-- Same local instance as in `Mathlib.Analysis.Fourier.AddCircleMulti`. -/
noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

private theorem kernelexists_unif_eq_volume (d : ℕ) :
    unif d = (volume : Measure (UnitAddTorus (Fin d))) := by
  rfl

private theorem kernelexists_kernelCoeff_neg (d : ℕ) (k : Fin d → ℤ) :
    kernelCoeff d (-k) = kernelCoeff d k := by
  have : latticeNorm (-k) = latticeNorm k := by simp [latticeNorm]
  simp [kernelCoeff, this]

private theorem kernelexists_sq_summable (d : ℕ) (hd : 2 ≤ d) :
    Summable (fun k : Fin d → ℤ => ‖(kernelCoeff d k : ℂ)‖ ^ (2 : ℝ)) := by
  have hs := summable_latticeNorm_rpow d (2 * d) (by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  refine (hs.mul_left (cd d ^ 2 / (2 * Real.pi) ^ (2 * d))).congr fun k => ?_
  by_cases hk : k = 0
  · simp [kernelCoeff, hk]
  · have hl : 0 < latticeNorm k := by
      unfold latticeNorm
      apply Real.sqrt_pos.2
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hk
      have hi : ((k i : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hi
      have pow_pos_of_ne_zero' : (0:ℝ) < ((k i : ℤ) : ℝ) ^ 2 := by positivity
      exact lt_of_lt_of_le pow_pos_of_ne_zero'
        (Finset.single_le_sum (f := fun i => ((k i : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ i))
    simp only [kernelCoeff, hk, ite_false, Complex.norm_real, Real.norm_eq_abs]
    rw [Real.rpow_two, sq_abs, Real.rpow_neg hl.le,
      show (2 * (d : ℝ)) = ((2 * d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have hp : 0 < 2 * Real.pi := by positivity
    rw [div_pow]
    field_simp
    ring

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

theorem kernel_exists (d : ℕ) (hd : 2 ≤ d) : ∃ g : LogGas.Torus.T d → ℝ, IsLogKernel d g := by
  classical
  have : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by
    rw [← kernelexists_unif_eq_volume]; infer_instance
  let c : (Fin d → ℤ) → ℂ := fun k => (kernelCoeff d k : ℂ)
  have hc : Memℓp c 2 := by
    rw [memℓp_gen_iff (by simp)]
    have := kernelexists_sq_summable d hd
    simpa [c] using this
  let F0 := (UnitAddTorus.mFourierBasis (d := Fin d)).repr.symm ⟨c, hc⟩
  have hF0 : ∀ k, UnitAddTorus.mFourierCoeff F0 k = c k := by
    intro k
    rw [← UnitAddTorus.mFourierBasis_repr]
    simp [F0]
  have hmeas := Lp.aestronglyMeasurable F0
  let F1 : UnitAddTorus (Fin d) → ℂ := hmeas.mk F0
  have hF1 : F0 =ᵐ[_] F1 := hmeas.ae_eq_mk
  have hF1m : StronglyMeasurable F1 := hmeas.stronglyMeasurable_mk
  have hint0 := (Lp.memLp F0).integrable (by norm_num)
  have hint1 := hint0.congr hF1
  refine ⟨fun x => (F1 x).re, ?_, ?_, ?_⟩
  · exact Complex.measurable_re.comp hF1m.measurable
  · rw [kernelexists_unif_eq_volume]
    exact hint1.re
  · intro k
    unfold coeff
    rw [kernelexists_unif_eq_volume]
    have hbd : ∀ n : Fin d → ℤ, ∀ x, ‖UnitAddTorus.mFourier n x‖ ≤ 1 := by
      intro n x
      have := (UnitAddTorus.mFourier (d := Fin d) (n := n)).norm_coe_le_norm x
      rwa [UnitAddTorus.mFourier_norm] at this
    have hmi : ∀ n : Fin d → ℤ,
        Integrable (fun x => UnitAddTorus.mFourier n x * F1 x) :=
      fun n => hint1.bdd_mul (UnitAddTorus.mFourier n).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall (hbd n))
    have hcf : ∀ n : Fin d → ℤ,
        ∫ x, UnitAddTorus.mFourier (-n) x * F1 x = c n := by
      intro n
      rw [← hF0 n, UnitAddTorus.mFourierCoeff]
      refine integral_congr_ae ?_
      filter_upwards [hF1] with x hx
      rw [smul_eq_mul, hx]
    have hconj : ∫ x, UnitAddTorus.mFourier (-k) x * (starRingEnd ℂ) (F1 x) = c k := by
      have h1 : ∀ x, UnitAddTorus.mFourier (-k) x * (starRingEnd ℂ) (F1 x) =
          (starRingEnd ℂ) (UnitAddTorus.mFourier (-(-k)) x * F1 x) := by
        intro x
        rw [UnitAddTorus.mFourier_neg (n := -k), map_mul, Complex.conj_conj]
      simp_rw [h1]
      rw [integral_conj, hcf (-k)]
      simp [c, kernelexists_kernelCoeff_neg]
    have hre : ∀ x, ((F1 x).re : ℂ) = (F1 x + (starRingEnd ℂ) (F1 x)) / 2 :=
      fun x => Complex.re_eq_add_conj _
    have hint1c : Integrable (fun x => (starRingEnd ℂ) (F1 x)) := by
      have := Complex.conjCLE.integrable_comp_iff.2 hint1
      simpa [Function.comp_def] using this
    have hi2 : Integrable (fun x => UnitAddTorus.mFourier (-k) x * (starRingEnd ℂ) (F1 x)) :=
      hint1c.bdd_mul (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall (hbd _))
    have hnc : ∀ x, negChar k x = UnitAddTorus.mFourier (-k) x := fun x => rfl
    simp_rw [hnc, hre, mul_div_assoc', mul_add]
    rw [integral_div, integral_add (hmi (-k)) hi2, hcf k, hconj]
    simp [c]
