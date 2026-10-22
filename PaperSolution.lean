import LogGas

/-!
# Standalone statement of the paper's Theorem 1.1 (uniform partition bound)

Independent paper target. `PaperTheorem` is a specification; its definition is not a proof.
Promoted from the completed Opus paper audit without changing mathematical definitions.
Only `Mathlib` is imported; there are no axioms, no `sorry`, no admitted definitions, and no
conclusion is encoded as a hypothesis or structure field.

Source: `notes/sec1-setting.tex`, eqs. (1.1) `eq:kernel-normalization`, (1.2)
`eq:homogeneous-partition-function`, (1.3) `eq:strict-subcritical-macroscopic-inequality`,
Theorem `thm:principal`, eq. (1.4) `eq:principal-order-one`.

Modelling choices (all discussed in `PAPER_THEOREM.md` / `DEVIATIONS.md`):

* Torus `ℝ^d/ℤ^d` = `Fin d → AddCircle 1`; `μ_unif` = product of the normalized Haar measures
  `AddCircle.haarAddCircle` (total mass one).
* The kernel `g` is NOT constructed. It is characterized by its Fourier coefficients
  `ĝ(k) = c_d / (2π|k|)^d` (`k ≠ 0`), `ĝ(0) = 0`, `c_d = 2^{d-1} π^{d/2} Γ(d/2)`, with the
  paper's convention `f̂(k) = ∫ f(x) e^{-2πik·x} dμ_unif(x)`. `PaperTheorem` quantifies over every
  integrable real representative with these coefficients. Integrable functions with equal Fourier
  coefficients agree a.e. (true, but not available in this Mathlib for `L¹`), and the partition
  function only sees `g` off a null set, so this is the paper's single kernel. Existence of such a
  `g` is the separate proposition `LogKernelExists` (true; not proved here).
* The asymptotic `g(x) = -log|x| + O_d(1)` of (1.1) is a consequence of the normalization for a
  suitable representative; it is recorded as `LogAsymptotic` but deliberately NOT a premise.
* Log-HLS (1.3) uses the joint Bochner integral on `μ ⊗ μ`. If that integrand were not integrable,
  Lean's value would be `0` and the premise would degenerate to `0 ≤ H(ρ)`, which is true; so
  `LogHLS` is implied by the paper's premise (it can only be weaker), and a proof of
  `PaperTheorem` would certify the paper's statement without any extra domain lemma. The variant
  `LogHLSWithDomain` additionally demands absolute integrability (true for the actual `g`, by the
  entropy/exponential-integrability Young inequality, but unproved here).
* The partition function is an extended nonnegative (`lintegral`) integral, so divergence is `⊤`,
  never silently `0`; the bound is a finite `ℝ≥0` constant.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LogGasPaper

/-- The period-one torus `𝕋^d = ℝ^d / ℤ^d`. -/
abbrev Torus (d : ℕ) := Fin d → AddCircle (1 : ℝ)

/-- `μ_unif`: normalized Lebesgue (= normalized Haar) probability measure on `𝕋^d`. -/
noncomputable def uniform (d : ℕ) : Measure (Torus d) :=
  Measure.pi fun _ => AddCircle.haarAddCircle

instance (d : ℕ) : IsProbabilityMeasure (uniform d) := by
  unfold uniform; infer_instance

/-- Euclidean distance to `0` on `𝕋^d` (coordinatewise circle distances combined in `ℓ²`). -/
noncomputable def radius {d : ℕ} (x : Torus d) : ℝ :=
  Real.sqrt (∑ i, dist (x i) 0 ^ 2)

/-- The character `x ↦ e^{-2πi k·x}` on `𝕋^d`. -/
noncomputable def negCharacter {d : ℕ} (k : Fin d → ℤ) (x : Torus d) : ℂ :=
  ∏ i, fourier (-(k i)) (x i)

/-- Fourier coefficient with the paper's convention `f̂(k) = ∫ f(x) e^{-2πik·x} dμ_unif(x)`. -/
noncomputable def fourierCoeff {d : ℕ} (f : Torus d → ℝ) (k : Fin d → ℤ) : ℂ :=
  ∫ x, negCharacter k x * (f x : ℂ) ∂uniform d

/-- Euclidean norm `|k|` of a lattice vector. -/
noncomputable def latticeNorm {d : ℕ} (k : Fin d → ℤ) : ℝ :=
  Real.sqrt (∑ i, ((k i : ℤ) : ℝ) ^ 2)

/-- `c_d = 2^{d-1} π^{d/2} Γ(d/2)`. -/
noncomputable def cd (d : ℕ) : ℝ :=
  2 ^ (d - 1) * Real.pi ^ ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2)

/-- `ĝ(k) = c_d / (2π|k|)^d` for `k ≠ 0`, and `ĝ(0) = 0` (eq. (1.1)). -/
noncomputable def kernelCoeff (d : ℕ) (k : Fin d → ℤ) : ℝ :=
  if k = 0 then 0 else cd d / (2 * Real.pi * latticeNorm k) ^ d

/-- `g` is (a representative of) the paper's mean-zero periodic logarithmic kernel. -/
def IsLogKernel (d : ℕ) (g : Torus d → ℝ) : Prop :=
  Measurable g ∧ Integrable g (uniform d) ∧
    ∀ k : Fin d → ℤ, fourierCoeff g k = (kernelCoeff d k : ℂ)

/-- Companion existence claim (true, not proved here): the kernel of (1.1) exists. -/
def LogKernelExists : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ g : Torus d → ℝ, IsLogKernel d g

/-- The third item of (1.1), `g(x) = -log|x| + O_d(1)` as `x → 0`, in a.e. form. Not a premise. -/
def LogAsymptotic {d : ℕ} (g : Torus d → ℝ) : Prop :=
  ∃ C R : ℝ, 0 < R ∧ ∀ᵐ x ∂uniform d, radius x < R → |g x + Real.log (radius x)| ≤ C

/-- A probability density (w.r.t. `μ_unif`) of finite entropy. -/
def FiniteEntropyDensity {d : ℕ} (ρ : Torus d → ℝ) : Prop :=
  Measurable ρ ∧ (∀ᵐ x ∂uniform d, 0 ≤ ρ x) ∧ Integrable ρ (uniform d) ∧
    (∫ x, ρ x ∂uniform d) = 1 ∧ Integrable (fun x => ρ x * Real.log (ρ x)) (uniform d)

/-- `H(ρ μ_unif | μ_unif) = ∫ ρ log ρ dμ_unif`. -/
noncomputable def relEntropy {d : ℕ} (ρ : Torus d → ℝ) : ℝ :=
  ∫ x, ρ x * Real.log (ρ x) ∂uniform d

/-- The log energy `∬ g(x-y) (ρ(x)-1)(ρ(y)-1) dμ_unif(x) dμ_unif(y)` (joint integral). -/
noncomputable def logEnergy {d : ℕ} (g : Torus d → ℝ) (ρ : Torus d → ℝ) : ℝ :=
  ∫ z, g (z.1 - z.2) * (ρ z.1 - 1) * (ρ z.2 - 1) ∂(uniform d).prod (uniform d)

/-- The log-HLS premise (1.3) with constant `B`. -/
def LogHLS {d : ℕ} (g : Torus d → ℝ) (B : ℝ) : Prop :=
  ∀ ρ : Torus d → ℝ, FiniteEntropyDensity ρ → (B / 2) * logEnergy g ρ ≤ relEntropy ρ

/-- Log-HLS together with the explicit domain condition (absolute integrability of the energy). -/
def LogHLSWithDomain {d : ℕ} (g : Torus d → ℝ) (B : ℝ) : Prop :=
  ∀ ρ : Torus d → ℝ, FiniteEntropyDensity ρ →
    Integrable (fun z : Torus d × Torus d => g (z.1 - z.2) * (ρ z.1 - 1) * (ρ z.2 - 1))
      ((uniform d).prod (uniform d)) ∧
    (B / 2) * logEnergy g ρ ≤ relEntropy ρ

/-- The domain-explicit premise implies the premise used in `PaperTheorem`. -/
theorem LogHLSWithDomain.toLogHLS {d : ℕ} {g : Torus d → ℝ} {B : ℝ}
    (h : LogHLSWithDomain g B) : LogHLS g B :=
  fun ρ hρ => (h ρ hρ).2

/-- `W_N(g) = (1/N) ∑_{i ≠ j} g(x_i - x_j)` (ordered off-diagonal pairs). -/
noncomputable def offDiagEnergy {d : ℕ} (g : Torus d → ℝ) (N : ℕ) (x : Fin N → Torus d) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i, g (x i - x j)

/-- `Z_{N,β} = 𝔼[e^{(β/2) W_N(g)}]` under i.i.d. uniform particles, as an extended integral. -/
noncomputable def partitionFunction {d : ℕ} (g : Torus d → ℝ) (N : ℕ) (β : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp ((β / 2) * offDiagEnergy g N x))
    ∂Measure.pi (fun _ : Fin N => uniform d)

/-- **Theorem 1.1 (uniform partition bound), as stated in the paper.**
For `d ≥ 2`, `0 < B ≤ 2d`, `0 ≤ β₀ < B` there is a finite `C = C(d, B, β₀)` such that, for the
logarithmic kernel `g` of (1.1) satisfying log-HLS (1.3) with constant `B`,
`sup_{N ≥ 2} sup_{0 ≤ β ≤ β₀} Z_{N,β} ≤ C`. The constant is chosen before `g`, `N`, `β`. -/
def PaperTheorem : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ B : ℝ, 0 < B → B ≤ 2 * d → ∀ β₀ : ℝ, 0 ≤ β₀ → β₀ < B →
    ∃ C : ℝ≥0, ∀ g : Torus d → ℝ, IsLogKernel d g → LogHLS g B →
      ∀ N : ℕ, 2 ≤ N → ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → partitionFunction g N β ≤ (C : ℝ≥0∞)

/-- Weaker per-representative form (constant may depend on the representative `g`). It is
equivalent to `PaperTheorem` once L¹ Fourier uniqueness and a.e.-invariance of
`partitionFunction` are available; only the trivial direction is proved here. -/
def PaperTheoremPerKernel : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ (g : Torus d → ℝ), IsLogKernel d g → ∀ B : ℝ, 0 < B → B ≤ 2 * d →
    LogHLS g B → ∀ β₀ : ℝ, 0 ≤ β₀ → β₀ < B →
      ∃ C : ℝ≥0, ∀ N : ℕ, 2 ≤ N → ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → partitionFunction g N β ≤ (C : ℝ≥0∞)

theorem PaperTheorem.perKernel (h : PaperTheorem) : PaperTheoremPerKernel := by
  intro d hd g hg B hB0 hB hH β₀ hβ0 hβB
  obtain ⟨C, hC⟩ := h d hd B hB0 hB β₀ hβ0 hβB
  exact ⟨C, hC g hg hH⟩

theorem main : PaperTheorem := LogGas.Paper.paper_main

theorem kernel_exists : LogKernelExists := LogGas.Paper.kernel_exists

end LogGasPaper

/- `main` and `kernel_exists` are the theorems from `LogGas.Paper` (definitional copies). -/
