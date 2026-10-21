import LogGas

/-!
Independent solution environment. Target definitions are explicit and imports come from LogGas.
The main/bulk theorem inhabitants remain absent until genuine proofs and bridges exist.
No theorem admissions occur here: the two targets are explicit propositions to
be inhabited by Solution.lean. Missing proofs must fail the final gate.
The torus is period one; its measure is normalized Haar, not unnormalized volume.
The conditional target treats g as supplied data; identifying the manuscript's
Fourier-normalized logarithmic kernel and constructing its inputs is a separate
fidelity/application obligation. No conclusion is an input field.
-/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace LogGasChallenge
abbrev Torus (d : ℕ) := Fin d → AddCircle (1 : ℝ)
noncomputable def uniform (d : ℕ) : Measure (Torus d) :=
  Measure.pi fun _ => AddCircle.haarAddCircle
noncomputable def radius {d : ℕ} (x : Torus d) : ℝ :=
  Real.sqrt (∑ i, dist (x i) 0 ^ 2)
noncomputable def energy {d : ℕ} (g : Torus d → ℝ) (N : ℕ) (x : Fin N → Torus d) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i, g (x i - x j)
noncomputable def weight {d : ℕ} (g : Torus d → ℝ) (N : ℕ) (β : ℝ)
    (x : Fin N → Torus d) : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((β / 2) * energy g N x))
noncomputable def partition {d : ℕ} (g : Torus d → ℝ) (N : ℕ) (β : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, weight g N β x ∂Measure.pi (fun _ => uniform d)
noncomputable def entropy {d : ℕ} (ρ : Torus d → ℝ) : ℝ :=
  ∫ x, ρ x * Real.log (ρ x) ∂uniform d
noncomputable def quadratic {d : ℕ} (K : Torus d → Torus d → ℝ)
    (f : Torus d → ℝ) : ℝ :=
  ∫ x, ∫ y, K x y * f x * f y ∂uniform d ∂uniform d

def density {d : ℕ} (ρ : Torus d → ℝ) : Prop :=
  Measurable ρ ∧ (∀ᵐ x ∂uniform d, 0 ≤ ρ x) ∧ Integrable ρ (uniform d) ∧
    (∫ x, ρ x ∂uniform d) = 1 ∧ Integrable (fun x => ρ x * Real.log (ρ x)) (uniform d)
def logHLS {d : ℕ} (g : Torus d → ℝ) (B : ℝ) : Prop :=
  ∀ ρ, density ρ →
    Integrable (fun z : Torus d × Torus d =>
      g (z.1 - z.2) * (ρ z.1 - 1) * (ρ z.2 - 1)) ((uniform d).prod (uniform d)) ∧
    (B / 2) * quadratic (fun x y => g (x - y)) (fun x => ρ x - 1) ≤ entropy ρ

def positive {d : ℕ} (g : Torus d → ℝ) : Prop :=
  ∀ f : Torus d → ℝ, Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    0 ≤ quadratic (fun x y => g (x - y)) f

def cutoff {d : ℕ} (g : Torus d → ℝ) : Prop :=
  ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ J : ℕ, 3 ≤ J →
    ∃ s b : Torus d → ℝ,
      Measurable s ∧ Integrable s (uniform d) ∧ Continuous b ∧
      (∀ x, b (-x) = b x) ∧ (∫ x, b x ∂uniform d) = 0 ∧
      (∀ᵐ x ∂uniform d, g x = b x + (s x - ∫ z, s z ∂uniform d)) ∧
      (∀ᵐ x ∂uniform d, 0 ≤ s x) ∧
      (∀ᵐ x ∂uniform d, (1 / (2 * (J : ℝ))) < radius x → s x = 0) ∧
      (∀ᵐ x ∂uniform d, s x ≤ max 0 (Real.log ((1 / (2 * (J : ℝ))) / radius x))) ∧
      0 ≤ (∫ z, s z ∂uniform d) ∧
      (∫ z, s z ∂uniform d) ≤ Cc * (1 / (2 * (J : ℝ))) ^ d ∧
      positive b ∧ positive (fun x => s x - ∫ z, s z ∂uniform d) ∧
      (∀ f : Torus d → ℝ, Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
        quadratic (fun x y => b (x - y)) f ≤ quadratic (fun x y => g (x - y)) f)

/-- Conditional main target: C is chosen before N and beta; extended integrals
prevent a divergent positive partition function being silently read as zero. -/
def principalStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ (g : Torus d → ℝ) (B β0 : ℝ),
    Measurable g → Integrable g (uniform d) → (∫ x, g x ∂uniform d) = 0 →
    (∀ᵐ x ∂uniform d, g (-x) = g x) →
    0 < B → B ≤ 2 * d → 0 ≤ β0 → β0 < B → logHLS g B → cutoff g →
    ∃ C : ℝ≥0, ∀ N : ℕ, 2 ≤ N → ∀ β : ℝ, 0 ≤ β → β ≤ β0 →
      partition g N β ≤ (C : ℝ≥0∞)

/-- Independent bulk target, for the actual period-one torus. -/
def bulkStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ (K : Torus d → Torus d → ℝ) (B β0 : ℝ),
    Continuous (Function.uncurry K) → (∀ x y, K x y = K y x) →
    (∀ x, ∫ y, K x y ∂uniform d = 0) →
    (∀ f : Torus d → ℝ, Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      0 ≤ quadratic K f) →
    0 < B → 0 ≤ β0 → β0 < B →
    (∀ ρ, density ρ → (B / 2) * quadratic K (fun x => ρ x - 1) ≤ entropy ρ) →
    ∃ C : ℝ≥0, ∀ N : ℕ, 1 ≤ N → ∀ β : ℝ, 0 ≤ β → β ≤ β0 →
      (∫⁻ x : Fin N → Torus d, ENNReal.ofReal (Real.exp ((β / 2) *
        ((1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i, K (x i) (x j))))
          ∂Measure.pi (fun _ => uniform d)) ≤ (C : ℝ≥0∞)
end LogGasChallenge
