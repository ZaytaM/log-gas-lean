import Mathlib

/-!
# Phase 1 — Lemma 6.1 (`lem:canonical-array-exponential`), one-block bound (6.3)

Source: `notes/sec6-lemma61.tex`.  Phase notes: `notes/phase1.md`.

Setting.  `(Ω, μ)` is a probability space, `Y : Fin m → Ω → E` are independent with laws
`ν i`, and `h : Fin m → Fin m → E → E → ℝ` are measurable kernels with integrable powers, used only for
`i < j`.  The transpose convention `h_{ji}(y,x) = h_{ij}(x,y)` of the paper is implemented
by `ext`. Centering and moment bounds hold almost everywhere, as in the paper.

The Bernoulli(1/2) index set `I` "independent of `Y`" is modelled by the exact average
`(∑ I : Finset (Fin m), ·) / 2 ^ m` over all subsets: `𝔼_I[F(I)] = 2^{-m} ∑_I F(I)`.

Standing hypotheses of the lemma are collected in the `Prop`-structure `Hyp`; the standing
hypotheses H1/H2 of `notes/hypotheses.md` are not needed in this phase.

Statements (phase notes D1–D7):
* D1 `split_identity`   — eq. `eq:array-split-identity` (6.5)
* D2 `random_split`     — eq. `eq:array-random-split` (6.6)
* D3 `vanishing_word`   — vanishing of monomials with a label of multiplicity one
* D4 `holder_group`, `word_moment` — eqs. `eq:array-holder-group` (6.9),
  `eq:array-word-moment` (6.10); `count_reduction` — eq. `eq:array-count-reduction` (6.11)
* D5 `count_small`, `count_large`, `count_bound` — eq. `eq:array-combinatorial-bound` (6.12)
* D6 `moment_bound`     — first half of eq. `eq:canonical-array-exponential` (6.3)
* D7 `exp_bound`        — second half of (6.3), via eq. `eq:array-exponential-series` (6.13)

The universal constant is fixed as `Cu = 16` (the proof produces `(32 e²)^k ≤ 16^{2k}`).
-/

set_option autoImplicit false
-- The probability-measure instances below are section variables; some elementary lemmas
-- do not use them, which would otherwise trigger this linter.
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal Nat

namespace LogGas.Decoupling

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-! ### Definitions -/

section Defs

variable {m : ℕ}

/-- Extension of the kernels `h i j`, `i < j`, to all ordered pairs by the transpose
convention `h_{ji}(y,x) = h_{ij}(x,y)`; the diagonal is zero ("zero kernels are allowed"). -/
def ext (h : Fin m → Fin m → E → E → ℝ) (i j : Fin m) (x y : E) : ℝ :=
  if i < j then h i j x y else if j < i then h j i y x else 0

/-- `S = ∑_{i<j} h_{ij}(Y_i, Y_j)`. -/
def S (h : Fin m → Fin m → E → E → ℝ) (Y : Fin m → Ω → E) (ω : Ω) : ℝ :=
  ∑ i, ∑ j ∈ Ioi i, h i j (Y i ω) (Y j ω)

/-- `D_I = ∑_{i ∈ I, j ∉ I} h_{ij}(Y_i, Y_j)` with the extended kernels. -/
def D (h : Fin m → Fin m → E → E → ℝ) (Y : Fin m → Ω → E) (I : Finset (Fin m)) (ω : Ω) : ℝ :=
  ∑ i ∈ I, ∑ j ∈ Iᶜ, ext h i j (Y i ω) (Y j ω)

/-- Multiplicity `a_ℓ = #{v : w v = ℓ}` of the label `ℓ` in the word `w`
(eq. `eq:row-multiplicity`). -/
def mult {n : ℕ} (w : Fin n → Fin m) (ℓ : Fin m) : ℕ :=
  (univ.filter (fun v => w v = ℓ)).card

/-- The monomial `T = ∏_v h_{i_v j_v}(Y_{i_v}, Y_{j_v})` indexed by a row word `row` and a
column word `col`. -/
def word (h : Fin m → Fin m → E → E → ℝ) (Y : Fin m → Ω → E) {n : ℕ}
    (row col : Fin n → Fin m) (ω : Ω) : ℝ :=
  ∏ v, ext h (row v) (col v) (Y (row v) ω) (Y (col v) ω)

/-- `A`: the number of multiplicity vectors `(a_ℓ)_{ℓ ≤ m}` with `∑ a_ℓ = 2k` and no entry
equal to `1` (entries are bounded by `2k`, so we range over `Fin m → Fin (2k+1)`). -/
def A (m k : ℕ) : ℕ :=
  (univ.filter (fun a : Fin m → Fin (2 * k + 1) =>
    ∑ ℓ, (a ℓ : ℕ) = 2 * k ∧ ∀ ℓ, (a ℓ : ℕ) ≠ 1)).card

/-- `B_k`: the number of words of length `2k` on `m` labels in which no label occurs exactly
once. -/
def B (m k : ℕ) : ℕ :=
  (univ.filter (fun w : Fin (2 * k) → Fin m => ∀ ℓ, mult w ℓ ≠ 1)).card

/-- The universal constant `C_u` of Lemma 6.1, fixed as `16`. -/
def Cu : ℝ := 16

/-- Standing hypotheses of Lemma 6.1 (`lem:canonical-array-exponential`):
independence of the `Y i` with laws `ν i`, measurable kernels with integrable powers, centering
(eq. `eq:canonical-array-centering`, 6.1) and the factorial moment bounds
(eq. `eq:canonical-array-kernel-moments`, 6.2), with almost-everywhere slice conditions. -/
structure Hyp (μ : Measure Ω) (ν : Fin m → Measure E) (Y : Fin m → Ω → E)
    (h : Fin m → Fin m → E → E → ℝ) (κ : ℝ) : Prop where
  κ_pos : 0 < κ
  Y_meas : ∀ i, Measurable (Y i)
  Y_indep : iIndepFun Y μ
  Y_law : ∀ i, μ.map (Y i) = ν i
  h_meas : ∀ i j, Measurable (Function.uncurry (h i j))
  /-- Finite absolute moments on the joint law; Fubini supplies a.e. slice integrability. -/
  h_int : ∀ i j (p : ℕ), 1 ≤ p →
    Integrable (fun z : E × E => |h i j z.1 z.2| ^ p) ((ν i).prod (ν j))
  /-- (6.1), first variable. -/
  centered_left : ∀ i j, i < j → ∀ᵐ y ∂ν j, ∫ x, h i j x y ∂(ν i) = 0
  /-- (6.1), second variable. -/
  centered_right : ∀ i j, i < j → ∀ᵐ x ∂ν i, ∫ y, h i j x y ∂(ν j) = 0
  /-- (6.2), first variable. -/
  moment_left : ∀ i j, i < j → ∀ p : ℕ, 1 ≤ p → ∀ᵐ y ∂ν j,
    ∫ x, |h i j x y| ^ p ∂(ν i) ≤ 2 * κ ^ p * (p.factorial : ℝ)
  /-- (6.2), second variable. -/
  moment_right : ∀ i j, i < j → ∀ p : ℕ, 1 ≤ p → ∀ᵐ x ∂ν i,
    ∫ y, |h i j x y| ^ p ∂(ν j) ≤ 2 * κ ^ p * (p.factorial : ℝ)

end Defs

/-! ### Lemmas -/

variable {m : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Fin m → Measure E}
  [∀ i, IsProbabilityMeasure (ν i)] {Y : Fin m → Ω → E}
  {h : Fin m → Fin m → E → E → ℝ} {κ : ℝ}

-- SKETCH: unfold `ext`, `split_ifs`, and discharge the impossible branches with
-- `lt_asymm` / `lt_irrefl` (or `omega` after `Fin.lt_def`).
omit [MeasurableSpace E] in
/-- The transpose convention `h_{ji}(y,x) = h_{ij}(x,y)` holds for the extended kernel. -/
theorem ext_symm (h : Fin m → Fin m → E → E → ℝ) (i j : Fin m) (x y : E) :
    ext h j i y x = ext h i j x y := by
  unfold ext; split_ifs <;> first | rfl | exact absurd ‹_› (lt_asymm ‹_›)

/-- Measurability of the transposed, zero-diagonal extension. -/
theorem measurable_ext (H : Hyp μ ν Y h κ) (i j : Fin m) :
    Measurable (Function.uncurry (ext h i j)) := by
  unfold ext; split_ifs
  · exact H.h_meas i j
  · exact (H.h_meas j i).comp measurable_swap
  · exact measurable_const

/-- Absolute powers of the extended kernel are integrable under the pair law. -/
theorem ext_integrable_pow (H : Hyp μ ν Y h κ) (i j : Fin m) (p : ℕ) (hp : 1 ≤ p) :
    Integrable (fun z : E × E => |ext h i j z.1 z.2| ^ p) ((ν i).prod (ν j)) := by
  unfold ext; split_ifs
  · exact H.h_int i j p hp
  · exact (H.h_int j i p hp).swap
  · simpa [zero_pow (by omega : p ≠ 0)] using
      (integrable_zero : Integrable (fun _ : E × E => (0 : ℝ)) ((ν i).prod (ν j)))

/-- Slice integrability is a consequence of joint integrability, with the correct null sets. -/
theorem ext_integrable_pow_left (H : Hyp μ ν Y h κ) (i j : Fin m) (p : ℕ) (hp : 1 ≤ p) :
    ∀ᵐ y ∂ν j, Integrable (fun x => |ext h i j x y| ^ p) (ν i) :=
  (ext_integrable_pow H i j p hp).prod_left_ae

theorem ext_integrable_pow_right (H : Hyp μ ν Y h κ) (i j : Fin m) (p : ℕ) (hp : 1 ≤ p) :
    ∀ᵐ x ∂ν i, Integrable (fun y => |ext h i j x y| ^ p) (ν j) :=
  (ext_integrable_pow H i j p hp).prod_right_ae

/-- Eq. (6.1) for the extended kernel, almost everywhere in its second variable. -/
theorem ext_centered (H : Hyp μ ν Y h κ) (i j : Fin m) :
    ∀ᵐ y ∂ν j, ∫ x, ext h i j x y ∂(ν i) = 0 := by
  unfold ext; split_ifs
  · exact H.centered_left _ _ ‹_›
  · exact H.centered_right _ _ ‹_›
  · simp

/-- Eq. (6.2) for the extended kernel, almost everywhere in its second variable. -/
theorem ext_moment (H : Hyp μ ν Y h κ) (i j : Fin m) (p : ℕ) (hp : 1 ≤ p) :
    ∀ᵐ y ∂ν j, ∫ x, |ext h i j x y| ^ p ∂(ν i) ≤ 2 * κ ^ p * (p.factorial : ℝ) := by
  unfold ext; split_ifs
  · exact H.moment_left _ _ ‹_› p hp
  · exact H.moment_right _ _ ‹_› p hp
  · have := H.κ_pos
    filter_upwards [] with y
    simp only [abs_zero, zero_pow (by omega : p ≠ 0), integral_zero]
    positivity

/-- Independent coordinates transport joint kernel moments to the sample space. -/
theorem ext_sample_integrable_pow (H : Hyp μ ν Y h κ) (i j : Fin m)
    (p : ℕ) (hp : 1 ≤ p) :
    Integrable (fun ω => |ext h i j (Y i ω) (Y j ω)| ^ p) μ := by
  by_cases hij : i = j
  · subst j
    simpa [ext, zero_pow (by omega : p ≠ 0)] using
      (integrable_zero : Integrable (fun _ : Ω => (0 : ℝ)) μ)
  · have hpair : MeasurePreserving (fun ω => (Y i ω, Y j ω)) μ ((ν i).prod (ν j)) := by
      refine ⟨(H.Y_meas i).prodMk (H.Y_meas j), ?_⟩
      rw [(H.Y_indep.indepFun hij).map_prod_eq_prod_map_map
        (H.Y_meas i).aemeasurable (H.Y_meas j).aemeasurable, H.Y_law i, H.Y_law j]
    exact hpair.integrable_comp_of_integrable (ext_integrable_pow H i j p hp)

/-- All finite absolute moments give membership in each finite positive `Lᵖ`. -/
theorem memLp_of_integrable_abs_pow {f : Ω → ℝ} (hf : Measurable f) (p : ℕ) (hp : 1 ≤ p)
    (hi : Integrable (fun ω => |f ω| ^ p) μ) : MemLp f (p : ℝ≥0∞) μ := by
  apply (integrable_norm_rpow_iff hf.aestronglyMeasurable
    (by exact_mod_cast (by omega : p ≠ 0)) (by simp)).mp
  simpa [Real.norm_eq_abs, Real.rpow_natCast] using hi

/-- Finite products of functions with all absolute moments are integrable (finite Hölder). -/
theorem integrable_finset_prod_of_moments {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, Measurable (f i))
    (hi : ∀ i ∈ s, ∀ p : ℕ, 1 ≤ p → Integrable (fun ω => |f i ω| ^ p) μ) :
    Integrable (fun ω => ∏ i ∈ s, f i ω) μ := by
  classical
  by_cases hs : s = ∅
  · subst s; simp
  have hn : 1 ≤ s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
  have hm : ∀ i ∈ s, MemLp (f i) (s.card : ℝ≥0∞) μ := fun i h =>
    memLp_of_integrable_abs_pow (hf i h) s.card hn (hi i h s.card hn)
  have hh := MemLp.fun_prod hm
  have he : (∑ _i ∈ s, ((s.card : ℝ≥0∞))⁻¹)⁻¹ = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [ENNReal.mul_inv_cancel (by exact_mod_cast (by omega : s.card ≠ 0)) (by simp)]
    simp
  rw [he] at hh
  exact memLp_one_iff_integrable.mp hh

/-- Word integrability required for Fubini is obtained from moments, without boundedness. -/
theorem integrable_word (H : Hyp μ ν Y h κ) {n : ℕ} (row col : Fin n → Fin m) :
    Integrable (word h Y row col) μ := by
  apply integrable_finset_prod_of_moments univ
    (fun v ω => ext h (row v) (col v) (Y (row v) ω) (Y (col v) ω))
  · intro v _
    exact (measurable_ext H _ _).comp ((H.Y_meas _).prodMk (H.Y_meas _))
  · intro v _ p hp
    exact ext_sample_integrable_pow H _ _ p hp

/-- Finite sums of the kernels have every absolute moment; `p = 0` is constant. -/
theorem integrable_S_pow (H : Hyp μ ν Y h κ) (p : ℕ) :
    Integrable (fun ω => |S h Y ω| ^ p) μ := by
  by_cases hp : p = 0
  · subst p; simp
  have hm : MemLp (S h Y) (p : ℝ≥0∞) μ := by
    apply memLp_finsetSum univ
    intro i _
    apply memLp_finsetSum (Ioi i)
    intro j hj
    have he := memLp_of_integrable_abs_pow
      ((measurable_ext H i j).comp ((H.Y_meas i).prodMk (H.Y_meas j))) p (by omega)
      (ext_sample_integrable_pow H i j p (by omega))
    simpa only [Function.comp_def, Function.uncurry_apply_pair, ext,
      if_pos (Finset.mem_Ioi.mp hj)] using he
  simpa only [Real.norm_eq_abs] using hm.integrable_norm_pow hp

theorem integrable_D_pow (H : Hyp μ ν Y h κ) (I : Finset (Fin m)) (p : ℕ) :
    Integrable (fun ω => |D h Y I ω| ^ p) μ := by
  by_cases hp : p = 0
  · subst p; simp
  have hm : MemLp (D h Y I) (p : ℝ≥0∞) μ := by
    apply memLp_finsetSum I
    intro i _
    apply memLp_finsetSum Iᶜ
    intro j _
    exact memLp_of_integrable_abs_pow
      ((measurable_ext H i j).comp ((H.Y_meas i).prodMk (H.Y_meas j))) p (by omega)
      (ext_sample_integrable_pow H i j p (by omega))
  simpa only [Real.norm_eq_abs] using hm.integrable_norm_pow hp

-- SKETCH (D1): rewrite `D h Y I ω` as `∑ i, ∑ j, (if i ∈ I ∧ j ∉ I then ext h i j .. else 0)`
-- (`Finset.sum_filter`, `Finset.mem_compl`), swap the sum over `I` inside
-- (`Finset.sum_comm`), and count: for `i ≠ j` exactly `2^(m-2)` subsets contain `i` but
-- not `j` (`Finset.card_powerset`-style counting, or `Fintype.card_subtype` with the
-- bijection `I ↦ I \ {i,j}`), while the diagonal contributes `0` (`ext h i i = 0`).  Then
-- pair `(i,j)` with `(j,i)` via `ext_symm` and `Finset.sum_sigma`/`Finset.sum_Ioi_add_sum_Iio`
-- style splitting to recover `2 * 2^(m-2) * S = 2^m * (S / 2)`.
/-- Eq. `eq:array-split-identity` (6.5): averaging `D_I` over all `2^m` index sets `I`
gives `S/2`, for every fixed sample `ω`. -/
theorem split_identity (h : Fin m → Fin m → E → E → ℝ) (Y : Fin m → Ω → E) (ω : Ω) :
    (∑ I : Finset (Fin m), D h Y I ω) / 2 ^ m = S h Y ω / 2 := by
  classical
  set a : Fin m → Fin m → ℝ := fun i j => ext h i j (Y i ω) (Y j ω) with ha
  have hcount : ∀ i j : Fin m, i ≠ j →
      ((univ.filter (fun I : Finset (Fin m) => i ∈ I ∧ j ∉ I)).card : ℝ) * 4 = 2 ^ m := by
    intro i j hij
    have hc : (univ.filter (fun I : Finset (Fin m) => i ∈ I ∧ j ∉ I)).card
        = ((({i, j} : Finset (Fin m))ᶜ).powerset).card := by
      symm
      apply Finset.card_bij (fun I _ => insert i I)
      · intro I hI
        rw [Finset.mem_powerset] at hI
        simp only [mem_filter, mem_univ, true_and, Finset.mem_insert]
        refine ⟨Or.inl trivial, ?_⟩
        intro hj
        rcases hj with hj | hj
        · exact hij hj.symm
        · have := hI hj; simp at this
      · intro I hI J hJ h2
        rw [Finset.mem_powerset] at hI hJ
        have hiI : i ∉ I := fun h' => by have := hI h'; simp at this
        have hiJ : i ∉ J := fun h' => by have := hJ h'; simp at this
        have := congrArg (fun s => s.erase i) h2
        simpa [Finset.erase_insert hiI, Finset.erase_insert hiJ] using this
      · intro J hJ
        simp only [mem_filter, mem_univ, true_and] at hJ
        refine ⟨J.erase i, ?_, Finset.insert_erase hJ.1⟩
        rw [Finset.mem_powerset]
        intro x hx
        simp only [Finset.mem_erase] at hx
        simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨hx.1, ?_⟩
        rintro rfl
        exact hJ.2 hx.2
    rw [hc, Finset.card_powerset, Finset.card_compl]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [Finset.card_pair hij]
    have hm : 2 ≤ m := by
      have := Finset.card_le_univ ({i, j} : Finset (Fin m))
      rw [Finset.card_pair hij] at this; simpa using this
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hm
    simp [pow_add]
    ring
  have hD : ∀ I : Finset (Fin m), D h Y I ω
      = ∑ i, ∑ j, if i ∈ I ∧ j ∉ I then a i j else 0 := by
    intro I
    unfold D
    have key : ∀ i, (∑ j, if i ∈ I ∧ j ∉ I then a i j else 0)
        = if i ∈ I then ∑ j ∈ Iᶜ, a i j else 0 := by
      intro i
      by_cases hi : i ∈ I
      · simp only [hi, true_and, if_true]
        rw [← Finset.sum_filter (fun j => j ∉ I)]
        congr 1
        ext; simp
      · simp [hi]
    simp_rw [key]
    rw [← Finset.sum_filter]
    simp
    rfl
  have hsum : ∑ I : Finset (Fin m), D h Y I ω
      = ∑ i, ∑ j, ((univ.filter (fun I : Finset (Fin m) => i ∈ I ∧ j ∉ I)).card : ℝ) * a i j := by
    simp_rw [hD]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hdiag : ∀ i, a i i = 0 := by intro i; simp [ha, ext]
  have hcard : ∀ i j, ((univ.filter (fun I : Finset (Fin m) => i ∈ I ∧ j ∉ I)).card : ℝ) * a i j
      = 2 ^ m / 4 * a i j := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [hdiag]
    · have := hcount i j hij
      congr 1
      linarith
  have hS : ∑ i, ∑ j, a i j = 2 * S h Y ω := by
    have hsymm : ∀ i j, a j i = a i j := fun i j => ext_symm h i j _ _
    have hlt : ∀ i j, i < j → a i j = h i j (Y i ω) (Y j ω) := by
      intro i j hij; simp [ha, ext, hij]
    have hdec : ∀ i j, a i j = (if i < j then a i j else 0) + (if j < i then a i j else 0) := by
      intro i j
      rcases lt_trichotomy i j with hij | hij | hij
      · simp [hij, not_lt.2 hij.le]
      · subst hij; simp [hdiag]
      · simp [hij, not_lt.2 hij.le]
    have h1 : ∑ i, ∑ j, (if i < j then a i j else 0) = S h Y ω := by
      unfold S
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_filter]
      refine Finset.sum_congr (by ext; simp) fun j hj => ?_
      exact hlt i j (by simpa using hj)
    have h2 : ∑ i, ∑ j, (if j < i then a i j else 0) = S h Y ω := by
      rw [Finset.sum_comm]
      unfold S
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_filter]
      refine Finset.sum_congr (by ext; simp) fun j hj => ?_
      have hj' : i < j := by simpa using hj
      have : a j i = a i j := ext_symm h i j _ _
      rw [this]; exact hlt i j hj'
    calc ∑ i, ∑ j, a i j
        = ∑ i, ∑ j, ((if i < j then a i j else 0) + (if j < i then a i j else 0)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hdec i j
      _ = 2 * S h Y ω := by
          simp_rw [Finset.sum_add_distrib]; rw [h1, h2]; ring
  rw [hsum]
  simp_rw [hcard, ← Finset.mul_sum]
  rw [hS]
  have : (2:ℝ) ^ m ≠ 0 := by positivity
  field_simp
  ring

-- SKETCH (D2): pointwise, `S ω = 2 * avg_I D_I ω` by `split_identity`, so
-- `|S ω|^(2k) = 2^(2k) * |avg_I D_I ω|^(2k) ≤ 2^(2k) * avg_I |D_I ω|^(2k)` by Jensen for the
-- convex function `x ↦ |x|^(2k)` (`(even_two_mul k).convexOn_pow` after `Even.pow_abs`,
-- with `ConvexOn.map_sum_le` and the uniform weights `2⁻¹^m`, `Finset.card_univ`,
-- `Fintype.card_finset`).  Integrate with `integral_mono`, `integral_finset_sum`,
-- `integral_const_mul`, `integral_div`; integrability from `H.h_int`, the independent pair laws, and finite Hölder.
-- Handle `k = 0` separately (the integrand is constant).
/-- Eq. `eq:array-random-split` (6.6): `𝔼|S|^{2k} ≤ 2^{2k} 𝔼_I 𝔼|D_I|^{2k}`. -/
theorem random_split (H : Hyp μ ν Y h κ) (k : ℕ) :
    ∫ ω, |S h Y ω| ^ (2 * k) ∂μ
      ≤ 2 ^ (2 * k) * ((∑ I : Finset (Fin m), ∫ ω, |D h Y I ω| ^ (2 * k) ∂μ) / 2 ^ m) := by
  have hDint : ∀ I, Integrable (fun ω => |D h Y I ω| ^ (2 * k)) μ :=
    fun I => integrable_D_pow H I _
  have hpt : ∀ ω, |S h Y ω| ^ (2 * k)
      ≤ 2 ^ (2 * k) * ((∑ I : Finset (Fin m), |D h Y I ω| ^ (2 * k)) / 2 ^ m) := by
    intro ω
    have hS : S h Y ω = 2 * ((∑ I : Finset (Fin m), D h Y I ω) / 2 ^ m) := by
      rw [split_identity]; ring
    have hw : ∑ _I : Finset (Fin m), (1 / 2 ^ m : ℝ) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
      simp
    have J := Real.pow_arith_mean_le_arith_mean_pow (Finset.univ : Finset (Finset (Fin m)))
      (fun _ => (1 / 2 ^ m : ℝ)) (fun I => |D h Y I ω|) (fun _ _ => by positivity) hw
      (fun I _ => abs_nonneg _) (2 * k)
    have e1 : (∑ I : Finset (Fin m), (1 / 2 ^ m : ℝ) * |D h Y I ω|)
        = (∑ I : Finset (Fin m), |D h Y I ω|) / 2 ^ m := by
      rw [← Finset.mul_sum]; ring
    have e2 : (∑ I : Finset (Fin m), (1 / 2 ^ m : ℝ) * |D h Y I ω| ^ (2 * k))
        = (∑ I : Finset (Fin m), |D h Y I ω| ^ (2 * k)) / 2 ^ m := by
      rw [← Finset.mul_sum]; ring
    rw [e1, e2] at J
    have h3 : |(∑ I : Finset (Fin m), D h Y I ω) / 2 ^ m|
        ≤ (∑ I : Finset (Fin m), |D h Y I ω|) / 2 ^ m := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 ^ m)]
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    rw [hS, abs_mul, mul_pow, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    gcongr
    exact le_trans (pow_le_pow_left₀ (abs_nonneg _) h3 _) J
  have hRint : Integrable (fun ω => 2 ^ (2 * k) *
      ((∑ I : Finset (Fin m), |D h Y I ω| ^ (2 * k)) / 2 ^ m)) μ :=
    ((MeasureTheory.integrable_finsetSum _ fun I _ => hDint I).div_const _).const_mul _
  have hSint : Integrable (fun ω => |S h Y ω| ^ (2 * k)) μ := integrable_S_pow H _
  calc ∫ ω, |S h Y ω| ^ (2 * k) ∂μ
      ≤ ∫ ω, 2 ^ (2 * k) * ((∑ I : Finset (Fin m), |D h Y I ω| ^ (2 * k)) / 2 ^ m) ∂μ :=
        integral_mono hSint hRint hpt
    _ = _ := by
        rw [integral_const_mul, integral_div, MeasureTheory.integral_finsetSum _ fun I _ => hDint I]

-- SKETCH (D3): by `ext_symm` (transposing `row ↔ col`) it suffices to treat a row label
-- `ℓ` with `mult row ℓ = 1`, i.e. `row v₀ = ℓ` for a unique `v₀` (`Finset.card_eq_one`).
-- Since rows lie in `I` and columns in `Iᶜ`, `ℓ` is not a column label, so
-- `word = ext h ℓ (col v₀) (Y ℓ) (Y (col v₀)) * R` with `R` an integrable product of powers of
-- `(Y j)_{j ≠ ℓ}` (`Finset.prod_erase_mul`).  `Y ℓ` is independent of `(Y j)_{j ≠ ℓ}`
-- (`H.Y_indep.indepFun_finset {ℓ} {ℓ}ᶜ`), so the law of the pair is the product measure
-- (`indepFun_iff_map_prod_eq_prod_map_map`, `H.Y_law`); rewrite with `integral_map` and
-- `integral_prod` (Fubini), and the inner `ν ℓ`-integral vanishes by `ext_centered`.
/-- Vanishing monomials: if some label occurs exactly once in the row word or in the column
word of a term of the expansion of `D_I^{2k}`, its expectation is `0` (uses (6.1) and
independence). -/
theorem vanishing_word (H : Hyp μ ν Y h κ) {n : ℕ} (I : Finset (Fin m))
    (row col : Fin n → Fin m) (hrow : ∀ v, row v ∈ I) (hcol : ∀ v, col v ∉ I)
    (hone : (∃ ℓ, mult row ℓ = 1) ∨ (∃ ℓ, mult col ℓ = 1)) :
    ∫ ω, word h Y row col ω ∂μ = 0 := by
  sorry

-- SKETCH (6.9): with `a = mult row ℓ ≥ 1`, Hölder with `a` equal exponents `1/a`:
-- `|∫ ∏_v f_v| ≤ ∫ ∏_v |f_v| ≤ ∏_v (∫ |f_v|^a)^(1/a)` (`abs_integral_le_integral_abs`,
-- `ENNReal.lintegral_prod_norm_pow_le` with `p v = 1/a`, `∑ p v = 1`, translated to Bochner
-- integrals via `ofReal_integral_eq_lintegral_ofReal` for the nonnegative integrable
-- integrands).  Each factor is `≤ (2 κ^a a!)^(1/a)` by `ext_moment`; the product of `a`
-- such factors is `2 κ^a a!` (`Real.rpow_natCast`, `Finset.prod_const`, `Real.rpow_mul`).
/-- Eq. `eq:array-holder-group` (6.9): for a row label `ℓ` of multiplicity `a_ℓ ≥ 1`
and frozen column values `y`,
`|Φ_ℓ(y)| = |𝔼 ∏_{v : i_v = ℓ} h_{ℓ j_v}(Y_ℓ, y_{j_v})| ≤ 2 κ^{a_ℓ} a_ℓ!`. -/
theorem holder_group_at (H : Hyp μ ν Y h κ) {n : ℕ} (ℓ : Fin m) (row col : Fin n → Fin m)
    (hℓ : 1 ≤ mult row ℓ) (y : Fin m → E)
    (hint : ∀ v, Integrable (fun x => |ext h ℓ (col v) x (y (col v))| ^ mult row ℓ) (ν ℓ))
    (hmoment : ∀ v, ∫ x, |ext h ℓ (col v) x (y (col v))| ^ mult row ℓ ∂ν ℓ
      ≤ 2 * κ ^ mult row ℓ * ((mult row ℓ).factorial : ℝ)) :
    |∫ x, ∏ v ∈ univ.filter (fun v => row v = ℓ), ext h ℓ (col v) x (y (col v)) ∂(ν ℓ)|
      ≤ 2 * κ ^ (mult row ℓ) * ((mult row ℓ).factorial : ℝ) := by
  classical
  have hmeas : ∀ v, Measurable fun x => ext h ℓ (col v) x (y (col v)) := by
    intro v; unfold ext; split_ifs
    · exact (H.h_meas _ _).comp (measurable_id.prodMk measurable_const)
    · exact (H.h_meas _ _).comp (measurable_const.prodMk measurable_id)
    · exact measurable_const
  set s := univ.filter (fun v => row v = ℓ) with hsdef
  set a := mult row ℓ with ha
  have hs : s.card = a := rfl
  have ha1 : 1 ≤ a := hℓ
  set F : Fin n → E → ℝ := fun v x => |ext h ℓ (col v) x (y (col v))| with hF
  have hFm : ∀ v, Measurable (F v) := fun v => (hmeas v).abs
  have hF0 : ∀ v x, 0 ≤ F v x := fun v x => abs_nonneg _
  have hFint : ∀ v, Integrable (fun x => F v x ^ a) (ν ℓ) := hint
  have key : ∫⁻ x, ENNReal.ofReal (∏ v ∈ s, F v x) ∂(ν ℓ)
      ≤ ENNReal.ofReal (2 * κ ^ a * (a.factorial : ℝ)) := by
    have hp : ∑ v ∈ s, (1 / (a : ℝ)) = 1 := by
      rw [Finset.sum_const, hs, nsmul_eq_mul]
      have : (a : ℝ) ≠ 0 := by positivity
      field_simp
    calc ∫⁻ x, ENNReal.ofReal (∏ v ∈ s, F v x) ∂(ν ℓ)
        = ∫⁻ x, ∏ v ∈ s, (ENNReal.ofReal (F v x) ^ (a : ℝ)) ^ (1 / (a : ℝ)) ∂(ν ℓ) := by
          congr 1; ext x
          rw [ENNReal.ofReal_prod_of_nonneg (fun v _ => hF0 v x)]
          refine Finset.prod_congr rfl fun v _ => ?_
          rw [← ENNReal.rpow_mul]
          have : (a : ℝ) ≠ 0 := by positivity
          rw [mul_one_div_cancel this, ENNReal.rpow_one]
      _ ≤ ∏ v ∈ s, (∫⁻ x, ENNReal.ofReal (F v x) ^ (a : ℝ) ∂(ν ℓ)) ^ (1 / (a : ℝ)) := by
          refine ENNReal.lintegral_prod_norm_pow_le s (fun v _ => ?_) hp (fun v _ => by positivity)
          exact ((hFm v).ennreal_ofReal.pow_const _).aemeasurable
      _ ≤ ∏ v ∈ s, (ENNReal.ofReal (2 * κ ^ a * (a.factorial : ℝ))) ^ (1 / (a : ℝ)) := by
          refine Finset.prod_le_prod' fun v _ => ?_
          refine ENNReal.rpow_le_rpow ?_ (by positivity)
          calc ∫⁻ x, ENNReal.ofReal (F v x) ^ (a : ℝ) ∂(ν ℓ)
              = ∫⁻ x, ENNReal.ofReal (F v x ^ a) ∂(ν ℓ) := by
                congr 1; ext x
                rw [ENNReal.ofReal_pow (hF0 v x), ← ENNReal.rpow_natCast]
            _ = ENNReal.ofReal (∫ x, F v x ^ a ∂(ν ℓ)) :=
                (ofReal_integral_eq_lintegral_ofReal (hFint v)
                  (ae_of_all _ fun x => pow_nonneg (hF0 v x) a)).symm
            _ ≤ _ := ENNReal.ofReal_le_ofReal (hmoment v)
      _ = ENNReal.ofReal (2 * κ ^ a * (a.factorial : ℝ)) := by
          rw [Finset.prod_const, hs, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          have : (a : ℝ) ≠ 0 := by positivity
          rw [one_div_mul_cancel this, ENNReal.rpow_one]
  calc |∫ x, ∏ v ∈ s, ext h ℓ (col v) x (y (col v)) ∂(ν ℓ)|
      ≤ ∫ x, |∏ v ∈ s, ext h ℓ (col v) x (y (col v))| ∂(ν ℓ) := abs_integral_le_integral_abs
    _ = ∫ x, ∏ v ∈ s, F v x ∂(ν ℓ) := by simp [hF, Finset.abs_prod]
    _ = (∫⁻ x, ENNReal.ofReal (∏ v ∈ s, F v x) ∂(ν ℓ)).toReal :=
        integral_eq_lintegral_of_nonneg_ae
          (ae_of_all _ fun x => Finset.prod_nonneg fun v _ => hF0 v x)
          (Finset.measurable_prod s fun v _ => hFm v).aestronglyMeasurable
    _ ≤ (ENNReal.ofReal (2 * κ ^ a * (a.factorial : ℝ))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top key
    _ = 2 * κ ^ a * (a.factorial : ℝ) :=
        ENNReal.toReal_ofReal (by have := H.κ_pos; positivity)

/-- Hölder's row bound holds for almost every frozen column vector, as required by Fubini. -/
theorem holder_group (H : Hyp μ ν Y h κ) {n : ℕ} (ℓ : Fin m) (row col : Fin n → Fin m)
    (hℓ : 1 ≤ mult row ℓ) :
    ∀ᵐ y ∂Measure.pi ν,
      |∫ x, ∏ v ∈ univ.filter (fun v => row v = ℓ), ext h ℓ (col v) x (y (col v)) ∂ν ℓ|
        ≤ 2 * κ ^ mult row ℓ * ((mult row ℓ).factorial : ℝ) := by
  have hi : ∀ v, ∀ᵐ y ∂Measure.pi ν,
      Integrable (fun x => |ext h ℓ (col v) x (y (col v))| ^ mult row ℓ) (ν ℓ) := by
    intro v
    exact (measurePreserving_eval ν (col v)).quasiMeasurePreserving.ae
      (ext_integrable_pow_left H ℓ (col v) _ hℓ)
  have hm : ∀ v, ∀ᵐ y ∂Measure.pi ν,
      ∫ x, |ext h ℓ (col v) x (y (col v))| ^ mult row ℓ ∂ν ℓ
        ≤ 2 * κ ^ mult row ℓ * ((mult row ℓ).factorial : ℝ) := by
    intro v
    exact (measurePreserving_eval ν (col v)).quasiMeasurePreserving.ae
      (ext_moment H ℓ (col v) _ hℓ)
  filter_upwards [ae_all_iff.mpr hi, ae_all_iff.mpr hm] with y hiy hmy
  exact holder_group_at H ℓ row col hℓ y hiy hmy

-- SKETCH (D4, 6.10): condition on the column block.  `(Y i)_{i ∈ I}` and `(Y j)_{j ∈ Iᶜ}`
-- are independent (`H.Y_indep.indepFun_finset I Iᶜ disjoint_compl_right`), so by
-- `indepFun_iff_map_prod_eq_prod_map_map`, `integral_map`, `integral_prod` the expectation
-- is `∫ (∫ word dP_I) dP_{Iᶜ}`; the row-block law `P_I` is `Measure.pi (fun i : I => ν i)`
-- (`iIndepFun_iff_map_fun_eq_pi_map` applied to `H.Y_indep.precomp Subtype.val_injective`).
-- Group the product by row label (`Finset.prod_fiberwise univ row`) and factor the
-- `Measure.pi`-integral (`integral_fintype_prod_eq_prod`); this is (6.8).  Bound each
-- active factor by `holder_group`, inactive labels (`a_ℓ = 0`) give `1`.  Finally
-- `∏_{active} 2 = 2^#active ≤ 2^k` since every active `a_ℓ ≥ 2` and `∑ a_ℓ = 2k`
-- (`Finset.sum_fiberwise`, `Finset.card_nsmul_le_sum`), and `∏_ℓ κ^{a_ℓ} = κ^{2k}`
-- (`Finset.prod_pow_eq_pow_sum`); `abs_integral_le_integral_abs`, `integral_mono`.
/-- Eq. `eq:array-word-moment` (6.10): for a surviving row word (no multiplicity equal to
one), `|𝔼 ∏_{v=1}^{2k} h_{i_v j_v}(Y_{i_v}, Y_{j_v})| ≤ 2^k κ^{2k} ∏_ℓ a_ℓ!`. -/
theorem word_moment (H : Hyp μ ν Y h κ) (k : ℕ) (I : Finset (Fin m))
    (row col : Fin (2 * k) → Fin m) (hrow : ∀ v, row v ∈ I) (hcol : ∀ v, col v ∉ I)
    (hsurv : ∀ ℓ, mult row ℓ ≠ 1) :
    |∫ ω, word h Y row col ω ∂μ|
      ≤ 2 ^ k * κ ^ (2 * k) * ∏ ℓ, ((mult row ℓ).factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [word, mult]
  classical
  have hext_meas : ∀ i j : Fin m, Measurable (fun p : E × E => ext h i j p.1 p.2) := by
    intro i j; unfold ext; split_ifs
    · exact H.h_meas _ _
    · exact (H.h_meas _ _).comp measurable_swap
    · exact measurable_const
  set G : (Fin m → E) → ℝ := fun y => ∏ v, ext h (row v) (col v) (y (row v)) (y (col v)) with hGdef
  have hG : Measurable G := Finset.measurable_prod _ fun v _ => by
    have hp : Measurable (fun y : Fin m → E => (y (row v), y (col v))) :=
      (measurable_pi_apply (row v)).prodMk (measurable_pi_apply (col v))
    exact (hext_meas (row v) (col v)).comp hp
  have hmap : μ.map (fun ω i => Y i ω) = Measure.pi ν := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (H.Y_meas i).aemeasurable)).1 H.Y_indep]
    congr; funext i; exact H.Y_law i
  have h1 : ∫ ω, word h Y row col ω ∂μ = ∫ y, G y ∂Measure.pi ν := by
    rw [← hmap, integral_map (Measurable.of_eval H.Y_meas).aemeasurable
      hG.aestronglyMeasurable]
    rfl
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun i => ν i) (· ∈ I)
  set K : ((↥I → E) × ({ i // i ∉ I } → E)) → ℝ := fun z => G ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin m => E) (· ∈ I)).symm z) with hK
  have hKm : Measurable K := hG.comp (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin m => E) (· ∈ I)).symm.measurable
  have h2 : ∫ y, G y ∂Measure.pi ν = ∫ z, K z ∂((Measure.pi fun i : ↥I => ν i).prod
      (Measure.pi fun i : { i // i ∉ I } => ν i)) := by
    have := hmp.integral_comp' (g := K)
    simp only [hK, MeasurableEquiv.symm_apply_apply] at this
    convert this
  have hGint : Integrable G (Measure.pi ν) := by
    rw [← hmap]
    exact (integrable_map_measure hG.aestronglyMeasurable
      (Measurable.of_eval H.Y_meas).aemeasurable).mpr (integrable_word H row col)
  have hKint : Integrable K ((Measure.pi fun i : ↥I => ν i).prod
      (Measure.pi fun i : { i // i ∉ I } => ν i)) := by
    convert hmp.symm.integrable_comp_of_integrable hGint using 1 <;>
      first | rfl | (congr <;> exact Subsingleton.elim _ _)
  have h3 : ∫ z, K z ∂((Measure.pi fun i : ↥I => ν i).prod
      (Measure.pi fun i : { i // i ∉ I } => ν i)) =
      ∫ v, ∫ u, K (u, v) ∂(Measure.pi fun i : ↥I => ν i) ∂(Measure.pi fun i : { i // i ∉ I } => ν i) :=
    integral_prod_symm K hKint
  have hgood : ∀ ℓ (t : Fin (2 * k)), ∀ᵐ v ∂(Measure.pi fun i : { i // i ∉ I } => ν i),
      Integrable (fun x => |ext h ℓ (col t) x (v ⟨col t, hcol t⟩)| ^ mult row ℓ) (ν ℓ) ∧
      (∫ x, |ext h ℓ (col t) x (v ⟨col t, hcol t⟩)| ^ mult row ℓ ∂ν ℓ)
        ≤ 2 * κ ^ mult row ℓ * ((mult row ℓ).factorial : ℝ) := by
    intro ℓ t
    by_cases hzero : mult row ℓ = 0
    · filter_upwards [] with v
      simp [hzero]
    · exact (measurePreserving_eval (fun i : { i // i ∉ I } => ν i) ⟨col t, hcol t⟩).quasiMeasurePreserving.ae
        ((ext_integrable_pow_left H ℓ (col t) _ (by omega)).and
          (ext_moment H ℓ (col t) _ (by omega)))
  have hinner : ∀ᵐ v ∂(Measure.pi fun i : { i // i ∉ I } => ν i), |∫ u, K (u, v) ∂(Measure.pi fun i : ↥I => ν i)|
      ≤ 2 ^ k * κ ^ (2 * k) * ∏ ℓ, ((mult row ℓ).factorial : ℝ) := by
    filter_upwards [ae_all_iff.mpr (fun ℓ => ae_all_iff.mpr (hgood ℓ))] with v hv
    have hsum : ∑ ℓ, mult row ℓ = 2 * k := by
      have := Finset.card_eq_sum_card_fiberwise (f := row) (s := (univ : Finset (Fin (2 * k))))
        (t := (univ : Finset (Fin m))) (by simp)
      simpa [mult] using this.symm
    obtain ⟨e0⟩ : Nonempty E := by
      obtain ⟨ω0⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
      exact ⟨Y (row ⟨0, by omega⟩) ω0⟩
    set y : Fin m → E := fun j => if hj : j ∈ I then e0 else v ⟨j, hj⟩ with hy
    have hycol : ∀ t, y (col t) = v ⟨col t, hcol t⟩ := fun t => by simp [hy, hcol t]
    set rowI : Fin (2 * k) → ↥I := fun t => ⟨row t, hrow t⟩ with hrowI
    set g : Fin m → ℝ := fun ℓ =>
      (if mult row ℓ = 0 then 1 else 2) * κ ^ (mult row ℓ) * ((mult row ℓ).factorial : ℝ) with hg
    have hκ := H.κ_pos
    have hKuv : ∀ u : ↥I → E, K (u, v) =
        ∏ ℓ : ↥I, ∏ t ∈ univ.filter (fun t => rowI t = ℓ), ext h ℓ (col t) (u ℓ) (y (col t)) := by
      intro u
      calc K (u, v) = ∏ t, ext h (row t) (col t) (u (rowI t)) (y (col t)) := by
            simp [hK, hGdef, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, hrow, hcol, hycol,
              hrowI]
        _ = ∏ ℓ : ↥I, ∏ t ∈ univ.filter (fun t => rowI t = ℓ),
              ext h (row t) (col t) (u (rowI t)) (y (col t)) :=
            (Finset.prod_fiberwise univ rowI _).symm
        _ = _ := Finset.prod_congr rfl fun ℓ _ => Finset.prod_congr rfl fun t ht => by
            have := (Finset.mem_filter.1 ht).2
            subst this; rfl
    have hfac : ∀ ℓ : ↥I, |∫ x, ∏ t ∈ univ.filter (fun t => rowI t = ℓ),
        ext h ℓ (col t) x (y (col t)) ∂(ν ℓ)| ≤ g ℓ := by
      intro ℓ
      have hfilt : univ.filter (fun t => rowI t = ℓ) = univ.filter (fun t => row t = ℓ.val) :=
        Finset.filter_congr fun t _ => by simp [hrowI, Subtype.ext_iff]
      rw [hfilt]
      by_cases h0 : mult row ℓ = 0
      · have : univ.filter (fun t => row t = ℓ.val) = ∅ := Finset.card_eq_zero.1 h0
        rw [this]; simp [hg, h0]
      · have := holder_group_at H ℓ.val row col (Nat.one_le_iff_ne_zero.2 h0) y
          (fun t => by simpa only [hycol] using (hv ℓ.val t).1)
          (fun t => by simpa only [hycol] using (hv ℓ.val t).2)
        calc _ ≤ _ := this
          _ = g ℓ := by simp [hg, h0]
    have hprod : ∏ ℓ : ↥I, g ℓ = ∏ ℓ : Fin m, g ℓ := by
      rw [Finset.prod_coe_sort I g]
      refine Finset.prod_subset (Finset.subset_univ _) fun ℓ _ hℓ => ?_
      have : mult row ℓ = 0 := by
        unfold mult; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro t _ heq; exact hℓ (heq ▸ hrow t)
      simp [hg, this]
    have hgbd : ∏ ℓ : Fin m, g ℓ ≤ 2 ^ k * κ ^ (2 * k) * ∏ ℓ, ((mult row ℓ).factorial : ℝ) := by
      have h2 : ∏ ℓ, g ℓ = (∏ ℓ, (if mult row ℓ = 0 then (1:ℝ) else 2)) * κ ^ (2 * k) *
          ∏ ℓ, ((mult row ℓ).factorial : ℝ) := by
        simp only [hg, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
      rw [h2]
      have hc : (univ.filter (fun ℓ => ¬ mult row ℓ = 0)).card ≤ k := by
        have : 2 * (univ.filter (fun ℓ => ¬ mult row ℓ = 0)).card ≤ ∑ ℓ, mult row ℓ := by
          calc 2 * (univ.filter (fun ℓ => ¬ mult row ℓ = 0)).card
              = ∑ ℓ ∈ univ.filter (fun ℓ => ¬ mult row ℓ = 0), 2 := by simp [mul_comm]
            _ ≤ ∑ ℓ ∈ univ.filter (fun ℓ => ¬ mult row ℓ = 0), mult row ℓ :=
                Finset.sum_le_sum fun ℓ hℓ => by
                  have := hsurv ℓ; have := (Finset.mem_filter.1 hℓ).2; omega
            _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        omega
      have h3 : ∏ ℓ, (if mult row ℓ = 0 then (1:ℝ) else 2) ≤ 2 ^ k := by
        rw [Finset.prod_ite]; simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
        exact pow_le_pow_right₀ (by norm_num) hc
      gcongr
    have hint : ∫ u, K (u, v) ∂(Measure.pi fun i : ↥I => ν i) =
        ∏ ℓ : ↥I, ∫ x, ∏ t ∈ univ.filter (fun t => rowI t = ℓ),
          ext h ℓ (col t) x (y (col t)) ∂(ν ℓ) := by
      simp only [hKuv]
      exact integral_fintype_prod_eq_prod (fun (ℓ : ↥I) x => ∏ t ∈ univ.filter (fun t => rowI t = ℓ),
        ext h ℓ (col t) x (y (col t))) (μ := fun i : ↥I => ν i)
    rw [hint, Finset.abs_prod]
    calc _ ≤ ∏ ℓ : ↥I, g ℓ := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun ℓ _ => hfac ℓ
      _ = _ := hprod
      _ ≤ _ := hgbd
  rw [h1, h2, h3]
  have := norm_integral_le_of_norm_le_const
    (μ := Measure.pi fun i : { i // i ∉ I } => ν i)
    (f := fun v => ∫ u, K (u, v) ∂(Measure.pi fun i : ↥I => ν i))
    (C := 2 ^ k * κ ^ (2 * k) * ∏ ℓ, ((mult row ℓ).factorial : ℝ))
    (hinner.mono fun v hv => by rw [Real.norm_eq_abs]; exact hv)
  simpa using this

-- SKETCH: group the words by their multiplicity vector `w ↦ mult w` (`Finset.sum_fiberwise`
-- / `Finset.sum_comp`).  The fibre over `a` has `Nat.multinomial univ a = (2k)! / ∏ a_ℓ!`
-- elements (`Nat.multinomial_spec`; the count of words with prescribed fibre sizes is
-- obtained by induction on `m` with `Finset.card_eq_of_equiv`, or via `Sym`/`Multiset`
-- `Multiset.card_filter`), so each fibre contributes exactly `(2k)!`.  The multiplicity
-- vectors that occur are exactly those counted by `A m k` (entries `≤ 2k`, sum `2k`, no `1`),
-- and `Finset.card_le_card_of_injOn` for the map into `Fin m → Fin (2k+1)`.
/-- Counting step inside eq. `eq:array-count-reduction` (6.11): "there are
`(2k)!/∏ a_ℓ!` row words with given multiplicities, so the factorials cancel":
`∑_{surviving row words} ∏_ℓ a_ℓ! ≤ (2k)! · A`. -/
theorem sum_factorial_mult (m k : ℕ) :
    ∑ w ∈ (univ : Finset (Fin (2 * k) → Fin m)).filter (fun w => ∀ ℓ, mult w ℓ ≠ 1),
        ∏ ℓ, ((mult w ℓ).factorial : ℝ)
      ≤ ((2 * k).factorial : ℝ) * A m k := by
  classical
  have fib : ∀ (a : Fin m → ℕ), ∑ ℓ, a ℓ = 2 * k →
      ((univ : Finset (Fin (2 * k) → Fin m)).filter (fun w => ∀ ℓ, mult w ℓ = a ℓ)).card
        = Nat.multinomial univ a := by
    intro a ha
    unfold mult
    generalize 2 * k = n at *
    have h := MvPolynomial.coeff_sum_X_pow_of_fintype (R := ℕ) (σ := Fin m)
      (Finsupp.equivFunOnFinite.symm a) n
    have hs : (Finsupp.equivFunOnFinite.symm a).sum (fun _ m => m) = n := by
      rw [Finsupp.sum_fintype _ _ (by simp)]; simpa using ha
    rw [if_pos hs] at h
    have hm : (Finsupp.equivFunOnFinite.symm a).multinomial = Nat.multinomial univ a := by
      rw [Finsupp.multinomial_eq_of_support_subset (s := univ) (by simp)]; rfl
    rw [hm, Nat.cast_id] at h
    rw [← h]
    have e : (∑ i : Fin m, (MvPolynomial.X i : MvPolynomial (Fin m) ℕ)) ^ n
        = ∑ w : Fin n → Fin m, ∏ v, MvPolynomial.X (w v) := by
      have := Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset (Fin m)))
        (fun _ j => (MvPolynomial.X j : MvPolynomial (Fin m) ℕ))
      simpa [Fintype.piFinset_univ] using this
    rw [e, MvPolynomial.coeff_sum]
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    have : ∏ v, (MvPolynomial.X (w v) : MvPolynomial (Fin m) ℕ)
        = MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun ℓ => #{v | w v = ℓ})) 1 := by
      rw [← Finset.prod_fiberwise_of_maps_to (s := univ) (t := univ) (g := w) (fun _ _ => mem_univ _),
        MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
      simp only [map_one, one_mul]
      refine Finset.prod_congr rfl fun ℓ _ => ?_
      rw [Finset.prod_congr rfl (fun v hv => by rw [(Finset.mem_filter.1 hv).2]), Finset.prod_const]
      rfl
    rw [this, MvPolynomial.coeff_monomial]
    simp [funext_iff, eq_comm]
  have hle : ∀ w : Fin (2 * k) → Fin m, ∀ ℓ, mult w ℓ < 2 * k + 1 := fun w ℓ =>
    Nat.lt_succ_of_le (by
      unfold mult
      simpa using Finset.card_le_univ (univ.filter (fun v : Fin (2 * k) => w v = ℓ)))
  have hsum : ∀ w : Fin (2 * k) → Fin m, ∑ ℓ, mult w ℓ = 2 * k := fun w => by
    unfold mult
    have := Finset.card_eq_sum_card_fiberwise (f := w) (s := (univ : Finset (Fin (2 * k)))) (t := univ)
      (fun _ _ => mem_univ _)
    simpa using this.symm
  let g : (Fin (2 * k) → Fin m) → (Fin m → Fin (2 * k + 1)) := fun w ℓ => ⟨mult w ℓ, hle w ℓ⟩
  rw [← Finset.sum_fiberwise_of_maps_to (s := (univ : Finset (Fin (2 * k) → Fin m)).filter
      (fun w => ∀ ℓ, mult w ℓ ≠ 1)) (t := univ.filter (fun a : Fin m → Fin (2 * k + 1) =>
        ∑ ℓ, (a ℓ : ℕ) = 2 * k ∧ ∀ ℓ, (a ℓ : ℕ) ≠ 1)) (g := g)]
  · have hA : ((2 * k).factorial : ℝ) * (A m k : ℝ) = ∑ a ∈ univ.filter (fun a : Fin m → Fin (2 * k + 1) =>
        ∑ ℓ, (a ℓ : ℕ) = 2 * k ∧ ∀ ℓ, (a ℓ : ℕ) ≠ 1), ((2 * k).factorial : ℝ) := by
      simp [A, mul_comm]
    rw [hA]
    refine Finset.sum_le_sum fun a ha => ?_
    obtain ⟨ha1, -⟩ := Finset.mem_filter.1 ha
    have hs : ∑ ℓ, ((a ℓ : ℕ)) = 2 * k := (Finset.mem_filter.1 ha).2.1
    have hc := fib (fun ℓ => (a ℓ : ℕ)) hs
    have hspec := Nat.multinomial_spec (univ : Finset (Fin m)) (fun ℓ => (a ℓ : ℕ))
    rw [hs] at hspec
    have hsub : ((univ : Finset (Fin (2 * k) → Fin m)).filter (fun w => ∀ ℓ, mult w ℓ ≠ 1)).filter
        (fun w => g w = a) ⊆ (univ : Finset (Fin (2 * k) → Fin m)).filter
          (fun w => ∀ ℓ, mult w ℓ = (a ℓ : ℕ)) := by
      intro w hw
      simp only [Finset.mem_filter, mem_univ, true_and] at hw ⊢
      intro ℓ
      rw [← hw.2]
    have hconst : ∀ w ∈ ((univ : Finset (Fin (2 * k) → Fin m)).filter (fun w => ∀ ℓ, mult w ℓ ≠ 1)).filter
        (fun w => g w = a), ∏ ℓ, ((mult w ℓ).factorial : ℝ) = ∏ ℓ, (((a ℓ : ℕ)).factorial : ℝ) := by
      intro w hw
      have := (Finset.mem_filter.1 hw).2
      refine Finset.prod_congr rfl fun ℓ _ => ?_
      rw [← this]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have h1 := Finset.card_le_card hsub
    rw [hc] at h1
    have h2 : ((Finset.card (((univ : Finset (Fin (2 * k) → Fin m)).filter (fun w => ∀ ℓ, mult w ℓ ≠ 1)).filter
        (fun w => g w = a)) : ℕ) : ℝ) ≤ (Nat.multinomial univ (fun ℓ => (a ℓ : ℕ)) : ℝ) := by exact_mod_cast h1
    have h3 : (∏ ℓ, (((a ℓ : ℕ)).factorial : ℝ)) * (Nat.multinomial univ (fun ℓ => (a ℓ : ℕ)) : ℝ)
        = ((2 * k).factorial : ℝ) := by exact_mod_cast hspec
    calc _ ≤ (Nat.multinomial univ (fun ℓ => (a ℓ : ℕ)) : ℝ) * ∏ ℓ, (((a ℓ : ℕ)).factorial : ℝ) := by
          gcongr
      _ = _ := by rw [← h3, mul_comm]
  · intro w hw
    simp only [Finset.mem_filter, mem_univ, true_and] at hw ⊢
    exact ⟨hsum w, fun ℓ => hw ℓ⟩

-- SKETCH (6.11): `|D_I|^(2k) = D_I^(2k)` (`pow_abs_two_mul`); expand
-- `D_I = ∑_{p ∈ I ×ˢ Iᶜ} f p` to the `2k`-th power as a sum over words
-- `Fin (2k) → I ×ˢ Iᶜ` (`Finset.sum_pow'`, `Finset.prod_univ_sum`), i.e. over pairs
-- `(row, col)` with `row v ∈ I`, `col v ∉ I`; so `∫ D_I^(2k) = ∑_{(row,col)} ∫ word`
-- (`integral_finset_sum`, integrability by `integrable_D_pow` and `integrable_word`).  Terms with a multiplicity-one
-- label vanish (`vanishing_word`); the others are bounded by `word_moment`
-- (`Finset.abs_sum_le_sum_abs`).  Sum over surviving `col` first (at most `B m k` of them,
-- `Finset.card_le_card` since columns in `Iᶜ` are a subset of all surviving words), then
-- over surviving `row` with `sum_factorial_mult`.
/-- Eq. `eq:array-count-reduction` (6.11): `𝔼|D_I|^{2k} ≤ 2^k κ^{2k} (2k)! A B_k`. -/
theorem count_reduction (H : Hyp μ ν Y h κ) (k : ℕ) (I : Finset (Fin m)) :
    ∫ ω, |D h Y I ω| ^ (2 * k) ∂μ
      ≤ 2 ^ k * κ ^ (2 * k) * ((2 * k).factorial : ℝ) * (A m k * B m k : ℕ) := by
  sorry

-- SKETCH (D5, case m < 2k): `A ≤ #{weak compositions of 2k into m parts}
-- = (2k+m-1).choose (m-1) ≤ 2^(2k+m-1) ≤ 2^(4k)` (`Nat.choose_le_two_pow`,
-- `Nat.pow_le_pow_right`; the composition count via `Finset.card_le_card_of_injOn` into
-- `Finset.Nat.antidiagonalTuple m (2k)` and `Finset.Nat.card_antidiagonalTuple` /
-- `Nat.card_multichoose`), and `B ≤ #(Fin (2k) → Fin m) = m^(2k)` (`Finset.card_filter_le`,
-- `Fintype.card_fun`, `Fintype.card_fin`).  Cast with `Nat.cast_le`, `Nat.cast_mul`.
/-- Eq. `eq:array-combinatorial-bound` (6.12), small-`m` case: if `m < 2k` then
`A B_k ≤ 2^{4k} m^{2k}`. -/
theorem count_small (m k : ℕ) (hmk : m < 2 * k) :
    ((A m k * B m k : ℕ) : ℝ) ≤ 2 ^ (4 * k) * (m : ℝ) ^ (2 * k) := by
  have hA : A m k ≤ 2 ^ (4 * k) := by
    have h1 : A m k ≤ ((univ : Finset (Fin m)).finsuppAntidiag (2 * k)).card := by
      unfold A
      apply Finset.card_le_card_of_injOn
        (fun a => Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ)))
      · intro a ha
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha
        simp [Finset.mem_finsuppAntidiag, ha.1]
      · intro a _ b _ hab
        funext i
        have := DFunLike.congr_fun hab i
        simpa [Fin.ext_iff] using this
    rw [Finset.card_finsuppAntidiag_nat_eq_choose] at h1
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    refine h1.trans ((Nat.choose_le_two_pow _ _).trans ?_)
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hB : B m k ≤ m ^ (2 * k) := by
    calc B m k ≤ Fintype.card (Fin (2 * k) → Fin m) := Finset.card_filter_le _ _
      _ = m ^ (2 * k) := by simp
  rw [Nat.cast_mul]
  have : ((A m k : ℕ) : ℝ) ≤ 2 ^ (4 * k) := by exact_mod_cast hA
  have : ((B m k : ℕ) : ℝ) ≤ (m : ℝ) ^ (2 * k) := by exact_mod_cast hB
  gcongr

-- SKETCH (D5, case m ≥ 2k): the active labels of a surviving vector/word form a set `T` of
-- size `n ≤ k`; there are `∑_{n ≤ k} m.choose n ≤ (e m / k)^k` such sets
-- (`Nat.choose_le_pow_div`, `Nat.factorial`-bound `k^k / k! ≤ e^k` from
-- `Real.pow_div_factorial_le_exp` or `Real.add_one_le_exp` iterated).  Given `T`, a positive
-- multiplicity vector on `T` summing to `2k` is a composition of `2k` into `n` parts:
-- at most `(2k-1).choose (n-1) ≤ 2^(2k) = 4^k` (`Nat.choose_le_two_pow`); and a word with
-- label set `T` is a function `Fin (2k) → T`: at most `n^(2k) ≤ k^(2k)`.  Multiply:
-- `A ≤ 4^k (em/k)^k`, `B ≤ k^(2k) (em/k)^k`, so `A B ≤ (4e²)^k m^(2k)`.
/-- Eq. `eq:array-combinatorial-bound` (6.12), large-`m` case: if `m ≥ 2k` then
`A ≤ 4^k (em/k)^k`, `B_k ≤ k^{2k} (em/k)^k`, hence `A B_k ≤ (4e²)^k m^{2k}`. -/
theorem count_large (m k : ℕ) (hmk : 2 * k ≤ m) :
    ((A m k * B m k : ℕ) : ℝ) ≤ (4 * Real.exp 1 ^ 2) ^ k * (m : ℝ) ^ (2 * k) := by
  have tset :
      (((univ : Finset (Finset (Fin m))).filter (fun T => T.card ≤ k)).card : ℝ) * (k:ℝ)^k
        ≤ (Real.exp 1 * m)^k := by
    have h1 : ((univ : Finset (Finset (Fin m))).filter (fun T => T.card ≤ k)).card
        ≤ ∑ n ∈ range (k+1), m.choose n := by
      calc _ ≤ ((range (k+1)).biUnion (fun n => powersetCard n (univ : Finset (Fin m)))).card := by
            apply card_le_card
            intro T hT
            simp only [mem_filter, mem_univ, true_and] at hT
            simp only [mem_biUnion, mem_range, mem_powersetCard]
            exact ⟨T.card, by omega, subset_univ _, rfl⟩
        _ ≤ ∑ n ∈ range (k+1), (powersetCard n (univ : Finset (Fin m))).card := card_biUnion_le
        _ = _ := by simp [card_powersetCard]
    have h2 : (∑ n ∈ range (k+1), (m.choose n : ℝ)) * (k:ℝ)^k
        ≤ (m:ℝ)^k * ∑ n ∈ range (k+1), (k:ℝ)^n / n ! := by
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hn' : n ≤ k := by simpa [Nat.lt_succ_iff] using hn
      have hc : (m.choose n : ℝ) ≤ (m:ℝ)^n / n ! := Nat.choose_le_pow_div n m
      have hkm : (k:ℝ) ≤ m := by exact_mod_cast (by omega : k ≤ m)
      have hp : (k:ℝ)^(k-n) ≤ (m:ℝ)^(k-n) := pow_le_pow_left₀ (by positivity) hkm _
      have hf : (0:ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
      calc (m.choose n : ℝ) * (k:ℝ)^k ≤ ((m:ℝ)^n / n !) * (k:ℝ)^k := by gcongr
        _ = ((m:ℝ)^n * (k:ℝ)^n * (k:ℝ)^(k-n)) / n ! := by
            have hk : (k:ℝ)^k = (k:ℝ)^n * (k:ℝ)^(k-n) := by
              rw [← pow_add, Nat.add_sub_cancel' hn']
            rw [hk]; ring
        _ ≤ ((m:ℝ)^n * (k:ℝ)^n * (m:ℝ)^(k-n)) / n ! := by gcongr
        _ = (m:ℝ)^k * ((k:ℝ)^n / n !) := by
            have : (m:ℝ)^k = (m:ℝ)^n * (m:ℝ)^(k-n) := by
              rw [← pow_add, Nat.add_sub_cancel' hn']
            rw [this]; ring
    have h3 := Real.sum_le_exp_of_nonneg (x := (k:ℝ)) (by positivity) (k+1)
    calc _ ≤ ((∑ n ∈ range (k+1), m.choose n : ℕ) : ℝ) * (k:ℝ)^k := by
          gcongr
      _ = (∑ n ∈ range (k+1), (m.choose n : ℝ)) * (k:ℝ)^k := by push_cast; rfl
      _ ≤ _ := h2
      _ ≤ (m:ℝ)^k * Real.exp k := by gcongr
      _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]; simp [mul_comm]
  have bbound :
      B m k ≤ ((univ : Finset (Finset (Fin m))).filter (fun T => T.card ≤ k)).card * k^(2*k) := by
    unfold B
    calc _ ≤ (((univ : Finset (Finset (Fin m))).filter (fun T => T.card ≤ k)).biUnion
          (fun T => Fintype.piFinset (fun _ : Fin (2*k) => T))).card := by
          apply card_le_card
          intro w hw
          simp only [mem_filter, mem_univ, true_and] at hw
          simp only [mem_biUnion, mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
          refine ⟨univ.image w, ?_, fun v => mem_image_of_mem _ (mem_univ _)⟩
          have hsum : ∑ ℓ ∈ univ.image w, mult w ℓ = 2 * k := by
            unfold mult
            have := Finset.card_eq_sum_card_image w (univ : Finset (Fin (2*k)))
            simpa using this.symm
          have hge : ∀ ℓ ∈ univ.image w, 2 ≤ mult w ℓ := by
            intro ℓ hℓ
            have h1 := hw ℓ
            obtain ⟨v, -, hv⟩ := mem_image.1 hℓ
            have : 0 < mult w ℓ := by
              unfold mult
              exact card_pos.2 ⟨v, by simp [hv]⟩
            omega
          have := Finset.card_nsmul_le_sum (univ.image w) (mult w) 2 hge
          have h' : (univ.image w).card * 2 ≤ ∑ ℓ ∈ univ.image w, mult w ℓ := by simpa using this
          omega
      _ ≤ ∑ T ∈ ((univ : Finset (Finset (Fin m))).filter (fun T => T.card ≤ k)),
            (Fintype.piFinset (fun _ : Fin (2*k) => T)).card := card_biUnion_le
      _ ≤ ∑ T ∈ ((univ : Finset (Finset (Fin m))).filter (fun T => T.card ≤ k)), k^(2*k) := by
          apply sum_le_sum
          intro T hT
          simp only [mem_filter, mem_univ, true_and] at hT
          rw [Fintype.card_piFinset]
          simp only [prod_const, card_univ, Fintype.card_fin]
          exact Nat.pow_le_pow_left hT _
      _ = _ := by simp
  have abound :
      A m k ≤ ((univ : Finset (Finset (Fin m))).filter (fun T => T.card ≤ k)).card * 4^k := by
    unfold A
    set S := (univ.filter (fun a : Fin m → Fin (2 * k + 1) =>
      ∑ ℓ, (a ℓ : ℕ) = 2 * k ∧ ∀ ℓ, (a ℓ : ℕ) ≠ 1)) with hS
    have hmem : ∀ a ∈ S, ∑ ℓ, (a ℓ : ℕ) = 2 * k ∧ ∀ ℓ, (a ℓ : ℕ) ≠ 1 := by
      intro a ha; simpa [hS] using ha
    have hsupp : ∀ a ∈ S, (univ.filter (fun ℓ => (a ℓ : ℕ) ≠ 0)).card ≤ k := by
      intro a ha
      obtain ⟨h1, h2⟩ := hmem a ha
      have hge : ∀ ℓ ∈ univ.filter (fun ℓ => (a ℓ : ℕ) ≠ 0), 2 ≤ (a ℓ : ℕ) := by
        intro ℓ hℓ
        have := (mem_filter.1 hℓ).2
        have := h2 ℓ
        omega
      have := Finset.card_nsmul_le_sum _ (fun ℓ => (a ℓ : ℕ)) 2 hge
      have h3 : ∑ ℓ ∈ univ.filter (fun ℓ => (a ℓ : ℕ) ≠ 0), (a ℓ : ℕ) = 2 * k := by
        rw [Finset.sum_filter_ne_zero]; exact h1
      simp only [smul_eq_mul] at this
      omega
    calc S.card ≤ (((univ : Finset (Finset (Fin m))).filter (fun T => T.card ≤ k)).biUnion
          (fun T => S.filter (fun a => univ.filter (fun ℓ => (a ℓ : ℕ) ≠ 0) = T))).card := by
          apply card_le_card
          intro a ha
          simp only [mem_biUnion, mem_filter, mem_univ, true_and]
          exact ⟨_, hsupp a ha, ha, rfl⟩
      _ ≤ ∑ T ∈ ((univ : Finset (Finset (Fin m))).filter (fun T => T.card ≤ k)),
            (S.filter (fun a => univ.filter (fun ℓ => (a ℓ : ℕ) ≠ 0) = T)).card := card_biUnion_le
      _ ≤ ∑ T ∈ ((univ : Finset (Finset (Fin m))).filter (fun T => T.card ≤ k)), 4^k := by
          apply sum_le_sum
          intro T hT
          simp only [mem_filter, mem_univ, true_and] at hT
          let f : (Fin m → Fin (2 * k + 1)) → (Fin m →₀ ℕ) := fun a =>
            Finsupp.equivFunOnFinite.symm (fun ℓ => if ℓ ∈ T then (a ℓ : ℕ) - 2 else 0)
          have hfv : ∀ a ℓ, f a ℓ = if ℓ ∈ T then (a ℓ : ℕ) - 2 else 0 := fun _ _ => rfl
          have hf : ∀ a ∈ S.filter (fun a => univ.filter (fun ℓ => (a ℓ : ℕ) ≠ 0) = T),
              f a ∈ T.finsuppAntidiag (2 * k - 2 * T.card) := by
            intro a ha
            simp only [mem_filter] at ha
            obtain ⟨ha, hT'⟩ := ha
            obtain ⟨h1, h2⟩ := hmem a ha
            have hge : ∀ ℓ ∈ T, 2 ≤ (a ℓ : ℕ) := by
              intro ℓ hℓ
              rw [← hT'] at hℓ
              have := (mem_filter.1 hℓ).2
              have := h2 ℓ
              omega
            have h3 : ∑ ℓ ∈ T, (a ℓ : ℕ) = 2 * k := by
              rw [← hT', Finset.sum_filter_ne_zero]; exact h1
            rw [mem_finsuppAntidiag]
            constructor
            · have : ∑ ℓ ∈ T, ((a ℓ : ℕ) - 2) + ∑ ℓ ∈ T, 2 = ∑ ℓ ∈ T, (a ℓ : ℕ) := by
                rw [← sum_add_distrib]
                exact sum_congr rfl (fun ℓ hℓ => Nat.sub_add_cancel (hge ℓ hℓ))
              simp only [sum_const, smul_eq_mul] at this
              rw [sum_congr rfl (fun ℓ hℓ => (hfv a ℓ).trans (if_pos hℓ))]
              omega
            · intro ℓ hℓ
              by_contra hn
              rw [Finsupp.mem_support_iff, hfv, if_neg hn] at hℓ
              exact hℓ rfl
          calc _ ≤ (T.finsuppAntidiag (2 * k - 2 * T.card)).card := by
                apply card_le_card_of_injOn f hf
                intro a ha b hb hab
                simp only [coe_filter, Set.mem_setOf_eq] at ha hb
                obtain ⟨ha, hTa⟩ := ha
                obtain ⟨hb, hTb⟩ := hb
                obtain ⟨h1, h2⟩ := hmem a ha
                obtain ⟨h1', h2'⟩ := hmem b hb
                funext ℓ
                have hfa := DFunLike.congr_fun hab ℓ
                rw [hfv, hfv] at hfa
                by_cases hℓ : ℓ ∈ T
                · rw [if_pos hℓ, if_pos hℓ] at hfa
                  have ga : 2 ≤ (a ℓ : ℕ) := by
                    rw [← hTa] at hℓ
                    have := (mem_filter.1 hℓ).2
                    have := h2 ℓ
                    omega
                  have gb : 2 ≤ (b ℓ : ℕ) := by
                    rw [← hTb] at hℓ
                    have := (mem_filter.1 hℓ).2
                    have := h2' ℓ
                    omega
                  apply Fin.ext; omega
                · have ea : (a ℓ : ℕ) = 0 := by
                    by_contra h
                    exact hℓ (hTa ▸ mem_filter.2 ⟨mem_univ _, h⟩)
                  have eb : (b ℓ : ℕ) = 0 := by
                    by_contra h
                    exact hℓ (hTb ▸ mem_filter.2 ⟨mem_univ _, h⟩)
                  apply Fin.ext; omega
            _ ≤ 4^k := by
                rw [card_finsuppAntidiag_nat_eq_choose]
                calc _ ≤ 2 ^ (T.card + (2 * k - 2 * T.card) - 1) := Nat.choose_le_two_pow _ _
                  _ ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
                  _ = 4^k := by rw [pow_mul]; norm_num
      _ = _ := by simp
  have hT0 : (0:ℝ) ≤ (((univ : Finset (Finset (Fin m))).filter (fun T => T.card ≤ k)).card : ℝ) := by positivity
  have hAB : ((A m k * B m k : ℕ) : ℝ) ≤ 4 ^ k * ((((univ : Finset (Finset (Fin m))).filter (fun T => T.card ≤ k)).card : ℝ) * (k:ℝ)^k) ^ 2 := by
    have h1 := abound
    have h2 := bbound
    have h3 : A m k * B m k ≤ (((univ : Finset (Finset (Fin m))).filter (fun T => T.card ≤ k)).card * 4^k) * (((univ : Finset (Finset (Fin m))).filter (fun T => T.card ≤ k)).card * k^(2*k)) := Nat.mul_le_mul h1 h2
    have h4 : ((A m k * B m k : ℕ) : ℝ) ≤ ((((univ : Finset (Finset (Fin m))).filter (fun T => T.card ≤ k)).card * 4^k) * (((univ : Finset (Finset (Fin m))).filter (fun T => T.card ≤ k)).card * k^(2*k)) : ℕ) := by exact_mod_cast h3
    refine h4.trans (le_of_eq ?_)
    push_cast
    rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
    ring
  calc _ ≤ _ := hAB
    _ ≤ 4 ^ k * ((Real.exp 1 * m)^k) ^ 2 := by gcongr
    _ = _ := by
      rw [← pow_mul, mul_comm k 2, pow_mul, mul_pow, mul_pow]
      ring


-- SKETCH (D5): `rcases lt_or_ge m (2 * k)`; in the first case use `count_small` and
-- `2^(4k) = 16^k ≤ (4 e²)^k` (`pow_le_pow_left₀`, `Real.exp_one_gt_d9`, `nlinarith`);
-- in the second, `count_large`.
/-- Eq. `eq:array-combinatorial-bound` (6.12), unified: `A B_k ≤ (4e²)^k m^{2k}` for all
`m, k`. -/
theorem count_bound (m k : ℕ) :
    ((A m k * B m k : ℕ) : ℝ) ≤ (4 * Real.exp 1 ^ 2) ^ k * (m : ℝ) ^ (2 * k) := by
  sorry

-- SKETCH (D6): chain `random_split`, `count_reduction` (for every `I`; `Finset.sum_le_sum`,
-- `Finset.sum_const`, `Fintype.card_finset`, `Finset.card_univ`, cancel `2^m`), and
-- `count_bound`: `𝔼|S|^(2k) ≤ 2^(2k) 2^k κ^(2k) (2k)! (4e²)^k m^(2k) = (32 e²)^k (κ m)^(2k) (2k)!`.
-- Conclude with `32 e² ≤ 256 = Cu^2` (`Real.exp_one_lt_d9`, `nlinarith`), `pow_mul`,
-- `mul_pow`, `pow_le_pow_left₀`.
/-- First half of eq. `eq:canonical-array-exponential` (6.3), the even-moment bound:
`𝔼|S|^{2k} ≤ (C_u κ m)^{2k} (2k)!` for every `k ≥ 1`. -/
theorem moment_bound (H : Hyp μ ν Y h κ) (k : ℕ) (hk : 1 ≤ k) :
    ∫ ω, |S h Y ω| ^ (2 * k) ∂μ ≤ (Cu * κ * m) ^ (2 * k) * ((2 * k).factorial : ℝ) := by
  sorry

-- SKETCH (D7, 6.13): pointwise `exp x ≤ 2 cosh x` (`Real.cosh_eq`, `Real.exp_pos`) and
-- `cosh x = ∑' k, x^(2k)/(2k)!` (`Real.hasSum_cosh`), so with `x = θ S/m`,
-- `exp (θ S/m) ≤ 2 ∑' k, |θ|^(2k) |S|^(2k) / (m^(2k) (2k)!)` (`pow_abs_two_mul`).
-- Interchange sum and integral for the nonnegative series (Tonelli: `lintegral_tsum`, or
-- `integral_tsum` with summability of the `L¹` norms), bound term `k ≥ 1` by `moment_bound`
-- (`div_le_iff₀`, `m ≥ 1`) and term `k = 0` by `integral_const`/`measure_univ`, to get
-- `≤ 2 ∑' k, (Cu κ |θ|)^(2k) = 2 / (1 - (Cu κ |θ|)^2)` (`tsum_geometric_of_lt_one` with
-- ratio `(Cu κ |θ|)^2 < 1`, `pow_mul`, `one_div`).
/-- Second half of eq. `eq:canonical-array-exponential` (6.3), via
eq. `eq:array-exponential-series` (6.13): `𝔼 e^{θ S/m} ≤ 2/(1-(C_u κ |θ|)^2)` whenever
`C_u κ |θ| < 1`. -/
theorem exp_bound (H : Hyp μ ν Y h κ) (hm : 1 ≤ m) (θ : ℝ) (hθ : Cu * κ * |θ| < 1) :
    ∫ ω, Real.exp (θ * S h Y ω / m) ∂μ ≤ 2 / (1 - (Cu * κ * |θ|) ^ 2) := by
  sorry

end LogGas.Decoupling
