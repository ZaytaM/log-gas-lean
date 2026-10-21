import LogGas.Decoupling

/-!
# Phase 2 — Lemma 6.1 (`lem:canonical-array-exponential`), grouped bound (6.4)

Source: `notes/sec6-lemma61.tex`, last paragraph of the proof.  Phase notes: `notes/phase2.md`.

Setting.  As in `LogGas.Decoupling`: `(Ω, μ)` a probability space, `Y : Fin m → Ω → E`
independent with laws `ν i`, kernels `h : Fin m → Fin m → E → E → ℝ` satisfying `Hyp`.
The `m` variables are partitioned into `M` groups by `grp : Fin m → Fin M`, each group has
at most `m*` members, and the interaction pattern between groups is a simple graph
`G : SimpleGraph (Fin M)` of maximum degree `≤ K - 1`: kernels between variables of distinct
non-adjacent groups vanish.

Statements (phase notes G1–G3):
* G1 `greedy_edge_coloring` — proper edge coloring with `≤ 2K-1` colors;
* G2 `blocks_indep`, `class_mgf` — block sums on disjoint variable sets are independent and
  the exponential moment of a class factors;
* G3 `grouped_exp_bound` — eq. `eq:canonical-grouped-exponential` (6.4), via
  eq. `eq:array-grouped-holder` (6.14).

Auxiliary statements: restriction/reindexing of `Hyp` (`Hyp.restrict`, `Hyp.reindex`), the
one-block bound with `m_b` in place of `m` (`block_exp_bound`, `block_factor`), the class
decomposition `class_decomposition`, and finite Hölder `holder_classes`.

The standing hypotheses H1/H2 of `notes/hypotheses.md` are not needed in this phase.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Finset Function
open scoped BigOperators ENNReal

namespace LogGas.Grouped

open LogGas.Decoupling

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-! ### G1: greedy edge coloring -/

-- SKETCH (G1): induction on the edge set (`Finset.induction_on` over `G.edgeFinset`, or
-- strong induction on `#G.edgeFinset` deleting one edge with `SimpleGraph.deleteEdges`).
-- An edge `s(a,b)` meets at most `(K-1-1) + (K-1-1) = 2K-4` other edges
-- (`SimpleGraph.degree`, `SimpleGraph.card_neighborFinset_eq_degree`), so among `2K-1`
-- colors one is free (`Finset.exists_mem_notMem_of_card_lt_card`, `Finset.card_image_le`).
-- Equivalently: the line graph `G.lineGraph` has max degree `≤ 2K-4` and is greedily
-- `(2K-1)`-colorable (`SimpleGraph.Colorable`, `lineGraph_adj_iff_exists`).  Extend the
-- resulting `G.edgeSet → Fin (2K-1)` to all pairs by a default value (`Fin.mk 0`), symmetric
-- via `Sym2.eq_swap`.
/-- Greedy edge coloring used for eq. `eq:canonical-grouped-exponential` (6.4): a finite
simple graph with all degrees `≤ K - 1` admits a symmetric coloring of its vertex pairs with
`2K - 1` colors such that two distinct edges sharing a vertex receive different colors. -/
theorem greedy_edge_coloring {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (K : ℕ) (hK : 1 ≤ K) (hdeg : ∀ v, G.degree v ≤ K - 1) :
    ∃ c : V → V → Fin (2 * K - 1), (∀ a b, c a b = c b a) ∧
      ∀ a b b', G.Adj a b → G.Adj a b' → b ≠ b' → c a b ≠ c a b' := by
  have key : ∀ s : Finset (Sym2 V), ∃ f : Sym2 V → Fin (2 * K - 1),
      ∀ e ∈ s, ∀ e' ∈ s, e ∈ G.edgeSet → e' ∈ G.edgeSet → e ≠ e' →
        (∃ v, v ∈ e ∧ v ∈ e') → f e ≠ f e' := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => ⟨0, by omega⟩, by simp⟩
    | insert a s has ih =>
      obtain ⟨f, hf⟩ := ih
      by_cases ha : a ∈ G.edgeSet
      · induction a using Sym2.ind with
        | _ u v =>
        have huv : G.Adj u v := ha
        set B : Finset (Sym2 V) :=
          ((G.incidenceFinset u ∪ G.incidenceFinset v).filter (· ∈ s)) with hB
        have hcard : (B.image f).card < 2 * K - 1 := by
          calc (B.image f).card ≤ B.card := Finset.card_image_le
            _ ≤ (G.incidenceFinset u ∪ G.incidenceFinset v).card := Finset.card_filter_le _ _
            _ ≤ (G.incidenceFinset u).card + (G.incidenceFinset v).card :=
                Finset.card_union_le _ _
            _ ≤ (K - 1) + (K - 1) := by
                rw [G.card_incidenceFinset_eq_degree, G.card_incidenceFinset_eq_degree]
                exact Nat.add_le_add (hdeg u) (hdeg v)
            _ < 2 * K - 1 := by omega
        obtain ⟨col, hcol⟩ : ∃ col : Fin (2 * K - 1), col ∉ B.image f := by
          by_contra hcon
          push_neg at hcon
          have : (Finset.univ : Finset (Fin (2 * K - 1))) ⊆ B.image f := fun x _ => hcon x
          have := Finset.card_le_card this
          simp at this
          omega
        refine ⟨Function.update f s(u, v) col, ?_⟩
        intro e he e' he' hE hE' hne ⟨w, hw, hw'⟩
        have key2 : ∀ x ∈ s, x ∈ G.edgeSet → (∃ w, w ∈ s(u, v) ∧ w ∈ x) →
            col ≠ f x := by
          intro x hx hxe ⟨w, hw, hwx⟩ hceq
          apply hcol
          rw [Finset.mem_image]
          refine ⟨x, ?_, hceq.symm⟩
          rw [hB, Finset.mem_filter, Finset.mem_union]
          refine ⟨?_, hx⟩
          rw [Sym2.mem_iff] at hw
          rcases hw with rfl | rfl
          · left; rw [SimpleGraph.mem_incidenceFinset]; exact ⟨hxe, hwx⟩
          · right; rw [SimpleGraph.mem_incidenceFinset]; exact ⟨hxe, hwx⟩
        rw [Finset.mem_insert] at he he'
        rcases he with rfl | he <;> rcases he' with rfl | he'
        · exact absurd rfl hne
        · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact has he')]
          exact key2 _ he' hE' ⟨w, hw, hw'⟩
        · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact has he)]
          exact (key2 _ he hE ⟨w, hw', hw⟩).symm
        · rw [Function.update_of_ne (by rintro rfl; exact has he),
            Function.update_of_ne (by rintro rfl; exact has he')]
          exact hf e he e' he' hE hE' hne ⟨w, hw, hw'⟩
      · refine ⟨f, ?_⟩
        intro e he e' he' hE hE' hne hw
        rw [Finset.mem_insert] at he he'
        rcases he with rfl | he
        · exact absurd hE ha
        rcases he' with rfl | he'
        · exact absurd hE' ha
        exact hf e he e' he' hE hE' hne hw
  obtain ⟨f, hf⟩ := key Finset.univ
  refine ⟨fun a b => f s(a, b), fun a b => by simp only [Sym2.eq_swap (a := a)], ?_⟩
  intro a b b' hab hab' hbb
  refine hf _ (Finset.mem_univ _) _ (Finset.mem_univ _) hab hab' ?_ ⟨a, by simp, by simp⟩
  intro h; exact hbb (Sym2.congr_right.mp h)

/-! ### Restriction and reindexing of the one-block hypotheses -/

section Blocks

variable {m : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Fin m → Measure E}
  [∀ i, IsProbabilityMeasure (ν i)] {Y : Fin m → Ω → E}
  {h : Fin m → Fin m → E → E → ℝ} {κ : ℝ}

/-- The kernel `h` with all pairs `(i, j)` not satisfying `p` replaced by the zero kernel
("zero kernels are allowed"). -/
def restrict (h : Fin m → Fin m → E → E → ℝ) (p : Fin m → Fin m → Prop)
    [∀ i j, Decidable (p i j)] (i j : Fin m) (x y : E) : ℝ :=
  if p i j then h i j x y else 0

-- SKETCH: every field of `Hyp` is either independent of `h` (copy from `H`) or is checked
-- by `unfold restrict; split_ifs`: the `then` branch is the corresponding field of `H`, the
-- `else` branch is the zero kernel (`measurable_const`, `integral_zero`, `abs_zero`,
-- `zero_pow`, and `0 ≤ 2 κ^p p!` by `positivity` using `H.κ_pos`).
/-- Zero kernels are allowed in Lemma 6.1: restricting the kernels to a set of pairs
preserves the hypotheses (6.1), (6.2). -/
theorem Hyp.restrict (H : Hyp μ ν Y h κ) (p : Fin m → Fin m → Prop)
    [∀ i j, Decidable (p i j)] : Hyp μ ν Y (restrict h p) κ := by
  have hz : ∀ (q : ℕ) (hq : 1 ≤ q), (0:ℝ) ≤ 2 * κ ^ q * (q.factorial : ℝ) := fun q _ => by
    have := H.κ_pos
    positivity
  refine { H with
    h_meas := ?_
    h_int := ?_
    centered_left := ?_
    centered_right := ?_
    moment_left := ?_
    moment_right := ?_ }
  · intro i j
    unfold LogGas.Grouped.restrict
    split_ifs
    · exact H.h_meas i j
    · exact measurable_const
  · intro i j q hq
    unfold LogGas.Grouped.restrict
    split_ifs
    · exact H.h_int i j q hq
    · simpa [zero_pow (by omega : q ≠ 0)] using
        (integrable_zero : Integrable (fun _ : E × E => (0 : ℝ)) ((ν i).prod (ν j)))
  · intro i j hij
    unfold LogGas.Grouped.restrict
    split_ifs
    · exact H.centered_left i j hij
    · simp
  · intro i j hij
    unfold LogGas.Grouped.restrict
    split_ifs
    · exact H.centered_right i j hij
    · simp
  · intro i j hij q hq
    unfold LogGas.Grouped.restrict
    split_ifs
    · exact H.moment_left i j hij q hq
    · filter_upwards [] with y
      simpa [zero_pow (by omega : q ≠ 0)] using hz q hq
  · intro i j hij q hq
    unfold LogGas.Grouped.restrict
    split_ifs
    · exact H.moment_right i j hij q hq
    · filter_upwards [] with x
      simpa [zero_pow (by omega : q ≠ 0)] using hz q hq

-- SKETCH: `Y_indep` is `H.Y_indep.precomp e.injective`; `Y_law`, `Y_meas`, `h_meas`, `h_int`
-- are instances of the fields of `H` at `e a`, `e b`.  For the `i < j` fields use
-- `e.strictMono` / `OrderEmbedding.lt_iff_lt` to transport `a < b` to `e a < e b`.
/-- Reindexing along a strictly monotone injection `e : Fin n ↪o Fin m` (the increasing
enumeration of a block of variables) preserves the hypotheses of Lemma 6.1. -/
theorem Hyp.reindex (H : Hyp μ ν Y h κ) {n : ℕ} (e : Fin n ↪o Fin m) :
    Hyp μ (fun a => ν (e a)) (fun a => Y (e a)) (fun a b => h (e a) (e b)) κ := by
  exact { κ_pos := H.κ_pos
          Y_meas := fun a => H.Y_meas (e a)
          Y_indep := H.Y_indep.precomp e.injective
          Y_law := fun a => H.Y_law (e a)
          h_meas := fun a b => H.h_meas (e a) (e b)
          h_int := fun a b q hq => H.h_int (e a) (e b) q hq
          centered_left := fun a b hab => H.centered_left (e a) (e b) (e.strictMono hab)
          centered_right := fun a b hab => H.centered_right (e a) (e b) (e.strictMono hab)
          moment_left := fun a b hab q hq => H.moment_left (e a) (e b) (e.strictMono hab) q hq
          moment_right := fun a b hab q hq => H.moment_right (e a) (e b) (e.strictMono hab) q hq }

-- SKETCH: unfold `S`; on the right drop all terms with `i ∉ T` or `j ∉ T` (`hvan`,
-- `Finset.sum_subset`, `Finset.sum_eq_zero`), leaving `∑ i ∈ T, ∑ j ∈ T.filter (i < ·), …`.
-- Reindex with the order isomorphism `Fin n ≃o T` underlying `T.orderEmbOfFin hT`
-- (`Finset.orderEmbOfFin_mem`, `Finset.range_orderEmbOfFin`, `Finset.sum_nbij` or
-- `Finset.sum_map`), using `OrderEmbedding.lt_iff_lt` to match `a < b` with `e a < e b`
-- (`Finset.mem_Ioi`).
omit [MeasurableSpace E] in
/-- A kernel supported on pairs of variables in `T` has the same `S` whether computed on all
`m` variables or on the `#T` variables of `T`, enumerated increasingly. -/
theorem S_reindex (h : Fin m → Fin m → E → E → ℝ) (Y : Fin m → Ω → E) {n : ℕ}
    (T : Finset (Fin m)) (hT : T.card = n)
    (hvan : ∀ i j, (i ∉ T ∨ j ∉ T) → ∀ x y, h i j x y = 0) (ω : Ω) :
    S (fun a b => h (T.orderEmbOfFin hT a) (T.orderEmbOfFin hT b))
        (fun a => Y (T.orderEmbOfFin hT a)) ω = S h Y ω := by
  set e := T.orderEmbOfFin hT with he
  have hmem : ∀ a, e a ∈ T := fun a => Finset.orderEmbOfFin_mem T hT a
  have hsurj : ∀ i ∈ T, ∃ a, e a = i := by
    intro i hi
    have : i ∈ Set.range e := by
      rw [he, Finset.range_orderEmbOfFin]; exact hi
    exact this
  unfold S
  have h1 : ∀ i, ∑ j ∈ Ioi i, h i j (Y i ω) (Y j ω)
      = ∑ j ∈ T.filter (i < ·), if i ∈ T then h i j (Y i ω) (Y j ω) else 0 := by
    intro i
    by_cases hi : i ∈ T
    · simp only [hi, if_true]
      symm
      apply Finset.sum_subset
      · intro j hj; simp at hj ⊢; exact hj.2
      · intro j hj hj'
        simp at hj hj'
        exact hvan i j (Or.inr (fun hjT => absurd (hj' hjT) (not_le.mpr hj))) _ _
    · simp only [hi, if_false, Finset.sum_const_zero]
      exact Finset.sum_eq_zero fun j _ => hvan i j (Or.inl hi) _ _
  simp_rw [h1]
  rw [← Finset.sum_subset (Finset.subset_univ T)]
  · apply Finset.sum_bij (fun a _ => e a)
    · intro a _; exact Finset.mem_coe.mp (hmem a) |> fun h => h
    · intro a _ b _ hab; exact e.injective hab
    · intro i hi
      obtain ⟨a, ha⟩ := hsurj i hi
      exact ⟨a, Finset.mem_univ _, ha⟩
    · intro a _
      simp only [hmem a, if_true]
      apply Finset.sum_bij (fun b _ => e b)
      · intro b hb
        simp only [Finset.mem_Ioi] at hb
        simp [hmem b, e.lt_iff_lt.mpr hb]
      · intro b _ c _ hbc; exact e.injective hbc
      · intro j hj
        simp only [Finset.mem_filter] at hj
        obtain ⟨b, hb⟩ := hsurj j hj.1
        refine ⟨b, ?_, hb⟩
        simp only [Finset.mem_Ioi]
        rw [← e.lt_iff_lt, hb]; exact hj.2
      · intro b _; rfl
  · intro i _ hi
    simp only [hi, if_false, Finset.sum_const_zero]

-- SKETCH: `Finset.measurable_sum` twice; each summand is
-- `(hh i j).comp ((hY i).prodMk (hY j))` after rewriting `h i j (Y i ω) (Y j ω)` as
-- `Function.uncurry (h i j) (Y i ω, Y j ω)`.
omit [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (ν i)] in
/-- `S` is measurable for measurable variables and kernels. -/
theorem measurable_S (hY : ∀ i, Measurable (Y i))
    (hh : ∀ i j, Measurable (Function.uncurry (h i j))) : Measurable (S h Y) := by
  sorry

/-- A separate bounded-kernel utility. Boundedness is an explicit extra premise,
not a consequence of the hypotheses of Lemma 6.1. -/
theorem exists_bound_S (H : Hyp μ ν Y h κ)
    (hbdd : ∀ i j, ∃ C : ℝ, ∀ x y, |h i j x y| ≤ C) :
    ∃ C : ℝ, ∀ ω, |S h Y ω| ≤ C := by
  classical
  choose C hC using hbdd
  refine ⟨∑ i, ∑ j ∈ Ioi i, C i j, fun ω => ?_⟩
  unfold S
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hC i j _ _))

-- SKETCH: set `n := T.card`, `e := T.orderEmbOfFin rfl`.  `H.reindex e` gives the
-- hypotheses on `Fin n`; `S_reindex h Y T rfl hvan ω` identifies the two `S`'s pointwise
-- (`integral_congr_ae` / `funext`).  Apply `LogGas.Decoupling.exp_bound` with `m := n`
-- (`hT` gives `1 ≤ n`), `θ`, `hθ`; the instance `∀ a, IsProbabilityMeasure (ν (e a))` is
-- `inferInstance`.
/-- Eq. `eq:canonical-array-exponential` (6.3) "with `m_b` in place of `m`": for a kernel
supported on pairs in a block `T` of `m_b = #T ≥ 1` variables,
`𝔼 e^{θ S/m_b} ≤ 2/(1-(C_u κ |θ|)^2)` whenever `C_u κ |θ| < 1`. -/
theorem block_exp_bound (H : Hyp μ ν Y h κ) (T : Finset (Fin m)) (hT : 1 ≤ T.card)
    (hvan : ∀ i j, (i ∉ T ∨ j ∉ T) → ∀ x y, h i j x y = 0) (θ : ℝ)
    (hθ : Cu * κ * |θ| < 1) :
    ∫ ω, Real.exp (θ * S h Y ω / T.card) ∂μ ≤ 2 / (1 - (Cu * κ * |θ|) ^ 2) := by
  sorry

-- SKETCH: if `T = ∅` then `S h Y = 0` by `hvan` (`Finset.sum_eq_zero`), the integrand is `1`
-- and `∫ 1 ∂μ = 1 ≤ 8/3` (`integral_const`, `measure_univ`).  Otherwise put
-- `θ := t * T.card / m`, so `θ * S / T.card = t * S / m` (`field_simp`, `T.card ≠ 0`,
-- `m ≠ 0`), and `Cu κ |θ| = Cu κ |t| #T / m ≤ Cu κ |t| (2 m*) / m ≤ 1/2 < 1`
-- (`abs_mul`, `abs_div`, `Nat.abs_cast`, `div_le_div_of_nonneg_right`, `hsize`).  Then
-- `block_exp_bound` and `2/(1-x^2) ≤ 2/(1-1/4) = 8/3` for `0 ≤ x ≤ 1/2`
-- (`div_le_div_of_nonneg_left`, `pow_le_pow_left₀`, `norm_num`).
/-- One block factor in eq. `eq:array-grouped-holder` (6.14): `𝔼[e^{t S_b/m}] ≤ 8/3` when
`#T_b ≤ 2 m_*` and `C_u κ |t| (2 m_*)/m ≤ 1/2`; empty blocks contribute `1`. -/
theorem block_factor (H : Hyp μ ν Y h κ) (hm : 1 ≤ m) (T : Finset (Fin m)) (mstar : ℕ)
    (hsize : T.card ≤ 2 * mstar)
    (hvan : ∀ i j, (i ∉ T ∨ j ∉ T) → ∀ x y, h i j x y = 0) (t : ℝ)
    (ht : Cu * κ * |t| * (2 * mstar) / m ≤ 1 / 2) :
    ∫ ω, Real.exp (t * S h Y ω / m) ∂μ ≤ 8 / 3 := by
  sorry

end Blocks

/-! ### G2: independence of the blocks of one class -/

section Classes

variable {m : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Fin m → Measure E}
  [∀ i, IsProbabilityMeasure (ν i)] {Y : Fin m → Ω → E}
  {h : Fin m → Fin m → E → E → ℝ} {κ : ℝ}

-- SKETCH (G2): `S (h' b) Y ω = Φ b (fun i : T b => Y i ω)` for the measurable map
-- `Φ b : (T b → E) → ℝ`, `Φ b z := ∑ i ∈ T b, ∑ j ∈ (T b).filter (i < ·), h' b i j (z i) (z j)`
-- (drop the vanishing terms with `hvan`, `Finset.sum_subset`).  The family
-- `b ↦ (fun i : T b => Y i ω)` is independent because the `T b` are pairwise disjoint:
-- use `iIndepFun_iff_measure_inter_preimage_eq_mul` / `iIndepFun_iff` and
-- `ProbabilityTheory.indep_iSup_of_disjoint` on the σ-algebras `⨆ i ∈ T b, (Y i)⁻¹ ·`
-- (`iIndepFun` is `iIndep (fun i => MeasurableSpace.comap (Y i) _)`), or
-- `iIndepFun_iff_map_fun_eq_pi_map` with the product structure of `Measure.pi`.  Then
-- `iIndepFun.comp` with the measurable `Φ b` (`Finset.measurable_sum`, `measurable_pi_apply`).
omit [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (ν i)] in
/-- Class independence for eq. `eq:array-grouped-holder` (6.14): block sums `S_{c,b}` whose
kernels are supported on pairwise disjoint sets of variables `T b` are independent. -/
theorem blocks_indep (hY_meas : ∀ i, Measurable (Y i)) (hY_indep : iIndepFun Y μ) {n : ℕ}
    (T : Fin n → Finset (Fin m)) (hT : Pairwise (Disjoint on T))
    (h' : Fin n → Fin m → Fin m → E → E → ℝ)
    (hmeas : ∀ b i j, Measurable (Function.uncurry (h' b i j)))
    (hvan : ∀ b i j, (i ∉ T b ∨ j ∉ T b) → ∀ x y, h' b i j x y = 0) :
    iIndepFun (fun b ω => S (h' b) Y ω) μ := by
  sorry

-- SKETCH: both sides are `mgf`'s: `∫ exp (t * X ω) ∂μ = mgf X μ t` by definition
-- (`ProbabilityTheory.mgf`), and `∑ b, S (h' b) Y ω = (∑ b, S (h' b) Y) ω`
-- (`Finset.sum_apply`).  Apply `ProbabilityTheory.iIndepFun.mgf_sum` to `blocks_indep`,
-- with measurability from `measurable_S`.
omit [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (ν i)] in
/-- The exponential moment of one class factors over its blocks
(`∏_b 𝔼[e^{2KuS_{c,b}/m}]` in eq. `eq:array-grouped-holder` (6.14)). -/
theorem class_mgf (hY_meas : ∀ i, Measurable (Y i)) (hY_indep : iIndepFun Y μ) {n : ℕ}
    (T : Fin n → Finset (Fin m)) (hT : Pairwise (Disjoint on T))
    (h' : Fin n → Fin m → Fin m → E → E → ℝ)
    (hmeas : ∀ b i j, Measurable (Function.uncurry (h' b i j)))
    (hvan : ∀ b i j, (i ∉ T b ∨ j ∉ T b) → ∀ x y, h' b i j x y = 0) (t : ℝ) :
    ∫ ω, Real.exp (t * ∑ b, S (h' b) Y ω) ∂μ
      = ∏ b, ∫ ω, Real.exp (t * S (h' b) Y ω) ∂μ := by
  sorry

-- SKETCH: if `M = 0` both sides are `1` (`Fintype.sum_empty`, `integral_const`,
-- `pow_zero`).  Otherwise rewrite `t * (∑ b, S_b) / m = (t/m) * ∑ b, S_b` and factor with
-- `class_mgf` (measurability from `(hH b).Y_meas`, `(hH b).Y_indep`, `(hH b).h_meas`).
-- Each factor `∫ exp ((t/m) * S_b)` equals `∫ exp (t * S_b / m) ≤ 8/3` by `block_factor`
-- applied to `hH b`, `hsize b`, `hvan b`, `ht`.  Conclude with `Finset.prod_le_prod`
-- (factors are nonnegative: `integral_nonneg`, `Real.exp_pos`), `Finset.prod_const`,
-- `Finset.card_univ`, `Fintype.card_fin`.
/-- One color class in eq. `eq:array-grouped-holder` (6.14): `M` blocks on pairwise disjoint
variable sets of size `≤ 2 m_*` give `𝔼[e^{t ∑_b S_b/m}] ≤ (8/3)^M` when
`C_u κ |t| (2 m_*)/m ≤ 1/2`. -/
theorem class_bound (hm : 1 ≤ m) {M : ℕ} (T : Fin M → Finset (Fin m))
    (hT : Pairwise (Disjoint on T)) (h' : Fin M → Fin m → Fin m → E → E → ℝ)
    (hH : ∀ b, Hyp μ ν Y (h' b) κ)
    (hvan : ∀ b i j, (i ∉ T b ∨ j ∉ T b) → ∀ x y, h' b i j x y = 0)
    (mstar : ℕ) (hsize : ∀ b, (T b).card ≤ 2 * mstar) (t : ℝ)
    (ht : Cu * κ * |t| * (2 * mstar) / m ≤ 1 / 2) :
    ∫ ω, Real.exp (t * (∑ b, S (h' b) Y ω) / m) ∂μ ≤ (8 / 3) ^ M := by
  sorry

end Classes

/-! ### Finite Hölder and the class decomposition -/

-- SKETCH: `Real.exp_sum` turns the integrand into `∏ c, exp (f c ω)`.  Apply the finite
-- Hölder inequality `ENNReal.lintegral_prod_norm_pow_le` with exponents `p c = 1/n`
-- (`Finset.sum_const`, `nsmul_eq_mul`, `mul_one_div_cancel`) to the nonnegative functions
-- `ofReal (exp (f c ω))`; `‖exp (f c ω)‖ ^ (n : ℝ) = exp (n * f c ω)` by
-- `Real.norm_of_nonneg`, `← Real.exp_mul` / `Real.rpow_natCast`.  Translate back to Bochner
-- integrals with `ofReal_integral_eq_lintegral_ofReal` (using `hint`, `hf`) and
-- `ENNReal.ofReal_rpow_of_nonneg`, `ENNReal.ofReal_prod_of_nonneg`, `ENNReal.ofReal_le_ofReal_iff`.
-- Integrability of `∏ c, exp (f c)` follows from Hölder as well, or from
-- `Integrable.of_bound` if the `f c` are bounded (not assumed here: use the `lintegral`
-- route and `integral_eq_lintegral_of_nonneg_ae`).
/-- Finite Hölder with `n` equal exponents (the "Hölder over the `2K` classes" step of
eq. `eq:array-grouped-holder` (6.14)):
`∫ exp(∑_c f_c) ≤ ∏_c (∫ exp(n f_c))^{1/n}` on a probability space. -/
theorem holder_classes (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n)
    (f : Fin n → Ω → ℝ) (hf : ∀ c, Measurable (f c))
    (hint : ∀ c, Integrable (fun ω => Real.exp (n * f c ω)) μ) :
    ∫ ω, Real.exp (∑ c, f c ω) ∂μ
      ≤ ∏ c, (∫ ω, Real.exp (n * f c ω) ∂μ) ^ (1 / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : ∑ _c : Fin n, (1 / (n : ℝ)) = 1 := by
    simp [Finset.sum_const, Finset.card_univ]; field_simp
  have hI : ∀ c, 0 ≤ ∫ ω, Real.exp (n * f c ω) ∂μ :=
    fun c => integral_nonneg (fun ω => (Real.exp_pos _).le)
  have hmeas : ∀ c, Measurable (fun ω => ENNReal.ofReal (Real.exp (n * f c ω))) :=
    fun c => ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (hf c)))
  have key := ENNReal.lintegral_prod_norm_pow_le (μ := μ) Finset.univ
    (f := fun c ω => ENNReal.ofReal (Real.exp (n * f c ω)))
    (fun c _ => (hmeas c).aemeasurable) hp (fun _ _ => by positivity)
  have hpt : ∀ ω, ∏ c : Fin n, ENNReal.ofReal (Real.exp (n * f c ω)) ^ (1 / (n : ℝ))
      = ENNReal.ofReal (Real.exp (∑ c, f c ω)) := by
    intro ω
    have : ∀ c : Fin n, ENNReal.ofReal (Real.exp (n * f c ω)) ^ (1 / (n : ℝ))
        = ENNReal.ofReal (Real.exp (f c ω)) := by
      intro c
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity),
        ← Real.exp_mul]
      congr 2
      field_simp
    simp_rw [this]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun c _ => (Real.exp_pos _).le), ← Real.exp_sum]
  simp_rw [hpt] at key
  have hR : ∀ c, ∫⁻ ω, ENNReal.ofReal (Real.exp (n * f c ω)) ∂μ
      = ENNReal.ofReal (∫ ω, Real.exp (n * f c ω) ∂μ) := fun c =>
    (ofReal_integral_eq_lintegral_ofReal (hint c)
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)).symm
  simp_rw [hR] at key
  have hrhs : ∏ c : Fin n, ENNReal.ofReal (∫ ω, Real.exp (n * f c ω) ∂μ) ^ (1 / (n : ℝ))
      = ENNReal.ofReal (∏ c, (∫ ω, Real.exp (n * f c ω) ∂μ) ^ (1 / (n : ℝ))) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun c _ => Real.rpow_nonneg (hI c) _)]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (hI c) (by positivity)]
  rw [hrhs] at key
  have hmeasS : Measurable (fun ω => Real.exp (∑ c, f c ω)) :=
    Real.measurable_exp.comp (Finset.measurable_sum _ fun c _ => hf c)
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hmeasS.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal
    (Finset.prod_nonneg fun c _ => Real.rpow_nonneg (hI c) _) key

section Grouped

variable {m : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Fin m → Measure E}
  [∀ i, IsProbabilityMeasure (ν i)] {Y : Fin m → Ω → E}
  {h : Fin m → Fin m → E → E → ℝ} {κ : ℝ}

-- SKETCH: take the coloring `col` from `greedy_edge_coloring G K hK hdeg`.  Classes
-- `c : Fin (2K)` with `c.val < 2K-1` collect the edges of color `c` (a matching: by the
-- coloring property every group lies on at most one edge of each color); index the edge
-- `{a, b}`, `a < b`, by its smaller endpoint `a`.  Define
-- `T c a := univ.filter (fun i => grp i = a ∨ ∃ b, a < b ∧ G.Adj a b ∧ col a b = c ∧ grp i = b)`
-- when some such `b` exists, else `∅`, and `h' c a := restrict h (pairs of distinct groups
-- `{grp i, grp j} = {a, b}` for that edge)`; the last class `c = 2K-1` has
-- `T c a := univ.filter (grp · = a)` and `h' c a := restrict h (fun i j => grp i = a ∧ grp j = a)`.
-- `Hyp` by `Hyp.restrict`; sizes `≤ 2 m*` from `hsize` via `Finset.card_union_le` /
-- `Finset.filter_or`; disjointness from the matching property (`Finset.disjoint_filter`);
-- vanishing by construction.  The sum identity: every pair `i < j` with `h i j ≠ 0` has
-- either `grp i = grp j` (last class, block `grp i`) or `G.Adj (grp i) (grp j)` (`hvan`),
-- in which case it lies in exactly the class `col (grp i) (grp j)` and block
-- `min (grp i) (grp j)`; so `∑ c, ∑ a, restrict … = h i j` pointwise by
-- `Finset.sum_ite_eq`/`Finset.sum_eq_single`, then `Finset.sum_comm` and `Finset.sum_congr`.
/-- The decomposition `S = ∑_{c=1}^{2K} ∑_b S_{c,b}` preceding eq. `eq:array-grouped-holder`
(6.14): `2K` classes of `M` blocks each (possibly empty), blocks of one class on pairwise
disjoint variable sets of size `≤ 2 m_*`, each block kernel satisfying the hypotheses of
Lemma 6.1. -/
theorem class_decomposition (H : Hyp μ ν Y h κ) {M : ℕ} (grp : Fin m → Fin M) (mstar : ℕ)
    (hsize : ∀ a, (univ.filter (fun i => grp i = a)).card ≤ mstar)
    (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (K : ℕ) (hK : 1 ≤ K)
    (hdeg : ∀ a, G.degree a ≤ K - 1)
    (hvan : ∀ i j, grp i ≠ grp j → ¬ G.Adj (grp i) (grp j) → ∀ x y, h i j x y = 0) :
    ∃ (T : Fin (2 * K) → Fin M → Finset (Fin m))
      (h' : Fin (2 * K) → Fin M → Fin m → Fin m → E → E → ℝ),
      (∀ c, Pairwise (Disjoint on T c)) ∧
      (∀ c a, (T c a).card ≤ 2 * mstar) ∧
      (∀ c a, Hyp μ ν Y (h' c a) κ) ∧
      (∀ c a i j, (i ∉ T c a ∨ j ∉ T c a) → ∀ x y, h' c a i j x y = 0) ∧
      ∀ ω, S h Y ω = ∑ c, ∑ a, S (h' c a) Y ω := by
  sorry

-- SKETCH (G3): obtain `T, h'` from `class_decomposition`.  Put
-- `f c ω := u * (∑ a, S (h' c a) Y ω) / m`, so `u * S h Y ω / m = ∑ c, f c ω`
-- (`Finset.mul_sum`, `Finset.sum_div`) and `(2K : ℝ) * f c ω = (2K u) * (∑ a, S …) / m`.
-- `holder_classes μ (n := 2K)`: measurability from `measurable_S`, integrability from
-- finite exponential moments at the required coupling, proved via the nonnegative
-- exponential series and `moment_bound`. No boundedness premise is available.  Each factor is
-- `≤ ((8/3)^M) ^ (1/(2K))` by `class_bound` with `t = 2 K u`, since
-- `Cu κ |2Ku| (2 m*)/m = 4 K Cu κ |u| m*/m ≤ 1/2` (`abs_mul`, `Nat.abs_cast`, `ring_nf`)
-- and `Real.rpow_le_rpow` (bases nonnegative by `integral_nonneg`).  Finally
-- `Finset.prod_const`, `Finset.card_univ`, `Fintype.card_fin`, `← Real.rpow_natCast`,
-- `← Real.rpow_mul`, `one_div_mul_cancel` give `(((8/3)^M)^(1/(2K)))^(2K) = (8/3)^M`.
/-- Eq. `eq:canonical-grouped-exponential` (6.4): with `M` groups of size `≤ m_*`, each
interacting with at most `K - 1` others, `𝔼[e^{uS/m}] ≤ (8/3)^M` whenever
`4 K C_u κ |u| m_*/m ≤ 1/2`. -/
theorem grouped_exp_bound (H : Hyp μ ν Y h κ) (hm : 1 ≤ m) {M : ℕ} (grp : Fin m → Fin M)
    (mstar : ℕ) (hsize : ∀ a, (univ.filter (fun i => grp i = a)).card ≤ mstar)
    (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (K : ℕ) (hK : 1 ≤ K)
    (hdeg : ∀ a, G.degree a ≤ K - 1)
    (hvan : ∀ i j, grp i ≠ grp j → ¬ G.Adj (grp i) (grp j) → ∀ x y, h i j x y = 0)
    (u : ℝ) (hu : 4 * K * Cu * κ * |u| * mstar / m ≤ 1 / 2) :
    ∫ ω, Real.exp (u * S h Y ω / m) ∂μ ≤ (8 / 3) ^ M := by
  sorry

end Grouped

end LogGas.Grouped
