import LogGas.TorusBase
import LogGas.BadEvent

/-!
# Equal-volume boxes on the torus

Eq. (1.5) (`eq:common-box-partition`) of `notes/sec1-setting.tex`: the torus `T d` is partitioned
into `J ^ d` half-open cubes of side `1/J`, each of `unif d`-measure `(J^d)⁻¹`, with sup-diameter
`< 1/J`.  The representative of a circle point is taken in `(0,1]` (`AddCircle.equivIoc 1 0`), so
the cell index of a coordinate is `⌈J t⌉ - 1`.  (Deviation from the suggested `equivIco`: cells
are `Ioc`-intervals; this does not change any stated target.)
-/

set_option autoImplicit false
open MeasureTheory

namespace LogGas.Torus

/-- Representative in `(0,1]` of a point of the circle. -/
noncomputable def gridRep (t : AddCircle (1 : ℝ)) : ℝ := (AddCircle.equivIoc 1 0 t).1

private theorem gridRep_mem (t : AddCircle (1 : ℝ)) : gridRep t ∈ Set.Ioc (0 : ℝ) 1 := by
  have := (AddCircle.equivIoc 1 0 t).2
  simpa [gridRep] using this

private theorem gridRep_coe {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    gridRep (s : AddCircle (1 : ℝ)) = s := by
  unfold gridRep
  rw [AddCircle.equivIoc_coe_eq (by simpa using hs)]

private theorem measurable_gridRep : Measurable gridRep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 0).measurable

/-- Cell index of a single circle coordinate. -/
noncomputable def gridIdx (J : ℕ) (hJ : 0 < J) (t : AddCircle (1 : ℝ)) : Fin J :=
  ⟨⌈(J : ℝ) * gridRep t⌉₊ - 1, by
    have h1 : ⌈(J : ℝ) * gridRep t⌉₊ ≤ J := by
      apply Nat.ceil_le.2
      have := (gridRep_mem t).2
      nlinarith [(Nat.cast_pos.2 hJ : (0 : ℝ) < J)]
    omega⟩

private theorem gridIdx_eq_iff (J : ℕ) (hJ : 0 < J) (t : AddCircle (1 : ℝ)) (k : Fin J) :
    gridIdx J hJ t = k ↔
      gridRep t ∈ Set.Ioc ((k : ℝ) / J) (((k : ℝ) + 1) / J) := by
  have hJ' : (0 : ℝ) < J := Nat.cast_pos.2 hJ
  have hpos : 0 < (J : ℝ) * gridRep t := mul_pos hJ' (gridRep_mem t).1
  have hc : 1 ≤ ⌈(J : ℝ) * gridRep t⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith)
  rw [Fin.ext_iff, gridIdx]
  simp only
  have : ⌈(J : ℝ) * gridRep t⌉₊ - 1 = k ↔ ⌈(J : ℝ) * gridRep t⌉₊ = k + 1 := by omega
  rw [this, Nat.ceil_eq_iff (by omega)]
  simp only [Nat.add_sub_cancel, Set.mem_Ioc, Nat.cast_add, Nat.cast_one]
  rw [div_lt_iff₀ hJ', le_div_iff₀ hJ', mul_comm (gridRep t)]

/-- Measurable cell index (`eq:common-box-partition`). -/
noncomputable def cellOf (d J : ℕ) (hJ : 0 < J) (x : T d) : Fin d → Fin J :=
  fun i => gridIdx J hJ (x i)

private theorem measurable_gridIdx (J : ℕ) (hJ : 0 < J) : Measurable (gridIdx J hJ) := by
  refine measurable_to_countable' fun k => ?_
  have : gridIdx J hJ ⁻¹' {k} = gridRep ⁻¹' Set.Ioc ((k : ℝ) / J) (((k : ℝ) + 1) / J) := by
    ext t; simp [gridIdx_eq_iff]
  rw [this]
  exact measurable_gridRep measurableSet_Ioc

theorem measurable_cellOf (d J : ℕ) (hJ : 0 < J) : Measurable (cellOf d J hJ) :=
  measurable_pi_iff.2 fun i => (measurable_gridIdx J hJ).comp (measurable_pi_apply i)

private theorem gridIdx_coe (J : ℕ) (hJ : 0 < J) (k : Fin J) {s : ℝ}
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    gridIdx J hJ (s : AddCircle (1 : ℝ)) = k ↔ s ∈ Set.Ioc ((k : ℝ) / J) (((k : ℝ) + 1) / J) := by
  rw [gridIdx_eq_iff, gridRep_coe hs]

private theorem gridIdx_haar (J : ℕ) (hJ : 0 < J) (k : Fin J) :
    (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) (gridIdx J hJ ⁻¹' {k}) =
      (J : ENNReal)⁻¹ := by
  have hJ' : (0 : ℝ) < J := Nat.cast_pos.2 hJ
  have h1 : (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) = volume := by
    have := AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))
    simp at this
    rw [this]
  rw [h1, AddCircle.add_projection_respects_measure 1 0 (measurable_gridIdx J hJ (measurableSet_singleton k))]
  have hk : (k : ℝ) + 1 ≤ J := by exact_mod_cast k.2
  have : QuotientAddGroup.mk ⁻¹' (gridIdx J hJ ⁻¹' {k}) ∩ Set.Ioc (0 : ℝ) (0 + 1) =
      Set.Ioc ((k : ℝ) / J) (((k : ℝ) + 1) / J) := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, zero_add]
    constructor
    · rintro ⟨h1, h2⟩
      exact (gridIdx_coe J hJ k h2).1 h1
    · intro h
      have h2 : s ∈ Set.Ioc (0 : ℝ) 1 := by
        refine ⟨lt_of_le_of_lt (by positivity) h.1, h.2.trans ?_⟩
        rw [div_le_one hJ']; exact hk
      exact ⟨(gridIdx_coe J hJ k h2).2 h, h2⟩
  rw [this, Real.volume_Ioc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hJ']
  congr 1
  field_simp
  ring

/-- Equal-volume boxes on the torus (`eq:common-box-partition`). -/
noncomputable def grid (d J : ℕ) (hJ : 0 < J) : LogGas.BadEvent.Boxes (unif d) (J ^ d) where
  A a := {x | cellOf d J hJ x = finFunctionFinEquiv.symm a}
  meas a := measurable_cellOf d J hJ (measurableSet_singleton _)
  disj a b hab := by
    refine Set.disjoint_left.2 fun x hxa hxb => hab ?_
    have : finFunctionFinEquiv.symm a = finFunctionFinEquiv.symm b :=
      (show cellOf d J hJ x = _ from hxa).symm.trans hxb
    exact finFunctionFinEquiv.symm.injective this
  cover := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨finFunctionFinEquiv (cellOf d J hJ x), ?_⟩
    simp
  vol a := by
    have : {x | cellOf d J hJ x = finFunctionFinEquiv.symm a} =
        Set.pi Set.univ fun i => gridIdx J hJ ⁻¹' {finFunctionFinEquiv.symm a i} := by
      ext x
      simp [cellOf, funext_iff]
    rw [this, unif, Measure.pi_pi]
    simp only [gridIdx_haar, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_pow, ENNReal.inv_pow]

theorem mem_grid_iff {d J : ℕ} {hJ : 0 < J} {a : Fin (J ^ d)} {x : T d} :
    x ∈ (grid d J hJ).A a ↔ cellOf d J hJ x = finFunctionFinEquiv.symm a := Iff.rfl

private theorem gridIdx_dist_lt (J : ℕ) (hJ : 0 < J) {s t : AddCircle (1 : ℝ)}
    (h : gridIdx J hJ s = gridIdx J hJ t) : dist s t < 1 / J := by
  have hJ' : (0 : ℝ) < J := Nat.cast_pos.2 hJ
  have h1 := (gridIdx_eq_iff J hJ s _).1 rfl
  have h2 := (gridIdx_eq_iff J hJ t _).1 h.symm
  have hlt : |gridRep s - gridRep t| < 1 / J := by
    rw [abs_lt]
    constructor <;> [skip; skip] <;>
    · have := h1.1; have := h1.2; have := h2.1; have := h2.2
      have e : (((gridIdx J hJ s : Fin J) : ℝ) + 1) / J = ((gridIdx J hJ s : Fin J) : ℝ) / J + 1 / J := by
        ring
      linarith
  have hs : (gridRep s : AddCircle (1 : ℝ)) = s := by simp [gridRep]
  have ht : (gridRep t : AddCircle (1 : ℝ)) = t := by simp [gridRep]
  calc dist s t = dist (gridRep s : AddCircle (1 : ℝ)) (gridRep t) := by rw [hs, ht]
    _ = ‖((gridRep s - gridRep t : ℝ) : AddCircle (1 : ℝ))‖ := by
        rw [dist_eq_norm, QuotientAddGroup.mk_sub]
    _ ≤ ‖gridRep s - gridRep t‖ := QuotientAddGroup.norm_mk_le_norm
    _ < 1 / J := by rwa [Real.norm_eq_abs]

theorem dist_lt_of_mem_grid {d J : ℕ} {hJ : 0 < J} (a : Fin (J ^ d)) {x y : T d}
    (hx : x ∈ (grid d J hJ).A a) (hy : y ∈ (grid d J hJ).A a) : dist x y < 1 / J := by
  have hJ' : (0 : ℝ) < J := Nat.cast_pos.2 hJ
  rw [dist_pi_lt_iff (by positivity)]
  intro i
  apply gridIdx_dist_lt
  have h1 : cellOf d J hJ x i = _ := congrFun (mem_grid_iff.1 hx) i
  have h2 : cellOf d J hJ y i = _ := congrFun (mem_grid_iff.1 hy) i
  exact h1.trans h2.symm

end LogGas.Torus

