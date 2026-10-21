Hyp.h_bdd (bounded kernels) is stronger than the paper and fails for h_r in Section 5
(log singularity). Replace by integrability: for all i j, p ≥ 1, the functions
x ↦ |h i j x y|^p and y ↦ |h i j x y|^p are integrable under ν i, ν j for every y, x,
and (x,y) ↦ |h i j x y|^p is integrable under (ν i).prod (ν j).
Then re-run workers on Decoupling; proofs that used h_bdd must switch to these.

Update 2026-10-20: the boundedness requirement was removed from `Decoupling.Hyp`
and `Singular.BoxKernel`. `Hyp.h_int` supplies joint moment integrability; Fubini proves
slice integrability almost everywhere. Centering and moment bounds now also hold a.e.,
as in Section 6. Thus this repair is weaker than the originally suggested every-slice
integrability and supports logarithmically singular kernels. The old bounded-sum utility
now explicitly requires bounded kernels and is unavailable to the general argument.

The direct bridge is `Singular.hyp_hker_labels`, via `hker_boxKernel` and the finite
nonnegative moment estimate `hker_moment`. These bridge proofs may still depend on
pre-existing unproved Section 5 lemmas; a successful build alone is not a completed
axiom audit of the singular application. Remaining obligations stay in the worker queue.

Resolved 2026-10-21: the seven remaining saved Grouped/Singular proof bodies were
refreshed against current main, with statements and all other material unchanged.
The full project build passed, and all 189 declarations passed a transitive axiom
audit using only propext, Classical.choice, and Quot.sound. No admitted proof
bodies remain. This includes the direct untruncated singular-kernel interface
`Singular.hyp_hker_labels` and the Section 5 result `Singular.lemma51`.
