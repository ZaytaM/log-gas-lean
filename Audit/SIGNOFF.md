# Statement layer: for the owner's sign-off

Status: **pending**. Owner: Matias Delgadino (co-author); co-authors may countersign.
What is asked: read `PaperChallenge.lean` (130 lines) against the manuscript and answer each item
below "as it stands" or "with the change …". After sign-off the layer is frozen by hash
(`FREEZE.md`); any later change to a signed statement needs your written approval in
`approved_changes.txt`. Sign by adding a dated line under "Record" (commit author = signer).

The Lean kernel has checked that `LogGasPaper.main : PaperTheorem` is proved. **Nothing checks that
`PaperTheorem` is Theorem 1.1.** That is what this sign-off establishes.

## S1. The theorem (`PaperTheorem`, `PaperChallenge.lean:134`)

```lean
def PaperTheorem : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ B : ℝ, 0 < B → B ≤ 2 * d → ∀ β₀ : ℝ, 0 ≤ β₀ → β₀ < B →
    ∃ C : ℝ≥0, ∀ g : Torus d → ℝ, IsLogKernel d g → LogHLS g B →
      ∀ N : ℕ, 2 ≤ N → ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → partitionFunction g N β ≤ (C : ℝ≥0∞)
```

Compare with the short draft, `thm:principal` (SD 163): *Under (1.3) [with constant B], for every
0 ≤ β₀ < B there is a finite C = C(d, B, β₀) with sup_{N≥2} sup_{0≤β≤β₀} Z_{N,β} ≤ C.*

Points to confirm:
- (a) C depends only on (d, B, β₀): `∃ C` precedes `∀ g`. ✔ as intended?
- (b) The extra premise `B ≤ 2d`. The paper uses (1.3) only with B < β_gm ≤ 2d; the restriction
  loses nothing, but it is not in the short draft's statement. Keep or drop?
- (c) `C : ℝ≥0` and `partitionFunction : ℝ≥0∞`: finiteness is asserted (divergence would be `⊤`).
- (d) Canonical manuscript, Part A(i) (C 455): "for every β₀ < β_gm, C = C(d, β₀)". This follows
  from `PaperTheorem` by choosing B ∈ (β₀, β_gm) and using the canonical (1.3) for b = B
  (C 1328–1340). Do you agree the formal statement is the paper's theorem *given* (1.3), and that
  the identification of β_gm (Beckner–Onofri) is a separate input, to be imported?

## S2. The kernel (`IsLogKernel`, :80; `kernelCoeff`, `cd`, `fourierCoeff`, :60–78)

g is characterized by `Measurable g ∧ Integrable g (uniform d) ∧ ∀ k, fourierCoeff g k = kernelCoeff d k`,
with `kernelCoeff d k = c_d / (2π |k|)^d` for k ≠ 0, 0 for k = 0, `c_d = 2^{d−1} π^{d/2} Γ(d/2)`,
convention f̂(k) = ∫ f(x) e^{−2πi k·x} dμ_unif. The theorem quantifies over *every* such g.
- (a) Normalization matches (1.1) / C `eq:kernel-normalization`?
- (b) Is "any integrable representative with these coefficients" acceptable as "the kernel g"?
  (Two such g agree a.e. — proved in `LogGas/FourierUnique.lean` — and Z_{N,β} sees g only a.e.)
- (c) `LogAsymptotic` (−log|x| + O(1)) is recorded but is **neither premise nor conclusion**. Agreed?

## S3. The log-HLS hypothesis (`LogHLS`, :106; `logEnergy`, :102; `FiniteEntropyDensity`, :93)

`(B/2) * ∬ g(x−y)(ρ x − 1)(ρ y − 1) dμ⊗μ ≤ ∫ ρ log ρ dμ` for every measurable ρ ≥ 0 a.e.,
integrable, ∫ρ = 1, with ρ log ρ integrable.
- (a) The double integral is a Lean Bochner integral: for ρ with non-integrable energy integrand
  it evaluates to 0 and the inequality is trivially true. Hence `LogHLS g B` is implied by the
  paper's (1.3) and the theorem is at least as strong as the paper's. Accept this encoding, or
  require `LogHLSWithDomain` (:110, with explicit integrability)?
- (b) Densities vs. measures: canonical (1.3) is over probability *measures* with finite entropy;
  finite entropy forces absolute continuity, so densities suffice. Agreed?

## S4. Partition function (`offDiagEnergy`, :122; `partitionFunction`, :126)

W_N = (1/N) Σ_i Σ_{j≠i} g(x_i − x_j) over *ordered* pairs; Z = ∫⁻ ofReal(exp((β/2) W_N)) dμ_unif^{⊗N}.
Matches (1.2) (SD 148) and C 174 (β/(2N) Σ_{i≠j}). Confirm sign (attractive) and factor.

## S5. Torus and metric (`Torus`, `uniform`, `radius`, :46–58)

`Torus d = Fin d → AddCircle 1`, `uniform d = Measure.pi (fun _ => haarAddCircle)` (mass one).
Mathlib's metric on this type is the **sup** metric; the Euclidean `|x|` of the paper is encoded
separately as `radius` (used only in `LogAsymptotic`, and inside the proof library for the cutoff).
No statement in `PaperTheorem` depends on the choice of metric. Confirm.

## S6. Scope: what is *not* claimed

- Satisfiability of `LogHLS g B` for any B > 0 (Beckner–Onofri; value of β_gm): **not proved**,
  to be imported. Until then `PaperTheorem` is a conditional theorem exactly as Theorem 1.1 is
  conditional on (1.3), and formally could be vacuous.
- Parts A(ii)–(iv) and Parts B–… of the canonical `thm:principal` (determinant asymptotics,
  β_pf = β_gm identity, lower limits above threshold, transported references): not formalized.
- Fidelity of the short draft's *proof prose* to the canonical proof: not part of the certificate.

## Record

- 2026-10-22: sheet prepared from the freeze commit; no signature yet.
- (signature lines: `YYYY-MM-DD <name>: signed S1–S6 as they stand` / `… with changes: …`)
