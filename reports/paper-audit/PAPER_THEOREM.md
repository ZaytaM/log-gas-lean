# The paper's theorem, stated precisely

Source: Delgadino–Gvalani–Rosenzweig, *An entropy bound for the attractive logarithmic gas*,
as excerpted in `notes/` (`00-preamble-macros.tex`, `sec1-setting.tex` … `sec6-lemma61.tex`,
`appendixA.tex`). Locators below refer to the LaTeX labels.

## 1. Setting (`sec:setting`)

* **Dimension.** An integer `d ≥ 2`.
* **Torus and law.** `𝕋^d = ℝ^d/ℤ^d` (period one in each coordinate); `μ_unif` is normalized
  Lebesgue measure on `𝕋^d`, i.e. the Haar probability measure, `μ_unif(𝕋^d) = 1`.
* **Fourier convention.** `f̂(k) = ∫_{𝕋^d} f(x) e^{-2πi k·x} dμ_unif(x)`, `k ∈ ℤ^d`.
* **Kernel** (`eq:kernel-normalization`, (1.1)). `g` is the mean-zero periodic logarithmic kernel
  ```
  ĝ(k) = c_d / (2π|k|)^d   (k ≠ 0),   ĝ(0) = 0,   c_d = 2^{d-1} π^{d/2} Γ(d/2),
  g(x) = -log|x| + O_d(1)   (x → 0).
  ```
  Here `|k|` is the Euclidean norm. Since `c_d/(2π)^d = Γ(d/2)/(2π^{d/2}) = 1/|S^{d-1}|`,
  `ĝ(k) = 1/(|S^{d-1}| |k|^d)`, the periodization of the Newtonian-type kernel whose ℝ^d transform
  is `|ξ|^{-d}/|S^{d-1}|`; this is consistent with the `-log|x|` asymptotic (checked against
  `eq:compact-split-fourier-order`: `φ(0)^{-1}∫_0^∞ t^{d-1} φ̂(tk) dt = φ(0)^{-1}|k|^{-d}
  |S^{d-1}|^{-1}∫_{ℝ^d} φ̂ = ĝ(k)`). `g` is *one fixed function* (up to a null set) for each `d`; it is
  not a parameter. Since `∑_{k≠0}|k|^{-2d} < ∞`, `g ∈ L²(𝕋^d)`; it is even, real, mean zero,
  bounded below, continuous off `0`, and `e^{b g/2} ∈ L¹` iff `b < 2d`.
* **Energy and partition function** (`eq:homogeneous-partition-function`, (1.2)). For
  `X_1,…,X_N` i.i.d. with law `μ_unif`,
  ```
  W_N(K) = (1/N) ∑_{i ≠ j} K(X_i, X_j)          (ordered off-diagonal pairs, factor 1/N),
  Z_{N,β} = 𝔼[ exp( (β/2) W_N(g) ) ],           K(x,y) := g(x - y).
  ```
  Each unordered pair thus enters with weight `β/N`; no diagonal terms appear (`g(0)` is never
  evaluated). The sign is attractive: large positive `g` near the diagonal increases the weight.
  Because `X_i - X_j` (`i ≠ j`) has law `μ_unif`, `Z_{N,β}` depends only on the a.e.-class of `g`.
  A priori `Z_{N,β} ∈ [1, ∞]` (Jensen, `𝔼 W_N(g) = 0`); the theorem asserts finiteness *and* a
  uniform bound, so it is properly an extended-real (`[0,∞]`) statement.

## 2. The only macroscopic assumption: H1 (log-HLS, `eq:strict-subcritical-macroscopic-inequality`, (1.3))

For some `B ∈ (0, 2d]`:
```
H(ρ μ_unif | μ_unif) := ∫ ρ log ρ dμ_unif
      ≥ (B/2) ∬ g(x - y) (ρ(x) - 1)(ρ(y) - 1) dμ_unif(x) dμ_unif(y)
```
for **every** probability density `ρ` (w.r.t. `μ_unif`: `ρ ≥ 0`, `∫ρ = 1`) of finite entropy
(`ρ log ρ ∈ L¹`). "No value or optimality of `B` is needed."

*Domain remark (not in the paper, needed to make (1.3) meaningful).* For finite-entropy `ρ` the
double integral converges absolutely: with `ℓ(z) = log_+(1/|z|)` and Young's inequality
`λ a b ≤ b log b − b + e^{λ a}` (`0 < λ < d`), `sup_x ∫ ℓ(x−y) ρ(y) dy ≤ λ^{-1}(H(ρ) + ∫e^{λℓ})`,
so `∬ |g(x−y)| ρ(x)ρ(y) < ∞`; the cross terms with `1` are bounded since `g ∈ L¹`. Hence
the paper's H1 is well-posed, and it is equivalent to either Lean encoding in
`PaperStatement.lean` (`LogHLS`, totalized but conservative; `LogHLSWithDomain`, integrability explicit).

## 3. Theorem 1.1 (`thm:principal`, (1.4) `eq:principal-order-one`)

> Under (1.3), for every `0 ≤ β₀ < B` there is a finite constant `C = C(d, B, β₀)` such that
> ```
> sup_{N ≥ 2} sup_{0 ≤ β ≤ β₀} Z_{N,β} ≤ C.
> ```

Quantifier order, written out:
```
∀ d ≥ 2. ∀ B ∈ (0, 2d] with H1(g_d, B). ∀ β₀ ∈ [0, B).
  ∃ C = C(d,B,β₀) < ∞.  ∀ N ∈ ℕ, N ≥ 2.  ∀ β ∈ [0, β₀].   Z_{N,β}(g_d) ≤ C.
```
* `β₀ = 0` is included (then `Z_{N,0} = 1`, "immediate").
* `N = 1` is excluded in the theorem (`Z_{1,β} = 1` anyway); Lemmas 4.1 and 5.1 are for `N ≥ 1`.
* `C` precedes `N` and `β`; it may depend on `d, B, β₀` only. Because `g = g_d` is determined by
  `d`, and the proof's auxiliary choices (`χ`, `p,q,s`, `δ`, `J`, the bulk grid) are fixed
  functions of `(d, B, β₀)`, nothing else enters. In a formalization quantifying over
  representatives `g`, `C` may be placed before `g` (as in `PaperTheorem`) because all
  representatives give the same `Z_{N,β}`.
* `B ≤ 2d` is used in Section 3: `β₀ < B ≤ 2d` allows `s > 1` with `b = sβ₀ < 2d`, so that
  `A_b = ∫ e^{bg/2} dμ_unif < ∞`.

Lean form: `LogGasPaper.PaperTheorem` in `PaperStatement.lean` (a specification, compiled; not
proved). See `COMPILE_LOG.md`.

## 4. H1 versus the project's H2 (important)

The paper's **only** premise is H1. The project (`notes/hypotheses.md`) additionally *assumes*

**H2 (cutoff package).** For each `J ≥ 3`, `r = 1/(2J)`, kernels `s_r ≥ 0`, `b_r` with
`g = b_r + (s_r − c_r)`, `c_r = ∫ s_r ≤ C r^d`, `supp s_r ⊂ {dist(·,0) ≤ r}`,
`s_r ≤ (log(r/dist))_+`, `b_r` bounded continuous even mean-zero, both quadratic forms `≥ 0`, and
the `b_r`-form dominated by the `g`-form.

In the paper **H2 is a theorem, not a premise**: Section 2 (`sec:physical-cutoff-proof`,
`eq:compact-positive-log-split`, `eq:compact-split-fourier-order`) constructs
`s_r = φ(0)^{-1} ∑_{m∈ℤ^d} ∫_0^r φ((x+m)/t) dt/t` from `φ = χ*χ`, `χ ∈ C_c^∞(B_{1/2})` radial,
nonnegative, nonzero, and proves every listed property from (1.1) alone (Fourier positivity
`0 ≤ ŝ̃_r ≤ ĝ`, support, `0 ≤ φ ≤ φ(0)` giving the log bound, `c_r = ‖φ‖₁ r^d/(dφ(0))`, rapid decay
of `b̂_r`). Therefore:

* `Challenge.principalStatement` (H1 ∧ H2 ⇒ bound, for an *arbitrary supplied* `g`) is a
  **different, conditional** statement. It would imply the paper's theorem only after
  (i) constructing/identifying the paper's `g`, (ii) proving H2 for it (Section 2),
  (iii) proving the extra conditions it lists (`Integrable g`, mean zero, a.e. even, the energy
  integrability conjunct inside its `logHLS`), and (iv) moving `C` before `g` (Fourier uniqueness
  + a.e.-invariance). None of (i)–(iv) exists in the repository.
* Conversely, the conditional target is mathematically more general (any `g` with H1+H2), and I
  found no reason to think it false: its premises supply every ingredient the paper's proof uses
  (see `DEVIATIONS.md` §C).

## 5. Proof architecture (for reference)

| Step | Source | Content |
| --- | --- | --- |
| Cutoff | §2 (2.1)–(2.2) | `g = b_r + s̃_r`, both PSD, `b_r` inherits H1 |
| Occupancy sum, Hölder | §2 (2.3)–(2.4) | `Z ≤ (𝔼e^{pβW(b_r)/2})^{1/p}(𝔼1_𝒜 e^{qβW(s̃_r)/2})^{1/q} + 𝔼1_ℬ e^{βW(g)/2}` |
| Bad event | §3 (3.1)–(3.3) | `Z_{N,b} ≤ A_b^{N−1}`; Chernoff; `≤ M^{1/s'} e^{N(log A_b/s − D/s')}` |
| Bulk | §4 Lemma 4.1, App. A | continuous-kernel bound via histogram, Gaussian, remainder |
| Singular | §5 Lemma 5.1 | split `a_r + h_r`, Lemma 6.1 one-block and grouped forms |
| Arrays | §6 Lemma 6.1 | decoupling, moment counting, grouped Hölder |
| Assembly | §5 "Conclusion" | `p,q` → `δ ≤ δ₀(qβ₀)` → `J ≥ J₀`, `J^{-d} < δ`, bad exponent `< 0` |

I re-derived every displayed inequality of §§2–6 and App. A while reading; the argument is
correct up to the minor gaps listed in `DEVIATIONS.md` §F.
