# Assumed hypotheses (not formalized)

Two inputs are stated as hypotheses of the final theorem, never proved. Every
Lean file may take them as explicit arguments; none may introduce other axioms.

## H1. Log-HLS inequality (paper eq. 1.3)

For the mean-zero periodic log kernel g on T^d and some B in (0, 2d]: for every
probability density ρ of finite entropy,

    ∫ ρ log ρ dμ ≥ (B/2) ∬ g(x-y)(ρ(x)-1)(ρ(y)-1) dμ(x) dμ(y).

In Lean this is a hypothesis `hlogHLS : ∀ ρ, ... ` on the structure carrying
the kernel; no value of B is needed.

## H2. Cutoff decomposition (paper Section 2, eqs. 2.1–2.2)

For every integer J ≥ 3 and r = 1/(2J) there exist kernels s_r, b_r on T^d with

- g = b_r + (s_r - c_r), where c_r = ∫ s_r dμ and 0 ≤ c_r ≤ C r^d;
- s_r ≥ 0 and s_r(x) = 0 whenever dist(x, 0) > r;
- s_r(z) ≤ (log(r / dist(z,0)))_+  (used for the moment bound 5.8);
- b_r is bounded, continuous, even, mean zero;
- the quadratic forms of b_r and of (s_r - c_r) are both nonnegative, and that
  of b_r is dominated by that of g (so b_r satisfies H1 with the same B).

In Lean this is a structure `CutoffData d J` with these fields, passed as a
hypothesis. Phase 3 (Lemma 5.1) and Phase 5 (assembly) consume it.

## Not hypotheses

Everything in Sections 3, 5, 6 and Appendix A is to be proved. The citation
to Ren–Wang for Lemma 4.1 is not used; Appendix A is the proof.
