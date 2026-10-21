# Independent mathematical fidelity review

Verdict: **findings — incomplete mathematical verification**.

Reviewer: `/root/fidelity_review`. This reviewer inspected the mathematical sources,
independent specification, selected actual supporting proofs and the dependency
contract. The reviewer did not implement or alter the candidate. Findings were
reported to the implementer; the final frozen candidate incorporates the
specification and dependency corrections described below. This is an independent
agent review in the same overall project, not an external human referee review.

## Blocking findings

1. **The bulk and main theorems are absent.** `LogGas/Bulk.lean` ends with the
   definition of `KHyp`; `LogGas.Bulk.lemma41` does not exist. There is no
   `LogGas/Main.lean` and no `LogGas.Main.theorem11`. Several Appendix A and
   assembly milestones are also absent. Neither `LogGasChallenge.principal`
   nor `LogGasChallenge.bulk` inhabits the corresponding target proposition.
   Existing Gaussian and square-completion lemmas are useful ingredients but do
   not establish the missing continuous-kernel partition estimate.
2. **Abstract implications have not been instantiated on the physical model.**
   The concrete torus/grid construction, periodic adjacency/volume estimates,
   H2-to-`SingularKernel` bridge and exponential slice integrability used by the
   bad-event estimate remain unproved. In particular, a.e. cutoff hypotheses
   must be transported to the pointwise abstract interfaces using justified
   representatives; they cannot simply be supplied as further assumptions.
3. **Full paper scope is broader than the conditional target.** The manuscript
   fixes a Fourier-normalized periodic logarithmic kernel and presents H1 as
   the macroscopic assumption. This project's authorized contract additionally
   assumes H2 (`notes/hypotheses.md`). The new target honestly treats `g` as
   supplied data satisfying H1/H2; it does not identify or construct the
   manuscript's particular kernel or prove its cutoff decomposition. A proof
   of this conditional target would therefore need a separate application
   argument before it certifies the manuscript's H1-only theorem.

## Specification checks

The period-one torus and normalized product Haar measure match the source
normalization. The radius is the Euclidean combination of coordinate circle
distances. The energy uses `1/N` times the ordered off-diagonal pair sum; the
Gibbs exponent is `beta/2` times that energy, with the source's positive sign.
The finite constant is chosen before all particle numbers and temperatures.
The principal target requires `N >= 2`; the bulk target requires `N >= 1`, as
in the manuscript. Both include the endpoint `beta0 = 0`.

The partition uses an extended nonnegative integral and a finite `NNReal`
bound, preventing a divergent Gibbs expectation from becoming zero through
Lean's totalized real integral. Finite-entropy densities explicitly include
normalization, nonnegativity and entropy integrability. The repaired H1 also
requires joint energy integrability, making its real quadratic expression
meaningful rather than silently accepting undefined-integral zero values.
For bounded continuous bulk kernels this energy domain is justified by
boundedness and density integrability.

H2 records the decomposition, support, logarithmic upper bound, mean bound,
positive quadratic forms and domination by `g`. Its continuous bulk is bounded
on the compact torus. Its a.e. conditions are suitable for independent Haar
particles, subject to the still-missing bridges noted above. No requested
partition bound is included as an input field. No obvious circular conclusion
or contradictory premise was found; no Lean nonvacuity witness was constructed
by this reviewer.

## Supporting proof checks and dependencies

The reviewer read the actual `Decoupling.exp_bound`, the integrability argument
in `Grouped.grouped_exp_bound`, `BadEvent.bad_gibbs_bound`, the singular-kernel
interface, its logarithmic moment argument and `Singular.lemma51`, together with
related definitions. D7 derives exponential integrability from summable even
moments; G3 supplies integrability before applying Holder; S8 bounds nonnegative
extended integrals before deriving its final real-integral bound. These sampled
paths do not reuse the invalid bounded-kernel premise. B6 explicitly requires
exponential slice integrability; its proof does not establish that application
premise on its own. This is a targeted source-level review, not a line-by-line
independent reproving of every supporting lemma.

The final contract tracks `PGRID`, `PSING` and `PEXP` separately. Refinement of
physical grids is now an A6 prerequisite, and the main parameter/application
path waits for the physical instances. PEXP explicitly requires deriving
exponential integrability for the supplied H2 kernel, rather than silently
specializing to an unidentified normalized kernel. The graph is a conservative
milestone map; provisional auxiliary names are not independently certified
mathematical statements. The actual final target types remain essential.

The compiler expression comparison alpha-normalizes binder display names and
removes elaborator metadata. These changes preserve the mathematical expression
and are appropriate for the supplementary structural comparison. This review
does not claim an external Comparator run. The separate Lean-verification
review and actual run evidence must establish compilation and kernel audits;
this reviewer did not run Lean locally or launch proof/model workers.

## Reviewed source and freeze

Read: `notes/sec1-setting.tex` through `sec6-lemma61.tex`, `notes/appendixA.tex`,
`notes/00-preamble-macros.tex`, `notes/hypotheses.md`, relevant phase notes,
`Challenge.lean`, `Solution.lean`, `verification/contracts.json`,
`verification/README.md`, the supporting declarations listed above and the
relevant harness code. The adjacent JSON receipt binds the complete candidate
input freeze, excluding review reports/receipts to avoid self-reference.

The earlier **107/107 closed queue entries certify existing proof obligations,
not coverage of declarations never written**. The final mathematical verdict
must remain incomplete until the bulk, main and concrete application obligations
are implemented and checked. This receipt intentionally has `verdict=findings`
and cannot satisfy the gate's required successful final mathematical review.

## Receipt refresh for final harness revision

The reviewer inspected the limited post-review changes in `scripts/verify.py`,
`scripts/tests/test_contracts.py` and `verification/contracts.json`. Fresh Lean
paths now allow only the fresh project path, resolved artifact directories of
the individually locked dependencies and the actual toolchain library path;
the test covers external package symlinks and rejection of old project paths.
Current review identities are recorded even when the verdict is `findings`,
while the separate successful-review gate still requires `passed`. These
changes do not turn this mathematical review into a success.

The physical obligations are now named `LogGas.Torus.grid`,
`LogGas.Physical.singular_instance` and
`LogGas.Physical.log_exp_integrable`. Moving these planned constructions below
Main avoids the future Bulk-to-Main-to-Bulk import cycle and does not discharge
the missing proofs. Challenge, Solution and the mathematical support sources
are unchanged. The adjacent receipt and missing-declaration list were refreshed
against the final input freeze; the verdict remains **findings**.
