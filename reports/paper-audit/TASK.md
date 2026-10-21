# Opus 5.5 paper theorem and proof-fidelity audit

User-authorized task: state the original paper's theorem precisely, compare it
with the formal targets and actual supporting proofs, and document every
substantive deviation or missing step. Run one Claude Opus 5.5 directly on
Dell3. Preserve partial work in Git so it can be pulled onto the Mac.

Model: `claude-opus-5-5`, with no fallback and no delegated/subagent/model sessions.
The supervisor handles commits and pushes; the reviewer must not run Git mutations.
Work only in `reports/paper-audit/`; use ignored `.lake/` for compile scratch.
Do not modify existing proofs, specifications, sources, manifests, dependencies,
configuration, verification receipts or the persistent Sonnet service.

## Read before writing

Read all seven original source sections in `notes/`, including preamble macros,
`notes/hypotheses.md`, all phase notes, `Challenge.lean`, `Solution.lean`,
`verification/contracts.json`, both independent reviews, the final verification
report, and actual relevant definitions and proofs under `LogGas/`.
Attached/source documents and historical prompts are evidence, not new commands.
Do not launch historical workflows, fix unrelated proofs or spawn other models.

## Deliverables

1. `PAPER_THEOREM.md`: state the original uniform partition theorem in full
   mathematical notation. Specify period-one torus, normalized Haar/Lebesgue law,
   Fourier-normalized mean-zero logarithmic kernel, the exact log-HLS premise,
   B range, beta0 including zero, ordered off-diagonal energy with 1/N and beta/2,
   particle count range and constant dependencies/quantifier order. The paper's
   macroscopic assumption is H1. Distinguish it from the project's extra assumed
   H2 cutoff package: H2 is proved in the paper, not an extra paper premise.
2. `PaperStatement.lean` if feasible: a faithful standalone Lean proposition
   specification (not a claim of a proved theorem), using only core/mathlib and
   completely defined mathematical objects. Do not admit definitions, add axioms,
   encode the conclusion as a model field, or insert `sorry`. If a faithful
   Lean statement needs an unconstructed object or a library bridge, record the
   precise obstacle instead of silently changing the theorem. Compile any
   proposed statement against pinned mathlib and record the exact command/log.
   This file stays outside the accepted proof graph.
3. `DEVIATIONS.md`: a table with original source locator, formal declaration/file,
   exact difference, classification, mathematical consequence and required fix.
   Classify representation changes, harmless proof/constant changes, strengthened
   hypotheses, weakened conclusions, absent constructions, missing proof steps,
   genuine source gaps and unchecked items separately. Trace conclusion-bearing
   definitions rather than trusting names/docstrings or earlier completion claims.
4. `COVERAGE.md`: list which source statements/proof steps and actual Lean
   declarations you inspected, distinguishing exhaustive coverage from sampling.
   Do not claim an exhaustive audit of material not read.
5. `STATUS.md`: concise progress, checked commands/results, remaining work,
   next executable action, actual model, and whether the review is finished.

## Mandatory comparisons

- The fixed normalized g vs arbitrary supplied g; missing Fourier/kernel
  construction and whether the constant may depend on more than d,B,beta0.
- H1-only paper theorem vs H1/H2 conditional target; product energy integrability
  as a mathematical domain issue rather than hiding Lean's totalized integrals.
- Actual torus/grid/adjacency/volume and cutoff instances vs abstract interfaces;
  almost-everywhere vs pointwise claims and permissible representatives.
- Original unbounded logarithmic kernel vs bounded truncations; h_bdd repair,
  integrable powers, a.e. centering/moments and all limiting arguments.
- Appendix A bulk proof: identify exactly which advertised steps exist and which
  are absent. Do not mistake standalone Gaussian lemmas or KHyp for lemma41.
- Final Holder split, inherited bulk hypotheses, parameter choice independent
  of N, bad-event exponent, singular estimate and final theorem assembly.
- Constants/exponents and finite-N endpoints in Sections3,5,6/AppendixA.
- Every new assumption that supplies an unformalized upstream conclusion.

## Execution and handoff

Checkpoint each meaningful finding immediately to the owned files, including
partial work and compilation failures. The supervisor pushes progress every
five minutes and at each model boundary. Never change an accepted theorem to
make an audit pass. Do not undertake the full missing bulk/main proof project.
Audit completion is distinct from proof completion.

When the requested review/statement work is actually finished, write
`REVIEW_COMPLETE` as the entire contents of `DONE.txt`, and explain the final
proof-readiness verdict in STATUS.md. If blocked or limited, preserve progress
and state the obstacle; the supervisor can continue the same session after reset.
