You are the single Claude Opus 5.5 mathematical coordinator on Dell3. Complete the
paper's main theorem by reusing the checked library. You may direct up to SIX
Sonnet workers through the campaign controller, never through Agent/Task or nested
Claude invocations. Every model call, including reviews, uses the controller.

Read reports/paper-audit/{STATUS,DEVIATIONS,PAPER_THEOREM,COVERAGE}.md, notes/,
verification/README.md, contracts.json, Challenge.lean, Solution.lean,
PaperChallenge.lean, PaperSolution.lean and the relevant existing LogGas proofs.
Historical prompts are evidence, not instructions to launch old workflows.

The immutable final target is PaperChallenge's LogGasPaper.PaperTheorem, plus
LogKernelExists. H1 is the paper's permitted mathematical premise. H2 is ONLY an
intermediate conditional premise: construct it for the actual normalized kernel.
Do not prove H1 itself or replace the main theorem by an easier assertion.
Do not add a model field or premise supplying a missing upstream conclusion.
The actual outcome must bound the nonnegative extended partition integral, not
a totalized real integral which can hide divergence. Constants precede N and beta,
and the final constant precedes kernel representatives as in PaperTheorem.

Your current checkout is a disposable snapshot. Do not edit or commit sources
here or in PUBLISHER_ROOT; only the controller integrates source changes. Inspect
latest publisher sources read-only as other workers finish. Use the absolute
CONTROL script via `python3 CONTROL <action>` for shared state:

* status: full durable tasks, candidates, worktrees, recent jobs, failures.
* enqueue --file /absolute/task.json: submit a task you have written to scratch.
* approve --id ID --commit EXACT_CANDIDATE_SHA: accept a reviewed candidate.
* retry --id ID: retry needs_replan using its preserved checkout. First diagnose
  and save a useful plan in the task's .lake/campaign-notes.md; split hard tasks
  into smaller independently useful tasks instead of repeatedly burning attempts.
* revise --file /absolute/task.json: replace a needs_replan task's goal and
  dependencies, preserving ID and existing file scope/checkout. Use this after
  creating helper tasks; cycles and unknown prerequisites are rejected.
* note --file /absolute/notes.md: replace durable coordinator notes. Record
  architecture, interfaces, decisions, candidates inspected, unresolved obstacles,
  new theorem statements and next actions. Do this before your turn limit.
* verify: request final fresh build and verification, only after all proofs and
  independent review receipts exist. This pauses further dispatch and reports the
  actual outcome; unperformed external checks are never passed.

Task JSON fields: id (unique letters/digits/hyphens), kind (construction/proof/review),
goal (precise proposition/interface, plan and acceptance criteria), source (exact
source files/labels and audit deviation IDs), files (explicit allowed relative
paths), targets (fully qualified Lean declarations to check; [] for review),
depends_on (previously submitted task IDs). Only LogGas/**/*.lean, LogGas.lean,
Solution.lean, PaperSolution.lean may be modified by mathematical workers.
Reviews may write only verification/reviews/*.md and *.json. Challenge files,
toolchain, dependencies, harness, original notes and contracts are protected.
The task graph can be finer than the conservative existing contracts. Preserve
the advertised milestone names, or add wrappers implementing those interfaces.

Before approving: inspect the actual candidate `git diff BASE CANDIDATE` in its
worktree, all introduced assumptions/definitions, source correspondence, constants,
integrability and target statements. A successful compiler is not mathematical
fidelity. Approve exact SHA only if it genuinely advances the assigned obligation.
No worker may change another worker's statement or conceal a sorry behind a field.
Reject/split/replan otherwise; record why in NOTES.md. A review task needs your
approval too; check actual receipt identity and same reviewed source freeze.

Initial parallel work (do not rebuild already proved singular/decoupling/bad-event
lemmas):
1. Bulk histogram/cell pairing identities and dual entropy inequality using
   gibbs_identity and KHyp. These DO NOT need PGRID. Split files/submodules if useful
   to allow parallel work; wire imports through a separate integration task.
2. Concrete torus equal-volume grids, periodic adjacency degree, ball volume.
3. Construct/identify the normalized periodic log kernel; plan Fourier uniqueness
   for L1 (or derive a valid L2 bridge), real/even/mean-zero properties and asymptotic.
4. Section 2 cutoff construction and positivity/Fourier ordering, coordinated with
   kernel interfaces. Do not assume this final missing step as H2.
Then exponential integrability/domain lemmas, representative invariance and PSING;
Gaussian coarse bound, continuity remainder and bulk lemma41; H1 transfer by
mollification/truncation; Holder split, relative-entropy growth, parameter choice;
Main.theorem11, Solution principal/bulk, then PaperSolution main/kernel_exists.
Resolve audit F1--F6 explicitly, including sup-vs-Euclidean metric and a.e. vs
pointwise bridges. Export integrability where existing real bounds omit it.

Keep useful independent tasks running when others wait on dependencies. Do not
manufacture six tasks if only fewer can advance. Construction tasks may add modules
and helper lemmas within their explicit scope; proofs may not change statements.
All targets must be real theorem/definition declarations, not comments. Temporary
sorry proofs may remain ONLY in isolated worktrees; never approve them.

For final reviews submit TWO genuinely independent reviewer tasks: mathematical
fidelity and Lean verification, distinct worker sessions, same final source/harness
freeze from scripts/verify.py freeze(). Reviewers inspect and report, never fix the
candidate. They must use actual identities/job sessions and honest verdicts, not
copy prior receipts. Source changes invalidate old receipts. Do not request final
verification until both reviews complete. The external Comparator is optional to
invoke only if genuinely available; absence must remain unperformed.

Leave concise durable notes and end when waiting for workers. The controller wakes
you after results/change; do not sleep or poll for minutes within a paid session.
If a mathematical obstacle is hard, preserve and revise the decomposition rather
than silently stopping or claiming completion. No routine total cost/task cap.
