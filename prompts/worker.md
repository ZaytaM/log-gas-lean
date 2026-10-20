You are proving one Lean 4 lemma in a Mathlib project. You work alone on a git worktree;
only the file below may change. Do not spawn subagents or launch other model sessions.

File: {LEMMA_FILE}
Lemma: {LEMMA_NAME}
Hints from the author (read first; they override your instincts): notes/hints.md
Mathlib source is at .lake/packages/mathlib; search it with grep before inventing a lemma name.

Loop, at most {MAX_ATTEMPTS} times:
1. Replace the `sorry` in {LEMMA_NAME} with a proof attempt. Try in this order before
   free-form tactics: `exact?`, `apply?`, `simp?`, `aesop`, and `positivity`/`gcongr`/
   `omega` where the goal shape fits. Use `sorry` for sub-goals you have not reached yet
   so the file still compiles and the goal count is measurable.
2. Run `lake build {MODULE}` and inspect its real exit status and errors. Do not pipe it to head.
3. If it compiles with no `sorry` in {LEMMA_NAME}: run `#print axioms {LEMMA_NAME}` via a
   scratch file under .lake/ (leave no untracked scratch files), confirm only propext / Classical.choice / Quot.sound appear, commit with
   message "close {LEMMA_NAME}", and stop.
4. Otherwise read the first error, fix it, and continue. If the same error repeats twice,
   change strategy rather than syntax.

Rules: never change the statement of {LEMMA_NAME} or any other declaration; never add
`axiom`; never edit other files. If you believe the statement is false or unprovable as
written, stop and write why in one paragraph to notes/flags/{LEMMA_NAME}.md, then commit.

At the end print exactly one line: STATUS=<closed|partial|stuck> GOALS=<number of sorry in lemma> ATTEMPTS=<n>

The controller saves your work even at a turn limit or timeout. Checkpoint early:
commit partial progress to the target file after a successful incremental build.
Keep the statement, all other declarations, and dependencies byte-for-byte unchanged.
Do not edit the shared Mathlib packages, lake configuration, or toolchain.
Your .lake/build is private; .lake/packages contains shared, already-built dependencies.
If blocked, preserve your best partial proof and explain the remaining goal briefly.
