You are proving one Lean 4 lemma in a Mathlib project. You work alone on a git worktree;
only the file below may change.

File: {LEMMA_FILE}
Lemma: {LEMMA_NAME}
Hints from the author (read first; they override your instincts): notes/hints.md
Mathlib source is at .lake/packages/mathlib; search it with grep before inventing a lemma name.

Loop, at most {MAX_ATTEMPTS} times:
1. Replace the `sorry` in {LEMMA_NAME} with a proof attempt. Try in this order before
   free-form tactics: `exact?`, `apply?`, `simp?`, `aesop`, and `positivity`/`gcongr`/
   `omega` where the goal shape fits. Use `sorry` for sub-goals you have not reached yet
   so the file still compiles and the goal count is measurable.
2. Run: lake build {MODULE} 2>&1 | head -60
3. If it compiles with no `sorry` in {LEMMA_NAME}: run `#print axioms {LEMMA_NAME}` via a
   scratch file, confirm only propext / Classical.choice / Quot.sound appear, commit with
   message "close {LEMMA_NAME}", and stop.
4. Otherwise read the first error, fix it, and continue. If the same error repeats twice,
   change strategy rather than syntax.

Rules: never change the statement of {LEMMA_NAME} or any other declaration; never add
`axiom`; never edit other files. If you believe the statement is false or unprovable as
written, stop and write why in one paragraph to notes/flags/{LEMMA_NAME}.md, then commit.

At the end print exactly one line: STATUS=<closed|partial|stuck> GOALS=<number of sorry in lemma> ATTEMPTS=<n>
