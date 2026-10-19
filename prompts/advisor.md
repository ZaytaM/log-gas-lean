A worker has failed to prove a Lean 4 / Mathlib lemma for several nights. Diagnose; do not prove.

Lemma file: {LEMMA_FILE}
Lemma: {LEMMA_NAME}
Paper source: {TEX_FILES}; standing hypotheses: notes/hypotheses.md
Worker attempt log (last 3 attempts with errors): {ATTEMPT_LOG}
Author hints so far: notes/hints.md

Answer with exactly one verdict, then its payload, nothing else:

VERDICT=strategy
  A different proof route the worker should take, 3–8 lines, naming Mathlib declarations
  you have verified exist by grep in .lake/packages/mathlib.

VERDICT=split
  Two or three auxiliary lemma statements, in Lean syntax, each `by sorry`, that together
  imply the target by a short argument you describe in two lines. The orchestrator will add them.

VERDICT=statement
  The statement as written does not match the paper or is unprovable. Quote the paper's
  text, state the mismatch in one sentence, and give the corrected Lean statement. This
  goes to the author for approval; do not edit files.

Prefer `strategy` over `split`, and `split` over `statement`. Keep the whole answer under 40 lines.
