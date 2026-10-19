You are writing the Lean 4 / Mathlib skeleton for one phase of a formalization.

Project root: the current directory (a Lake project; `lakefile.toml` lists Mathlib).
Phase notes: {PHASE_NOTES}  (read it fully; it names the target file and statements)
Paper source for this phase: {TEX_FILES}  (LaTeX; macros in notes/00-preamble-macros.tex)
Standing hypotheses: notes/hypotheses.md  (these may appear as arguments; never as axioms)

Produce or update the target Lean file so that:
1. Every numbered statement of the phase is a `theorem` or `lemma` whose name is
   `LogGas.<phase>.<short_name>` and whose docstring quotes the paper's equation label.
2. Every proof is exactly `by sorry`, except trivial restatements you can close in one line.
3. Each lemma is preceded by a comment `-- SKETCH: ...` of 2–6 lines giving the proof
   plan from the paper, naming the Mathlib concepts you expect to be used.
4. Statements are in the weakest generality that still matches the paper. Prefer
   bounded measurable functions and finite index types (`Fin n`) over general ones.
   Put integrability or measurability side conditions as explicit hypotheses.
5. Order lemmas so each depends only on earlier ones in the file or on Mathlib.
6. The file must compile: run `lake build LogGas.<File>` and fix errors until it does.

Do not attempt proofs beyond one-liners. Do not change other files.
When finished, print a list: lemma name — one-line statement — expected difficulty (low/medium/high).
