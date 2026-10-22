# Fidelity review of the log-gas formalization: instructions for the reviewer

You are reviewing a Lean 4 formalization of Theorem 1.1 of *An entropy bound for the attractive
logarithmic gas* (Delgadino, Gvalani, Rosenzweig). Your job is a fresh-context **fidelity
review**: decide whether the Lean statements say what the manuscript says. Do **not** check
whether the proofs are correct — the Lean kernel has (see "Evidence"). Work from this package
only. Do not modify anything under `snapshot/`. Form your own judgement before reading any
earlier review.

## What you are given

- `snapshot/`: the repository at the commit named in `evidence/COMMIT.txt`.
  - `snapshot/manuscript/attractive_log_gas_short_draft.tex` (+ `.pdf`): the document the
    formalization follows (statements copied from the canonical paper; proof prose paraphrased).
  - `snapshot/manuscript/attractive_log_gas_I.tex` (+ `.pdf`): the canonical manuscript. Its
    `thm:principal` Part A(i) (line 448–460) and (1.3) (line 1335) are the statement of record.
  - `snapshot/PaperChallenge.lean`: the **frozen statement** (`LogGasPaper.PaperTheorem`,
    `LogKernelExists`) and the definitions it uses. 130 lines, imports only Mathlib.
  - `snapshot/Challenge.lean`: the earlier conditional target (`LogGasChallenge.principalStatement`,
    `bulkStatement`).
  - `snapshot/LogGas/`: the proof library (44 modules). You need it only for Task 4.
  - `snapshot/Audit/statement_map.md`: the authors' map from manuscript items to Lean names, with
    encoding choices marked **REVIEW**. `snapshot/Audit/tex_numbering.txt` gives label line numbers.
  - `snapshot/Audit/SIGNOFF.md`: the questions put to the owner. Answer them independently.
  - `snapshot/reports/paper-audit/DEVIATIONS.md`, `PAPER_THEOREM.md`: an earlier model audit made
    *before* the proofs existed. Do not rely on it; consult it afterwards to note agreement or not.
  - `snapshot/verification/reviews/*.md`: the campaign-internal reviews. Same rule.
- `evidence/`
  - `COMMIT.txt`, `freeze.json`: commit and SHA-256 of every source file.
  - `print_axioms.txt`: `#print axioms` for the four targets and the 24 milestone declarations.
    Each depends only on `propext`, `Classical.choice`, `Quot.sound`.
  - `statement_types.txt`: `pp.all` elaborated types of every frozen declaration (what Lean
    actually sees, with all implicit arguments and coercions explicit). Use it when the surface
    syntax is ambiguous.
  - `final-verification.log`: the full gate output (build, parity, kernel replay, reviews).
  - `manuscript.sha256`: hashes of the manuscript files.

## Tasks

1. **Theorem 1.1, end to end.** Read the short draft's `thm:principal` (line 163) and standing
   definitions (1.1)–(1.3), then the canonical Part A(i) (line 455) and (1.3) (line 1335). Read
   `PaperChallenge.lean` from `Torus` to `PaperTheorem`, unfolding every definition down to Mathlib
   (`uniform`, `fourierCoeff`, `kernelCoeff`, `IsLogKernel`, `FiniteEntropyDensity`, `relEntropy`,
   `logEnergy`, `LogHLS`, `offDiagEnergy`, `partitionFunction`). Decide whether `PaperTheorem` is
   the manuscript's theorem. Check: quantifier order (is C before g, N, β?); the domain of N, β,
   B, β₀; `ℝ≥0∞` vs `ℝ` (where is `⊤` possible? truncated subtraction? `x/0`?); Bochner integrals
   of possibly non-integrable functions (Lean gives 0); a.e. vs everywhere; normalizations
   (1/N, β/2, ordered vs unordered pairs, c_d, 2π, sign of the interaction).
2. **The kernel.** Is "every integrable g with `fourierCoeff g k = kernelCoeff d k`" an acceptable
   encoding of "the kernel g of (1.1)"? Check c_d, the Fourier convention and the lattice norm.
   Note that `LogAsymptotic` is neither premise nor conclusion.
3. **Encodings marked REVIEW** in `statement_map.md` (P1, P3, P7, P9, S8, A2, PGRID, PSING). For
   each, say whether it is faithful, a harmless strengthening, or a weakening, and why.
4. **Non-vacuity.** Look for ways `PaperTheorem` could be trivially true:
   - unsatisfiable premises: can some g satisfy `IsLogKernel d g` *and* `LogHLS g B` with B > 0?
     (`LogKernelExists` is proved; `LogHLS` satisfiability is NOT proved — state what you believe
     and what would settle it);
   - conclusions true because a value is `⊤`, `0`, or a junk value (`Classical.choose`, division by
     0, Bochner integral of a non-integrable function);
   - definitions coinciding with something trivial (e.g. a `partitionFunction` that is always
     finite for a wrong reason).
   Report concrete instances; do not stop at generic worries.
5. **Definitional copies.** `LogGas.Paper.paperTheorem` (`LogGas/PaperMain.lean`) and the
   `LogGas.Torus`/`LogGas.Spec` definitions are copies of the `LogGasPaper` ones so that the
   library does not import the challenge. Confirm `PaperSolution.lean` proves the *frozen*
   `LogGasPaper.PaperTheorem` (the gate elaborates `example : PaperTheorem := LogGasPaper.main`;
   check that this is what you would expect and that no definition in `PaperSolution.lean`
   differs from `PaperChallenge.lean` — `diff` the two files).
6. **Coverage.** Which parts of the canonical `thm:principal` are covered (Part A(i) only), and is
   that stated honestly in `Audit/README.md` and `SIGNOFF.md`?

## Output

One Markdown file `output/review_<your-identity>_<date>.md`:
1. A verdict paragraph: is `PaperTheorem` a faithful formalization of Theorem 1.1 (given (1.3)),
   yes or no, with the main reasons.
2. A table `ID | manuscript item (file:line) | Lean (file:line) | PASS / ISSUE / NOTE | evidence`.
   An **ISSUE** changes mathematical content; a **NOTE** is an encoding choice that does not.
3. One section per ISSUE: exact Lean text, exact manuscript text, why they differ, suggested fix.
4. Results of Tasks 4–6.
5. Where you disagree with `DEVIATIONS.md` or the campaign-internal reviews, if anywhere.

Quote line numbers. When you cannot decide, say so and say what would settle it. Record your
identity (model and version, or name), the date, and the commit you reviewed. Do not change the
proofs or the repository.
