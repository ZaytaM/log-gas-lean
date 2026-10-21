# PaperStatement.lean compile record

Date: 2026-10-21T20:45:53Z. Host: dell3.ma.utexas.edu. Toolchain: Lean (version 4.36.0-rc1, x86_64-unknown-linux-gnu, commit c9afcddf514a6772bd4d649f7cfc04eff0b9f15e, Release).
Mathlib: 625d8914199bc567cca9b91f90e8e5afafa5ae51 (pinned in lake-manifest.json: 625d8914199bc567cca9b91f90e8e5afafa5ae51).

No `lake` command was run (avoids any manifest resolution/rebuild). `lean` was invoked directly with
`LEAN_PATH` = the `.lake/build/lib/lean` directory of every pinned package under `.lake/packages/` (symlinks resolved):

```
LP=$(for p in .lake/packages/*; do printf "%s:" "$(readlink -f $p)/.lake/build/lib/lean"; done)
LEAN_PATH=$LP lean reports/paper-audit/PaperStatement.lean
```

File sha256: df8ee418b05166313bd744f63b4e099d187b4ea63b7cbae0d8989a808243a88b

## Attempt 1 (failed)

Exit 1. All definitions elaborated; the only errors were in my trivial lemma `PaperTheorem.perKernel`
(wrong `intro` order). Output:

```
reports/paper-audit/PaperStatement.lean:149:36: error: Application type mismatch: The argument
  β₀
has type
  LogHLS g B
of sort `Prop` but is expected to have type
  ℝ
of sort `Type` in the application
  h d hd B hB0 hB β₀
reports/paper-audit/PaperStatement.lean:150:20: error: Application type mismatch: The argument
  hH
has type
  hβ0 < B
but is expected to have type
  LogHLS g B
in the application
  hC g hg hH

real	0m36.454s
user	0m3.149s
sys	0m5.610s
```

## Attempt 2 (final file) — exit 0, no errors, no warnings

```

real	0m27.322s
user	0m3.127s
sys	0m4.481s
```

## Axiom check

Scratch copy `.lake/paper-audit-scratch/PaperStatementAxioms.lean` (ignored dir) = the final file plus:

```

#print axioms LogGasPaper.LogHLSWithDomain.toLogHLS
#print axioms LogGasPaper.PaperTheorem.perKernel
#print axioms LogGasPaper.PaperTheorem
#print axioms LogGasPaper.LogKernelExists
#check @LogGasPaper.PaperTheorem
example : (LogGasPaper.uniform 2) Set.univ = 1 := measure_univ
```

Command `LEAN_PATH=$LP lean .lake/paper-audit-scratch/PaperStatementAxioms.lean`, exit 0, output:

```
'LogGasPaper.LogHLSWithDomain.toLogHLS' depends on axioms: [propext, Classical.choice, Quot.sound]
'LogGasPaper.PaperTheorem.perKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'LogGasPaper.PaperTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'LogGasPaper.LogKernelExists' depends on axioms: [propext, Classical.choice, Quot.sound]
LogGasPaper.PaperTheorem : Prop
```

This certifies only that the *statement* is well-formed and axiom-clean. `PaperTheorem` is NOT proved.
