# log-gas-lean

Lean 4 formalization of Theorem 1.1 of *An entropy bound for the attractive logarithmic gas*
(Delgadino–Gvalani–Rosenzweig). Toolchain `leanprover/lean4:v4.36.0-rc1`, Mathlib
`625d8914199bc567cca9b91f90e8e5afafa5ae51` (pinned in `verification/dependency-lock.json`).

**Status (2026-10-22).** `PaperSolution.lean` proves `LogGasPaper.main : PaperTheorem` and
`LogGasPaper.kernel_exists : LogKernelExists` against the frozen statement file `PaperChallenge.lean`
(which imports only Mathlib). A fresh build, `#print axioms` (only `propext`, `Classical.choice`,
`Quot.sound`), definition parity between challenge and solution, and a `leanchecker` replay all pass
(`scripts/verify.py --fresh`, evidence under `logs/verification/`). No `sorry` remains anywhere.

What that does and does not certify is recorded in **`Audit/`** (start at `Audit/README.md`):
the statement layer is frozen but awaits the owner's sign-off (`Audit/SIGNOFF.md`); fresh-context
fidelity reviews and an independent-kernel replay (lean4export + Nanoda on fac5, `Audit/Replay/`) are
prepared but not yet run; the satisfiability of the log-HLS hypothesis (Beckner–Onofri input) is not
proved here and is to be imported. The manuscript of record and the map from its statements to Lean
are `Audit/MANUSCRIPT.md` and `Audit/statement_map.md`.

The theorem was produced by two automated campaigns on Dell3 (a proof queue for the pre-written
statements, then an Opus-coordinated construction campaign for the missing modules); both are
complete and stopped. Their machinery (`scripts/`, `prompts/`, `reports/`, `state/`) is retained
for provenance; nothing needs to run for the proofs to be checked.

## Layout

- `PaperChallenge.lean`, `PaperSolution.lean` — the paper theorem: frozen statement and its proof.
- `Challenge.lean`, `Solution.lean` — the earlier conditional H1/H2 target and its proof.
- `LogGas/` — the proof library (44 modules); `LogGas/PaperMain.lean` assembles the theorem.
- `Audit/` — certification record (freeze, sign-off, statement map, reviews, replay).
- `manuscript/` — manuscript of record (short draft followed by the formalization; canonical paper).
- `verification/` — the gate (`scripts/verify.py`), contracts, dependency lock, review receipts.
- `notes/` — TeX excerpts of the short draft used by the campaigns (hashes in `contracts.json`).

## Checking the proofs yourself

```
lake exe cache get          # Mathlib oleans for the pinned revision
lake build PaperChallenge PaperSolution Challenge Solution
python3 scripts/verify.py --fresh
```

The gate reports `incomplete` until an external-kernel check is supplied; see `verification/README.md`
and `Audit/Replay/DESIGN.md`.

## Campaign machinery (historical)

The sections below describe the automated campaigns that produced the proofs; they are complete.

### Operate on Dell3

From this repository on Dell3:

```
bash scripts/install_service.sh     # install reboot/watchdog recovery and start
bash scripts/service.sh status     # queue, usage, controller, reset and push status
bash scripts/service.sh stop       # save active work; watchdog honors this stop
bash scripts/service.sh start      # resume explicitly after a manual stop
bash scripts/service.sh retry-blocked  # after resolving author-review issues
```

From the Mac, prefix these commands with `ssh dell3` and run them in
`~/work/log-gas-lean`. The tmux session is `loggas-service`; its log is
`logs/service/controller.log`. `scripts/pipeline.sh` is a compatibility entry
point for the continuous controller; it no longer runs just one nightly batch.

The installer preserves other cron entries. It adds reboot recovery and a
five-minute watchdog. A completed queue or explicit stop is not restarted by
that watchdog. Unexpected controller exits are retried by the supervisor.

## Progress, verification, and recovery

- `reports/persistent.md`: deterministic queue report, estimated cost and attention items.
- `state/worker_usage.tsv`: per-attempt outcomes, token/cache usage, cost and duration.
  Costs include every service model invocation; unknown usage is explicitly marked.
- `state/runtime/queue.sqlite3`: durable tasks, attempts and quota-reset state.
  This directory and detailed logs are intentionally untracked.
- `wt/service/`: private worker checkouts with separate `.lake/build` outputs;
  installed dependency packages are shared. Existing legacy worktrees are retained.
- Repeatedly stuck targets rotate through the queue with increasing cooldowns,
  capped at daily retries. Author-review flags block only the affected target.
- Before accepting a proof, the controller requires the statement and other
  declarations to be unchanged, builds its module, and checks its transitive
  axioms against `propext`, `Classical.choice`, and `Quot.sound`.
- Proofs introduced centrally also receive an axiom check. A proof whose prerequisites
  remain unfinished is `waiting_dependencies`; it is rechecked after source changes
  without launching another model worker.
- Complete saved proofs are refreshed against current main and checked before any
  model is called. A prerequisite merged during a worker run is also refreshed before
  its candidate is audited. Complete candidates waiting on prerequisites use
  `waiting_saved_dependencies` and are rechecked after source changes without new
  model usage or increased attempt counts.
- Each merge gets a full project build and another axiom check on main. A valid
  proof is recovered even if its worker finished at the turn limit.
- Proofs, author flags, and usage reports are committed and pushed incrementally.
  A failed push leaves commits intact and retries automatically. A divergent
  remote is reported for operator reconciliation; it is never force-pushed.
- Interrupted workers are identified by PID plus process start time, stopped,
  and their files recovered. Partial proof snapshots and checkpoint refs survive
  retries. Restart recovery also rolls back an interrupted, unverified integration.

The controller also checks required source milestones. When existing proofs are
closed but required declarations are absent, it reports `needs_implementation`
and stops model dispatch. The watchdog respects that state; after implementing
missing declarations, start the service explicitly. Final completion requires
the separate build, source-coverage, target-contract and independent review gate:
`python3 scripts/verify.py --fresh`. When only blocked existing targets remain,
the service stays alive and reports the needed author decisions.

## Settings and tests

Edit `scripts/pipeline.conf` while the service is stopped, then restart it.
Workers have 20 model turns and a 10-minute timeout per invocation. Subagent
and recursive model delegation are disabled. `pipeline.conf.cheap` is a legacy
preset; its dollar/task caps have no effect on the persistent controller.
`PRIORITY_MODULES` places ready tasks from the repaired Decoupling/Grouped chain first;
retry cooldowns still allow other modules to progress.

Offline regression tests use fake models and Lean commands with real Git worktrees:

```
python3 -m unittest discover -s scripts/tests -v
```

No model usage is consumed by these tests. Heavy builds and real proof work run
on Dell3. Keep the main checkout dedicated to the controller while it is active.
