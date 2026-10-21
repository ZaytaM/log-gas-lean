# log-gas-lean

Lean 4 formalization of “An entropy bound for the attractive logarithmic gas”
(Delgadino–Gvalani–Rosenzweig), running continuously on Dell3.

**Final theorem verification is incomplete.** All 107 previously queued proof
placeholders were closed, but the source-coverage gate now detects that the
bulk theorem `LogGas.Bulk.lemma41` and principal theorem
`LogGas.Main.theorem11` were never implemented. The proof queue's old `complete`
state did not certify those absent declarations. See
[the independent specification, dependency contracts and final verification](verification/README.md).

The construction campaign uses one Claude Opus 5.5 coordinator and up to six
Sonnet workers. It creates missing modules/lemmas, reviews exact candidate patches,
and integrates only rebuilt results. Start/manage it with:

```
bash scripts/campaign.sh install  # reboot recovery + watchdog + start
bash scripts/campaign.sh status
bash scripts/campaign.sh stop
```

The previous `service.sh` proof-only queue is retained for history and must remain
stopped while the campaign owns main. Runtime state is in
`state/runtime/campaign/`, preserved checkouts in `wt/campaign/`, progress in
`reports/campaign.md`, and per-call usage in `state/campaign-usage.tsv`.
Coordinator and worker costs are client estimates; missing usage is unknown.
There is no routine total cost cap.

`PaperChallenge.lean` independently specifies the full paper theorem and kernel
existence. `PaperSolution.lean` must prove both; compiling their definitions is
not completion. The older H1/H2 Challenge remains an intermediate milestone.

The legacy controller kept six Sonnet workers busy across Claude allowance resets.
It waits automatically when an actual session, weekly, or rate limit is reached,
then retries after the advertised reset time. When no reset time is available,
it backs off from five minutes to one hour. Turn limits and individual errors
checkpoint and requeue that target; they do not stop unrelated work.
There is no routine total-task or estimated-dollar stopping budget.

## Operate on Dell3

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
