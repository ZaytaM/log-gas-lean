# log-gas-lean

Lean 4 formalization of “An entropy bound for the attractive logarithmic gas”
(Delgadino–Gvalani–Rosenzweig), running continuously on Dell3.

The controller keeps six Sonnet workers busy across Claude allowance resets.
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
- Each merge gets a full project build and another axiom check on main. A valid
  proof is recovered even if its worker finished at the turn limit.
- Proofs, author flags, and usage reports are committed and pushed incrementally.
  A failed push leaves commits intact and retries automatically. A divergent
  remote is reported for operator reconciliation; it is never force-pushed.
- Interrupted workers are identified by PID plus process start time, stopped,
  and their files recovered. Partial proof snapshots and checkpoint refs survive
  retries. Restart recovery also rolls back an interrupted, unverified integration.

The controller completes when all discovered source obligations are closed.
This verifies the encoded statements; correspondence to the paper still needs
mathematical review. When only blocked targets remain, the service stays alive
and reports the needed author decisions.

## Settings and tests

Edit `scripts/pipeline.conf` while the service is stopped, then restart it.
Workers have 20 model turns and a 10-minute timeout per invocation. Subagent
and recursive model delegation are disabled. `pipeline.conf.cheap` is a legacy
preset; its dollar/task caps have no effect on the persistent controller.

Offline regression tests use fake models and Lean commands with real Git worktrees:

```
python3 -m unittest discover -s scripts/tests -v
```

No model usage is consumed by these tests. Heavy builds and real proof work run
on Dell3. Keep the main checkout dedicated to the controller while it is active.
