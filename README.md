# log-gas-lean

Lean 4 formalization of "An entropy bound for the attractive logarithmic gas"
(Delgadino–Gvalani–Rosenzweig), run nightly on dell3 by a model pipeline.

Layout
- `LogGas/*.lean` — one file per phase (Warmup, Decoupling, Grouped, BadEvent, Singular, Bulk, Main)
- `notes/*.tex` — the paper split by section; `notes/phaseN.md` — targets per phase; `notes/hypotheses.md`
- `notes/hints.md` — author hints, read by every worker; `notes/flags/` — worker/advisor flags needing the author
- `prompts/` — orchestrator, worker, advisor, reporter prompt templates
- `scripts/pipeline.sh` — nightly run; `scripts/pipeline.conf` — knobs; `scripts/orchestrate.sh` — skeleton for a phase
- `reports/YYYY-MM-DD.md` — morning report; `state/tracker.md` — one row per night; `advice/` — advisor outputs

Nightly run (from the Mac, via the offload skill or by hand):
    ssh dell3 'tmux new -d -s loggas "bash ~/bin/dell3_run.sh ~/work/log-gas-lean cmd \"bash scripts/pipeline.sh\""'

Schedule it: on dell3, `crontab -e` and add
    0 22 * * * bash $HOME/bin/dell3_run.sh $HOME/work/log-gas-lean cmd "bash scripts/pipeline.sh" >/dev/null 2>&1
so the report is ready by 09:00.

Claude Code flags used: `-p`, `--model`, `--max-turns`, `--output-format json`,
`--dangerously-skip-permissions`. Verify with `claude --help` after an update.

Run hygiene (added 2026-10-20 after the first night failed silently)
- The run clears `wt/` and all `wip/*` branches at the start; a branch with unmerged
  commits is kept as `failed/<lemma>-<run>` for inspection.
- Worker STATUS values: closed | partial | stuck | timeout | failed (model never ran) | unknown.
- If the baseline build fails or the model is unavailable for every worker (session or
  usage limit), the run writes a stub report, commits, and exits 1. Check `logs/<run>/summary.txt`.
- `scripts/quota_error.py` decides "model unavailable" for workers, advisor, reporter and orchestrator.
- `state/tracker.md` rows are written by the script, not the reporter.
- `scripts/pipeline.conf.cheap` holds the low-cost defaults (sonnet workers, $40 cap, advisor on).
