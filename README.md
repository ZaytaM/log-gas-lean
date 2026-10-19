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
