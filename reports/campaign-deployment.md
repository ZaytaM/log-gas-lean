# Main theorem campaign deployment

Deployed on Dell3, 2026-10-21. Mathematical proof remains incomplete.

- Independent PaperChallenge/PaperSolution specifications compile against pinned Lean/mathlib.
- Actual project build succeeded: LogGas, Challenge, Solution, PaperChallenge, PaperSolution, VerificationAudit (18139 jobs).
- Linux full regression suite: 33 tests passed in 62.297 seconds.
- Final checkpoint/recovery suite: 11 tests passed; real Git and fake model/Lean calls, no model spend in tests.
- One direct Claude Opus 5.5 coordinator; at most six Sonnet workers; no nested model delegation.
- Separate construction/proof/review tasks, prerequisite and file ownership gating, exact candidate review, isolated integration build.
- Quota pauses save all work and automatically retry after reset. Reboot/watchdog recovery installed by campaign.sh.
- Main contains reviewed, rebuilt milestones and honest progress reports. Unverified partial work goes to campaign/wip/* branches.
- Full theorem completion requires PaperTheorem and LogKernelExists proof inhabitants, conditional targets, fresh verification, and two current independent review receipts.
- External Comparator remains unperformed unless genuinely available; no completion or independent-kernel success is claimed.

Runtime: state/runtime/campaign/queue.sqlite3. Logs: logs/campaign/.
Progress: reports/campaign.md. Usage: state/campaign-usage.tsv.
