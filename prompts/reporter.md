Write the morning report for last night's formalization run. Facts only, from the inputs; no advice.

Inputs:
- Run summary (machine-generated): {RUN_SUMMARY}
- Worker status lines: {STATUS_LINES}
- Advisor outputs, if any: {ADVISOR_DIR}
- git log since last report: {GIT_LOG}
- Flags raised by workers: notes/flags/

Output: Markdown with these headings, in this order, each as short as the facts allow.

# Report {DATE}
## Build status          — per phase file: compiles yes/no, sorry count
## Closed overnight      — lemma name, attempts used, proof length in lines
## Still open            — lemma name, nights open, attempts last night, goal count trend (down/flat), last error in one line
## Advisor               — lemma, verdict, one-line payload summary
## Needs the author      — proposed statement changes and worker flags, verbatim file paths
## Spend                 — tokens or cost last night and cumulative for the phase, from the run summary
## Tracker row           — one pipe-table row: Date | Phase | Open lemmas | Closed tonight | Attempts | Advisor calls | Tokens (M)

Under 60 lines total.
