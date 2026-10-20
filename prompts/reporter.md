Write the morning report for last night's formalization run. Facts only, from the inputs; no advice.

Inputs:
- Run summary (machine-generated): {RUN_SUMMARY}
- Worker status lines: {STATUS_LINES}
  (STATUS is closed | partial | stuck | timeout | failed | unknown; `failed` means the model
  call never ran, `timeout` means the worker hit the wall clock, `unknown` means it printed no status)
- Open lemmas before the run, with file and sorry count: {OPEN_LIST}
- Nights each lemma has been open, after tonight: {NIGHTS_FILE}
- Advisor outputs, if any: {ADVISOR_DIR}
- git log since last report: {GIT_LOG}
- Flags raised by workers: notes/flags/

Output: Markdown with these headings, in this order, each as short as the facts allow.

# Report {DATE}
## Build status          — per phase file: compiles yes/no, sorry count
## Closed overnight      — lemma name, attempts used, proof length in lines
## Still open            — lemma name, nights open, attempts last night, goal count, last error in one line
## Advisor               — lemma, verdict, one-line payload summary
## Needs the author      — proposed statement changes and worker flags, verbatim file paths
## Spend                 — cost last night from the run summary; say "not reported" if absent

Under 60 lines total. Do not add a tracker row; the script writes it.
