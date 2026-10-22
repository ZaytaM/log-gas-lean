# Independent-kernel replay on fac5: design

Status: design and runner written 2026-10-22; **not run**. Needs: the owner's go, a Rust toolchain
in user space on fac5 (rustup, no root), and about 1–2 h of wall-clock on fac5.

## 0. What is verified

* **Solution tree**: the frozen commit `FREEZE_COMMIT` of `main` on GitHub (`git clone` at that
  commit; nothing copied from dell3), built from the pinned `lake-manifest.json`.
* **Challenge tree**: the same clone restricted to `PaperChallenge.lean` + `Challenge.lean` with their
  frozen hashes verified against `Audit/frozen_statements.sha256`; built as libraries `PaperChallenge`,
  `Challenge` (they import only Mathlib).
* **Targets**: `LogGasPaper.main : LogGasPaper.PaperTheorem`, `LogGasPaper.kernel_exists :
  LogGasPaper.LogKernelExists`, `LogGasChallenge.principal`, `LogGasChallenge.bulk`.
* **Permitted axioms**: `propext`, `Classical.choice`, `Quot.sound`. (`Lean.trustCompiler` must
  *not* be needed; `native_decide` is excluded by the source gate.)

## 1. Why fac5 qualifies, and what it does not give for free

No campaign agent ever ran on fac5 (they ran on dell3). But fac5 **shares the NFS home with dell3**,
so nothing under `~` counts as independent. The runner therefore uses a fresh prefix under
`/tmp/loggas-replay-<run>/` on fac5's local disk for: its own `elan`/toolchain copy (hash-checked
against the official release checksums), the `lean4export` and `nanoda_lib` builds, the clone, and
all outputs. Only the Mathlib olean cache is downloaded (from Mathlib's public cache); its
contents are re-typechecked by Nanoda anyway, so a corrupted cache cannot produce a false accept.
fac5 is a shared login host (8 cores, 31 GB RAM): the runner uses `nice -n 19`, at most 4 build
threads, and stops if free RAM drops below 4 GB or `/tmp` below 6 GB.

## 2. Tools and versions (checked 2026-10-22)

| Tool | Version | Role |
|---|---|---|
| `lean4export` | tag `v4.36.0-rc1` (commit `df81913`), emits NDJSON format **3.1.0** | exports the kernel environment (names/levels/exprs/declarations) of a module closure |
| `nanoda_lib` | master (Cargo 0.4.26), accepts format ≥3.1.0 <3.2.0 | **independent Rust re-implementation of the Lean 4 kernel**; re-typechecks every declaration of the export |
| `leanchecker` | shipped with the toolchain | Lean's own kernel replay, `--fresh`; recorded separately (not independent) |
| `Audit/Replay/compare_exports.py` | ours | the Comparator role: checks that the solution export contains the four targets, that their **types** are structurally identical to the challenge export's definitions of `PaperTheorem` etc. (α-equivalent terms, modulo index renumbering), that every definition reachable from those types is identical in both exports, and that the axioms reachable from the targets are within the permitted set |

Nanoda does not print "accepted"; success is exit 0 and the line `Checked N declarations with no
errors` (with `print_success_message: true`). The receipt records exit codes and that line.

## 3. Procedure (`runner_fac5.sh`)

1. Preflight: `uptime`, free RAM/disk, no other heavy job of ours; record `fac5` identity.
2. Fresh prefix; install `elan` into it (`ELAN_HOME`), toolchain `v4.36.0-rc1`; record
   `lean --version` and the SHA-256 of `lean`, `lake`, `leanchecker` binaries.
3. Install Rust via rustup into the prefix (`RUSTUP_HOME`, `CARGO_HOME`); build `nanoda_bin`
   (`cargo build --release`) from a clone of `ammkrn/nanoda_lib` at a recorded commit.
4. Clone `lean4export` at tag `v4.36.0-rc1`; `lake build`; record binary hash.
5. Clone the project at `FREEZE_COMMIT`; verify `Audit/frozen_statements.sha256` and
   `Audit/manuscript.sha256`; `lake exe cache get`; `lake build PaperChallenge Challenge PaperSolution
   Solution` (fresh `.lake/build`); record job counts and that no `sorry` warning appears.
6. Export: `lake env lean4export PaperChallenge Challenge > challenge.ndjson`;
   `lake env lean4export PaperSolution Solution > solution.ndjson`. Record sizes and SHA-256.
7. Compare: `python3 compare_exports.py challenge.ndjson solution.ndjson --targets …` → exit 0.
8. Nanoda: `nanoda_bin nanoda_config.json` on `solution.ndjson` (config: permitted axioms as above,
   `unpermitted_axiom_hard_error: true`, `nat_extension`/`string_extension: true`) → exit 0 and
   "Checked N declarations with no errors".
9. `lake env leanchecker --fresh PaperSolution` and `… Solution` → exit 0 (recorded separately).
10. Receipt `receipt-<run>.json`: host, UTC start/end, every commit/tag/hash above, export hashes,
    exit codes, Nanoda output line, comparator summary; plus `log/` with every command's output.
    Copy the receipt into `Audit/Replay/` and commit from the Mac or dell3 (the fac5 clone is
    read-only for the project and is deleted after the receipt is copied).

## 4. Limits

* Definition faithfulness is not machine-verified (layers 2–3).
* The comparator ignores attributes (`simp`, `instance`, reducibility) and `mdata`; neither affects
  the kernel meaning of a theorem.
* Mathlib's own declarations are re-typechecked by Nanoda but not compared between trees (they are
  the same pinned revision, enforced by the lock).
* No isolated VM/Landlock sandbox: fac5 is a shared host under the department's administration.
  The runner records tool hashes and the project commit so the run is reproducible; it does not
  claim to defend against a compromised host.
