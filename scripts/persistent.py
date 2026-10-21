#!/usr/bin/env python3
"""Durable, single-controller Lean proof queue. Only workers call a model."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import signal
import sqlite3
import subprocess
import sys
import time

from runner_support import classify, declarations, proof_only_change, reset_time, standard_axioms

ROOT = Path(__file__).resolve().parent.parent
RUNTIME = ROOT / 'state/runtime'
SCHEMA = '''
CREATE TABLE IF NOT EXISTS tasks (
 id TEXT PRIMARY KEY, file TEXT NOT NULL, module TEXT NOT NULL, name TEXT NOT NULL,
 state TEXT NOT NULL DEFAULT 'pending', attempts INTEGER NOT NULL DEFAULT 0,
 last_attempt REAL NOT NULL DEFAULT 0, not_before REAL NOT NULL DEFAULT 0,
 worktree TEXT, branch TEXT, error TEXT NOT NULL DEFAULT '');
CREATE TABLE IF NOT EXISTS jobs (
 id INTEGER PRIMARY KEY, task TEXT NOT NULL, started REAL NOT NULL, ended REAL,
 outcome TEXT, proof_result TEXT, cost REAL, usage_known INTEGER NOT NULL DEFAULT 0,
 usage TEXT, turns INTEGER, duration_ms INTEGER, pid INTEGER, pid_start TEXT,
 base_commit TEXT, exit_code INTEGER);
CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT NOT NULL);
'''


def config(root=ROOT):
    result = {}
    for line in (root / 'scripts/pipeline.conf').read_text().splitlines():
        if not re.match(r'^[A-Z_]+=', line): continue
        key, value = line.split('=', 1)
        parts = shlex.split(value, comments=True)
        result[key] = parts[0] if parts else ''
    return result


def connect(path=RUNTIME / 'queue.sqlite3'):
    path.parent.mkdir(parents=True, exist_ok=True)
    db = sqlite3.connect(path, timeout=30)
    db.row_factory = sqlite3.Row
    # Dell3 home directories are on NFS; avoid WAL's shared-memory requirement.
    db.execute('PRAGMA journal_mode=DELETE')
    db.execute('PRAGMA synchronous=FULL')
    db.executescript(SCHEMA)
    return db


def meta(db, key, default=''):
    row = db.execute('SELECT value FROM meta WHERE key=?', (key,)).fetchone()
    return row[0] if row else default


def put_meta(db, key, value):
    with db:
        db.execute('INSERT INTO meta VALUES (?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value', (key, str(value)))


def cmd(args, cwd=ROOT, timeout=300):
    p = subprocess.Popen(args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                         text=True, start_new_session=True)
    try:
        output, _ = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        p.communicate()
        raise
    return p.returncode, output


def checked(args, cwd=ROOT, timeout=300, strip=True):
    code, output = cmd(args, cwd, timeout)
    if code: raise RuntimeError(f'{shlex.join(map(str, args))}: {output[-4000:]}')
    return output.strip() if strip else output


def stamp(value=None):
    return datetime.fromtimestamp(value or time.time(), timezone.utc).isoformat(timespec='seconds')


def process_start(pid):
    try:
        return Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()[19]
    except (OSError, IndexError):
        return ''


def terminate_group(pid, process=None):
    for sig, delay in [(signal.SIGINT, 15), (signal.SIGTERM, 5), (signal.SIGKILL, 0)]:
        try: os.killpg(pid, sig)
        except ProcessLookupError: return
        deadline = time.monotonic() + delay
        while time.monotonic() < deadline:
            if process is not None and process.poll() is not None:
                # Kill any descendants that outlive their model process.
                try: os.killpg(pid, signal.SIGKILL)
                except ProcessLookupError: pass
                return
            try:
                if Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()[0] == 'Z': return
            except (OSError, IndexError): pass
            try: os.kill(pid, 0)
            except ProcessLookupError: return
            time.sleep(.2)


def retry_delay(attempts):
    # Visit other lemmas first; repeatedly stuck targets eventually get daily retries.
    return min(86400, 60 * 2 ** min(max(attempts-1, 0), 11))


class Runner:
    def __init__(self):
        self.db = connect()
        self.cfg = config()
        self.active = {}
        self.stopping = False
        self.last_report = 0
        self.last_push = 0
        (ROOT / 'logs/service').mkdir(parents=True, exist_ok=True)

    def log(self, message):
        print(f'{stamp()} {message}', flush=True)

    def discover(self):
        seen = {}
        sources = [(path, path.read_text()) for path in sorted((ROOT / 'LogGas').glob('*.lean'))]
        fingerprint = hashlib.sha256('\0'.join(text for _, text in sources).encode()).hexdigest()
        changed = fingerprint != getattr(self, '_source_fingerprint', None)
        with self.db:
            for path, source in sources:
                file = str(path.relative_to(ROOT))
                module = file[:-5].replace('/', '.')
                for decl in declarations(source):
                    task_id = module + ':' + decl.name
                    seen[task_id] = decl
                    if decl.sorry:
                        self.db.execute('INSERT OR IGNORE INTO tasks(id,file,module,name) VALUES(?,?,?,?)',
                                        (task_id, file, module, decl.name))
        tasks = self.db.execute('SELECT * FROM tasks').fetchall()
        candidates = [task for task in tasks if task['id'] in seen and not seen[task['id']].sorry
                      and (changed or task['state'] not in ('closed', 'waiting_dependencies'))]
        # One Lean startup imports all needed modules and audits all targets. Do not hold
        # a SQLite write transaction while Lean runs (monitoring must remain available).
        audits = self.axioms_many(ROOT, candidates) if candidates else {}
        with self.db:
            for task in tasks:
                decl = seen.get(task['id'])
                if decl is None and task['state'] != 'closed':
                    self.db.execute("UPDATE tasks SET state='blocked',error='Declaration disappeared; inspect source' WHERE id=?", (task['id'],))
                elif decl and decl.sorry and task['state'] in ('closed', 'waiting_dependencies'):
                    self.db.execute("UPDATE tasks SET state='pending',not_before=0,error='Source proof reopened' WHERE id=?", (task['id'],))
                elif task['name'] in audits:
                    verified = audits[task['name']]
                    self.db.execute("UPDATE tasks SET state=?,error=? WHERE id=?",
                        ('closed' if verified else 'waiting_dependencies',
                         '' if verified else 'Proof present; awaiting prerequisite proofs and a clean axiom audit', task['id']))
        self._source_fingerprint = fingerprint

    def build(self, cwd, module=None, tag='build'):
        args = ['lake', 'build'] + ([module] if module else [])
        code, output = cmd(args, cwd, int(self.cfg.get('BUILD_TIMEOUT', '1800')))
        (ROOT / 'logs/service' / f'{tag}.log').write_text(output)
        return code == 0

    def axioms(self, cwd, task, tag):
        scratch = RUNTIME / f'axioms-{tag}.lean'
        scratch.write_text(f'import {task["module"]}\n#print axioms {task["name"]}\n')
        try:
            code, output = cmd(['lake', 'env', 'lean', str(scratch)], cwd, 300)
            (ROOT / 'logs/service' / f'axioms-{tag}.log').write_text(output)
            return code == 0 and standard_axioms(output)
        finally:
            scratch.unlink(missing_ok=True)

    def axioms_many(self, cwd, tasks):
        scratch = RUNTIME / 'axioms-discovery.lean'
        imports = ''.join('import ' + module + '\n' for module in sorted({t['module'] for t in tasks}))
        scratch.write_text(imports + ''.join('#print axioms ' + t['name'] + '\n' for t in tasks))
        try:
            code, output = cmd(['lake', 'env', 'lean', str(scratch)], cwd, 300)
            (ROOT / 'logs/service/axioms-discovery.log').write_text(output)
            results = {t['name']: False for t in tasks}
            if code == 0:
                for match in re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[[^]]*\]|does not depend on any axioms)", output, re.S):
                    if match[1] in results: results[match[1]] = standard_axioms(match[0])
            return results
        finally:
            scratch.unlink(missing_ok=True)

    def prepare(self, task):
        task_hash = hashlib.sha256(task['id'].encode()).hexdigest()[:16]
        worktree = ROOT / 'wt/service' / task_hash
        branch = 'proof-service/' + task_hash
        current = (ROOT / task['file']).read_text()
        saved = None
        if worktree.exists():
            previous = (worktree / task['file']).read_text()
            base = checked(['git', 'merge-base', 'HEAD', 'main'], worktree)
            before = checked(['git', 'show', f'{base}:{task["file"]}'], worktree, strip=False)
            if not proof_only_change(before, previous, task['name']):
                raise ValueError('Saved worker changed material outside its target proof; retained for inspection')
            saved = next((d for d in declarations(previous) if d.name == task['name']), None)
            if saved:
                snapshot = RUNTIME / f'checkpoint-{task_hash}-{task["attempts"]}.lean'
                snapshot.write_text(previous)
                old_head = checked(['git', 'rev-parse', 'HEAD'], worktree)
                checked(['git', 'update-ref', f'refs/heads/proof-checkpoints/{task_hash}-{task["attempts"]}', old_head])
            checked(['git', 'reset', '--hard', 'main'], worktree)
            if saved:
                new = next(d for d in declarations(current) if d.name == task['name'])
                candidate = current[:new.proof] + previous[saved.proof:saved.end] + current[new.end:]
                if proof_only_change(current, candidate, task['name']):
                    (worktree / task['file']).write_text(candidate)
        else:
            worktree.parent.mkdir(parents=True, exist_ok=True)
            # Never reset a pre-existing branch: failed work is deliberately retained.
            if cmd(['git', 'rev-parse', '--verify', branch])[0] == 0:
                checked(['git', 'worktree', 'add', str(worktree), branch])
                return self.prepare(task)
            checked(['git', 'worktree', 'add', '-b', branch, str(worktree), 'main'])
        lake = worktree / '.lake'
        lake.mkdir(exist_ok=True)
        packages = lake / 'packages'
        if not packages.exists(): packages.symlink_to(ROOT / '.lake/packages', target_is_directory=True)
        # Dependencies/caches are shared; this checkout's .lake/build is independent.
        manifest = ROOT / 'lake-manifest.json'
        if manifest.exists(): (worktree / 'lake-manifest.json').write_bytes(manifest.read_bytes())
        return worktree, branch

    def start(self, task):
        try:
            worktree, branch = self.prepare(task)
        except ValueError as exc:
            with self.db:
                self.db.execute("UPDATE tasks SET state='blocked',error=? WHERE id=?", (str(exc), task['id']))
            self.log(f'Needs attention: {task["name"]}: {exc}')
            return
        prompt = (ROOT / 'prompts/worker.md').read_text()
        for key, value in {'LEMMA_FILE':task['file'], 'MODULE':task['module'],
                           'LEMMA_NAME':task['name'], 'MAX_ATTEMPTS':self.cfg.get('MAX_ATTEMPTS', '5')}.items():
            prompt = prompt.replace('{' + key + '}', value)
        prompt += f'\nPrevious attempts: {task["attempts"]}. Last outcome: {task["error"][-1500:]}.\n'
        notes = worktree / '.lake/worker-notes.md'
        if notes.exists():
            prompt += '\nSaved notes from the previous attempt:\n' + notes.read_text()[-3000:] + '\n'
        now = time.time()
        base = checked(['git', 'rev-parse', 'main'])
        with self.db:
            job = self.db.execute('INSERT INTO jobs(task,started,base_commit) VALUES(?,?,?)', (task['id'], now, base)).lastrowid
            self.db.execute("UPDATE tasks SET state='running',attempts=attempts+1,last_attempt=?,worktree=?,branch=? WHERE id=?", (now, str(worktree), branch, task['id']))
        out = (ROOT / 'logs/service' / f'{job}.json').open('w')
        err = (ROOT / 'logs/service' / f'{job}.err').open('w')
        args = ['claude', '-p', '--model', self.cfg.get('MODEL_WORKER', 'sonnet'),
                '--max-turns', self.cfg.get('MAX_TURNS', '20'), '--disallowedTools', 'Agent', 'Task',
                '--dangerously-skip-permissions', '--output-format', 'json', prompt]
        try:
            marker = RUNTIME / f'job-{job}-pid.json'
            process = subprocess.Popen([sys.executable, str(ROOT / 'scripts/worker_exec.py'), str(marker), *args],
                                       cwd=worktree, stdout=out, stderr=err, start_new_session=True)
        finally:
            out.close(); err.close()
        with self.db:
            self.db.execute('UPDATE jobs SET pid=?,pid_start=? WHERE id=?', (process.pid, process_start(process.pid), job))
        self.active[job] = (process, now)
        self.log(f'Started job {job}: {task["name"]} (attempt {task["attempts"]+1})')

    def finish(self, job_id, exit_code, forced=None):
        job = self.db.execute('SELECT * FROM jobs WHERE id=?', (job_id,)).fetchone()
        task = self.db.execute('SELECT * FROM tasks WHERE id=?', (job['task'],)).fetchone()
        result_path = ROOT / 'logs/service' / f'{job_id}.json'
        try: data = json.loads(result_path.read_text())
        except (OSError, ValueError): data = None
        err_path = ROOT / 'logs/service' / f'{job_id}.err'
        stderr = err_path.read_text() if err_path.exists() else ''
        outcome = forced or classify(data, stderr, exit_code)
        now = time.time()
        with self.db:
            self.db.execute('UPDATE jobs SET ended=?,outcome=?,cost=?,usage_known=?,usage=?,turns=?,duration_ms=?,exit_code=? WHERE id=?',
                (now, outcome, (data or {}).get('total_cost_usd'),
                 int(bool((data or {}).get('usage')) and (data or {}).get('total_cost_usd') is not None),
                 json.dumps((data or {}).get('usage')), (data or {}).get('num_turns'),
                 (data or {}).get('duration_ms'), exit_code, job_id))
            self.db.execute("UPDATE tasks SET state='verifying' WHERE id=?", (task['id'],))
        if outcome in ('quota', 'rate_limit', 'authentication'):
            failures = int(meta(self.db, 'limit_failures', '0')) + 1
            put_meta(self.db, 'limit_failures', failures)
            fallback = min(3600, 300 * 2 ** min(failures-1, 4)) if outcome == 'quota' else (1800 if outcome == 'authentication' else min(900, 60*failures))
            # A finished worker may wait behind integration builds. Interpret the
            # advertised clock at the response time, so a reset just passed does
            # not accidentally become a next-day wait.
            observed = min(now, result_path.stat().st_mtime) if result_path.exists() else now
            until = max(now + 60, reset_time(json.dumps(data or {}) + stderr, observed, fallback))
            until = max(until, float(meta(self.db, 'pause_until', '0')))
            put_meta(self.db, 'pause_until', until)
            put_meta(self.db, 'pause_reason', outcome)
            self.log(f'{outcome}: saved queue; next automatic retry {stamp(until)}')
        elif outcome == 'success':
            put_meta(self.db, 'limit_failures', 0)
        self.accept(task, job, outcome)

    def accept(self, task, job, outcome):
        """A valid saved proof can succeed even if the final model turn hit its limit."""
        worktree = Path(task['worktree']) if task['worktree'] else None
        error = outcome
        state = 'pending'
        integration_base = None
        try:
            if not worktree or not worktree.exists(): raise ValueError('Worker directory missing')
            before = checked(['git', 'show', f'{job["base_commit"]}:{task["file"]}'], strip=False)
            after = (worktree / task['file']).read_text()
            changed = set(checked(['git', 'diff', '--name-only', job['base_commit']], worktree).splitlines())
            untracked = set(checked(['git', 'ls-files', '--others', '--exclude-standard'], worktree).splitlines())
            flags = {p for p in changed | untracked if p.startswith('notes/flags/') and p.endswith('.md')}
            illegal = (changed | untracked) - flags - {task['file']}
            if illegal: raise ValueError('Unexpected worker files: ' + ', '.join(sorted(illegal)))
            if not proof_only_change(before, after, task['name']):
                raise ValueError('Worker changed a statement or material outside its target proof')
            if flags:
                for file in flags:
                    dest = ROOT / file
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    if dest.exists() and dest.read_bytes() != (worktree / file).read_bytes():
                        dest = dest.with_name(dest.stem + f'-job{job["id"]}.md')
                    dest.write_bytes((worktree / file).read_bytes())
                    checked(['git', 'add', str(dest)])
                if cmd(['git', 'diff', '--cached', '--quiet'])[0]: checked(['git', 'commit', '-m', f'Flag {task["name"]} for author review'])
                state, error = 'blocked', 'Author review requested; see notes/flags'
            else:
                decl = next(d for d in declarations(after) if d.name == task['name'])
                if decl.sorry:
                    error = outcome + ': partial proof checkpoint retained'
                elif not self.build(worktree, task['module'], f'job-{job["id"]}-build'):
                    error = 'Candidate proof did not build; checkpoint retained'
                elif not self.axioms(worktree, task, str(job['id'])):
                    error = 'Candidate failed axiom check; checkpoint retained'
                else:
                    checked(['git', 'add', task['file']], worktree)
                    if cmd(['git', 'diff', '--cached', '--quiet'], worktree)[0]:
                        checked(['git', 'commit', '-m', 'Prove ' + task['name']], worktree)
                    base = checked(['git', 'rev-parse', 'HEAD'])
                    integration_base = base
                    put_meta(self.db, 'integration_base', base)
                    code, output = cmd(['git', 'merge', '--no-edit', task['branch']])
                    (ROOT / 'logs/service' / f'job-{job["id"]}-merge.log').write_text(output)
                    if code:
                        cmd(['git', 'merge', '--abort'])
                        error = 'Merge conflict; retry against current main'
                    elif self.build(ROOT, tag=f'job-{job["id"]}-main') and self.axioms(ROOT, task, f'{job["id"]}-main'):
                        state, error = 'closed', ''
                    else:
                        # Only roll back our own integration commit; worker branch is kept.
                        checked(['git', 'reset', '--hard', base])
                        error = 'Integration build/axiom check failed; worker proof retained'
                    put_meta(self.db, 'integration_base', '')
                    integration_base = None
        except ValueError as exc:
            state, error = 'blocked', str(exc)
        except (RuntimeError, subprocess.TimeoutExpired, OSError) as exc:
            if integration_base:
                cmd(['git', 'merge', '--abort'])
                checked(['git', 'reset', '--hard', integration_base])
                put_meta(self.db, 'integration_base', '')
            state, error = 'pending', f'{type(exc).__name__}: {str(exc)[-1500:]}'
        attempts = self.db.execute('SELECT attempts FROM tasks WHERE id=?', (task['id'],)).fetchone()[0]
        with self.db:
            self.db.execute('UPDATE tasks SET state=?,not_before=?,error=? WHERE id=?',
                            (state, time.time() + retry_delay(attempts), error, task['id']))
            self.db.execute('UPDATE jobs SET proof_result=? WHERE id=?', (state, job['id']))
        self.log(f'Job {job["id"]}: {task["name"]}: {state} ({outcome}) {error}')
        if state == 'closed' and worktree:
            # Proof is committed in main; removing this service-owned worktree is safe.
            cmd(['git', 'worktree', 'remove', '--force', str(worktree)])
        self.report()
        self.publish()

    def recover(self):
        """Reconcile a crash at any point between model launch and merge bookkeeping."""
        jobs = self.db.execute("SELECT jobs.* FROM jobs JOIN tasks ON tasks.id=jobs.task WHERE tasks.state IN ('running','verifying') AND jobs.id=(SELECT MAX(j.id) FROM jobs j WHERE j.task=tasks.id)").fetchall()
        for job in jobs:
            pid, start = job['pid'], job['pid_start']
            marker = RUNTIME / f'job-{job["id"]}-pid.json'
            if marker.exists():
                saved = json.loads(marker.read_text())
                pid, start = saved['pid'], saved['start']
            if pid and start and process_start(pid) == start:
                self.log(f'Recovering interrupted job {job["id"]}; stopping its orphaned process group')
                terminate_group(pid)
            self.finish(job['id'], job['exit_code'] or 143, forced=job['outcome'] or 'interrupted')

    def report(self):
        tasks = self.db.execute('SELECT state,COUNT(*) n FROM tasks GROUP BY state').fetchall()
        totals = self.db.execute('SELECT COUNT(*) n,SUM(cost) cost,SUM(usage_known=0) missing FROM jobs').fetchone()
        pause = float(meta(self.db, 'pause_until', '0'))
        body = ['# Persistent Lean verification', '', f'Updated: {stamp()}', '',
                f'State: {meta(self.db,"service_state","starting")}.',
                f'Workers configured: {self.cfg.get("MAX_WORKERS", "3")}; active: {len(self.active)}.',
                'Task and estimated-dollar caps: disabled; subscription limits trigger automatic waiting.', '',
                *[f'- {r["state"]}: {r["n"]}' for r in tasks], '',
                f'Attempts: {totals["n"]}; reported cost: ${totals["cost"] or 0:.4f}; attempts with unknown/incomplete usage: {totals["missing"] or 0}.',
                f'Automatic retry: {stamp(pause)} ({meta(self.db,"pause_reason")})' if pause > time.time() else 'Queue is eligible to dispatch work.', '',
                'Costs are client estimates and do not measure subscription allowance precisely.',
                'Closed means the target proof passed source, build and axiom checks on main.',
                'Waiting_dependencies means a proof is present but its transitive axiom audit is not yet clean; no model worker is spent on it.', '', '## Needs attention', '']
        body += [f'- {t["name"]}: {t["error"]}' for t in self.db.execute("SELECT name,error FROM tasks WHERE state='blocked'")]
        (ROOT / 'reports/persistent.md').write_text('\n'.join(body) + '\n')
        fields = ['id','task','started','ended','outcome','proof_result','cost','usage_known','turns','duration_ms','usage']
        with (ROOT / 'state/worker_usage.tsv').open('w') as f:
            f.write('\t'.join(fields) + '\n')
            for job in self.db.execute('SELECT * FROM jobs ORDER BY id'):
                f.write('\t'.join(str(job[k] if job[k] is not None else 'unknown').replace('\t', ' ').replace('\n', ' ') for k in fields) + '\n')
        self.last_report = time.time()

    def publish(self):
        checked(['git', 'add', 'reports/persistent.md', 'state/worker_usage.tsv'])
        if cmd(['git', 'diff', '--cached', '--quiet'])[0]:
            checked(['git', 'commit', '-m', 'Checkpoint persistent Lean proof queue'])
        try:
            code, output = cmd(['git', 'push', 'origin', 'main'], timeout=90)
        except (subprocess.TimeoutExpired, OSError) as exc:
            code, output = 1, str(exc)
        self.last_push = time.time()
        if code:
            # Do not rebase underneath active workers; retain committed work and retry.
            put_meta(self.db, 'push_error', output[-2000:])
            self.log('Push failed; committed proofs retained locally, will retry automatically')
        else:
            put_meta(self.db, 'push_error', '')

    def run(self):
        lock = (RUNTIME / 'controller.lock').open('w')
        try: fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError: raise SystemExit('A persistent controller is already running')
        if (RUNTIME / 'stop').exists(): return
        if checked(['git', 'branch', '--show-current']) != 'main': raise RuntimeError('Controller must run on main')
        integration_base = meta(self.db, 'integration_base')
        if integration_base:
            self.log('Rolling back interrupted integration; candidate retained on its worker branch')
            cmd(['git', 'merge', '--abort'])
            checked(['git', 'reset', '--hard', integration_base])
            put_meta(self.db, 'integration_base', '')
        dirty = checked(['git', 'status', '--porcelain'], strip=False)
        allowed = {'reports/persistent.md', 'state/worker_usage.tsv'}
        if dirty and any(line[3:] not in allowed for line in dirty.splitlines()):
            raise RuntimeError('Main checkout has unexpected uncommitted files; inspect before starting')
        if dirty:
            checked(['git', 'add', *sorted(allowed)])
            checked(['git', 'commit', '-m', 'Recover interrupted queue report'])
        put_meta(self.db, 'controller_pid', os.getpid())
        put_meta(self.db, 'controller_start', process_start(os.getpid()))
        signal.signal(signal.SIGTERM, lambda *_: setattr(self, 'stopping', True))
        signal.signal(signal.SIGINT, lambda *_: setattr(self, 'stopping', True))
        put_meta(self.db, 'service_state', 'verifying_baseline')
        put_meta(self.db, 'heartbeat', time.time())
        self.log('Persistent controller starting; no task/cost stopping budget')
        try:
            if not self.build(ROOT, tag='baseline'): raise RuntimeError('Baseline build failed; see logs/service/baseline.log')
            self.recover()
            put_meta(self.db, 'service_state', 'auditing_dependencies')
            self.discover()
            while not self.stopping and not (RUNTIME / 'stop').exists():
                put_meta(self.db, 'heartbeat', time.time())
                for job, (process, started) in list(self.active.items()):
                    forced = None
                    if process.poll() is None and time.time() - started > int(self.cfg.get('WORKER_TIMEOUT', '600')):
                        terminate_group(process.pid, process); forced = 'timeout'
                    if process.poll() is not None:
                        self.active.pop(job)
                        self.finish(job, process.returncode, forced)
                self.discover()
                if not self.active and not self.db.execute("SELECT 1 FROM tasks WHERE state!='closed' LIMIT 1").fetchone():
                    put_meta(self.db, 'service_state', 'complete')
                    self.log('All discovered Lean obligations are closed; service complete')
                    break
                pause = float(meta(self.db, 'pause_until', '0'))
                if not self.stopping and not (RUNTIME / 'stop').exists() and time.time() >= pause:
                    limit = max(1, min(6, int(self.cfg.get('MAX_WORKERS', '3'))))
                    if os.getloadavg()[0] > int(self.cfg.get('LOAD_HALVE_ABOVE', '50')): limit = max(1, limit//2)
                    while len(self.active) < limit:
                        priority = self.cfg.get('PRIORITY_MODULES', '').split()
                        ranking = ('CASE WHEN module IN (' + ','.join('?' for _ in priority) + ') THEN 0 ELSE 1 END,') if priority else ''
                        task = self.db.execute("SELECT * FROM tasks WHERE state='pending' AND not_before<=? ORDER BY " + ranking + "attempts,last_attempt,id LIMIT 1", (time.time(), *priority)).fetchone()
                        if not task: break
                        self.start(task)
                state = 'waiting_quota' if pause > time.time() else 'running'
                if not self.active and state == 'running':
                    state = 'waiting_retry' if self.db.execute("SELECT 1 FROM tasks WHERE state='pending' LIMIT 1").fetchone() else 'needs_attention'
                put_meta(self.db, 'service_state', state)
                if time.time() - self.last_report >= 300:
                    self.report()
                    self.publish()
                time.sleep(2)
        finally:
            for job, (process, _) in list(self.active.items()):
                terminate_group(process.pid, process)
                process.wait()
                self.active.pop(job)
                self.finish(job, process.returncode, 'interrupted')
            if self.stopping or (RUNTIME / 'stop').exists():
                put_meta(self.db, 'service_state', 'stopped')
            elif sys.exc_info()[0] is not None:
                put_meta(self.db, 'service_state', 'recovering')
            self.report()
            self.publish()
            put_meta(self.db, 'controller_pid', '')
            put_meta(self.db, 'controller_start', '')
            self.log('Controller stopped; queue and proof checkpoints retained')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['run', 'status', 'stop', 'retry-blocked'])
    args = parser.parse_args()
    if args.action == 'run': Runner().run()
    elif args.action == 'stop':
        RUNTIME.mkdir(parents=True, exist_ok=True)
        (RUNTIME / 'stop').touch()
        print('Stop requested; active work will be saved before exit.')
    else:
        db = connect()
        if args.action == 'retry-blocked':
            with db: db.execute("UPDATE tasks SET state='pending',not_before=0 WHERE state='blocked'")
            print('Blocked targets requeued for review against the current source.')
            return
        pid = meta(db, 'controller_pid')
        alive = bool(pid and meta(db, 'controller_start') and process_start(int(pid)) == meta(db, 'controller_start'))
        print(json.dumps({'controller_alive':alive, 'service_state':meta(db,'service_state','not_started'),
                          'heartbeat':meta(db,'heartbeat'), 'retry_at':meta(db,'pause_until'),
                          'pause_reason':meta(db,'pause_reason'), 'push_error':meta(db,'push_error'),
                          'tasks':dict(db.execute('SELECT state,COUNT(*) FROM tasks GROUP BY state').fetchall()),
                          'reported_cost_usd':db.execute('SELECT SUM(cost) FROM jobs').fetchone()[0]}, indent=2))


if __name__ == '__main__': main()
