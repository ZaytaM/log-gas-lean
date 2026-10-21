#!/usr/bin/env python3
"""One resumable Opus5.5 reviewer; checkpoint only owned audit outputs to Git."""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import queue
import signal
import subprocess
import sys
import threading
import time
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT/'reports/paper-audit'
RUNTIME = ROOT/'state/runtime/paper-audit'
LOGS = ROOT/'logs/paper-audit'
MODEL = 'claude-opus-5-5'
sys.path.insert(0, str(ROOT/'scripts'))
from runner_support import classify, reset_time
from verify import freeze


def now():
    return datetime.now(timezone.utc).isoformat(timespec='seconds')


def git(*args):
    p = subprocess.run(['git', *args], cwd=ROOT, text=True, capture_output=True, timeout=120)
    if p.returncode:
        raise RuntimeError(p.stderr[-1500:])
    return p.stdout.strip()


def main():
    os.chdir(ROOT)
    RUNTIME.mkdir(parents=True, exist_ok=True)
    LOGS.mkdir(parents=True, exist_ok=True)
    lock = (RUNTIME/'lock').open('a')
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        raise SystemExit('An Opus paper audit is already running')
    if git('branch', '--show-current') != 'main':
        raise SystemExit('Audit publisher requires main')
    baseline = freeze()
    protected = {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in (OUT/'run.py', OUT/'TASK.md')}
    state_path = RUNTIME/'status.json'
    state = json.loads(state_path.read_text()) if state_path.exists() else {}
    state.update(requested_model=MODEL, phase='starting', supervisor_pid=os.getpid())

    def save(phase=None, **values):
        if phase:
            state['phase'] = phase
        state.update(values, updated_utc=now())
        state_path.write_text(json.dumps(state, indent=2)+'\n')
        (OUT/'RUN_STATUS.md').write_text(
            '# Direct Claude paper audit\n\n'
            f"State: {state['phase']}. Updated: {state['updated_utc']}.\n\n"
            f"Requested model: `{MODEL}`. Reported model: `{state.get('actual_model', 'not confirmed')}`.\n\n"
            f"Attempt: {state.get('attempt', 0)}. Supervisor PID: {os.getpid()}.\n\n"
            f"{state.get('message', '')}\n\n"
            'One reviewer; delegation disabled. Review completion does not mean the proof is complete.\n')

    def publish():
        if freeze() != baseline or any(hashlib.sha256(p.read_bytes()).hexdigest()!=h for p,h in protected.items()):
            raise RuntimeError('Protected source/harness changed; preserving work for operator inspection')
        staged = git('diff', '--cached', '--name-only').splitlines()
        if any(not p.startswith('reports/paper-audit/') for p in staged):
            raise RuntimeError('Unrelated staged changes; refusing to include them')
        git('add', '--', 'reports/paper-audit')
        if git('diff', '--cached', '--name-only'):
            git('commit', '-m', 'Checkpoint Opus 5.5 paper theorem and deviation audit')
        try:
            git('push', 'origin', 'main')
            state['push_error'] = ''
        except RuntimeError as exc:
            state['push_error'] = str(exc)
        state_path.write_text(json.dumps(state,indent=2)+'\n')

    def wait_until(deadline):
        while time.time() < deadline:
            time.sleep(min(30, deadline-time.time()))
            if (RUNTIME/'stop').exists():
                return

    save(message='Preparing the exact paper theorem and proof-fidelity review.')
    publish()
    while not (RUNTIME/'stop').exists():
        state['attempt'] = int(state.get('attempt',0))+1
        attempt = state['attempt']
        prompt = (OUT/'TASK.md').read_text()
        prompt += '\nContinue saved partial outputs if any. Your supervisor alone commits/pushes. TASK.md and run.py are read-only.\n'
        if state.get('last_outcome'):
            prompt += '\nPrevious outcome: '+state['last_outcome']+'. Resume the review from the saved files.\n'
        argv = ['claude','-p','--model',MODEL,'--max-turns','60',
                '--disallowedTools','Agent','Task','--dangerously-skip-permissions',
                '--output-format','stream-json','--verbose',prompt]
        if state.get('session_id'):
            argv += ['--resume',state['session_id']]
        events = queue.Queue()
        started = time.time()
        stderr_path = LOGS/f'attempt-{attempt}.stderr'
        stream_path = LOGS/f'attempt-{attempt}.jsonl'
        with stderr_path.open('w') as stderr, stream_path.open('w') as stream:
            p = subprocess.Popen(argv,cwd=ROOT,stdout=subprocess.PIPE,stderr=stderr,
                                 text=True,bufsize=1,start_new_session=True)
            save('running', child_pid=p.pid, message='Claude is reading sources and writing owned audit files.')
            def reader():
                for line in p.stdout:
                    events.put(line)
                events.put(None)
            threading.Thread(target=reader,daemon=True).start()
            last_checkpoint = time.time()
            eof = False
            result = None
            try:
                while not eof:
                    if (RUNTIME/'stop').exists():
                        os.killpg(p.pid,signal.SIGTERM)
                    try:
                        line = events.get(timeout=1)
                    except queue.Empty:
                        line = ''
                    if line is None:
                        eof = True
                    elif line:
                        stream.write(line); stream.flush()
                        try:
                            event = json.loads(line)
                        except ValueError:
                            continue
                        if event.get('session_id'):
                            state['session_id'] = event['session_id']
                        if event.get('type')=='system' and event.get('model'):
                            actual = event['model']
                            if not actual.startswith(MODEL):
                                raise RuntimeError('Requested Opus5.5 but CLI reported '+actual)
                            save(actual_model=actual)
                        if event.get('type')=='assistant' and not event.get('error'):
                            save(assistant_started=True)
                        if event.get('type')=='result':
                            result = event
                    if time.time()-last_checkpoint >= 300:
                        save(message='Publishing partial audit outputs; review remains in progress.')
                        publish(); last_checkpoint=time.time()
                code = p.wait()
            except BaseException:
                if p.poll() is None:
                    os.killpg(p.pid,signal.SIGTERM)
                    p.wait(timeout=30)
                raise
        stderr = stderr_path.read_text()
        outcome = classify(result,stderr,code)
        text = json.dumps(result or {})+'\n'+stderr
        invalid_model = any(s in text.lower() for s in ('model not found','model_not_found','invalid model','unknown model','selected model','may not exist','does not exist','not available for your','not have access to model'))
        state['last_outcome'] = outcome
        usage = result.get('usage') if result else None
        cost = result.get('total_cost_usd') if result else None
        usage_path = OUT/'USAGE.md'
        if not usage_path.exists():
            usage_path.write_text('# Direct Opus audit usage\n\nClient cost estimates; unknown is not zero.\n\n| Attempt | UTC | Outcome | Estimated USD | Duration seconds |\n|---|---|---|---|---|\n')
        with usage_path.open('a') as f:
            f.write(f'| {attempt} | {now()} | {outcome} | {cost if cost is not None else "unknown"} | {time.time()-started:.1f} |\n')
        (RUNTIME/f'usage-{attempt}.json').write_text(json.dumps(dict(model=state.get('actual_model'),cost=cost,usage=usage,outcome=outcome),indent=2)+'\n')
        done = OUT/'DONE.txt'
        required = ['PAPER_THEOREM.md','DEVIATIONS.md','COVERAGE.md','STATUS.md']
        if invalid_model:
            save('blocked_model',message='Requested Opus5.5 is unavailable; no fallback model was used.')
            publish(); return
        if (done.exists() and done.read_text().strip()=='REVIEW_COMPLETE'
                and all((OUT/name).exists() for name in required) and code==0):
            save('review_complete',child_pid=None,message='Review outputs finished. Read STATUS.md for the mathematical proof-readiness verdict.')
            publish(); return
        if (RUNTIME/'stop').exists():
            save('stopped',child_pid=None);publish();return
        if outcome in ('quota','rate_limit','authentication'):
            until = reset_time(text,time.time(),1800 if outcome=='authentication' else 300)
            save('waiting_'+outcome,child_pid=None,retry_at=until,message='Saved partial work; retrying automatically after the advertised reset/backoff.')
            publish(); wait_until(until)
        elif outcome in ('turn_limit','success'):
            save('continuing',child_pid=None,message='Saved current progress; continuing the same reviewer session.')
            publish()
        else:
            save('waiting_error',child_pid=None,message='Saved partial work; retrying this same model in five minutes. See runtime logs.')
            publish();wait_until(time.time()+300)
    save('stopped',child_pid=None);publish()


if __name__=='__main__':
    try:
        main()
    except Exception as exc:
        path = RUNTIME/'status.json'
        state = json.loads(path.read_text()) if path.exists() else {}
        state.update(phase='blocked_error', message=str(exc), updated_utc=now())
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(json.dumps(state,indent=2)+'\n')
        (OUT/'RUN_STATUS.md').write_text('# Direct Claude paper audit\n\nState: blocked_error.\n\n'+str(exc)+'\n')
        raise
