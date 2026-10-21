#!/usr/bin/env python3
"""Durable construction/proof campaign. One publisher, bounded workers, reviewed patches.

The coordinator uses this same CLI to submit tasks and approve exact candidate
commits. Models never mutate the publisher checkout. Runtime files stay on Dell3.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import shutil
import sqlite3
import subprocess
import sys
import time
from datetime import datetime, timezone

from runner_support import classify, mask_comments, reset_time, standard_axioms, proof_only_change

ROOT = Path(__file__).resolve().parents[1]
STATE = ROOT/'state/runtime/campaign'
LOGS = ROOT/'logs/campaign'
COORD = 'claude-opus-5-5'
WORKER = 'sonnet'
LIMIT = 6
SCHEMA = '''
CREATE TABLE IF NOT EXISTS tasks(id TEXT PRIMARY KEY, spec TEXT NOT NULL,
 state TEXT NOT NULL DEFAULT 'pending', attempt INTEGER NOT NULL DEFAULT 0,
 worktree TEXT, base TEXT, candidate TEXT, approval TEXT, error TEXT DEFAULT '',
 retry REAL NOT NULL DEFAULT 0);
CREATE TABLE IF NOT EXISTS jobs(id INTEGER PRIMARY KEY, task TEXT, role TEXT,
 pid INTEGER, start_id TEXT, started REAL, ended REAL, result TEXT, cost REAL,
 usage TEXT, session TEXT, worktree TEXT, base TEXT);
CREATE TABLE IF NOT EXISTS meta(key TEXT PRIMARY KEY,value TEXT);
'''


def now():
    return datetime.now(timezone.utc).isoformat(timespec='seconds')


def dbopen():
    STATE.mkdir(parents=True, exist_ok=True)
    c = sqlite3.connect(STATE/'queue.sqlite3', timeout=30)
    c.row_factory = sqlite3.Row
    c.execute('PRAGMA journal_mode=DELETE')
    c.execute('PRAGMA synchronous=FULL')
    c.executescript(SCHEMA)
    return c


def get(c, key, default=''):
    r = c.execute('SELECT value FROM meta WHERE key=?', (key,)).fetchone()
    return r[0] if r else default


def put(c, key, value):
    with c:
        c.execute('INSERT INTO meta VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value', (key,str(value)))


def run(argv, cwd=None, timeout=1800, check=True):
    cwd = ROOT if cwd is None else cwd
    p = subprocess.Popen([str(a) for a in argv], cwd=cwd, text=True,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)
    try:
        output, _ = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        output, _ = p.communicate()
        raise RuntimeError('Timed out: '+str(argv[:4])+'\n'+output[-2000:])
    if check and p.returncode:
        raise RuntimeError(str(argv[:5])+'\n'+output[-5000:])
    return output.strip() if check else (p.returncode, output)


def git(*args, cwd=None):
    cwd = ROOT if cwd is None else cwd
    return run(['git',*args],cwd,120)


def start_id(pid):
    try:
        return Path(f'/proc/{pid}/stat').read_text().rsplit(')',1)[1].split()[19]
    except (OSError,IndexError):
        return ''


def kill(pid):
    try:
        os.killpg(pid,signal.SIGTERM)
    except ProcessLookupError:
        return
    for _ in range(50):
        if not start_id(pid):
            return
        time.sleep(.1)
    try:
        os.killpg(pid,signal.SIGKILL)
    except ProcessLookupError:
        pass


def valid_spec(spec):
    if not re.fullmatch(r'[a-zA-Z0-9][a-zA-Z0-9_-]{0,70}',spec.get('id','')):
        raise ValueError('Invalid task ID')
    if spec.get('kind') not in ('construction','proof','review'):
        raise ValueError('kind must be construction, proof or review')
    for key in ('goal','source'):
        if not isinstance(spec.get(key),str) or not spec[key].strip():
            raise ValueError('Missing '+key)
    files = spec.get('files',[])
    if not files or len(files)!=len(set(files)):
        raise ValueError('Explicit unique file scope required')
    for f in files:
        p = Path(f)
        if p.is_absolute() or '..' in p.parts or not (
            (f.startswith('LogGas/') and f.endswith('.lean')) or
            f in ('LogGas.lean','Solution.lean','PaperSolution.lean') or
            (spec['kind']=='review' and f.startswith('verification/reviews/') and p.suffix in ('.json','.md'))):
            raise ValueError('Protected/out-of-scope path: '+f)
    deps = spec.get('depends_on',[])
    if not isinstance(deps,list) or spec['id'] in deps:
        raise ValueError('Invalid dependencies')
    targets = spec.get('targets',[])
    if spec['kind']!='review' and not targets:
        raise ValueError('Expected declarations required')
    if spec['kind']=='proof' and (len(targets)!=1 or len(files)!=1):
        raise ValueError('Proof tasks require one declaration and one file; use construction for larger changes')
    if any(not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*',t) for t in targets):
        raise ValueError('Invalid target declaration')
    return spec


def submit(c,spec):
    valid_spec(spec)
    for dep in spec.get('depends_on',[]):
        if not c.execute('SELECT 1 FROM tasks WHERE id=?',(dep,)).fetchone():
            raise ValueError('Submit prerequisite first: '+dep)
    with c:
        c.execute('INSERT INTO tasks(id,spec) VALUES(?,?)',(spec['id'],json.dumps(spec)))


def revise(c,spec):
    valid_spec(spec)
    old=c.execute('SELECT * FROM tasks WHERE id=?',(spec['id'],)).fetchone()
    if not old or old['state']!='needs_replan':
        raise ValueError('Only needs_replan tasks may be revised')
    if set(spec['files'])!=set(json.loads(old['spec'])['files']):
        raise ValueError('Keep existing checkout file scope; submit a new task for other files')
    graph={r['id']:json.loads(r['spec']).get('depends_on',[]) for r in c.execute('SELECT * FROM tasks')}
    graph[spec['id']]=spec.get('depends_on',[])
    def walk(key,stack):
        if key not in graph:raise ValueError('Unknown dependency: '+key)
        if key in stack:raise ValueError('Cyclic task dependencies')
        for dep in graph[key]:walk(dep,stack|{key})
    for key in graph:walk(key,set())
    with c:
        c.execute("UPDATE tasks SET spec=?,state='pending',candidate=NULL,approval=NULL WHERE id=?",(json.dumps(spec),spec['id']))


def status(c):
    return dict(utc=now(), phase=get(c,'phase','not_started'),
        pause_until=get(c,'pause_until','0'), pause_reason=get(c,'pause_reason'),
        push_error=get(c,'push_error'), coordinator_model=get(c,'coordinator_model','unconfirmed'),
        max_workers=LIMIT, worker_model=WORKER,
        tasks=[dict(r) for r in c.execute('SELECT * FROM tasks ORDER BY rowid')],
        jobs=[dict(r) for r in c.execute('SELECT * FROM jobs ORDER BY id DESC LIMIT 20')])


def ready_tasks(c,active_count):
    """Never oversubscribe or overlap files, including candidates awaiting review."""
    done={r['id'] for r in c.execute("SELECT id FROM tasks WHERE state='done'")}
    owned=set()
    for row in c.execute("SELECT spec FROM tasks WHERE state IN ('running','awaiting_review','approved')"):
        owned.update(json.loads(row['spec'])['files'])
    ready=[]
    for task in c.execute("SELECT * FROM tasks WHERE state='pending' AND retry<=? ORDER BY rowid",(time.time(),)):
        spec=json.loads(task['spec'])
        if active_count+len(ready)>=LIMIT:break
        if not set(spec.get('depends_on',[]))<=done or set(spec['files'])&owned:continue
        ready.append(task)
        owned.update(spec['files'])
    return ready


class Campaign:
    def __init__(self):
        self.c=dbopen()
        self.active={}
        self.last_publish=0
        self.last_coord=0
        self.coord_signature=None
        LOGS.mkdir(parents=True,exist_ok=True)

    def checkout(self,name):
        path=ROOT/'wt/campaign'/name
        if not path.exists():
            path.parent.mkdir(parents=True,exist_ok=True)
            git('worktree','add','--detach',str(path),'HEAD')
            lake=path/'.lake'
            lake.mkdir(exist_ok=True)
            (lake/'packages').symlink_to((ROOT/'.lake/packages').resolve(),target_is_directory=True)
            manifest=ROOT/'verification/dependency-lock.json'
            if manifest.exists():
                (path/'lake-manifest.json').write_bytes(manifest.read_bytes())
        return path

    def publish(self):
        snapshot=status(self.c)
        rows=snapshot['tasks']
        report=ROOT/'reports/campaign.md'
        report.write_text('# Main theorem campaign\n\n'+
            f"Updated: {now()}. State: {snapshot['phase']}.\n\n"+
            f"Coordinator: {snapshot['coordinator_model']}; up to {LIMIT} Sonnet workers.\n\n"+
            f"Pause until (Unix UTC): {snapshot['pause_until']}; reason: {snapshot['pause_reason'] or 'none'}.\n\n"+
            '**The paper theorem is not certified until the final verification gate passes.**\n\n'+
            '| Task | State | Attempts | Detail |\n|---|---|---|---|\n'+
            ''.join(f"| {r['id']} | {r['state']} | {r['attempt']} | {r['error'][-400:].replace(chr(10),' ').replace('|','/')} |\n" for r in rows))
        usage=ROOT/'state/campaign-usage.tsv'
        jobs=self.c.execute('SELECT id,task,role,started,ended,result,cost,usage FROM jobs ORDER BY id').fetchall()
        usage.write_text('job\ttask\trole\tstarted\tended\toutcome\testimated_usd\tusage_json\n'+
            ''.join('\t'.join(str(r[k]) if r[k] is not None else 'unknown' for k in r.keys())+'\n' for r in jobs))
        if git('diff','--cached','--name-only'):
            raise RuntimeError('Unexpected staged changes in publisher')
        git('add','--','reports/campaign.md','state/campaign-usage.tsv')
        if git('diff','--cached','--name-only'):
            git('commit','-m','Report main theorem campaign progress and usage')
        try:
            git('push','origin','main')
            put(self.c,'push_error','')
        except RuntimeError as e:
            put(self.c,'push_error',str(e))
        self.last_publish=time.time()

    def launch(self,task=None):
        role='worker' if task else 'coordinator'
        with self.c:
            j=self.c.execute('INSERT INTO jobs(task,role,started) VALUES(?,?,?)',
                            (task['id'] if task else None,role,time.time())).lastrowid
        if task:
            spec=json.loads(task['spec'])
            path=Path(task['worktree']) if task['worktree'] else self.checkout(f'{task["id"]}-{j}')
            base=task['base'] or git('rev-parse','HEAD',cwd=path)
            if task['worktree'] and base!=git('rev-parse','HEAD'):
                # Preserve the old checkout and replay partial work onto new
                # prerequisites. Conflicts stay in the new private checkout for
                # the worker to resolve; main is never reset.
                present=[f for f in spec['files'] if (path/f).exists()]
                if present:git('add','--',*present,cwd=path)
                patchfile=STATE/(task['id']+'-resume.patch')
                patchfile.write_text(git('diff','--cached','--binary','--full-index',base,cwd=path)+'\n')
                fresh=self.checkout(f'{task["id"]}-{j}')
                base=git('rev-parse','HEAD',cwd=fresh)
                if patchfile.read_text().strip():
                    code,out=run(['git','apply','--3way',str(patchfile)],fresh,120,False)
                    (LOGS/f'{j}-refresh.log').write_text(out)
                notes=path/'.lake/campaign-notes.md'
                if notes.exists():shutil.copyfile(notes,fresh/'.lake/campaign-notes.md')
                path=fresh
            prompt=(ROOT/'prompts/campaign-worker.md').read_text()+'\nTASK:\n'+json.dumps(spec,indent=2)
            prompt+=f'\nYour actual reviewer/job identity: dell3-sonnet-job-{j}.\n'
            prompt+='\nPrevious outcome: '+task['error'][-2500:]
            prompt+='\nPublisher root (read only) for latest upstream interfaces: '+str(ROOT)
            with self.c:
                self.c.execute("UPDATE tasks SET state='running',attempt=attempt+1,worktree=?,base=? WHERE id=?",(str(path),base,task['id']))
            turns='40' if spec['kind']=='review' else '30'
        else:
            path=self.checkout('coordinator-'+str(j))
            base=git('rev-parse','HEAD')
            prompt=(ROOT/'prompts/campaign-coordinator.md').read_text()
            prompt+=f'\nPUBLISHER_ROOT={ROOT}\nCONTROL={ROOT}/scripts/campaign.py\n'
            prompt+='\nCURRENT STATE:\n'+json.dumps(status(self.c),indent=2)
            prompt+='\nRead shared NOTES.md at '+str(STATE/'NOTES.md')+' if present. Save durable decisions there.'
            turns='60'
        model=WORKER if task else COORD
        argv=['claude','-p','--model',model,'--max-turns',turns,'--disallowedTools','Agent','Task',
              '--dangerously-skip-permissions','--output-format','stream-json','--verbose',prompt]
        log=(LOGS/f'{j}.jsonl').open('w')
        err=(LOGS/f'{j}.stderr').open('w')
        p=subprocess.Popen(argv,cwd=path,stdout=log,stderr=err,start_new_session=True)
        log.close();err.close()
        with self.c:
            self.c.execute('UPDATE jobs SET pid=?,start_id=?,worktree=?,base=? WHERE id=?',
                           (p.pid,start_id(p.pid),str(path),base,j))
        self.active[j]=(p,time.time(),role)
        if not task:
            self.last_coord=time.time()

    def finish(self,j,code):
        job=self.c.execute('SELECT * FROM jobs WHERE id=?',(j,)).fetchone()
        result=None
        models=set()
        session=None
        for line in (LOGS/f'{j}.jsonl').read_text().splitlines():
            try:
                e=json.loads(line)
            except ValueError:
                continue
            if e.get('session_id'):session=e['session_id']
            if e.get('type')=='system' and e.get('model'):models.add(e['model'])
            if e.get('type')=='assistant' and e.get('message',{}).get('model'):
                models.add(e['message']['model'])
            if e.get('type')=='result':result=e
        stderr=(LOGS/f'{j}.stderr').read_text()
        outcome=classify(result,stderr,code)
        wanted=COORD if job['role']=='coordinator' else 'claude-sonnet'
        # Exact Opus family required; Sonnet alias must resolve to Sonnet.
        if models and not all(m.startswith(wanted) for m in models):
            put(self.c,'fatal_model','Unexpected model(s): '+','.join(models))
        error_text=(json.dumps(result or {})+'\n'+stderr).lower()
        if any(s in error_text for s in ('model not found','invalid model','unknown model','not have access to model')):
            put(self.c,'fatal_model','Requested model unavailable; no fallback is configured')
        if job['role']=='coordinator' and models:
            put(self.c,'coordinator_model',','.join(sorted(models)))
        with self.c:
            self.c.execute('UPDATE jobs SET ended=?,result=?,cost=?,usage=?,session=? WHERE id=?',
                (time.time(),outcome,result.get('total_cost_usd') if result else None,
                 json.dumps(result.get('usage')) if result and result.get('usage') else None,session,j))
        if outcome in ('quota','rate_limit','authentication'):
            text=json.dumps(result or {})+'\n'+stderr
            deadline=reset_time(text,time.time(),1800 if outcome=='authentication' else 300)
            put(self.c,'pause_until',max(float(get(self.c,'pause_until','0')),deadline))
            put(self.c,'pause_reason',outcome)
        if job['role']=='worker':
            task=self.c.execute('SELECT * FROM tasks WHERE id=?',(job['task'],)).fetchone()
            try:
                self.candidate(task)
            except Exception as e:
                checkpoint=''
                try:checkpoint=self.checkpoint_partial(task)
                except Exception as backup_error:checkpoint=' WIP push pending: '+str(backup_error)[-500:]
                with self.c:
                    self.c.execute("UPDATE tasks SET state='needs_replan',error=? WHERE id=?",(outcome+': '+str(e)+checkpoint,task['id']))

    def checkpoint_partial(self,task):
        """Publish explicitly unverified work separately; never admit it onto main."""
        spec=json.loads(task['spec']);path=Path(task['worktree'])
        changed=set(git('diff','--name-only',task['base'],cwd=path).splitlines())
        changed.update(git('ls-files','--others','--exclude-standard',cwd=path).splitlines())
        if not changed:return ''
        if changed-set(spec['files']):return ' Out-of-scope checkout retained privately.'
        if any(not (path/f).is_file() or (path/f).is_symlink() for f in changed):return ' Invalid paths retained privately.'
        git('add','--',*sorted(changed),cwd=path)
        if git('diff','--cached','--name-only',cwd=path):
            git('commit','-m','UNVERIFIED partial '+task['id'],cwd=path)
        branch=f'campaign/wip/{task["id"]}-{task["attempt"]}'
        git('push','origin','HEAD:refs/heads/'+branch,cwd=path)
        return ' Unverified checkpoint: '+branch

    def scope(self,path,base,spec):
        changed=set(git('diff','--name-only',base,cwd=path).splitlines())
        changed.update(git('ls-files','--others','--exclude-standard',cwd=path).splitlines())
        if not changed:
            raise ValueError('No candidate changes; preserve checkout and split/replan task')
        illegal=changed-set(spec['files'])
        if illegal:
            raise ValueError('Out-of-scope changes: '+','.join(sorted(illegal)))
        if git('ls-files','--deleted',cwd=path):
            raise ValueError('Deleting tracked files is not allowed')
        for f in changed:
            p=path/f
            if p.is_symlink() or not p.is_file():
                raise ValueError('Candidate path is not a regular file: '+f)
            if f.endswith('.lean') and re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b|skipKernelTC',mask_comments(p.read_text())):
                raise ValueError('Candidate contains an admission/unsafe bypass: '+f)
        if spec['kind']=='proof':
            f=spec['files'][0]
            before=run(['git','show',base+':'+f],path,120,False)[1]
            if not proof_only_change(before,(path/f).read_text(),spec['targets'][0]):
                raise ValueError('Proof task changed its statement or material outside the assigned proof')
        return changed

    def check(self,path,spec,tag):
        modules=sorted({f[:-5].replace('/','.') for f in spec['files'] if f.endswith('.lean')})
        if not modules:
            from verify import freeze
            for f in spec['files']:
                if not f.endswith('.json'):continue
                receipt=json.loads((path/f).read_text())
                if receipt.get('role') not in ('mathematical-fidelity','lean-verification') or not receipt.get('reviewer'):
                    raise ValueError('Review receipt missing actual role/identity')
                if receipt.get('reviewed_files')!=freeze(path):
                    raise ValueError('Review receipt does not match the actual source/harness freeze')
            return
        code,out=run(['lake','build',*modules],path,3600,False)
        (LOGS/f'{tag}-build.log').write_text(out)
        if code:raise ValueError('Build failed: '+out[-3000:])
        scratch=path/'.lake/campaign-check.lean'
        scratch.write_text(''.join('import '+m+'\n' for m in modules)+
            ''.join('#print axioms '+n+'\n' for n in spec['targets']))
        code,out=run(['lake','env','lean',str(scratch)],path,600,False)
        (LOGS/f'{tag}-axioms.log').write_text(out)
        matches=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[[^]]*\]|does not depend on any axioms)",out,re.S)
        if code or set(matches)!=set(spec['targets']):
            raise ValueError('Missing target/axiom output: '+out[-2500:])
        for line in re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[[^]]*\]|does not depend on any axioms)",out,re.S):
            if not standard_axioms(line[0]):raise ValueError('Forbidden transitive axiom: '+line[0])

    def candidate(self,task):
        spec=json.loads(task['spec']);path=Path(task['worktree'])
        changed=self.scope(path,task['base'],spec)
        self.check(path,spec,task['id'])
        git('add','--',*sorted(changed),cwd=path)
        if git('diff','--cached','--name-only',cwd=path):
            git('commit','-m','Candidate '+task['id'],cwd=path)
        sha=git('rev-parse','HEAD',cwd=path)
        if sha==task['base']:raise ValueError('Empty candidate')
        with self.c:
            self.c.execute("UPDATE tasks SET state='awaiting_review',candidate=?,approval=NULL,error=? WHERE id=?",(sha,'Build/target checks passed; Opus review required',task['id']))

    def integrate(self,task):
        spec=json.loads(task['spec'])
        if task['approval']!=task['candidate']:raise ValueError('Stale candidate approval')
        candidate=Path(task['worktree'])
        self.scope(candidate,task['base'],spec)
        if git('status','--porcelain',cwd=candidate):raise ValueError('Candidate changed after review')
        staging=self.checkout('integration-'+task['id']+'-'+str(task['attempt']))
        # Flatten the reviewed candidate against its recorded base; isolated staging
        # applies it to current main without rewriting or resetting publisher history.
        patch=STATE/(task['id']+'.patch')
        patch.write_text(git('diff','--binary',task['base'],task['candidate'],cwd=candidate)+'\n')
        run(['git','apply','--index',str(patch)],staging,120)
        git('commit','-m','Implement '+task['id']+' (Opus reviewed)',cwd=staging)
        self.check(staging,spec,'integration-'+task['id'])
        # Check all currently present project modules; missing milestones are not pass claims.
        code,out=run(['lake','build','LogGas','Challenge','Solution','PaperChallenge','PaperSolution','VerificationAudit'],staging,3600,False)
        (LOGS/f'integration-{task["id"]}-project.log').write_text(out)
        if code:raise ValueError('Integration build failed: '+out[-2500:])
        if git('status','--porcelain'):raise ValueError('Publisher dirty; refusing integration')
        git('merge','--ff-only',git('rev-parse','HEAD',cwd=staging))
        with self.c:
            self.c.execute("UPDATE tasks SET state='done',error=? WHERE id=?",('Reviewed, rebuilt and merged at '+git('rev-parse','HEAD'),task['id']))

    def recover(self):
        for job in self.c.execute('SELECT * FROM jobs WHERE ended IS NULL').fetchall():
            if start_id(job['pid'])==job['start_id'] and job['start_id']:
                kill(job['pid'])
            with self.c:
                self.c.execute("UPDATE jobs SET ended=?,result='interrupted' WHERE id=?",(time.time(),job['id']))
                if job['task']:
                    self.c.execute("UPDATE tasks SET state='needs_replan',error='Interrupted; inspect preserved checkout before retry' WHERE id=?",(job['task'],))

    def loop(self):
        lock=(STATE/'lock').open('a')
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        if git('branch','--show-current')!='main' or git('status','--porcelain'):
            raise RuntimeError('Publisher requires a clean main checkout')
        lockfile=ROOT/'verification/dependency-lock.json'
        if (ROOT/'lake-manifest.json').read_bytes()!=lockfile.read_bytes():
            raise RuntimeError('Runtime manifest differs from pinned dependency lock')
        for package in json.loads(lockfile.read_text())['packages']:
            if git('rev-parse','HEAD',cwd=ROOT/'.lake/packages'/package['name'])!=package['rev']:
                raise RuntimeError('Installed dependency revision differs: '+package['name'])
        self.recover()
        put(self.c,'phase','running')
        self.publish()
        while not (STATE/'stop').exists():
            for j,(p,started,role) in list(self.active.items()):
                if not get(self.c,'observed_model_'+str(j)):
                    with (LOGS/f'{j}.jsonl').open() as stream:
                        first=stream.readline(1048576)
                    try:event=json.loads(first)
                    except ValueError:event={}
                    if event.get('model'):
                        model=event['model']
                        wanted=COORD if role=='coordinator' else 'claude-sonnet'
                        if not model.startswith(wanted):
                            put(self.c,'fatal_model','Unexpected running model: '+model)
                        put(self.c,'observed_model_'+str(j),model)
                        if role=='coordinator':put(self.c,'coordinator_model',model)
                timeout=2400 if role=='coordinator' else 1200
                if p.poll() is None and time.time()-started>timeout:
                    kill(p.pid)
                if p.poll() is not None:
                    self.finish(j,p.returncode)
                    self.active.pop(j)
            if get(self.c,'fatal_model'):
                put(self.c,'phase','blocked_model');self.publish();break
            for task in self.c.execute("SELECT * FROM tasks WHERE state='approved'").fetchall():
                try:self.integrate(task)
                except Exception as e:
                    with self.c:
                        self.c.execute("UPDATE tasks SET state='needs_replan',approval=NULL,error=? WHERE id=?",(str(e),task['id']))
            paused=float(get(self.c,'pause_until','0'))>time.time()
            put(self.c,'phase','waiting_'+get(self.c,'pause_reason') if paused else 'running')
            if get(self.c,'verify_requested') and not self.active:
                unfinished=self.c.execute("SELECT COUNT(*) FROM tasks WHERE state!='done'").fetchone()[0]
                if unfinished:
                    put(self.c,'verify_requested','')
                    put(self.c,'verification_error','Cannot verify with unfinished tasks')
                else:
                    put(self.c,'phase','verifying');self.publish()
                    code,out=run(['python3','scripts/verify.py','--fresh'],ROOT,14400,False)
                    (LOGS/'final-verification.log').write_text(out)
                    put(self.c,'phase','complete' if code==0 else 'needs_verification_attention')
                    put(self.c,'verification_result',out[-5000:])
                    self.publish()
                    (STATE/'stop').touch()
                    return
            if not paused and not get(self.c,'verify_requested'):
                for task in ready_tasks(self.c,sum(role=='worker' for _,_,role in self.active.values())):
                    self.launch(task)
                signature=tuple((r['id'],r['state'],r['candidate']) for r in self.c.execute('SELECT * FROM tasks ORDER BY id'))
                active_coord=any(role=='coordinator' for _,_,role in self.active.values())
                if not active_coord and (self.last_coord==0 or (time.time()-self.last_coord>300 and signature!=self.coord_signature) or time.time()-self.last_coord>1800):
                    self.launch();self.coord_signature=signature
            if time.time()-self.last_publish>=300:self.publish()
            time.sleep(2)
        for j,(p,_,_) in self.active.items():
            if p.poll() is None:kill(p.pid)
        if not get(self.c,'fatal_model'):put(self.c,'phase','stopped')
        self.publish()


def main():
    parser=argparse.ArgumentParser(__doc__)
    parser.add_argument('action',choices=['run','status','enqueue','approve','retry','revise','stop','note','verify'])
    parser.add_argument('--file',type=Path)
    parser.add_argument('--id')
    parser.add_argument('--commit')
    args=parser.parse_args()
    c=dbopen()
    if args.action=='run':Campaign().loop()
    elif args.action=='status':print(json.dumps(status(c),indent=2))
    elif args.action=='enqueue':submit(c,json.loads(args.file.read_text()))
    elif args.action=='revise':revise(c,json.loads(args.file.read_text()))
    elif args.action=='approve':
        with c:
            count=c.execute("UPDATE tasks SET state='approved',approval=? WHERE id=? AND state='awaiting_review' AND candidate=?",(args.commit,args.id,args.commit)).rowcount
        if count!=1:raise SystemExit('Approval rejected: candidate/state mismatch')
    elif args.action=='retry':
        with c:
            count=c.execute("UPDATE tasks SET state='pending',candidate=NULL,approval=NULL WHERE id=? AND state='needs_replan'",(args.id,)).rowcount
        if count!=1:raise SystemExit('Retry requires needs_replan')
    elif args.action=='stop':(STATE/'stop').touch()
    elif args.action=='note':(STATE/'NOTES.md').write_text(args.file.read_text())
    elif args.action=='verify':put(c,'verify_requested','1')


if __name__=='__main__':main()
