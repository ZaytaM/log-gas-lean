"""Offline regression tests; fake models/Lean, real Git worktrees and queue state."""
from datetime import datetime
import importlib.util
import json
import os
from pathlib import Path
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
from zoneinfo import ZoneInfo

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
from runner_support import classify, declarations, mask_comments, proof_only_change, reset_time, standard_axioms


class SupportTests(unittest.TestCase):
    def test_turn_limit_is_not_quota(self):
        self.assertEqual(classify({'is_error':True,'subtype':'error_max_turns','errors':['Reached maximum number of turns (20)']}), 'turn_limit')
        self.assertEqual(classify({'is_error':True,'result':"You've hit your session limit · resets 2pm (America/Chicago)"}), 'quota')
        self.assertEqual(classify({'is_error':True,'terminal_reason':'api_error','errors':['HTTP 503']}), 'error')
        self.assertEqual(classify(None), 'invalid_output')
        self.assertEqual(classify(None, 'HTTP 429'), 'rate_limit')
        self.assertEqual(classify(None, exit_code=124), 'timeout')
        # Telemetry and worker prose must not look like API failures.
        self.assertEqual(classify({'is_error':False,'subtype':'success','time_to_request_ms':401,'api_error_status':None}), 'success')
        self.assertEqual(classify({'is_error':False,'subtype':'success','result':'no quota or rate limit issue; not a 429'}), 'success')
        self.assertEqual(classify({'is_error':True,'api_error_status':401,'result':'Invalid API key'}), 'authentication')
        self.assertEqual(classify({'is_error':True,'result':'API Error: 429 overloaded'}), 'rate_limit')
        self.assertEqual(classify({'is_error':False,'subtype':'success'}, exit_code=1), 'error')

    def test_timezone_and_fallback(self):
        zone = ZoneInfo('America/Chicago')
        now = datetime(2026,10,20,10,0,tzinfo=zone).timestamp()
        result = reset_time("You've hit your session limit · resets 2pm (America/Chicago)", now)
        self.assertEqual(result, datetime(2026,10,20,14,1,tzinfo=zone).timestamp())
        self.assertEqual(reset_time('unknown',now,600),now+600)

    def test_source_and_axioms(self):
        source = '/- sorry /- nested -/ -/\nnamespace A\nsection S\ntheorem x : True := by\n  sorry\nend S\nend A\n'
        ds = declarations(source)
        self.assertEqual([(d.name,d.sorry) for d in ds], [('A.x',1)])
        self.assertTrue(proof_only_change(source,source.replace('  sorry','  trivial'),'A.x'))
        self.assertFalse(proof_only_change(source,source.replace(': True',': False'),'A.x'))
        self.assertTrue(standard_axioms("'A.x' depends on axioms: [propext, Classical.choice, Quot.sound]"))
        self.assertFalse(standard_axioms("'A.x' depends on axioms: [sorryAx]"))
        self.assertFalse(standard_axioms("'A.x' depends on axioms: [A.native_decide.ax_1]"))


FAKE_CLAUDE = r'''#!/usr/bin/env python3
import json,os,pathlib,re,sys,time
mode=os.environ.get('FAKE_MODE','turn_limit')
prompt=sys.argv[-1]
if mode=='quota':
 print(json.dumps({'is_error':True,'result':"You've hit your session limit · resets 11pm (America/Chicago)",'total_cost_usd':0,'usage':{'input_tokens':1}}));sys.exit(1)
if mode=='slow': time.sleep(60)
path=pathlib.Path(re.search(r'^File: (.+)$',prompt,re.M)[1])
path.write_text(path.read_text().replace('sorry','trivial'))
time.sleep(.2)
print(json.dumps({'is_error':mode=='turn_limit','subtype':'error_max_turns' if mode=='turn_limit' else 'success','terminal_reason':'max_turns' if mode=='turn_limit' else None,'num_turns':21,'total_cost_usd':.2,'duration_ms':200,'usage':{'input_tokens':5,'output_tokens':12,'cache_read_input_tokens':100}}))
'''
FAKE_LAKE = r'''#!/usr/bin/env python3
import pathlib,sys
if sys.argv[1]=='env':
 import re
 for name in re.findall(r'#print axioms (\S+)',pathlib.Path(sys.argv[-1]).read_text()):
  print("'%s' depends on axioms: [propext, Classical.choice, Quot.sound]" % name)
else: print('Build completed successfully')
'''


class IntegrationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)/'repo'
        self.root.mkdir()
        self.bin = Path(self.tmp.name)/'bin'; self.bin.mkdir()
        for name, text in [('claude',FAKE_CLAUDE),('lake',FAKE_LAKE)]:
            path=self.bin/name;path.write_text(text);path.chmod(0o755)
        shutil.copytree(SCRIPTS,self.root/'scripts',ignore=shutil.ignore_patterns('__pycache__','tests'))
        (self.root/'scripts/pipeline.conf').write_text('MAX_WORKERS=3\nMODEL_WORKER=sonnet\nMAX_TURNS=20\nWORKER_TIMEOUT=600\nLOAD_HALVE_ABOVE=10000\n')
        (self.root/'prompts').mkdir()
        (self.root/'prompts/worker.md').write_text('File: {LEMMA_FILE}\nLemma: {LEMMA_NAME}\n')
        (self.root/'LogGas').mkdir()
        (self.root/'.lake/packages').mkdir(parents=True)
        (self.root/'reports').mkdir(); (self.root/'state').mkdir()
        (self.root/'.gitignore').write_text('.lake/\nwt/\nlogs/\nstate/runtime/\n__pycache__/\n')
        for i in range(7):
            (self.root/f'LogGas/T{i}.lean').write_text(f'namespace T{i}\ntheorem proof : True := by\n  sorry\nend T{i}\n')
        self.git('init','-b','main')
        self.git('config','user.name','Test'); self.git('config','user.email','test@example.invalid')
        self.git('add','.'); self.git('commit','-m','fixture')
        bare=Path(self.tmp.name)/'origin.git'
        subprocess.run(['git','init','--bare',str(bare)],check=True,capture_output=True)
        self.git('remote','add','origin',str(bare)); self.git('push','-u','origin','main')
        self.processes=[]

    def tearDown(self):
        for p in self.processes:
            if p.poll() is None:
                (self.root/'state/runtime/stop').touch()
                try: p.wait(timeout=25)
                except subprocess.TimeoutExpired: p.kill();p.wait()
        self.tmp.cleanup()

    def git(self,*args):
        return subprocess.run(['git',*args],cwd=self.root,check=True,capture_output=True,text=True).stdout

    def launch(self,mode):
        env=dict(os.environ,PATH=str(self.bin)+os.pathsep+os.environ['PATH'],FAKE_MODE=mode,PYTHONDONTWRITEBYTECODE='1')
        log=(self.root/f'{mode}.log')
        # Keep test logs outside the worktree, so the real clean-checkout guard applies.
        log=Path(self.tmp.name)/f'{mode}-{len(self.processes)}.log'
        with log.open('w') as f:
            p=subprocess.Popen([sys.executable,str(self.root/'scripts/persistent.py'),'run'],cwd=self.root,env=env,stdout=f,stderr=f)
        self.processes.append(p)
        return p,log

    def db(self):
        return sqlite3.connect(self.root/'state/runtime/queue.sqlite3')

    def wait_for(self,p,predicate,log,seconds=25):
        end=time.time()+seconds
        while time.time()<end:
            try:
                with self.db() as db:
                    if predicate(db): return
            except sqlite3.OperationalError: pass
            if p.poll() is not None: self.fail(log.read_text())
            time.sleep(.05)
        self.fail('Timed out: '+log.read_text())

    def test_close_rearms_axiom_waiting_tasks(self):
        spec = importlib.util.spec_from_file_location('rearm_test_runner', SCRIPTS/'persistent.py')
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        db = sqlite3.connect(':memory:')
        db.executescript(module.SCHEMA)
        later = time.time() + 43200
        rows = [('A', 'pending', 'Candidate failed axiom check; checkpoint retained'),
                ('B', 'pending', 'Integration build/axiom check failed; worker proof retained'),
                ('C', 'pending', 'Candidate proof did not build; checkpoint retained'),
                ('D', 'blocked', 'Candidate failed axiom check; checkpoint retained'),
                ('E', 'waiting_saved_dependencies', 'Candidate failed axiom check; checkpoint retained')]
        for name, state, error in rows:
            db.execute('INSERT INTO tasks(id,file,module,name,state,not_before,error) VALUES(?,?,?,?,?,?,?)',
                       ('M:' + name, 'M.lean', 'M', name, state, later, error))
        with db: self.assertEqual(module.rearm_after_close(db), 3)
        due = dict(db.execute('SELECT name, not_before FROM tasks').fetchall())
        self.assertEqual((due['A'], due['B'], due['E']), (0, 0, 0))
        self.assertEqual((due['C'], due['D']), (later, later))

    def recovery_runner(self):
        spec = importlib.util.spec_from_file_location('saved_recovery_runner', self.root/'scripts/persistent.py')
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        runner = module.Runner()
        runner.log = lambda message: None
        runner.report = lambda: None
        runner.publish = lambda: None
        runner.build = lambda *args, **kwargs: True
        return module, runner

    def saved_task(self, runner):
        file = 'LogGas/T0.lean'
        path = self.root/file
        path.write_text('namespace T0\ntheorem prerequisite : True := by\n  sorry\ntheorem proof : True := by\n  sorry\nend T0\n')
        self.git('add', file); self.git('commit', '-m', 'Dependent proof fixture')
        task_id = 'LogGas.T0:T0.proof'
        with runner.db:
            runner.db.execute('INSERT INTO tasks(id,file,module,name,attempts) VALUES(?,?,?,?,?)',
                              (task_id,file,'LogGas.T0','T0.proof',1))
        task = runner.db.execute('SELECT * FROM tasks WHERE id=?',(task_id,)).fetchone()
        wt, branch = runner.prepare(task)
        saved = wt/file
        saved.write_text(saved.read_text().replace('theorem proof : True := by\n  sorry',
                                                'theorem proof : True := by\n  trivial'))
        with runner.db:
            runner.db.execute('UPDATE tasks SET worktree=?,branch=? WHERE id=?',(str(wt),branch,task_id))
            job_id = runner.db.execute('INSERT INTO jobs(task,started,base_commit,outcome,cost,usage_known) VALUES(?,?,?,?,?,?)',
                                      (task_id,time.time(),self.git('rev-parse','HEAD').strip(),'success',.2,1)).lastrowid
        return runner.db.execute('SELECT * FROM tasks WHERE id=?',(task_id,)).fetchone(), runner.db.execute('SELECT * FROM jobs WHERE id=?',(job_id,)).fetchone()

    def test_accept_refreshes_a_prerequisite_closed_during_worker_run(self):
        module, runner = self.recovery_runner()
        task, job = self.saved_task(runner)
        path = self.root/task['file']
        path.write_text(path.read_text().replace('theorem prerequisite : True := by\n  sorry',
                                               'theorem prerequisite : True := by\n  trivial'))
        self.git('add',task['file']); self.git('commit','-m','Close prerequisite while worker runs')
        runner.axioms = lambda wt, *args: not any(d.sorry for d in module.declarations((wt/task['file']).read_text()))
        runner.accept(task,job,'success')
        self.assertEqual(runner.db.execute('SELECT state FROM tasks').fetchone()[0],'closed')
        self.assertFalse(any(d.sorry for d in module.declarations(path.read_text())))
        self.assertEqual(runner.db.execute('SELECT COUNT(*) FROM jobs').fetchone()[0],1)
        runner.db.close()

    def test_complete_saved_proof_is_rechecked_without_model_usage(self):
        module, runner = self.recovery_runner()
        task, job = self.saved_task(runner)
        from unittest.mock import Mock
        runner.accept = Mock()
        real_popen = module.subprocess.Popen
        def no_models(args, *other, **kwargs):
            self.assertFalse(any('worker_exec.py' in str(a) or str(a)=='claude' for a in args))
            return real_popen(args,*other,**kwargs)
        with patch.object(module.subprocess,'Popen',side_effect=no_models):
            runner.start(task)
        self.assertEqual(runner.accept.call_args.args[2],'saved_proof_recheck')
        self.assertEqual(runner.db.execute('SELECT COUNT(*) FROM jobs').fetchone()[0],1)
        self.assertEqual(runner.db.execute('SELECT attempts FROM tasks').fetchone()[0],1)
        self.assertEqual(runner.db.execute('SELECT SUM(cost) FROM jobs').fetchone()[0],.2)
        runner.db.close()

    def test_complete_candidate_waits_without_launching_more_workers(self):
        module, runner = self.recovery_runner()
        task,job = self.saved_task(runner)
        runner.axioms = lambda *args: False
        runner.accept(task,job,'success')
        self.assertEqual(runner.db.execute('SELECT state FROM tasks').fetchone()[0],'waiting_saved_dependencies')
        with runner.db: self.assertEqual(module.rearm_after_close(runner.db),1)
        state,due = runner.db.execute('SELECT state,not_before FROM tasks').fetchone()
        self.assertEqual((state,due),('pending',0))
        runner.db.close()

    def test_discovery_waits_for_dependency_axioms(self):
        spec = importlib.util.spec_from_file_location('discovery_test_runner', SCRIPTS/'persistent.py')
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        db = sqlite3.connect(':memory:')
        db.row_factory = sqlite3.Row
        db.executescript(module.SCHEMA)
        runner = module.Runner.__new__(module.Runner)
        runner.db = db
        checked_names = []
        runner.axioms_many = lambda cwd, tasks: {task['name']: checked_names.append(task['name']) or False for task in tasks}
        with patch.object(module, 'ROOT', self.root):
            runner.discover()
            path = self.root/'LogGas/T0.lean'
            path.write_text(path.read_text().replace('sorry', 'trivial'))
            runner.discover()
            row = db.execute("SELECT state FROM tasks WHERE name='T0.proof'").fetchone()
            self.assertEqual(row[0], 'waiting_dependencies')
            before = len(checked_names)
            runner.discover()
            self.assertEqual(len(checked_names), before)
            runner.axioms_many = lambda cwd, tasks: {task['name']: True for task in tasks}
            # Closing a prerequisite changes the sources, triggering a fresh audit.
            dep = self.root/'LogGas/T1.lean'
            dep.write_text(dep.read_text().replace('sorry', 'trivial'))
            runner.discover()
            self.assertEqual(db.execute("SELECT state FROM tasks WHERE name='T0.proof'").fetchone()[0], 'closed')
            path.write_text(path.read_text().replace('trivial', 'sorry'))
            runner.discover()
            self.assertEqual(db.execute("SELECT state FROM tasks WHERE name='T0.proof'").fetchone()[0], 'pending')
        db.close()

    def test_batched_axioms_keep_each_target_separate(self):
        spec = importlib.util.spec_from_file_location('batch_audit_test_runner', SCRIPTS/'persistent.py')
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        runtime = self.root/'state/runtime'
        runtime.mkdir()
        (self.root/'logs/service').mkdir(parents=True)
        runner = module.Runner.__new__(module.Runner)
        targets = [{'module':'T0', 'name':'T0.proof'}, {'module':'T1', 'name':'T1.proof'}]
        output = "'T0.proof' depends on axioms: [propext, Classical.choice, Quot.sound]\n'T1.proof' depends on axioms: [propext,\n sorryAx]\n"
        with patch.multiple(module, ROOT=self.root, RUNTIME=runtime):
            with patch.object(module, 'cmd', return_value=(0, output)):
                self.assertEqual(runner.axioms_many(self.root, targets), {'T0.proof':True, 'T1.proof':False})
            with patch.object(module, 'cmd', return_value=(1, output)):
                self.assertEqual(runner.axioms_many(self.root, targets), {'T0.proof':False, 'T1.proof':False})
        self.assertFalse((runtime/'axioms-discovery.lean').exists())

    def test_more_than_five_tasks_and_completed_turn_limit(self):
        p,log=self.launch('turn_limit')
        p.wait(timeout=35)
        self.assertEqual(p.returncode,0,log.read_text())
        with self.db() as db:
            self.assertEqual(db.execute("SELECT COUNT(*) FROM tasks WHERE state='closed'").fetchone()[0],7)
            self.assertEqual(db.execute("SELECT COUNT(*) FROM jobs WHERE outcome='turn_limit'").fetchone()[0],7)
            self.assertIsNone(db.execute("SELECT value FROM meta WHERE key='pause_until'").fetchone())
            events=[]
            for a,b in db.execute('SELECT started,ended FROM jobs'): events += [(a,1),(b,-1)]
            active=peak=0
            for _,delta in sorted(events): active+=delta;peak=max(peak,active)
            self.assertLessEqual(peak,3)
        self.assertIn('All discovered Lean obligations are closed',log.read_text())

    def test_quota_wait_survives_restart_then_resumes(self):
        p,log=self.launch('quota')
        self.wait_for(p,lambda db: db.execute("SELECT 1 FROM meta WHERE key='pause_until'").fetchone(),log)
        (self.root/'state/runtime/stop').touch(); p.wait(timeout=25)
        with self.db() as db:
            self.assertGreater(float(db.execute("SELECT value FROM meta WHERE key='pause_until'").fetchone()[0]),time.time())
            self.assertGreater(db.execute("SELECT COUNT(*) FROM tasks WHERE state='pending'").fetchone()[0],0)
            # Advance the persisted reset clock rather than spending real minutes waiting.
            db.execute("UPDATE meta SET value='0' WHERE key='pause_until'")
            db.execute('UPDATE tasks SET not_before=0')
        (self.root/'state/runtime/stop').unlink()
        p,log=self.launch('success'); p.wait(timeout=35)
        self.assertEqual(p.returncode,0,log.read_text())
        with self.db() as db:
            self.assertEqual(db.execute("SELECT COUNT(*) FROM tasks WHERE state='closed'").fetchone()[0],7)
            self.assertGreater(db.execute("SELECT COUNT(*) FROM jobs WHERE outcome='quota'").fetchone()[0],0)

    def test_six_workers_can_run_concurrently(self):
        path=self.root/'scripts/pipeline.conf'
        path.write_text(path.read_text().replace('MAX_WORKERS=3','MAX_WORKERS=6'))
        self.git('add','scripts/pipeline.conf'); self.git('commit','-m','Configure six workers')
        p,log=self.launch('success'); p.wait(timeout=35)
        self.assertEqual(p.returncode,0,log.read_text())
        with self.db() as db:
            events=[]
            for a,b in db.execute('SELECT started,ended FROM jobs'): events += [(a,1),(b,-1)]
            active=peak=0
            for _,delta in sorted(events): active+=delta;peak=max(peak,active)
            self.assertEqual(peak,6)
            self.assertEqual(db.execute("SELECT COUNT(*) FROM tasks WHERE state='closed'").fetchone()[0],7)

    def test_startup_recovers_untracked_report_files(self):
        (self.root/'reports/persistent.md').write_text('Interrupted report\n')
        (self.root/'state/worker_usage.tsv').write_text('Interrupted usage report\n')
        p,log=self.launch('success'); p.wait(timeout=35)
        self.assertEqual(p.returncode,0,log.read_text())
        with self.db() as db:
            self.assertEqual(db.execute("SELECT COUNT(*) FROM tasks WHERE state='closed'").fetchone()[0],7)

    def test_startup_still_rejects_unexpected_untracked_files(self):
        (self.root/'reports/unexpected.txt').write_text('Unrelated user work\n')
        p,log=self.launch('success'); p.wait(timeout=10)
        self.assertNotEqual(p.returncode,0)
        self.assertIn('reports/unexpected.txt',log.read_text())
        with self.db() as db:
            self.assertEqual(db.execute('SELECT COUNT(*) FROM jobs').fetchone()[0],0)

    def test_single_controller_and_checkpoint_on_stop(self):
        p,log=self.launch('slow')
        self.wait_for(p,lambda db: db.execute('SELECT 1 FROM jobs WHERE pid IS NOT NULL').fetchone(),log)
        second,otherlog=self.launch('success'); second.wait(timeout=10)
        self.assertNotEqual(second.returncode,0)
        self.assertIn('already running',otherlog.read_text())
        (self.root/'state/runtime/stop').touch(); p.wait(timeout=25)
        self.assertEqual(p.returncode,0,log.read_text())
        with self.db() as db:
            self.assertEqual(db.execute("SELECT COUNT(*) FROM tasks WHERE state='running'").fetchone()[0],0)
            self.assertGreater(db.execute("SELECT COUNT(*) FROM jobs WHERE outcome='interrupted'").fetchone()[0],0)

    @unittest.skipUnless(sys.platform.startswith('linux'), 'Linux /proc process identity recovery')
    def test_crash_reclaims_orphan_workers(self):
        p,log=self.launch('slow')
        self.wait_for(p,lambda db: db.execute('SELECT COUNT(*) FROM jobs WHERE pid IS NOT NULL').fetchone()[0]==3,log)
        p.kill();p.wait()
        p,log=self.launch('success')
        # The job outcome is persisted before acceptance finishes restoring the task.
        # Wait for both before overriding the test-only retry timers.
        self.wait_for(p,lambda db: db.execute("SELECT COUNT(*) FROM jobs WHERE outcome='interrupted'").fetchone()[0]==3
                      and db.execute("SELECT COUNT(*) FROM tasks WHERE state IN ('running','verifying')").fetchone()[0]==0,log)
        with self.db() as db: db.execute("UPDATE tasks SET not_before=0 WHERE state='pending'")
        p.wait(timeout=35)
        self.assertEqual(p.returncode,0,log.read_text())
        with self.db() as db:
            self.assertEqual(db.execute("SELECT COUNT(*) FROM tasks WHERE state='closed'").fetchone()[0],7)


if __name__ == '__main__': unittest.main()
