"""Real Git integration with fake Lean/model results; never consumes model usage."""
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import campaign as m


class CampaignTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)/'project'
        self.root.mkdir()
        self.state=self.root/'state/runtime/campaign'
        self.logs=self.root/'logs/campaign'
        self.logs.mkdir(parents=True)
        self.patchers=[patch.object(m,'ROOT',self.root),patch.object(m,'STATE',self.state),patch.object(m,'LOGS',self.logs)]
        for p in self.patchers:p.start();self.addCleanup(p.stop)
        m.run(['git','init','-b','main'],self.root)
        m.run(['git','config','user.email','test@example.invalid'],self.root)
        m.run(['git','config','user.name','Test'],self.root)
        (self.root/'.gitignore').write_text('wt/\n.lake/\nstate/runtime/\nlogs/\n')
        (self.root/'LogGas').mkdir()
        (self.root/'LogGas/A.lean').write_text('namespace LogGas.A\ntheorem x : True := by trivial\nend LogGas.A\n')
        (self.root/'.lake/packages').mkdir(parents=True)
        m.run(['git','add','.'],self.root)
        m.run(['git','commit','-m','base'],self.root)
        self.runner=m.Campaign()
        self.c=self.runner.c
        self.addCleanup(self.c.close)
        self.spec=dict(id='task-a',kind='construction',files=['LogGas/A.lean'],
            targets=['LogGas.A.x'],goal='Prove actual obligation',source='notes/source.tex label x',depends_on=[])

    def row(self):return self.c.execute('SELECT * FROM tasks WHERE id=?',('task-a',)).fetchone()

    def prepare(self):
        m.submit(self.c,self.spec)
        path=self.runner.checkout('candidate')
        base=m.git('rev-parse','HEAD',cwd=path)
        (path/'LogGas/A.lean').write_text('namespace LogGas.A\ntheorem x : True := by decide\nend LogGas.A\n')
        with self.c:
            self.c.execute("UPDATE tasks SET worktree=?,base=?,attempt=1,state='running' WHERE id=?",(str(path),base,'task-a'))
        return path

    def fake_lean(self,argv,cwd=m.ROOT,timeout=1800,check=True):
        if argv[0]=='lake':
            if argv[1]=='env':
                return (0,"'LogGas.A.x' depends on axioms: [propext, Classical.choice, Quot.sound]\n")
            return (0,'built')
        return self.real_run(argv,cwd,timeout,check)

    def test_scope_rejects_harness_and_challenge_changes(self):
        for f in ['Challenge.lean','PaperChallenge.lean','scripts/verify.py','../escape.lean','/tmp/a.lean']:
            with self.assertRaises(ValueError):m.valid_spec(dict(self.spec,files=[f]))

    def test_unknown_prerequisite_and_cycles_rejected(self):
        with self.assertRaises(ValueError):m.submit(self.c,dict(self.spec,depends_on=['absent']))
        m.submit(self.c,self.spec)
        m.submit(self.c,dict(self.spec,id='b',depends_on=['task-a']))
        self.c.execute("UPDATE tasks SET state='needs_replan'");self.c.commit()
        with self.assertRaisesRegex(ValueError,'Cyclic'):m.revise(self.c,dict(self.spec,depends_on=['b']))

    def test_six_worker_limit_dependency_gating_and_file_ownership(self):
        m.submit(self.c,self.spec)
        m.submit(self.c,dict(self.spec,id='waiting',files=['LogGas/Waiting.lean'],depends_on=['task-a']))
        m.submit(self.c,dict(self.spec,id='same-file'))
        for i in range(10):
            m.submit(self.c,dict(self.spec,id='other-'+str(i),files=[f'LogGas/Other{i}.lean']))
        ready=m.ready_tasks(self.c,0)
        self.assertEqual(len(ready),6)
        self.assertNotIn('waiting',[r['id'] for r in ready])
        self.assertNotIn('same-file',[r['id'] for r in ready])
        self.assertEqual(len(m.ready_tasks(self.c,5)),1)
        self.assertEqual(len(m.ready_tasks(self.c,6)),0)
        self.c.execute("UPDATE tasks SET state='awaiting_review' WHERE id='task-a'");self.c.commit()
        self.assertNotIn('same-file',[r['id'] for r in m.ready_tasks(self.c,0)])

    def test_candidate_requires_review_and_integrates_real_git(self):
        path=self.prepare()
        self.real_run=m.run
        with patch.object(m,'run',self.fake_lean):
            self.runner.candidate(self.row())
            row=self.row()
            self.assertEqual(row['state'],'awaiting_review')
            self.assertIn('trivial',(self.root/'LogGas/A.lean').read_text())
            with self.assertRaisesRegex(ValueError,'Stale'):self.runner.integrate(row)
            self.c.execute("UPDATE tasks SET approval=candidate,state='approved'");self.c.commit()
            self.runner.integrate(self.row())
        self.assertEqual(self.row()['state'],'done')
        self.assertIn('decide',(self.root/'LogGas/A.lean').read_text())

    def test_changed_candidate_cannot_reuse_approval(self):
        path=self.prepare()
        self.real_run=m.run
        with patch.object(m,'run',self.fake_lean):self.runner.candidate(self.row())
        self.c.execute('UPDATE tasks SET approval=candidate');self.c.commit()
        (path/'LogGas/A.lean').write_text('changed after review\n')
        with self.assertRaisesRegex(ValueError,'changed after review'):self.runner.integrate(self.row())

    def test_admissions_and_statement_changes_rejected(self):
        path=self.prepare()
        (path/'LogGas/A.lean').write_text('theorem x : False := by sorry\n')
        with self.assertRaisesRegex(ValueError,'admission'):self.runner.scope(path,self.row()['base'],self.spec)
        (path/'LogGas/A.lean').write_text('namespace LogGas.A\ntheorem x : False := by trivial\nend LogGas.A\n')
        with self.assertRaisesRegex(ValueError,'statement'):self.runner.scope(path,self.row()['base'],dict(self.spec,kind='proof'))

    def test_nonstandard_target_axiom_is_rejected(self):
        path=self.prepare()
        def fake(argv,*args,**kwargs):
            if argv[:2]==['lake','build']:return 0,'built'
            return 0,"'LogGas.A.x' depends on axioms: [sorryAx]"
        with patch.object(m,'run',fake),self.assertRaisesRegex(ValueError,'Forbidden'):
            self.runner.check(path,self.spec,'axiom-test')

    def test_actual_worker_process_fake_cli_and_candidate_handoff(self):
        m.submit(self.c,self.spec)
        (self.root/'prompts').mkdir()
        (self.root/'prompts/campaign-worker.md').write_text('Fake worker test')
        binpath=Path(self.tmp.name)/'bin';binpath.mkdir()
        cli=binpath/'claude'
        cli.write_text('#!/usr/bin/env python3\nimport json\nfrom pathlib import Path\n'+
            'p=Path("LogGas/A.lean")\np.write_text(p.read_text().replace("by trivial","by decide"))\n'+
            'print(json.dumps({"type":"system","model":"claude-sonnet-test","session_id":"fake-session"}))\n'+
            'print(json.dumps({"type":"result","subtype":"success","total_cost_usd":0,"usage":{"output_tokens":1}}))\n')
        cli.chmod(0o755)
        self.real_run=m.run
        with patch.dict(os.environ,PATH=str(binpath)+os.pathsep+os.environ['PATH']),patch.object(m,'run',self.fake_lean):
            self.runner.launch(self.row())
            j,(process,_,_)=next(iter(self.runner.active.items()))
            process.wait(timeout=10)
            self.runner.finish(j,process.returncode)
        self.assertEqual(self.row()['state'],'awaiting_review')
        self.assertEqual(self.c.execute('SELECT cost FROM jobs').fetchone()[0],0)

    def test_crash_recovery_retains_partial_checkout(self):
        path=self.prepare()
        self.c.execute("INSERT INTO jobs(task,role,started,pid,start_id) VALUES('task-a','worker',0,999999999,'gone')")
        self.c.commit()
        self.runner.recover()
        self.assertEqual(self.row()['state'],'needs_replan')
        self.assertIn('decide',(path/'LogGas/A.lean').read_text())

    def test_quota_preserves_usage_unknown_and_pauses_all_dispatch(self):
        self.c.execute("INSERT INTO jobs(role,started) VALUES('coordinator',0)");self.c.commit()
        j=self.c.execute('SELECT max(id) FROM jobs').fetchone()[0]
        (self.logs/f'{j}.jsonl').write_text(json.dumps(dict(type='result',is_error=True,result="You've hit your usage limit; resets 11pm (America/Chicago)"))+'\n')
        (self.logs/f'{j}.stderr').write_text('')
        self.runner.finish(j,1)
        self.assertEqual(m.get(self.c,'pause_reason'),'quota')
        self.assertGreater(float(m.get(self.c,'pause_until')),0)
        self.assertIsNone(self.c.execute('SELECT cost FROM jobs').fetchone()[0])


if __name__=='__main__':unittest.main()
