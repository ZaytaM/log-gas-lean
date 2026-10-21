"""Fail-closed coverage, prerequisite gating, and exact-freeze review tests."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from contracts import Contracts
from verify import fresh_paths_valid, review_valid


class ContractTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root/'verification').mkdir()
        (self.root/'LogGas').mkdir()
        (self.root/'LogGas/A.lean').write_text('namespace LogGas.A\ntheorem first : True := by trivial\nend LogGas.A\n')
        self.data = dict(roots=['final'], nodes=[
            dict(id='first', declarations=['LogGas.A.first'], depends_on=[]),
            dict(id='final', declarations=['LogGas.Main.theorem11'], depends_on=['first'])])

    def contract(self):
        (self.root/'verification/contracts.json').write_text(json.dumps(self.data))
        return Contracts(self.root)

    def test_missing_final_is_not_queue_completion(self):
        self.assertEqual(self.contract().missing(), ['LogGas.Main.theorem11'])

    def test_prerequisites_require_verified_closure(self):
        c = self.contract()
        self.assertEqual(c.waiting('LogGas.Main.theorem11', set()), ['LogGas.A.first'])
        self.assertEqual(c.waiting('LogGas.Main.theorem11', {'LogGas.A.first'}), [])

    def test_cycles_and_unknown_dependencies_rejected(self):
        self.data['nodes'][0]['depends_on'] = ['final']
        with self.assertRaisesRegex(ValueError, 'Cyclic'):
            self.contract()
        self.data['nodes'][0]['depends_on'] = ['missing']
        with self.assertRaisesRegex(ValueError, 'Unknown prerequisite'):
            self.contract()

    def test_stale_and_failed_review_receipts_rejected(self):
        p = self.root/'review.json'
        data = dict(role='mathematical-fidelity', reviewer='independent-reviewer', verdict='passed',
                    reviewed_files={'source.lean':'hash1'})
        p.write_text(json.dumps(data))
        self.assertTrue(review_valid(p, {'source.lean':'hash1'}, 'mathematical-fidelity'))
        self.assertFalse(review_valid(p, {'source.lean':'hash2'}, 'mathematical-fidelity'))
        data['verdict'] = 'findings'; p.write_text(json.dumps(data))
        self.assertFalse(review_valid(p, {'source.lean':'hash1'}, 'mathematical-fidelity'))

    def test_fresh_paths_reject_old_relative_and_symlinked_artifacts(self):
        (self.root/'.lake/packages').mkdir(parents=True)
        (self.root/'verification/dependency-lock.json').write_text(json.dumps({'packages':[{'name':'mathlib'}]}))
        external = self.root/'external-mathlib'
        external.mkdir()
        (self.root/'.lake/packages/mathlib').symlink_to(external, target_is_directory=True)
        self.assertTrue(fresh_paths_valid('.lake/fresh/lib/lean:'+str(external/'.lake/build/lib/lean')+'\n', self.root, '.lake/fresh'))
        self.assertFalse(fresh_paths_valid('.lake/build/lib/lean\n', self.root, '.lake/fresh'))
        self.assertTrue(fresh_paths_valid('/opt/pinned-lean/lib/lean', self.root, '.lake/fresh', '/opt/pinned-lean'))
        self.assertFalse(fresh_paths_valid('/opt/other-lean/lib/lean', self.root, '.lake/fresh', '/opt/pinned-lean'))
        (self.root/'.lake/fresh').symlink_to(self.root/'.lake/build', target_is_directory=True)
        self.assertFalse(fresh_paths_valid('.lake/fresh/lib/lean', self.root, '.lake/fresh'))
