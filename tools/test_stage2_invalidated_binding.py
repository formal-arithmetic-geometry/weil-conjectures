"""An interface repair must not re-publish only the withdrawn declarations."""
import copy
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import stage2_delivery as s2

ITEM = 'lem-maint-invalidated-interface'
NODE = 'dag/nodes/sec-smooth-purity/' + ITEM + '.json'
NOTE = 'coord/repair-notes/' + ITEM + '.json'
MODULE = 'Sheaf.Paper.MaintInvalidatedInterface'


class InvalidatedBinding(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='stage2-invalidated-')
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        self.git('init', '-q')
        self.git('config', 'user.name', 'Bin Wu')
        self.git('config', 'user.email', '844524296@qq.com')
        self.node = {'id': ITEM, 'kind': 'statement', 'status': 'split',
                     'statement': 'Fixture.', 'stmt_deps': [], 'proof_deps': [], 'lean': None}
        self.old = {'module': MODULE, 'declaration': 'Fixture.old',
                    'declarations': ['Fixture.old', 'Fixture.helper']}
        self.note = {'state': 'released', 'stage': '2', 'invalidated_lean': self.old,
                     'reason': 'Canonical transport preserving completion units is missing.'}

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, text=True).strip()

    def write(self, rel, data):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(data)

    def delivery(self, declaration='Fixture.old', declarations=None, active=True):
        note = dict(self.note, state='released' if active else 'resolved')
        self.write(NODE, json.dumps(self.node))
        self.write(NOTE, json.dumps(note))
        self.write('lean/' + MODULE.replace('.', '/') + '.lean',
                   'module\nnamespace Fixture\n'
                   '/-- Source: fixture. -/\ntheorem old : True := by trivial\n'
                   '/-- Source: fixture. -/\ntheorem helper : True := by trivial\n'
                   '/-- Source: fixture. -/\ntheorem normalized : True := by trivial\n'
                   'end Fixture\n')
        self.git('add', '.')
        self.git('commit', '-qm', 'withdraw unusable interface')
        self.git('branch', 'sheaf-dag')
        node = copy.deepcopy(self.node)
        rec = {'module': MODULE, 'declaration': declaration,
               'statement': 'theorem ' + declaration.rsplit('.', 1)[-1] + ' : True',
               'existing': True, 'branch': 'sheaf-dag', 'by': 'Q23', 'date': '2026-10-16'}
        if declarations is not None:
            rec['declarations'] = declarations
        node['lean'] = rec
        self.write(NODE, json.dumps(node))
        self.write('coord/reports/Q23/' + ITEM + '.md',
                   '## Worker report\nRegression fixture.\n\n'
                   '## Second reading by Q23\nChecked the fixture.\n')
        self.git('add', '.')
        self.git('commit', '-qm', 'candidate interface')
        return s2.read_delivery(s2.Git(self.root), 'HEAD', 'sheaf-dag', 'Q23', ITEM)

    def invalidated_failures(self, delivery):
        return [text for letter, text in delivery['fails'] if 'maintenance-invalidated' in text]

    def test_existing_alias_cannot_restore_withdrawn_binding(self):
        failures = self.invalidated_failures(self.delivery())
        self.assertEqual(len(failures), 1)
        self.assertIn('completion units', failures[0])

    def test_full_old_declaration_list_is_also_rejected(self):
        self.assertTrue(self.invalidated_failures(self.delivery(declarations=self.old['declarations'])))

    def test_new_published_transport_can_be_recorded(self):
        self.assertFalse(self.invalidated_failures(self.delivery(declarations=['Fixture.old', 'Fixture.normalized'])))

    def test_different_existing_interface_is_allowed(self):
        self.assertFalse(self.invalidated_failures(self.delivery(declaration='Fixture.normalized')))

    def test_resolved_repair_does_not_restrict_reuse(self):
        self.assertFalse(self.invalidated_failures(self.delivery(active=False)))

    def test_checks_committed_base_not_mutable_repair_note(self):
        self.delivery()
        self.write(NOTE, json.dumps(dict(self.note, state='resolved')))
        d = s2.read_delivery(s2.Git(self.root), 'HEAD', 'sheaf-dag', 'Q23', ITEM)
        self.assertTrue(self.invalidated_failures(d))


if __name__ == '__main__':
    unittest.main()
