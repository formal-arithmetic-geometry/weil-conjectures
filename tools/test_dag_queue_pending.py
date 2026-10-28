"""Dependencies stated only by a delivery that passed review (not landed) release their dependents (the owner, 2026-10-28)."""
import pathlib
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import assumed  # noqa: E402
import dag_queue as dq  # noqa: E402
import own_decl  # noqa: E402
import units  # noqa: E402


class PendingDeps(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = pathlib.Path(temp.name)
        (self.root / 'coord').mkdir()
        for patcher in (
            patch.object(dq.li, 'ROOT', self.root),
            patch.object(dq.li, 'config', return_value={}),
            patch.object(dq, '_NOTES', {}),
            patch.object(dq, '_ASSUMED', {}),
            patch.object(assumed, 'nodes', return_value={}),
            patch.object(units, 'route', return_value=[]),
            patch.object(dq, 'closed_upstream', side_effect=lambda d: d.get('closed', False)),
            patch.object(own_decl, 'own', return_value=None),
        ):
            patcher.start()
            self.addCleanup(patcher.stop)

    @staticmethod
    def split(item, module=None, **fields):
        d = dict(id=item, status='split', reviewed={'result': 'pass'}, **fields)
        if module:
            d['lean'] = {'module': module, 'declaration': item}
        return d

    def graph(self):
        g = dq.Dag({
            'target': self.split('target', target=True, module='M.Target', proof_deps=['a', 'b', 'c', 'e', 'f']),
            'a': self.split('a'),                       # unstated; its stage-2 delivery passed review
            'b': self.split('b'),                       # unstated, nothing delivered
            'c': self.split('c', module='M.C', proof_deps=['a']),
            'd': self.split('d', module='M.D', proof_deps=['a', 'b']),
            'e': self.split('e', stmt_deps=['a']),      # its statement needs a
            'f': self.split('f', stmt_deps=['b']),      # its statement needs b
        })
        g.targets.append('target')
        g.dist = g.distances(cut=False); g.queue_dist = g.distances(cut=False)
        g.queue_dist1 = g.distances(cut=True)
        g.__dict__['_progress_open'] = set(g.live)
        g.__dict__['_priority_open'] = set()
        return g

    def test_without_pending_nothing_changes(self):
        g = self.graph()
        self.assertEqual({m for m, _ in g.waiting()}, {'M.Target', 'M.C', 'M.D'})
        self.assertEqual(g.early_modules, {})
        s2 = {r[2] for r in g.stage2()[0]}
        self.assertNotIn('e', s2)
        self.assertEqual(g.early, {})

    def test_pending_dependency_releases_dependents(self):
        g = self.graph()
        g.pending = {'a': {'group': 'NA', 'item': 'a', 'head': 'h' * 40, 'stage': '2', 'module': 'M.A'}}
        waiting = {m for m, _ in g.waiting()}
        self.assertNotIn('M.C', waiting)                 # waits only for a: released early
        self.assertEqual(g.early_modules.get('M.C'), {'a'})
        self.assertIn('M.D', waiting)                    # also waits for b: still waiting
        self.assertNotIn('M.D', g.early_modules)
        self.assertIn('M.Target', waiting)
        s2 = {r[2] for r in g.stage2()[0]}
        self.assertIn('e', s2)                           # its statement dependency passed review
        self.assertEqual(g.early['e'], ['a'])
        self.assertNotIn('f', s2)
        self.assertIn('a', s2)                           # the pending node itself stays a stage-2 item until it lands
        self.assertFalse(g.stated('a'))
        self.assertTrue(g.available('a'))


if __name__ == '__main__':
    unittest.main()
