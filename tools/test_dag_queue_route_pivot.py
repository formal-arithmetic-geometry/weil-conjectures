"""The queue obeys human route exclusions without hiding the actual DAG."""
import collections
import json
import pathlib
import tempfile
import unittest
from unittest.mock import patch

import assumed
import dag_queue as dq
import nt_stage2
import units


class RoutePivotQueue(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = pathlib.Path(temp.name)
        (self.root / 'coord').mkdir()
        self.drop = self.root / 'coord/route-pivot-dropped.txt'
        self.drop.write_text('# human route decision\ndropped\n')
        for patcher in (
            patch.object(dq.li, 'ROOT', self.root),
            patch.object(dq.li, 'config', return_value={}),
            patch.object(dq, '_NOTES', {}),
            patch.object(dq, '_ASSUMED', {}),
            patch.object(assumed, 'nodes', return_value={}),
            patch.object(units, 'route', return_value=[]),
            patch.object(dq, 'closed_upstream', side_effect=lambda d: d.get('closed', False)),
        ):
            patcher.start()
            self.addCleanup(patcher.stop)

    def node(self, item, **fields):
        return dict(id=item, status='unsplit', **fields)

    def split(self, item, **fields):
        return dict(id=item, status='split', reviewed={'result': 'pass'}, **fields)

    def graph(self, shared=False):
        return dq.Dag({
            'target': self.split('target', target=True,
                                 proof_deps=['dropped'] + (['child'] if shared else [])),
            'dropped': self.split('dropped', proof_deps=['child']),
            'child': self.node('child'),
        })

    def test_dropped_route_is_not_work_but_remains_visible_to_validation(self):
        g = self.graph()
        self.assertEqual(set(g.dist), {'target', 'dropped', 'child'})
        self.assertEqual(g.deps('target', 'all'), ['dropped'])
        self.assertEqual(set(g.queue_dist), {'target'})
        self.assertEqual(g.stage1(), [])
        self.assertFalse(g.needs_statement('dropped'))
        self.assertFalse(g.stated('dropped'))
        self.assertEqual({r[2] for r in g.stage2()[0]}, {'target'})

    def test_shared_dependency_keeps_its_active_route(self):
        g = self.graph(shared=True)
        self.assertEqual({i for _, i in g.stage1()}, {'child'})
        self.assertEqual(g.queue_dist['child'], 1)

    def test_statement_handoff_does_not_reintroduce_dropped_subtree(self):
        g = dq.Dag({
            'target': self.split('target', target=True, closed=True, stmt_deps=['dropped']),
            'dropped': self.split('dropped', stmt_deps=['child']),
            'child': self.node('child'),
        })
        self.assertEqual(g.stage1(), [])
        self.assertEqual(g.stmt_needed(['dropped']), set())

    def test_preopen_and_released_note_cannot_revive_a_dropped_route(self):
        (self.root / 'coord/preopen.txt').write_text('dropped\n')
        notes = self.root / 'coord/repair-notes'
        notes.mkdir()
        (notes / 'dropped.json').write_text(json.dumps({
            'state': 'released', 'stage': '1', 'keep_plan': True,
        }))
        g = self.graph()
        self.assertTrue(dq.stage1_repair_owed('dropped'))
        self.assertEqual(g.stage1(), [])

    def test_explicit_readmission_reopens_the_work(self):
        self.assertEqual(self.graph().stage1(), [])
        self.drop.write_text('# re-admitted by human\n')
        g = self.graph()
        self.assertEqual({i for _, i in g.stage1()}, {'child'})
        self.assertIn('dropped', g.queue_dist)

    def test_missing_drop_file_keeps_existing_queue_behavior(self):
        self.drop.unlink()
        self.assertEqual({i for _, i in self.graph().stage1()}, {'child'})

    def test_dropped_dependency_is_still_an_unstated_proof_prerequisite(self):
        g = dq.Dag({
            'target': self.split('target', target=True, lean={'module': 'Sheaf.Target'},
                                 proof_deps=['dropped']),
            'dropped': self.split('dropped'),
        })
        self.assertEqual(g.waiting(), [('Sheaf.Target', 'dropped')])

    def test_runtime_stage2_wait_cannot_reintroduce_excluded_node(self):
        g = self.graph()
        self.assertEqual(nt_stage2.frontier(g, ['dropped']), [])
        with patch.object(nt_stage2, 'waits', return_value={'consumer': ['dropped']}):
            self.assertEqual(nt_stage2.eligible(g, [], collections.Counter())[0], [])


if __name__ == '__main__':
    unittest.main()
