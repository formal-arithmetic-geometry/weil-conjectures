import pathlib, tempfile, unittest
from unittest.mock import patch
import os
os.environ["SHEAF_LEAD"] = "L-only"
import batch_land as bl
import batch_recovery as recovery
import import_cycles as ic

class MissingSources(unittest.TestCase):
    def test_delivery_packages_and_base(self):
        with tempfile.TemporaryDirectory() as d:
            root=pathlib.Path(d); (root/'Mathlib').mkdir(); (root/'Mathlib/Real.lean').touch()
            (root/'Sheaf').mkdir(); (root/'Sheaf/Ghost.olean').touch()
            texts={'Sheaf.A': 'module\npublic import Mathlib.Real\nimport Sheaf.Base\nimport Sheaf.B\n', 'Sheaf.B':'module\n'}
            ic.refuse_missing(texts, {'Sheaf.Base'}, [root])
            texts['Sheaf.A'] += 'public import Sheaf.Ghost\nimport Mathlib.Missing\n'
            with self.assertRaisesRegex(RuntimeError, 'Mathlib.Missing.*Sheaf.Ghost'):
                ic.refuse_missing(texts, {'Sheaf.Base'}, [root])
    def test_multiple_imports_on_one_line(self):
        with self.assertRaisesRegex(RuntimeError, 'Missing'):
            ic.refuse_missing({'A':'public import Present Missing'}, {'Present'}, [])

    def test_comments_are_ignored(self):
        ic.refuse_missing({'A': '/- import Ghost\n/- public import Missing -/ -/\n-- import Fake\n'}, set(), [])

class RecoveryCost(unittest.TestCase):
    def test_delta_once_for_many_failures(self):
        entries=[dict(modules=['Shared'])]; calls=[]
        graph={f'F{i}':{'Shared'} for i in range(215)}
        result=recovery.select(entries,list(graph),graph,lambda e,m: calls.append(m) or ['value'])
        self.assertEqual(calls,['Shared']); self.assertEqual(len(result),215)
    def test_stop_checkpoint(self):
        with patch.object(bl,'STOP_REQUESTED',lambda:True):
            with self.assertRaises(bl.Wait):
                recovery.select([],['F'],{},lambda *a:[],checkpoint=bl.stop_checkpoint)

class FreshResult(unittest.TestCase):
    def test_green_closes_without_preparing_next_batch(self):
        with tempfile.TemporaryDirectory() as d:
            root=pathlib.Path(d); opened=root/'open.json'; done=root/'done'; done.mkdir()
            b=dict(id='B',time=bl.ld.now(),round=0,handled=[],entries=[dict(state='landed',landing='L',group='G',item='A',head='abcdef')])
            bl.write_json(opened,b); bl.write_json(done/'L.json',dict(result='verified',commit='green'))
            pre=type('Pre',(),{'pump':lambda *a: self.fail('must close first')})()
            with patch.object(bl,'OPEN',opened),patch.object(bl,'CLOSED',root/'closed'),patch.object(bl.ld,'DONE',done),patch.object(bl,'clear_alert'):
                self.assertEqual(bl.step({'_pre':pre},lambda *a:None),'verified')
                self.assertFalse(opened.exists())
    def test_new_result_during_attribution_discards_old_red(self):
        with tempfile.TemporaryDirectory() as d:
            root=pathlib.Path(d); opened=root/'open.json'; builds=root/'builds'; builds.mkdir()
            b=dict(id='B',time=bl.ld.now(),round=0,handled=[],entries=[dict(state='landed',landing='L',group='G',item='A',head='abcdef')])
            bl.write_json(opened,b); last=dict(result='red',time='red',included=['L'],failing=['A']); bl.write_json(builds/'last.json',last)
            def triage(*a):
                bl.write_json(builds/'last.json',dict(result='green',time='green'))
                return dict(decisions=[],open=[],unattributed=['A'])
            with patch.object(bl,'OPEN',opened),patch.object(bl.ld,'B',builds),patch.object(bl.ld,'DONE',root/'done'),patch.object(bl,'library_imports',lambda:{}),patch.object(bl,'triage',triage),patch.object(bl,'execute') as execute,patch.object(bl,'closure_fallback') as fallback:
                self.assertEqual(bl.step({},lambda *a:None),'waiting')
                execute.assert_not_called(); fallback.assert_not_called()
                self.assertEqual(bl.read_json(opened),b)

if __name__=='__main__': unittest.main()
