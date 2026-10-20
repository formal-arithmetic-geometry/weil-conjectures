"""Source queue ordering tests; no Lean invocation."""
import importlib.util
import pathlib
import tempfile
import unittest
from unittest.mock import patch

spec=importlib.util.spec_from_file_location('sheaf_work_queue',pathlib.Path(__file__).with_name('queue.py'))
queue=importlib.util.module_from_spec(spec)
spec.loader.exec_module(queue)


class RepairOrder(unittest.TestCase):
    def test_repairs_follow_file_order_then_disputed_and_distance(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=pathlib.Path(tmp)
            (root/'repairs.txt').write_text(
                '  # ignored comment\nSheaf.Small arbitrary data\n\n'
                'Sheaf.Medium dependency repair\nSheaf.Data undetermined witness\nSheaf.Small duplicate\n')
            modules={'Sheaf.Small':8,'Sheaf.Medium':1,'Sheaf.Near':0,
                     'Sheaf.Far':5,'Sheaf.Disputed':4,'Sheaf.Waiting':2,'Sheaf.Data':7}
            for module in modules:
                (root/module).write_text(('def data := Classical.choose exists_data\n' if module=='Sheaf.Data' else 'theorem t : True := by sorry\n')+
                                        ('-- STATEMENT-DISPUTED\n' if module=='Sheaf.Disputed' else ''))
            import sorry_route  # the live route (local/sorry-route.json) knows none of these modules
            with patch.object(queue,'WORK',root),patch.object(queue.li,'file_of',lambda m:root/m),\
                 patch.object(sorry_route,'load',lambda:None):
                items,held=queue.stage3({},modules,{'Sheaf.Waiting','Sheaf.Small'})
            # 2026-10-17: a waiting module is not an item, also a repair with sorry (Sheaf.Small); a repair without sorry is
            self.assertEqual([item[2] for item in items],
                             ['Sheaf.Medium','Sheaf.Data','Sheaf.Disputed','Sheaf.Near','Sheaf.Far'])
            self.assertEqual([item[4] for item in items],['repair','repair','disputed','proof','proof'])
            self.assertEqual(items[1][3],0)
            self.assertEqual(held,[(2,'Sheaf.Waiting',1),(8,'Sheaf.Small',1)])

    def test_below_route_items_follow_route_by_distance(self):
        # the human, 2026-10-18: a sorried module below a route sorry is an item, after the route modules, nearest route
        # sorry first; a sorried closure module neither on the route nor below it is not an item (bypassed)
        with tempfile.TemporaryDirectory() as tmp:
            root=pathlib.Path(tmp)
            modules={'Sheaf.OnRoute':3,'Sheaf.Bypassed':1,'Sheaf.Near':2,'Sheaf.Far':4,'Sheaf.NotImported':None}
            for module in modules:
                (root/module).write_text('theorem t : True := by sorry\n')
            dist={m:d for m,d in modules.items() if d is not None}
            import sorry_route
            fake={'t':0,'route':{'Sheaf.OnRoute'},'batches':{'batch3':{'Sheaf.OnRoute'}}}
            below={'batch3':{'Sheaf.Near':2,'Sheaf.NotImported':1,'Sheaf.OnRoute':0},'batch4':{'Sheaf.Far':3,'Sheaf.Near':5}}
            with patch.object(queue,'WORK',root),patch.object(queue.li,'file_of',lambda m:root/m),\
                 patch.object(sorry_route,'load',lambda:fake),patch.object(sorry_route,'changed_in_batches',lambda r,imps:set()):
                items,held=queue.stage3({},dist,{'Sheaf.Far'},below)
                self.assertEqual([item[2] for item in items],['Sheaf.OnRoute','Sheaf.NotImported','Sheaf.Near'])
                self.assertEqual([item[5] for item in items],[0,1,2])
                self.assertEqual(items[1][1],queue.FAR)
                self.assertEqual(held,[(4,'Sheaf.Far',1)])   # below a route sorry but a dependency is unstated: waiting
                self.assertEqual(queue.STATE['off_route'],['Sheaf.Bypassed'])
                items,held=queue.stage3({},dist,set(),{})   # no reach computed: the route only
                self.assertEqual([item[2] for item in items],['Sheaf.OnRoute'])


if __name__=='__main__': unittest.main()
