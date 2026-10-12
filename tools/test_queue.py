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
                'Sheaf.Medium dependency repair\nSheaf.Small duplicate\n')
            modules={'Sheaf.Small':8,'Sheaf.Medium':1,'Sheaf.Near':0,
                     'Sheaf.Far':5,'Sheaf.Disputed':4,'Sheaf.Waiting':2}
            for module in modules:
                (root/module).write_text('theorem t : True := by sorry\n'+
                                        ('-- STATEMENT-DISPUTED\n' if module=='Sheaf.Disputed' else ''))
            with patch.object(queue,'WORK',root),patch.object(queue.li,'file_of',lambda m:root/m):
                items,held=queue.stage3({},modules,{'Sheaf.Waiting','Sheaf.Small'})
            self.assertEqual([item[2] for item in items],
                             ['Sheaf.Small','Sheaf.Medium','Sheaf.Disputed','Sheaf.Near','Sheaf.Far'])
            self.assertEqual([item[4] for item in items],['repair','repair','disputed','proof','proof'])
            self.assertEqual(held,[(2,'Sheaf.Waiting',1)])


if __name__=='__main__': unittest.main()
