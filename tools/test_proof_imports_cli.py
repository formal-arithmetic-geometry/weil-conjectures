"""The old deployed cycle's CLI contract, with source-only temporary files."""
import contextlib,io,json,pathlib,sys,tempfile,unittest
from unittest.mock import patch
sys.path.insert(0,str(pathlib.Path(__file__).parent))
import add_proof_imports as api
class OldCycle(unittest.TestCase):
 def test_check_then_json_write_and_open_batch_refusal(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=pathlib.Path(tmp);(root/'lean/Sheaf').mkdir(parents=True)
   a=root/'lean/Sheaf/A.lean';a.write_text('module\npublic theorem a : True := by sorry\n')
   (root/'lean/Sheaf/B.lean').write_text('module\n')
   def plan():return {'#counts':{},'added':[('Sheaf.A','Sheaf.B',[],'')]},{'Sheaf.A':{'Sheaf.B'},'Sheaf.B':set()}
   jf=root/'cycle.json'
   with patch.object(api.li,'ROOT',root),patch.object(api.li,'file_of',side_effect=lambda m:root/'lean'/pathlib.Path(*m.split('.')).with_suffix('.lean')),patch.object(api,'plan',side_effect=plan),contextlib.redirect_stdout(io.StringIO()):
    with patch.object(sys,'argv',['add_proof_imports.py','--check']):self.assertEqual(api.main(),1)
    self.assertNotIn('import Sheaf.B',a.read_text())
    with patch.object(sys,'argv',['add_proof_imports.py','--json',str(jf)]):self.assertEqual(api.main(),0)
    self.assertIn('import Sheaf.B',a.read_text());self.assertEqual(json.loads(jf.read_text())['added'][0][:2],['Sheaf.A','Sheaf.B'])
    (root/'local/batch').mkdir(parents=True);(root/'local/batch/open.json').write_text('{}')
    before=a.read_bytes()
    with patch.object(sys,'argv',['add_proof_imports.py','--json',str(jf)]):self.assertEqual(api.main(),4)
    self.assertEqual(a.read_bytes(),before)
if __name__=='__main__':unittest.main()
