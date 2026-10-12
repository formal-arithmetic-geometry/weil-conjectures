"""Adaptation policy and launcher counterfactuals, with compiler fakes only."""
import copy, importlib.util, pathlib, sys, tempfile, unittest
from unittest.mock import patch
sys.path.insert(0, str(pathlib.Path(__file__).parent))
import stage3_delivery as s3
import stage2_delivery as s2
import review_class as rc

class Adaptation(unittest.TestCase):
    def data(self, old=None, new=None):
        old = old or 'module\npublic theorem use : True := by exact upstream\n'
        new = new or 'module\npublic theorem use : True := by simpa using upstream\n'
        itemold='module\npublic def upstream : True := True.intro\n'
        itemnew='module\npublic def upstream : True := by trivial\n'
        mods=[{'role':'item','module':'Sheaf.A','file':'lean/Sheaf/A.lean','old':itemold,'text':itemnew,
               'diff':s3.diff_module(itemold,itemnew)},
              {'role':'adapted','module':'Sheaf.B','file':'lean/Sheaf/B.lean','old':old,'text':new,
               'diff':s3.diff_module(old,new)}]
        return dict(modules=mods, interface={'Sheaf.A':['upstream']}, users={},nodes={},base='HEAD',
                    changes={'coord/changes/a.md':'## Reason\nfix\n## Old\nold\n## New\nnew\n## Users\nSheaf.B other\n## Status\nopen\n'},
                    report='## Forced adaptations\nSheaf.B: original error; forced lines explained',notes=[],fails=[])
    def check(self,D,holder=None):
        with patch.object(s3,'claim_holder',return_value=holder), patch.object(s3,'downstream_users',return_value={}):
            s3.check_changes(D,lambda L,x:D['fails'].append((L,x)),'mine',{})
        return D['fails']
    def test_unclaimed_and_other_holder_allowed(self):
        for holder in [None,'other']:
            self.assertEqual(self.check(self.data(),holder),[])
    def test_signature_remove_public_add_visibility_rejected(self):
        for new in ['module\npublic theorem use : False := by sorry\n','module\n',
                    'module\nprivate theorem use : True := by trivial\n',
                    'module\npublic theorem use : True := by trivial\npublic def extra : Nat := 0\n']:
            self.assertTrue(self.check(self.data(new=new)))
    def test_private_helper_allowed(self):
        new='module\nprivate theorem help : True := by trivial\npublic theorem use : True := help\n'
        self.assertEqual(self.check(self.data(new=new)),[])
    def test_evidence_and_own_interface_required(self):
        D=self.data();D['report']='';self.assertTrue(self.check(D))
        D=self.data();D['modules'][0]['diff']['interface']=[];self.assertTrue(self.check(D))
        D=self.data();self.assertTrue(self.check(D,'unnamed-holder'))
    def test_never_auto_even_claimed(self):
        D=self.data()
        with patch.object(rc,'git',return_value='head'),patch.object(rc,'ROOT',pathlib.Path('/nonexistent')):
            self.assertEqual(rc.classify('mine','Sheaf.A',D)[0],'CODEX')

if __name__=='__main__':unittest.main()
