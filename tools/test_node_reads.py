"""Immutable DAG cache invalidation in a temporary git repository."""
import pathlib,sys,tempfile,unittest
sys.path.insert(0,str(pathlib.Path(__file__).parent))
import stage2_delivery as s2

class Nodes(unittest.TestCase):
    def test_immutable_tree_cache_changes_and_blob_ids(self):
        with tempfile.TemporaryDirectory() as tmp:
            import subprocess,json
            root=pathlib.Path(tmp)
            def git(*args):return subprocess.run(['git',*args],cwd=root,capture_output=True,text=True,check=True).stdout.strip()
            git('init','-q');git('config','user.name','test');git('config','user.email','test@example.invalid')
            p=root/'dag/nodes/x/a.json';p.parent.mkdir(parents=True);p.write_text('{"id":"a"}')
            git('add','.');git('commit','-qm','base');G=s2.Git(root)
            a=s2.nodes_at(G,'HEAD');self.assertEqual(a['a']['id'],'a')
            (root/'ledger').write_text('note');git('add','.');git('commit','-qm','ledger')
            self.assertIs(a,s2.nodes_at(G,'HEAD'))
            p.write_text('{"id":"a","new":true}');git('add','.');git('commit','-qm','new tree')
            self.assertTrue(s2.nodes_at(G,'HEAD')['a']['new']);self.assertNotIn('new',a['a'])

if __name__=='__main__':unittest.main()
