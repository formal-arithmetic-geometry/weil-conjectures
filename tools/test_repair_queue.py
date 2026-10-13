"""Repair reservation/handoff tests; no Lean or global builds."""
import os
os.environ["SHEAF_LEAD"]="L-only"
import contextlib, json, pathlib, subprocess, sys, tempfile, unittest
from unittest.mock import patch
sys.path.insert(0,str(pathlib.Path(__file__).parent))
import repair_queue as rq, claim, batch_land as bl, stage3_delivery as s3

class Queue(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=pathlib.Path(self.tmp.name)
        for name,value in ((rq,'ROOT'),(rq,'JOBS'),(rq,'NOTES'),(claim,'WORK'),(claim,'C'),(claim,'RETURNS'),(bl,'ROOT'),(bl,'PASSED'),(bl.md,'ROOT'),(s3,'ROOT')):
            path=self.root
            if value=='JOBS':path/= 'local/batch/repair'
            elif value=='NOTES':path/='coord/repair-notes'
            elif value=='WORK':path/='coord'
            elif value=='C':path/='coord/claims'
            elif value=='RETURNS':path/='coord/returns'
            elif value=='PASSED':path/='local/batch/passed'
            path.mkdir(parents=True,exist_ok=True)
            self.addCleanup(patch.object(name,value,path).stop) if False else None
            p=patch.object(name,value,path);p.start();self.addCleanup(p.stop)
        subprocess.run(['git','init','-q'],cwd=self.root,check=True)
        subprocess.run(['git','config','user.name','test'],cwd=self.root,check=True)
        subprocess.run(['git','config','user.email','test@example.invalid'],cwd=self.root,check=True)
        p=self.root/'lean/Sheaf/A.lean';p.parent.mkdir(parents=True);p.write_text('old')
        self.commit();self.before=rq.git('rev-parse','HEAD');p.write_text('broken');self.commit()
        rq.git('branch','sheaf-dag')
        self.e=dict(group='G',item='Sheaf.A',head=rq.git('rev-parse','HEAD'),commit=rq.git('rev-parse','HEAD'),landing='L',modules=['Sheaf.A'])
    def commit(self):
        subprocess.run(['git','add','.'],cwd=self.root,check=True)
        subprocess.run(['git','commit','-qm','test'],cwd=self.root,check=True)
    def stage(self):return rq.stage(self.e,self.e['head'],[dict(failure='Sheaf.B',case='breaker')],'compiler error')
    def reserve(self,j):rq.write(rq.claim_path(j['item']),dict(who=j['group'],repair=j['id'],t=__import__('time').time()))
    def test_outbox_activation_idempotent(self):
        j=self.stage();self.assertFalse(rq.active(j));self.reserve(j)
        self.assertTrue(rq.active(j));self.assertEqual(self.stage()['id'],j['id'])
        self.assertIn('broken',j['diff']);self.assertEqual(rq.counts()['repair_still_running'],1)
    def test_scoped_exception_requires_reservation(self):
        j=self.stage();self.assertIsNone(s3.repair_job(j['group'],j['item']))
        self.reserve(j);self.assertEqual(s3.repair_job(j['group'],j['item'])['id'],j['id'])
    def test_failed_release_carries_full_note_and_return(self):
        j=self.stage();self.reserve(j)
        def fake_run(args,**kw):
            if args[0]==sys.executable:
                with patch.object(sys,'argv',['claim.py',*args[2:]]),patch.object(claim,'sorries',lambda _:1):
                    code=claim.main()
                return type('P',(),{'returncode':code})()
            return type('P',(),{'returncode':0})()
        with patch.object(bl.md,'merge_lock',lambda:contextlib.nullcontext()),patch.object(rq.subprocess,'run',fake_run),patch.object(bl,'refresh_recovery_queue'):
            rq.result(j['id'],'failed','attempt 1 tried proof; attempt 2 timeout',attempts=2)
        self.assertFalse(rq.claim_path(j['item']).exists())
        self.assertEqual(claim.repair_note(j['item'])['state'],'released')
        self.assertEqual(rq.counts()['released_to_queue'],1)
        with patch.object(claim,'node_finished',lambda _:True),patch.object(claim,'stage2_parked',lambda _:False):
            self.assertTrue(claim.take('ANY',j['item']))
        text=(claim.RETURNS/'ANY.md').read_text()
        self.assertIn('compiler error',text);self.assertIn('attempt 2 timeout',text)
    def test_retry_budget_inherited_on_red_repair(self):
        j=self.stage();j.update(attempts=2,note='two attempts');rq.write(rq.JOBS/(j['id']+'.json'),j)
        self.e.update(group=j['group'],landing='L2')
        new=self.stage();self.assertEqual(new['attempts'],2);self.assertEqual(new['prior_notes'],'two attempts')
    def test_priority(self):
        # Priority is attached to the exact accepted head, not arbitrary XR names.
        j=self.stage();self.reserve(j)
        rq.git('branch','deliver/'+j['group']+'/'+j['item'],j['head'])
        def passed(o):bl.write_json(bl.marker(o.group,o.item),dict(head=o.head))
        with patch.object(bl,'cmd_pass',passed):rq.result(j['id'],'delivered','independent reader checked',head=j['head'],attempts=1)
        self.assertTrue(rq.read(bl.marker(j['group'],j['item']))['repair_priority'])
        self.assertEqual(rq.read(rq.JOBS/(j['id']+'.json'))['state'],'delivered')

if __name__=='__main__':unittest.main()
