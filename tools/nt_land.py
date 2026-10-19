#!/usr/bin/env python3
import pathlib,sys,subprocess,os,json
P=pathlib.Path(__file__).resolve().parent.parent
LIVE=P.parent/'weil-conjectures-sheaf'
sys.path.insert(0,str(P/'tools'))
from mergelock import merge_lock
g,item,head,verdict,note,fixes=sys.argv[1:7]
drop_nodes=sys.argv[7] if len(sys.argv)>7 else ''
assert __import__('re').fullmatch(r'[A-Z][A-Z0-9]{1,3}', g) and verdict in ('PASS','FIX','RETURN')
from retire_stage1 import retire_completed
br='deliver/'+g+'/'+item
r=subprocess.run(['git','rev-parse','--verify',br],cwd=P,capture_output=True,text=True)
if r.returncode and retire_completed(g,item,head):
 print('SUPERSEDED',item,'delivery already archived');sys.exit(0)
if r.returncode or r.stdout.strip()!=head:
 print('HEAD MOVED/SUPERSEDED',item); sys.exit(1)
# A live reviewed completion supersedes this packet, including an old RETURN.
# Retire its branch, return and obsolete claim together instead of asking a
# worker to change an already accepted interface just to pass preflight.
if retire_completed(g,item,head):
 print('SUPERSEDED',item,'completed stage-1 delivery archived; stale handoff retired');sys.exit(0)
if verdict=='RETURN':
 args=['return',g,item,note]
else:
 args=[g,item,'--stage','1','--reviewer',os.environ.get('NT_REVIEWER') or 'NT-Codex-'+g+'-'+head[:9],'--head',head,'--spot-checked',note,'--verdict',verdict]
 if verdict=='FIX': args += ['--apply-fixes',fixes]
 if drop_nodes: args += ['--drop-nodes',drop_nodes]
env=dict(os.environ,SHEAF_LEAD='L-only',SHEAF_DAG='dag/nodes')
mr=subprocess.run([sys.executable,'tools/merge_delivery.py',*args],cwd=P,env=env,text=True,capture_output=True)
print(mr.stdout,end=''); print(mr.stderr,end='',file=sys.stderr)
if mr.returncode and 'no longer stage-1-open' in mr.stdout and retire_completed(g,item,head):
 print('SUPERSEDED',item,'completion arrived during landing; stale handoff retired');sys.exit(0)
if mr.returncode or verdict=='RETURN': sys.exit(mr.returncode)
if LIVE.resolve()==P.resolve():   # 2026-10-19: one repository; the landing above committed everything here
 print('PROMOTED',item,'files 0 collisions 0 live',subprocess.check_output(['git','rev-parse','--short','HEAD'],cwd=P,text=True).strip());sys.exit(0)
# 2026-10-15: use the human's full commit email for the shared promotion as well.
# The side merge is reviewed and recorded. Promote exactly its DAG files to live under the live lock.
import re
m=re.search(r'MERGED\s+\S+\s+([0-9a-f]+)', mr.stdout)
commit=m.group(1) if m else subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
parent=subprocess.check_output(['git','rev-parse',commit+'^'],cwd=P,text=True).strip()
files=subprocess.check_output(['git','diff','--name-only',parent,commit,'--','dag/nodes'],cwd=P,text=True).splitlines()
collisions=[]; copied=[]
with merge_lock(LIVE/'coord/.merge.lock'):
 for rel in files:
  src=P/rel; dst=LIVE/rel
  if not src.exists(): continue
  # Compare with the pre-delivery staging version, not the delivered result.
  prior=subprocess.run(['git','show',parent+':'+rel],cwd=P,text=True,capture_output=True)
  before=json.loads(prior.stdout) if prior.returncode==0 else None
  if before and before.get('id','').startswith('nt-target-'): before.pop('target',None)
  current=json.loads(dst.read_text()) if dst.exists() else None
  after=json.loads(subprocess.check_output(['git','show',commit+':'+rel],cwd=P,text=True))
  if current != before and current != after:
   collisions.append(rel); continue
  dst.parent.mkdir(parents=True,exist_ok=True)
  d=after
  if d.get('id','').startswith('nt-target-') or d.get('target') is True: d.pop('target',None)
  dst.write_text(json.dumps(d,indent=1,ensure_ascii=False)+'\n'); copied.append(rel)
 if collisions:
  hp=P/'coord/HUMAN.md'; hp.write_text(hp.read_text()+'\n## Shared landing collisions\n' + ''.join('- '+x+' (live kept)\n' for x in collisions))
 paths=copied
 if paths and subprocess.check_output(['git','diff','--name-only','--',*paths],cwd=LIVE,text=True).strip():
  subprocess.run(['git','add','-A','--',*paths],cwd=LIVE,check=True)
  msg=f'Stage-1 shared landing {item} ({g})\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>'
  subprocess.run(['git','-c','user.name=Bin Wu','-c','user.email=844524296@qq.com','commit','--author=Bin Wu <844524296@qq.com>','-m',msg],cwd=LIVE,check=True)
 print('PROMOTED',item,'files',len(copied),'collisions',len(collisions),'live',subprocess.check_output(['git','rev-parse','--short','HEAD'],cwd=LIVE,text=True).strip())
