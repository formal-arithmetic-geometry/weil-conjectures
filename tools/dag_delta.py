"""Source-only DAG checks relative to a committed base, without checking out Lean."""
import pathlib,subprocess,sys,tempfile,tarfile,io,re
ROOT=pathlib.Path(__file__).resolve().parent.parent
# SHEAF_DAG_DELTA_CACHE: the server preflight shares one cache across its slots (keyed by tree hashes, 2026-10-17)
CACHE=pathlib.Path(__import__('os').environ.get('SHEAF_DAG_DELTA_CACHE') or ROOT/'local/dag-delta-cache')
def _key(ref,paths):
 r=subprocess.run(['git','rev-parse',*[ref+':'+p for p in paths]],cwd=ROOT,capture_output=True,text=True)
 # pfinc 2026-10-17: 'v2' = the baseline reads the base tree's own dag/nodes (see _check_ref); older entries were computed
 # on whatever DAG SHEAF_DAG named in the calling slot
 return None if r.returncode else __import__('hashlib').sha1(('v2\n'+r.stdout).encode()).hexdigest()
def check_ref(ref):
 # 2026-10-16 20:30 (launcher): check_dag.py --cycles takes ~20 s and merge_delivery ran it on HEAD under
 # coord/.merge.lock for every landing (~50-65 s lock hold per landing, sync starved). The result depends only on the
 # trees archived below, so it is cached by their hashes; returns/queue commits do not change the key.
 paths=['dag','tools','coord/sheaf.env']
 if subprocess.run(['git','cat-file','-e',ref+':coord/newtargets-stage1-completions.json'],cwd=ROOT,capture_output=True).returncode==0:
  paths.append('coord/newtargets-stage1-completions.json')
 key=_key(ref,paths)
 if key and (CACHE/key).exists():
  try:return (CACHE/key).read_text()
  except OSError:pass
 lk=None
 if key:   # 2026-10-17 (cpu): preflights on the same base wait for the first computation instead of repeating it
  try:
   import fcntl;CACHE.mkdir(parents=True,exist_ok=True);lk=open(CACHE/(key+'.lock'),'w');fcntl.flock(lk,fcntl.LOCK_EX)
   if (CACHE/key).exists():
    lk.close();return (CACHE/key).read_text()
  except OSError:pass
 try:out=_check_ref(ref,paths)
 except BaseException:
  if lk:lk.close()
  raise
 if key:
  try:
   CACHE.mkdir(parents=True,exist_ok=True);t=CACHE/(key+'.%d.tmp'%__import__('os').getpid());t.write_text(out);t.replace(CACHE/key)
   import time as _t
   for old in CACHE.iterdir():
    if _t.time()-old.stat().st_mtime>86400:old.unlink(missing_ok=True)
  except OSError:pass
 if lk:lk.close()
 return out
def warm_head():
 # run after a landing commit, outside the lock: the next landing then finds HEAD's baseline cached
 subprocess.Popen(['nice','-n','10',sys.executable,'-c','import sys;sys.path.insert(0,"tools");import dag_delta;dag_delta.check_ref("HEAD")'],
                  cwd=ROOT,start_new_session=True,stdin=subprocess.DEVNULL,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
def _check_ref(ref,paths):
 with tempfile.TemporaryDirectory(prefix='sheaf-dag-base-') as tmp:
  payload=subprocess.check_output(['git','archive',ref,*paths],cwd=ROOT)
  with tarfile.open(fileobj=io.BytesIO(payload)) as tar:tar.extractall(tmp,filter='data')
  # pfinc 2026-10-17: the server preflight sets SHEAF_DAG to its slot's absolute dag/nodes; inherited here, the "base"
  # check read the delivery's DAG (of whichever slot computed the shared cache entry first). A SHEAF_DAG naming this
  # repository's own dag/nodes by an absolute path now names the archived base tree's dag/nodes.
  env=dict(__import__('os').environ)
  sd=env.get('SHEAF_DAG')
  if sd and pathlib.Path(sd).is_absolute() and pathlib.Path(sd).resolve()==(ROOT/'dag/nodes').resolve():
   env['SHEAF_DAG']='dag/nodes'
  r=subprocess.run([sys.executable,'tools/check_dag.py','--cycles'],cwd=tmp,capture_output=True,text=True,check=False,env=env)
  return (r.stdout+r.stderr).replace(tmp,'<ROOT>')
def findings(text,ids):
 return [line for line in text.splitlines() if line.startswith(('ids:','targets:','error','unit','cycle','deps')) or 'ERROR' in line or (line.startswith('route') and mentions(line,ids))]
def mentions(line,ids):
 tokens=set(re.findall(r'[a-z][a-z0-9]*(?:-[a-z0-9]+)+',line))
 return bool(set(ids)&tokens)
def introduced(current,base_text,ids):
 old=set(findings(base_text,ids))
 return [line for line in findings(current.replace(str(ROOT),'<ROOT>'),ids) if line not in old or (line.startswith(('cycles:','deps:','ids:','route:')) and mentions(line,ids))]


def delivery_findings(current, base_text, ids):
 """Return blocking findings and advisory routes for a stage-1 delivery.

 Route findings are recorded, not refused (human decision, 2026-10-16).
 Keep introduced() unfiltered for diagnostic callers and share this policy
 between preflight and landing so they cannot disagree about an incoming edge.
 """
 selected = introduced(current, base_text, ids)
 return ([line for line in selected if not line.startswith('route:')],
         [line for line in selected if line.startswith('route:')])
