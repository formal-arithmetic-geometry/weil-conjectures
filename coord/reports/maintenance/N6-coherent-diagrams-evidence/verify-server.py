import json,pathlib,subprocess,os
roots=[pathlib.Path('/home/ubuntu/weil-conjectures-sheaf'),pathlib.Path('/home/ubuntu/weil-newtargets')]
names=['lem-coef-infinity-functor-pushout','lem-coef-space-geometric-descent','lem-coef-cat-infinity-colimits-cartesian-closure']
for root in roots:
 print('ROOT',root)
 print('HEAD',subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip())
 for n in names:
  rel='dag/nodes/sec-six-functors/'+n+'.json';d=json.loads((root/rel).read_text())
  committed=json.loads(subprocess.check_output(['git','show','HEAD:'+rel],cwd=root,text=True))
  assert d==committed,(root,n,'uncommitted changes')
  assert 'lem-coef-simplicial-model-coherent-diagrams' not in d.get('stmt_deps',[])+d.get('proof_deps',[])
  assert not any('\n'+'atural' in s['text'] for s in d.get('proof',[]))
  print(n,'committed; proof deps',d['proof_deps'])
root=roots[1];D={}
for p in (root/'dag/nodes').glob('*/*.json'):
 try:
  d=json.loads(p.read_text());D[d['id']]=d
 except:pass
item='lem-coef-simplicial-model-coherent-diagrams'
# Reinsert all necessary dependencies of the pre-maintenance ten-step proof;
# the check must not depend on the active worker dropping citations.
D[item]['proof_deps']=['lem-coef-enriched-diagram-size-generation','lem-coef-kan-quillen-right-proper','lem-coef-presentable-small-object-factorization','lem-coef-presentable-cellular-factorization','lem-coef-model-weak-equivalences-accessible','lem-coef-smith-model-recognition','lem-coef-enriched-diagram-rectification','lem-coef-simplicial-model-nerve-localization','lem-cbc-enhanced-functor-cone-calculus']
seen=set();stack=[];cycles=[];missing=set()
def go(n):
 if n in stack:cycles.append(stack[stack.index(n):]+[n]);return
 if n in seen:return
 if n not in D:missing.add(n);return
 seen.add(n);stack.append(n)
 for x in D[n].get('stmt_deps',[])+D[n].get('proof_deps',[]):go(x)
 stack.pop()
go(item)
print('FULL_ORIGINAL_DEPENDENCIES_AUDIT',json.dumps({'reachable':len(seen),'cycles':cycles,'missing':sorted(missing)}))
assert not cycles and not missing
for n in names[:2]:
 env=dict(os.environ,SHEAF_DAG=str(root/'dag/nodes'))
 r=subprocess.run(['python3','tools/review_split.py',n],cwd=root,env=env,capture_output=True,text=True)
 print('REVIEW',n,'exit',r.returncode);print(r.stdout+r.stderr)
 assert not r.returncode
