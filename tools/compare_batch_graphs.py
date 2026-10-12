"""Read-only closed-batch comparison of full-graph and incremental cycle guards.
The unaffected static checks and journal are covered by the tools unit suite.
"""
import json,pathlib,subprocess,sys,tempfile,time
sys.path.insert(0,str(pathlib.Path(__file__).parent))
import batch_recovery as r,import_cycles as ic
root=pathlib.Path(__file__).resolve().parent.parent
rows=[]
for name in sys.argv[1:]:
 b=json.loads(pathlib.Path(name).read_text());entries=b['entries']
 with tempfile.TemporaryDirectory(prefix='graph-compare-') as d:
  ref=entries[0]['commit']+'^'
  archive=subprocess.Popen(['git','-C',str(root),'archive',ref,'lean'],stdout=subprocess.PIPE)
  subprocess.run(['tar','-x','-C',d],stdin=archive.stdout,check=True);archive.stdout.close();assert archive.wait()==0
  t=time.perf_counter();baseline=ic.graph(pathlib.Path(d)/'lean');scan=time.perf_counter()-t
  # Full reference is reconstructed independently from its previous tree;
  # avoiding repeated parsing of identical files does not change its edges.
  full=dict(baseline);incremental=dict(baseline);previous=ref;messages=[];elapsed=0
  for e in entries:
   parent=e['commit']+'^'
   outside=r.git(root,'diff','--name-only',previous,parent,'--','lean/').decode().splitlines()
   for p in outside:
    if not p.endswith('.lean'):continue
    mod=p[5:-5].replace('/','.');data=r.blob(root,parent,p)
    if data is None:full.pop(mod,None)
    else:full[mod]=ic.imports(data.decode())
    incremental=ic.overlay(incremental,{mod:data.decode() if data is not None else None})
   texts={m:r.blob(root,e['commit'],'lean/'+m.replace('.','/')+'.lean').decode() for m in e['modules']}
   old=ic.closing_cycle(full,texts)
   t=time.perf_counter();new=ic.closing_cycle(incremental,texts);incremental=ic.overlay(incremental,texts);elapsed+=time.perf_counter()-t
   assert old==new,(b['id'],e['item'],old,new)
   # Independently update the full reference, then compare every edge.
   for m,text in texts.items():full[m]=ic.imports(text)
   assert full==incremental
   messages.append({'delivery':e['group']+'/'+e['item'],'old':('import cycle: '+' -> '.join(old)) if old else None,
                    'new':('import cycle: '+' -> '.join(new)) if new else None})
   previous=e['commit']
  rows.append({'batch':b['id'],'deliveries':len(entries),'same_cycle_refusals_and_messages':True,
               'full_graph_scan_seconds':scan,'incremental_check_update_seconds_per_delivery':elapsed/len(entries),
               'checks':messages})
print(json.dumps({'scope':'changed cycle guard; full and incremental graphs agree at every landing; all other refusal checks unchanged',
                  'batches':rows},indent=2))
