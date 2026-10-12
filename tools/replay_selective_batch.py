"""Read-only red incident replay: git archive/show, JSON and pure selectors; no compiler."""
import json, pathlib, subprocess, sys, tempfile, time
sys.path.insert(0,str(pathlib.Path(__file__).parent))
import batch_recovery as r, import_cycles as cycles, leanindex as li
root=pathlib.Path(__file__).resolve().parent.parent
batch=json.loads(pathlib.Path(sys.argv[1]).read_text()); entries=batch['entries']
snapshot=entries[-1]['commit']
failures=['Sheaf.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound']
with tempfile.TemporaryDirectory(prefix='blfix-replay-') as d:
    archive=subprocess.Popen(['git','-C',str(root),'archive',snapshot,'lean'],stdout=subprocess.PIPE)
    subprocess.run(['tar','-x','-C',d],stdin=archive.stdout,check=True);archive.stdout.close()
    assert archive.wait()==0
    t=time.perf_counter(); graph=cycles.graph(pathlib.Path(d)/'lean'); scan=time.perf_counter()-t
    deltas={}
    def changes(e,m):
        path='lean/'+m.replace('.','/')+'.lean'
        a,z=r.blob(root,e['commit']+'^',path),r.blob(root,e['commit'],path)
        ns=r.interface_delta(a.decode() if a is not None else None,z.decode() if z is not None else None)
        deltas[e['group']+'/'+e['item']+':'+m]=ns
        return ns
    selected=r.select(entries,failures,graph,changes)
    suspects=[e for o in selected for e in o['suspects']]
    deps=r.dependents(entries,suspects,graph)
    result={'batch':batch['id'],'snapshot':snapshot,'failures':failures,
      'return':[e['group']+'/'+e['item'] for e in suspects],
      'waiting':[e['group']+'/'+e['item'] for e in deps],
      'survivors':len(entries)-len(suspects)-len(deps),
      'builds':2,'estimated_minutes':6.0,
      'qualification':'initial red plus one survivor rebuild, assuming no additional fault; source-only replay, no compiler',
      'graph_scan_seconds':scan,'interface_deltas':deltas}
    t=time.perf_counter()
    for e in entries:
        texts={m:r.blob(root,e['commit'],'lean/'+m.replace('.','/')+'.lean').decode() for m in e['modules']}
        cycles.closing_cycle(graph,texts);graph=cycles.overlay(graph,texts)
    result['graph_checks_and_git_read_seconds_per_delivery']=(time.perf_counter()-t)/len(entries)
    print(json.dumps(result,indent=2))
