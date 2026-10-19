#!/usr/bin/env python3
"""Changed-node DAG checks, with reach/unit effects and edge-local cycle detection.

No SCC scan: every new cycle has a new edge u->v; search v for u. Existing
cycles through a touched node are also rejected, matching dag_delta policy.
Reachability and unit-realization checks can affect unchanged nodes, so their
before/after findings are compared over the entire affected graph in memory.
"""
import json
import dag_queue as dq
import blueprint_refs as bp
import units as un

def reachable(graph,start,target=None):
    seen=set();todo=list(start)
    while todo:
        u=todo.pop()
        if u==target:return True
        if u in seen:continue
        seen.add(u);todo.extend(v for v in graph.get(u,()) if v not in seen)
    return False if target is not None else seen

def graph(nodes):
    merged={i for i,d in nodes.items() if dq.field(d,'merged') or str(dq.field(d,'status') or '').lower()=='merged'}
    return {i:[c for c in dict.fromkeys(dq.deps_of(d,'all')) if c in nodes and c not in merged] for i,d in nodes.items() if i not in merged},merged

def global_findings(nodes):
    g=dq.Dag(nodes)
    out=set(un.check(nodes,verbose=False))|set(bp.errors(nodes))
    if not g.targets:out.add('targets: no node is a target')
    former=[i for i,d in g.live.items() if d.get('target_former')]
    reach=g.distances_from(g.targets+former)
    for i,d in g.live.items():
        flagged='unreachable' in (d.get('import_flags') or [])
        if i not in reach and not flagged:out.add(f'reach: {i} is not reached from a target and is not flagged unreachable')
        if i in reach and flagged:out.add(f'reach: {i} is flagged unreachable but a target reaches it')
    return out

def stale_flag(f):
    return f.startswith('reach: ') and f.endswith(' is flagged unreachable but a target reaches it')

def local_findings(after,changed):
    """Checks needed by both the worker dry run and the landing graph check."""
    new_graph,merged=graph(after);bad=[]
    for i in changed:
        d=after[i];m=dq.field(d,'merged')
        if dq.field(d,'id')!=i:bad.append(f'ids: {i} changed its id')
        if i in merged:
            if not m or str(m) not in new_graph:bad.append(f'deps: {i} is merged into {m!r}, which is not a live node')
            continue
        pd={str(x) for x in (dq.field(d,'proof_deps') or [])}
        for which in ('stmt','proof'):
            for c in dq.deps_of(d,which):
                if c not in after:bad.append(f'deps: {i} ({which}) -> {c}: no such node')
                elif c in merged:bad.append(f'deps: {i} ({which}) -> {c}: merged into {dq.field(after[c],"merged")}')
        pf=dq.field(d,'proof')
        if isinstance(pf,list):
            for k,step in enumerate(pf,1):
                if isinstance(step,dict):
                    for u in step.get('uses') or []:
                        if str(u) not in pd:bad.append(f'deps: {i} step {k} uses {u}, which is not in proof_deps')
        for v in new_graph.get(i,()):
            # Existing cycles involving a delivered node also block its landing.
            if reachable(new_graph,[v],i):bad.append(f'cycles: {i} -> {v} reaches {i}')
    return sorted(set(bad))

def check(before,after,changed):
    bad=local_findings(after,changed)
    old_global=global_findings(before);new_global=global_findings(after)
    # 2026-10-16 (the human: no restrictions that refuse valid work): a dependency outside its unit's blueprint route
    # is recorded, not refused; the route order is a reading order, not a mathematical condition.
    # 2026-10-18 (land2fix): a delivery that adds an edge into a node flagged `unreachable` makes the flag stale; being
    # reached is not a defect of the delivery (HEAD already carries ~520 such stale flags). This finding named only the
    # unchanged flagged node, so no delivery was blamed and every stage-2 batch was refused from 14:44 on.
    bad.extend(sorted(f for f in new_global-old_global if not f.startswith('route:') and not stale_flag(f)))
    # Blueprint validity of every touched node is mandatory, including inherited
    # dependency errors. review_split adds strict provenance for the item/new nodes.
    for f in new_global & old_global:
        if f.startswith('blueprint:') and any(f.startswith('blueprint: '+i+':') or f.startswith('blueprint: '+i+' ') for i in changed):bad.append(f)
    return sorted(set(bad))

def validate(plans):
    before=dq.load();after=dict(before);changed=set()
    for p in plans:
        for nid,rel in p['nodes'].items():
            after[nid]=json.loads(p['writes'][rel]);changed.add(nid)
    return check(before,after,changed)
