#!/usr/bin/env python3
"""Stage-2 immutable parallel preparation and transactional batch/continuous writes.

prepare MANIFEST OUTPUT: read/check deliveries concurrently, no project writes.
commit PLANS RECEIPTS [--bulk]: recheck optimistic guards, one write/promotion.
Compilation receipts bind the immutable plan digest; compiler runs on launcher.
"""
import collections, concurrent.futures, contextlib, copy, hashlib, io, json, multiprocessing
import os, pathlib, pickle, re, subprocess, sys, tempfile, time, traceback
# tools/queue.py otherwise shadows multiprocessing's standard-library queue.
import importlib.util, sysconfig
_queue_spec=importlib.util.spec_from_file_location('queue',pathlib.Path(sysconfig.get_path('stdlib'))/'queue.py')
_queue=importlib.util.module_from_spec(_queue_spec);_queue_spec.loader.exec_module(_queue);sys.modules['queue']=_queue
os.environ['SHEAF_LEAD']='L-only'
import merge_delivery as md
import stage2_delivery as s2
import leanindex as li
import nt_batch2 as batch
import dag_queue as dq
import blueprint_refs as bp
import review_split as split
from mergelock import merge_lock
P=md.ROOT
STATE=P/'local/stage2/parallel'
INDEX=None
NODES=None
FILES=None
CFG=None

def digest(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,ensure_ascii=False).encode()).hexdigest()

def read(rel):
    p=P/rel
    return p.read_text() if p.is_file() else None

def token():
    # Include uncommitted source/DAG bytes: sync may leave work before its commit.
    out={}
    for root,pattern in [('dag/nodes','*.json'),('dag/units','*.json'),('dag/chapters','*.json'),('lean/Sheaf','*.lean'),('lean/WeilConjectures','*.lean')]:
        for p in (P/root).rglob(pattern):
            st=p.stat();out[p.relative_to(P).as_posix()]=(st.st_mtime_ns,st.st_size)
    for rel in ['coord/sheaf.env','coord/newtargets.json','coord/newtargets-stage1-completions.json','dag/lean_names_upstream.json']:
        p=P/rel
        if p.exists():
            st=p.stat();out[rel]=(st.st_mtime_ns,st.st_size)
    return digest(out)

def cached_index():
    global INDEX
    STATE.mkdir(parents=True,exist_ok=True)
    path=STATE/'source-index.pickle'
    stamp={str(p.relative_to(P)): (p.stat().st_mtime_ns,p.stat().st_size) for root in li.library_dirs() for p in (P/'lean'/root).rglob('*.lean')}
    for name in ('Challenge.lean','TargetsCheck.lean'):
        p=P/'lean'/name
        if p.exists():stamp[str(p.relative_to(P))]=(p.stat().st_mtime_ns,p.stat().st_size)
    index=batch.SourceIndex()
    try:
        old=pickle.loads(path.read_bytes())
        index.decls,index.imports,index.statements,index.by_module=old['data'];index.loaded=True
        for rel in set(stamp)|set(old['stamp']):
            if stamp.get(rel)!=old['stamp'].get(rel):index.refresh(rel)
        print('PARALLEL SOURCE INDEX reused',len(stamp),'modules',flush=True)
    except (OSError,ValueError,KeyError,EOFError,pickle.UnpicklingError):index.load()
    tmp=path.with_suffix('.'+str(os.getpid())+'.tmp');tmp.write_bytes(pickle.dumps({'stamp':stamp,'data':(index.decls,index.imports,index.statements,index.by_module)},protocol=5));tmp.replace(path)
    INDEX=index
    return index

def freeze_config():
    # These inputs are frozen only for this preparation and guarded at commit.
    global CFG
    CFG=li.config();li.config=lambda:dict(CFG)
    path=P/'coord/newtargets-stage1-completions.json'
    completions=json.loads(path.read_text()) if path.exists() else {}
    def completed(d):
        rec=completions.get(str(dq.field(d,'id')))
        if not isinstance(rec,dict) or rec.get('by')!='L-only':return False
        payload={k:d.get(k) for k in ('statement','lean')}
        h=hashlib.sha256(json.dumps(payload,sort_keys=True,ensure_ascii=False).encode()).hexdigest()
        declarations={(d.get('lean') or {}).get('declaration')}|set((d.get('lean') or {}).get('declarations') or [])
        audit=(d.get('lean_audit') or {}).get(dq.done_branch()) or {}
        declarations.update(x.get('name') for x in audit.get('decls',[]) if not x.get('sorry'))
        ah=hashlib.sha256(json.dumps(audit,sort_keys=True,ensure_ascii=False).encode()).hexdigest()
        return rec.get('result')=='complete' and rec.get('interface_sha256')==h and rec.get('basis') in ('live-proved','first-task-existing-declaration') and bool(rec.get('declaration')) and rec['declaration'] in declarations and (not rec.get('audit_sha256') or rec['audit_sha256']==ah)
    dq.recorded_stage1_completion=completed

def run_split(nodes,files,items):
    out=io.StringIO()
    with contextlib.redirect_stdout(out):split.main(nodes,files,items)
    return batch.split_findings(out.getvalue())

def backfill(docs,nodes):
    # Same mechanical backfill, restricted to the plan's nodes, in memory.
    merged=dict(nodes);merged.update(docs)
    class Sink:
        def __init__(self,nid):self.nid=nid
        def write_text(self,text,*a,**k):
            if self.nid in docs:docs[self.nid]=json.loads(text)
    old=bp.load;bp.load=lambda:(merged,{nid:Sink(nid) for nid in merged})
    try:
        with contextlib.redirect_stdout(io.StringIO()):bp.backfill()
    finally:bp.load=old

def prune(mod,old,new,index):
    import import_prune_check as ipc
    with tempfile.TemporaryDirectory(prefix='nt-prune-', dir="/dev/shm/nt-tmp") as tmp:
        a=pathlib.Path(tmp)/'old';b=pathlib.Path(tmp)/'new';a.write_text(old or '');b.write_text(new)
        argv=sys.argv;scan=li.scan;stmts=li.library_statements
        li.scan=lambda:(index.decls,dict(index.imports));li.library_statements=lambda:index.statements
        out=io.StringIO()
        try:
            sys.argv=['import_prune_check.py',mod,str(a),str(b)]
            with contextlib.redirect_stdout(out):rc=ipc.main()
        finally:sys.argv=argv;li.scan=scan;li.library_statements=stmts
        if rc:raise md.Fail(out.getvalue())

class Preparation:
    preparing=True
    def __init__(self,row):self.row=row;self.result=None
    def prepare(self,o,D,records,reviewed,reviewed_new):
        cur=copy.deepcopy(NODES[o.item]);cur['lean']=records[o.item]
        cur['reviewed_lean']=dict(reviewed,statement_corrected=True) if D.get('corrected') else reviewed
        if D.get('corrected'):
            for k in md.STAGE2_ITEM_CORRECTION:
                if k in D['node']:cur[k]=D['node'][k]
                else:cur.pop(k,None)
        elif D.get('added_deps'):
            sd=list(cur.get('stmt_deps') or []);cur['stmt_deps']=sd+[x for x in D['added_deps'] if x not in sd]
        docs={o.item:cur};paths={o.item:D['node_path']}
        for nid,x in D['new'].items():
            nd=copy.deepcopy(x['node']);nd['lean']=records[nid];nd['reviewed']=reviewed_new;nd['reviewed_lean']=reviewed
            docs[nid]=nd;paths[nid]=x['path']
        for nid,x in D['deps'].items():
            nd=copy.deepcopy(NODES[nid]);nd['lean']=records[nid];nd['reviewed_lean']=reviewed
            docs[nid]=nd;paths[nid]=x['path']
        backfill(docs,NODES)
        view=dict(NODES);view.update(docs);files=dict(FILES);files.update({n:P/p for n,p in paths.items()})
        before=run_split(NODES,FILES,[o.item]);after=run_split(view,files,[o.item])
        bad=[o.item+': '+f for f in after.get(o.item,set())-before.get(o.item,set())]
        if bad:raise md.Fail('review_split.py: '+' | '.join(sorted(bad)))
        index=copy.copy(INDEX)
        local_names=collections.defaultdict(set);local_stmts=collections.defaultdict(set)
        index.imports=dict(INDEX.imports)
        for m in D['modules']:
            mod=m['module']
            for q in li.decls_in_text(m['text']):local_names[q].add(mod)
            for q,st in li.statements_in_text(m['text']).items():
                if st:local_stmts[st].add((q,mod))
            index.imports[mod]=li.imports_of(m['text'])
        index.decls=collections.ChainMap({q:INDEX.decls.get(q,set())|mods for q,mods in local_names.items()},INDEX.decls)
        index.statements=collections.ChainMap({st:INDEX.statements.get(st,set())|vals for st,vals in local_stmts.items()},INDEX.statements)
        expected={p:read(p) for p in paths.values()}
        writes={paths[nid]:md.dump(nd) for nid,nd in docs.items()}
        for m in D['modules']:
            old=read(m['file']);expected[m['file']]=old;writes[m['file']]=m['text']
            prune(m['module'],old,m['text'],index)
        report=D['report_path'];expected[report]=read(report);writes[report]=D['report']
        self.result={'row':self.row,'expected':expected,'writes':writes,'nodes':paths,'modules':D['modules'],
                     'ledger':f'merged deliver/{o.group}/{o.item} (stage 2; reviewer {o.verdict}; parallel immutable checks)',
                     'message':f'State {o.item} ({o.group}, reviewed by {o.reviewer})',
                     'split_baseline':{k:sorted(v) for k,v in before.items()}}
        ownmods={m['module'] for m in D['modules']}
        imports=set()
        for m in D['modules']:imports.update(li.closure(m['module'],index.imports,{}))
        self.result['imports']={}
        for mod in imports-ownmods:
            rel='lean/'+mod.replace('.','/')+'.lean';path=P/rel
            if path.is_file():
                st=path.stat();self.result['imports'][rel]=[st.st_mtime_ns,st.st_size]
        self.result['id']=digest(self.result)
        return 0

def worker(row):
    started=time.monotonic()
    if row.get('verdict')=='RETURN':return {'row':row,'result':'RETURN','note':row['note']}
    try:
        # 2026-10-16 (launcher): workers state missing prerequisites themselves, so two deliveries often state the same
        # dependency; when another one has landed it meanwhile, keep the landed record (--revert-nodes) instead of
        # returning; the file-only compile of the delivery against the current library then decides.
        reverts=[]
        while True:
            try:
                opts=batch.options(row);opts.revert_nodes=','.join(reverts) or None
                obj=Preparation(row);md.cmd_merge2(opts,batch=obj);break
            except md.Fail as exc:
                m=re.match(r"the dependency node (\S+): its `lean` changed on",str(exc))
                if not m or m.group(1) in reverts or len(reverts)>=8:raise
                reverts.append(m.group(1));print('REVERT DEPENDENCY',row['item'],m.group(1),flush=True)
        result=obj.result
        if reverts:result['note_reverted']=reverts
        print('PREPARED',row['item'],round(time.monotonic()-started,2),'s',flush=True)
        return result
    except md.Fail as exc:
        print('REFUSED',row['item'],str(exc)[:400],flush=True)
        return {'row':row,'result':'RETURN','note':str(exc)}
    except Exception:
        return {'row':row,'result':'retry','note':traceback.format_exc()}

def prepare(rows):
    global NODES,FILES
    initial=token();freeze_config();cached_index();s2._names()
    NODES=dq.load();FILES={p.stem:p for p in dq.nodes_dir().rglob('*.json')}
    with concurrent.futures.ProcessPoolExecutor(max_workers=int(os.environ.get('NT_CHECK_JOBS','16')),mp_context=multiprocessing.get_context('fork')) as pool:
        plans=list(pool.map(worker,rows))
    # Each plan records its precise read/write guard; unrelated DAG syncs do not invalidate it.
    for plan in plans:
        if 'id' in plan:
            plan['guard']=initial
            batch.atomic(STATE/(plan['id']+'.json'),plan)
    return plans

def findings(text):
    return {x for x in text.splitlines() if x.startswith(('ids:','deps:','cycles:','targets:','reach:','units:','route:','blueprint:','error')) or 'ERROR' in x}

def full():return batch.run_tool('check_dag.py','--cycles')

def archive(row,kind):
    ref='refs/heads/deliver/'+row['group']+'/'+row['item']
    if md.git('rev-parse','-q','--verify',ref,check=False)!=row['head']:return False
    md.git('update-ref',f'refs/stage2-{kind}/{row["group"]}/{row["item"]}/{row["head"]}',row['head'])
    md.git('update-ref','-d',ref,row['head']);return True

def do_return(row,note):
    with md.merge_lock():
        ref='refs/heads/deliver/'+row['group']+'/'+row['item']
        if md.git('rev-parse','-q','--verify',ref,check=False)!=row['head']:return {'result':'retired'}
    md.cmd_return(row['group'],row['item'],'L: independent stage-2 immutable head '+row['head'][:12]+': '+note)
    with md.merge_lock():archive(row,'returned')
    return {'result':'RETURN','note':note}

def ordered_plans(plans,results):
    """Choose the exact write set before validating its combined DAG."""
    chosen=[];owned={}
    for p in plans:
        bad=[]
        for rel in set(p['writes']) & set(owned):
            old,new=owned[rel],p['writes'][rel]
            if rel.startswith('dag/nodes/'):
                substantive=lambda d:{k:v for k,v in json.loads(d).items() if k not in ('reviewed','reviewed_lean')}
                if substantive(old)==substantive(new):continue
            if old!=new:bad.append(rel)
        if bad:
            results[p['row']['head']]={'result':'retry','note':'ordered conflicting paths need fresh checks: '+', '.join(bad)}
        else:chosen.append(p);owned.update(p['writes'])
    return chosen

def continuous_findings(plans):
    import nt_incremental2
    bad=nt_incremental2.validate(plans)
    before=dq.load();after=dict(before)
    files={p.stem:p for p in dq.nodes_dir().rglob('*.json')}
    for p in plans:
        for nid,rel in p['nodes'].items():after[nid]=json.loads(p['writes'][rel]);files[nid]=P/rel
    items=[p['row']['item'] for p in plans]
    baseline=run_split(before,files,items);checked=run_split(after,files,items)
    for item in items:bad.extend(item+': '+f for f in checked.get(item,set())-baseline.get(item,set()))
    return sorted(set(bad))

def solo_offenders(plans,bad,check):
    """2026-10-18 (land2fix): a finding that names no node of any delivery (a unit or reach finding about an unchanged
    node) is blamed on each delivery that produces it when checked alone against the same base."""
    if len(plans)<2:return {p['id'] for p in plans}
    want=set(bad)
    return {p['id'] for p in plans if want & set(check([p]))}

def validated_survivors(plans,returns,check=continuous_findings):
    # Removing one delivery can expose a dangling edge in another delivery.
    while plans:
        bad=check(plans)
        if not bad:return plans
        offenders={p['id'] for p in plans if any(batch.dag_delta.mentions(f,p['nodes']) for f in bad)}
        if not offenders:
            offenders=solo_offenders(plans,bad,check)
            if offenders:print('SOLO ATTRIBUTION',len(offenders),'of',len(plans),' | '.join(bad)[:400],flush=True)
        if not offenders:raise md.Fail('unattributed incremental finding: '+' | '.join(bad))
        returns.extend((p['row'],'incremental DAG validation: '+' | '.join(bad)) for p in plans if p['id'] in offenders)
        plans=[p for p in plans if p['id'] not in offenders]
    return plans

def compile_infrastructure_failure(receipt):
    """Compiler JSON failures cannot be repaired by changing a Lean delivery."""
    if receipt.get('infra'):
        return True
    if not receipt.get('rc'):
        return False
    out = str(receipt.get('out', '')).strip()
    return bool(re.fullmatch(
        r"JSONDecodeError\(.+\)|(?:Extra data|Expecting value|"
        r"Expecting property name enclosed in double quotes|Unterminated string starting at)"
        r": line \d+ column \d+ \(char \d+\)", out, re.S))


def commit(plans,receipts,promote,bulk=False):
    # All expensive checks and compilation have finished before either guard.
    results={};ready=[];returns=[]
    for plan in plans:
        row=plan['row']
        if 'id' not in plan:
            if plan.get('result')=='RETURN':returns.append((row,plan['note']))
            else:results[row['head']]={'result':'retry','note':plan.get('note','incomplete preparation')}
            continue
        saved=json.loads((STATE/(plan['id']+'.json')).read_text())
        if saved!=plan:raise md.Fail('prepared plan differs from server record')
        receipt=receipts.get(plan['id'])
        if not receipt or receipt.get('id')!=plan['id']:
            results[row['head']]={'result':'retry','note':'missing compile receipt'};continue
        if compile_infrastructure_failure(receipt):
            note = receipt.get('out', '')
            if not note.startswith('INFRASTRUCTURE RETRY'):
                note = 'INFRASTRUCTURE RETRY (compiler JSON): ' + note
            results[row['head']]={'result':'retry','note':note[:600]};continue
        if receipt.get('rc',1) and receipt.get('out','').startswith('overlay '):
            # A side-only dependency may not elaborate against the local mirror.
            # Confirm both compile passes against the server's published artifacts.
            payload=json.dumps({'files':{m['file'][5:]:m['text'] for m in plan['modules']}})
            checks=[]
            for _ in range(2):
                check=subprocess.run([sys.executable,'tools/nt_compile.py','--json'],cwd=P,input=payload,capture_output=True,text=True)
                checks.append(check.stdout+check.stderr)
                if check.returncode:break
            receipt=dict(receipt,rc=check.returncode,out=receipt['out']+'\nSERVER CONFIRMATION\n'+'\n'.join(checks))
            print('SERVER COMPILE CONFIRMATION',row['item'],receipt['rc'],flush=True)
        if receipt.get('rc',1):
            returns.append((row,'file-only compilation failed: '+receipt.get('out','')[-5000:]));continue
        ready.append(plan)
    if ready:
        # Baseline before the transaction. Full validation once after bulk writes.
        freeze_config();index=cached_index();accepted=[]
        for p in ready:
            changed=[rel for rel,old in p['expected'].items() if read(rel)!=old]
            for rel,stamp in p.get('imports',{}).items():
                path=P/rel
                if not path.is_file() or [path.stat().st_mtime_ns,path.stat().st_size]!=stamp:changed.append(rel)
            if changed:
                results[p['row']['head']]={'result':'retry','note':'delivery or compile dependency changed: '+', '.join(changed)};continue
            try:
                for m in p['modules']:prune(m['module'],p['expected'][m['file']],m['text'],index)
            except md.Fail as exc:
                returns.append((p['row'],'current source index: '+str(exc)));continue
            for m in p['modules']:
                mod=m['module']
                for q in li.decls_in_text(m['text']):index.decls[q].add(mod)
                for q,st in li.statements_in_text(m['text']).items():
                    if st:index.statements[st].add((q,mod))
                index.imports[mod]=li.imports_of(m['text'])
            accepted.append(p)
        ready=ordered_plans(accepted,results);base_guard=token()
    if ready:
        freeze_config()
        baseline=full() if bulk else None
        # Continuous validation works on a virtual DAG and never writes files.
        if not bulk:
            ready=validated_survivors(ready,returns)
        started=time.monotonic()
        with merge_lock(P/'coord/.stage2-promotion.lock'):
            batch.recover(promote)
            with md.merge_lock():
                if token()!=base_guard:
                    # 2026-10-16 (launcher): the whole-tree token changed on nearly every batch (stage-1 landings, sync,
                    # other batches during the minutes of validation and lock waits), so every batch was retried and none
                    # landed. Only a plan whose own inputs changed (files it read, modules it imports) is retried now.
                    def _stale(pl):
                        for rel,old in (pl.get('expected') or {}).items():
                            if read(rel)!=old:return True
                        for rel,(mt,sz) in (pl.get('imports') or {}).items():
                            q=P/rel
                            if not q.is_file():return True
                            st=q.stat()
                            if (st.st_mtime_ns,st.st_size)!=(mt,sz):return True
                        return False
                    stale=[pl for pl in ready if _stale(pl)]
                    for pl in stale:results[pl['row']['head']]={'result':'retry','note':'its own inputs changed before write'}
                    ready=[pl for pl in ready if pl not in stale]
                changed_heads={p['row']['head'] for p in ready if md.git('rev-parse','-q','--verify','refs/heads/deliver/'+p['row']['group']+'/'+p['row']['item'],check=False)!=p['row']['head']}
                if changed_heads:
                    for p in ready:results[p['row']['head']]={'result':'retired' if p['row']['head'] in changed_heads else 'retry','note':'batch heads changed before write'}
                    ready=[]
                tx=batch.Batch([p['row'] for p in ready]);tx.defer_queue=not bulk;tx.defer_claims=True
                inventory={'coord/ledger.md','coord/deliveries.log'}
                if bulk:inventory.update(('coord/queue.tsv','coord/queue.md','coord/blueprint-index.tsv'))
                for p in ready:
                    inventory.update(p['writes'])
                    row=p['row'];inventory.add('coord/returns/'+row['group']+'.md')
                    inventory.add('coord/claims/'+row['item'].replace('/','__')+'.lock')
                    inventory.add('coord/repair-notes/'+row['item']+'.json')
                tx.prepare_originals(sorted(inventory))
                try:
                    active=[];owned={}
                    for p in ready:
                        row=p['row'];ref='refs/heads/deliver/'+row['group']+'/'+row['item']
                        if md.git('rev-parse','-q','--verify',ref,check=False)!=row['head']:
                            results[row['head']]={'result':'retired'};continue
                        import nt_land2
                        lc=nt_land2.live_conflicts(p['writes'],p['expected'])
                        if lc:
                            # collide fix 2026-10-17: live changed a node this delivery changes; it leaves this round
                            # (kept queued) and the rest of the batch lands.
                            results[row['head']]={'result':'retry','note':'live concurrent change, out of this round: '+', '.join(lc)}
                            print('LIVE CONFLICT, out of this round',row['item'],lc,flush=True);continue
                        overlap=set(p['writes'])&set(owned)
                        # Shared metadata-only nodes are ordered if their Lean records
                        # agree. Any substantive overlap goes through fresh preparation.
                        bad=[]
                        for rel in overlap:
                            if rel.startswith('dag/nodes/'):
                                old=json.loads(owned[rel]);new=json.loads(p['writes'][rel]);before=json.loads(p['expected'][rel] or '{}')
                                substantive=lambda d:{k:v for k,v in d.items() if k not in ('reviewed','reviewed_lean')}
                                if substantive(old)==substantive(new):continue
                            if owned[rel]!=p['writes'][rel]:bad.append(rel)
                        changed=[rel for rel,old in p['expected'].items() if rel not in overlap and read(rel)!=old]
                        if bad or changed:
                            results[row['head']]={'result':'retry','note':'ordered conflicting paths need fresh checks: '+', '.join(bad+changed)};continue
                        tree=tx.tree()
                        for rel,value in p['writes'].items():
                            if rel in tx.owned:
                                # Already journaled; no second ownership or rollback scope.
                                (P/rel).write_text(value)
                            else:tree.write(rel,value)
                            owned[rel]=value
                        o=batch.options(row)
                        tx.stage(o,tree,list(p['writes'])+['coord/ledger.md','coord/deliveries.log'],p['nodes'],p['ledger'],p['message'],'deliver/'+row['group']+'/'+row['item'])
                        active.append(p)
                    if tx.staged and bulk:
                        checked=full()
                        bad=sorted(findings(checked)-findings(baseline))
                        ids={n for p in active for n in p['nodes']}
                        bad += [f for f in findings(checked) & findings(baseline) if f.startswith(('cycles:','deps:','ids:')) and batch.dag_delta.mentions(f,ids)]
                        split_now=batch.split_findings(batch.run_tool('review_split.py','--stage2',*(p['row']['item'] for p in active)))
                        for p in active:
                            item=p['row']['item']
                            bad.extend(item+': '+f for f in split_now.get(item,set())-set(p['split_baseline'].get(item,[])))
                        if bad:
                            offenders={p['id'] for p in active if any(batch.dag_delta.mentions(f,p['nodes']) for f in bad)}
                            if not offenders:raise md.Fail('unattributed batch finding: '+' | '.join(bad))
                            survivors=[p for p in active if p['id'] not in offenders]
                            returns.extend((p['row'],'batch DAG validation: '+' | '.join(bad)) for p in active if p['id'] in offenders)
                            tx.rollback();active=[]
                            for p in survivors:
                                tree=tx.tree()
                                for rel,val in p['writes'].items():
                                    if rel in tx.owned:(P/rel).write_text(val)
                                    else:tree.write(rel,val)
                                tx.stage(batch.options(p['row']),tree,list(p['writes'])+['coord/ledger.md','coord/deliveries.log'],p['nodes'],p['ledger'],p['message'],'deliver/'+p['row']['group']+'/'+p['row']['item']);active.append(p)
                            checked=full()
                            bad=sorted(findings(checked)-findings(baseline))
                            if bad:raise md.Fail('batch recheck failed: '+' | '.join(bad))
                    sha=tx.finish() if tx.staged else None
                    if not sha:tx.rollback();tx.path.unlink()
                except BaseException:
                    if not batch.committed(tx.record):
                        tx.rollback()
                        if tx.record['originals']:md.git('reset','-q','HEAD','--',*tx.record['originals'])
                        tx.path.unlink(missing_ok=True)
                    raise
            if sha:
                batch.promote_skipping(promote,sha,tx.record.get('id',''))
                with md.merge_lock():batch.release_claims(tx.record);batch.retire(tx.record['rows']);tx.path.unlink()
                for p in active:results[p['row']['head']]={'result':p['row']['verdict'],'side':sha}
        print('PARALLEL CRITICAL SECTION',round(time.monotonic()-started,2),'s;',len(active),'landed',flush=True)
    for row,note in returns:results[row['head']]=do_return(row,note)
    print('BATCH_RESULT '+json.dumps(results),flush=True)
    return results

def main():
    action=sys.argv[1]
    if action=='prepare':
        plans=prepare(json.loads(pathlib.Path(sys.argv[2]).read_text()));batch.atomic(pathlib.Path(sys.argv[3]),plans)
    elif action=='commit':
        import nt_land2
        commit(json.loads(pathlib.Path(sys.argv[2]).read_text()),json.loads(pathlib.Path(sys.argv[3]).read_text()),nt_land2.promote,'--bulk' in sys.argv)
    else:raise SystemExit(__doc__)
if __name__=='__main__':main()
