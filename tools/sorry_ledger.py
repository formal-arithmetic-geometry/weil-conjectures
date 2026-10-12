#!/usr/bin/env python3
"""Source-only deterministic hole ledger. No Lean or builds.

Unit: one per declaration containing sorry/admit/sorryAx, or an axiom declaration;
structure/class default fields are separate declarations. Unattributed holes and
lexer failures produce explicit other rows. Source-qualified names cannot recover
macro-generated or elaborated private/anonymous names; synthetic keys expose this.
Delta: closed = holed declaration still present, now hole-free; added = absent or
hole-free declaration now holed; changed = holed at both ends, normalized masked
signature differs; deleted is separate, never counted as proved. Net=closed-added.
Closure repeats queue.analyse's BFS from TargetsCheck's imports (plain imports too).
Classes, in precedence order: moved = changed holed statement OR every closed new
proof references a same-commit added hole and net<=0; pruned = holed modules leave
closure; decomposed = closed and added; proved = closed, no added/changed/deleted;
other otherwise. Reference approximation: qualified or terminal name token in new
proof, in same/import-reachable module, transitively through closed declarations and same-commit proved helpers.
This is source evidence, not elaborated dependency information or a proof verdict.
History is first-parent, recomputed every run. Claims come from the input git tree.
"""
from __future__ import annotations
import argparse
import collections
import functools
import fcntl
import os
import tempfile
import json
import pathlib
import re
import subprocess
import leanindex as li
import stage2_delivery as s2
ROOT=pathlib.Path(__file__).resolve().parent.parent
BASELINES=[('889327369','Queue at the start of stage 3'),
           ('660345513','Application of proof-dependency imports')]
HOLE=re.compile(r"(?<![\w'.«])(?:sorry|admit|sorryAx)(?![\w'»])")
DEFECT={'def','instance','structure field'}


def git(*args):
    return subprocess.check_output(['git','-C',str(ROOT),*args])


_SPECIAL=re.compile(r'/-|--|«|r\#*"|"|\'')
_COMMENT=re.compile(r'/-|-/')
_STRING=re.compile(r'"(?:\\[\s\S]|[^"\\])*"')


def segments(text):
    """Lean lexical delimiters, skipping ordinary code in regex-sized spans.

    Quoted names take priority over delimiters inside them. Raw strings honor
    their exact hash terminator; nested comments use a depth counter.
    """
    i=0
    while i<len(text):
        m=_SPECIAL.search(text,i)
        if not m:
            yield 'code',i,len(text); break
        a=m.start()
        if a>i: yield 'code',i,a
        token=m[0]; kind='code'; b=m.end()
        if token=='«':
            b=text.find('»',b)
            if b<0: raise li.LexError(f'unterminated quoted identifier at {a}')
            b+=1
        elif token=='--':
            kind='line'; b=text.find('\n',b)
            if b<0: b=len(text)
        elif token=='/-':
            kind='block'; depth=1
            while depth:
                end=_COMMENT.search(text,b)
                if not end: raise li.LexError(f'unterminated comment at {a}')
                depth+=1 if end[0]=='/-' else -1
                b=end.end()
        elif token.startswith('r') and (a==0 or not li._ident_cont(text[a-1])):
            kind='string'; terminator='"'+token[1:-1]
            end=text.find(terminator,b)
            if end<0: raise li.LexError(f'unterminated raw string at {a}')
            b=end+len(terminator)
        elif token=='"' or token.startswith('r'):
            if token.startswith('r'):
                # An identifier ending in r followed by a normal string.
                yield 'code',a,b-1; a=b-1
            kind='string'; end=_STRING.match(text,a)
            if not end: raise li.LexError(f'unterminated string at {a}')
            b=end.end()
        elif token=="'" and (a==0 or not li._ident_cont(text[a-1])):
            char=li._CHAR.match(text,a)
            if char: kind='char'; b=char.end()
        yield kind,a,b
        i=b


def mask(text, identifiers=False, parts=None):
    """Faithful position-preserving lexer mask; «...» is lexed before comments.

    Keep quoted names for declaration parsing; mask them for hole token matching.
    The lexer handles nested comments, escaped/raw strings, character literals.
    """
    out=list(text)
    for kind,a,b in (segments(text) if parts is None else parts):
        if kind in (*li.COMMENT_KINDS,'string','char') or (identifiers and text[a:a+1]=='«'):
            out[a:b]=['\n' if c=='\n' else ' ' for c in text[a:b]]
    return ''.join(out)


def scan_text(text):
    rows,warnings=[],[]
    try:
        parts=list(segments(text))
        code=mask(text,parts=parts); tokens=mask(text,True,parts)
        # Reuse the tested scope/signature/let-binder parser, substituting its old
        # masker (which mishandles comment delimiters in quoted names). Single
        # threaded, restored on exceptions; no global modification survives.
        original=s2.mask
        try:
            s2.mask=lambda t:t
            decls=s2.declarations(code)
        finally:
            s2.mask=original
    except (li.LexError,UnicodeError) as e:
        return [dict(name='<unparsed>',kind='other',signature='',proof='',markers=['unavailable'],line=1)],[str(e)]
    occupied=set(); duplicates=collections.Counter()
    for d in decls:
        a,b=d['kw_pos'],d['end']
        name=d['name'] or '<anonymous:'+s2.normalize(code[a:d['sig_end']])+'>'
        duplicates[name]+=1
        if duplicates[name]>1:
            warnings.append('duplicate source declaration: '+name)
            name+=f'::<{duplicates[name]}>'
        kind=d['kw'] if d['kw'] in ('theorem','lemma','def','instance') else ('def' if d['kw'] in ('abbrev','opaque') else 'other')
        fields=[]
        if d['kw'] in ('structure','class'):
            fs=list(re.finditer(r'^([ \t]+)(«[^»]+»|[\w\'.]+)\s*(?=[:(])',code[d['sig_end']:b],re.M))
            if fs:
                indent=min(len(f[1]) for f in fs)
                fields=[(d['sig_end']+f.start(),f[2]) for f in fs if len(f[1])==indent]
        for i,(start,field) in enumerate(fields):
            end=fields[i+1][0] if i+1<len(fields) else b
            ms=list(HOLE.finditer(tokens,start,end)); occupied.update(m.start() for m in ms)
            if True:  # Retain proved fields for closed-versus-deleted accounting.
                rows.append(dict(name=name+'.'+field,kind='structure field',
                                 signature=s2.normalize(code[start:end].split(':=',1)[0]),
                                 proof=tokens[start:end],markers=sorted({m[0] for m in ms}),
                                 line=text.count('\n',0,start)+1))
        ms=[m for m in HOLE.finditer(tokens,a,b) if m.start() not in occupied]
        occupied.update(m.start() for m in ms)
        markers={m[0] for m in ms}
        if d['kw']=='axiom': markers.add('axiom')
        if markers and not d['name']: warnings.append('anonymous holed declaration: '+name)
        rows.append(dict(name=name,kind=kind,signature=s2.normalize(code[a:d['sig_end']]),
                         proof=tokens[d['sig_end']:b],markers=sorted(markers),line=text.count('\n',0,a)+1))
    for m in HOLE.finditer(tokens):
        if m.start() not in occupied:
            line=text.count('\n',0,m.start())+1
            rows.append(dict(name=f'<unattributed:{line}:{m.start()}>',kind='other',
                             signature='',proof='',markers=[m[0]],line=line))
            warnings.append(f'unattributed {m[0]} at line {line}')
    return rows,sorted(set(warnings))


_CAT=None

def read_blob(oid):
    global _CAT
    if _CAT is None:
        _CAT=subprocess.Popen(['git','-C',str(ROOT),'cat-file','--batch'],
                              stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    _CAT.stdin.write((oid+'\n').encode()); _CAT.stdin.flush()
    header=_CAT.stdout.readline().split()
    if len(header)!=3: raise ValueError('unavailable git blob '+oid)
    result=_CAT.stdout.read(int(header[2])); _CAT.stdout.read(1)
    return result


@functools.lru_cache(None)
def blob(oid):
    text=read_blob(oid).decode('utf-8')
    rows,errors=scan_text(text)
    try: imports=set(li._IMPORT.findall(mask(text)))
    except li.LexError as e: imports=set(); errors.append(str(e))
    return rows,imports,errors


def missing_gate(old, new):
    """Only supplement stage3_delivery: it already rejects parsed non-theorem
    holes and newly introduced forbidden keyword kinds. Catch admits (previously
    allowed), extra axioms when that keyword already existed, and lexer/field gaps.
    Called after its checks pass, so ordinary defects are not reported twice.
    """
    before, _ = scan_text(old or '')
    after, errors = scan_text(new)
    old_by = {r['name']:r for r in before}
    failures = []
    if any(r['markers']==['unavailable'] for r in after):
        return ['hole census cannot parse delivered source: '+'; '.join(errors)]
    for r in after:
        previous = old_by.get(r['name'])
        changed = previous is None or (r['proof'],r['signature']) != (previous['proof'],previous['signature'])
        if not changed: continue
        if 'admit' in r['markers']:
            failures.append(r['name']+': admit is forbidden; use a named theorem with sorry')
        if 'axiom' in r['markers'] and (previous is None or 'axiom' not in previous['markers']):
            failures.append(r['name']+': new axiom declaration is forbidden')
        if r['markers'] and r['kind'] in DEFECT:
            failures.append(r['name']+': new/changed hole inside '+r['kind']+' is forbidden (hollow data)')
        if r['markers'] and r['name'].startswith('<unattributed:'):
            failures.append(r['name']+': cannot attribute hole; leave holes only in named theorems')
    return sorted(set(failures))


def relevant(p):
    return (p.startswith(('lean/Sheaf/','lean/WeilConjectures/')) and p.endswith('.lean')) or p in (
        'lean/Sheaf.lean','lean/WeilConjectures.lean','lean/TargetsCheck.lean','lean/Challenge.lean')


def tree(ref):
    out={}
    for line in git('ls-tree','-r',ref).decode().splitlines():
        meta,p=line.split('\t',1)
        if relevant(p): out[p]=meta.split()[2]
    return out


def snapshot(files, previous=None, changed=None):
    if previous is None:
        imports,decls,errors={},{},{}
        changed=set(files)
    else:
        imports=previous['imports'].copy(); decls=previous['decls'].copy()
        errors=previous['errors'].copy()
        changed=set(changed)
        mods={p[5:-5].replace('/','.') for p in changed}
        decls={k:r for k,r in decls.items() if k[0] not in mods}
        for mod in mods:
            imports.pop(mod,None); errors.pop(mod,None)
    for p in sorted(changed):
        if p not in files: continue
        mod=p[5:-5].replace('/','.')
        try: rows,imps,errs=blob(files[p])
        except UnicodeError as e:
            rows,errs=scan_text('"'); imps=set(); errs.append(str(e))
        imports[mod]=imps; errors[mod]=[mod+': '+w for w in errs]
        if mod not in ('Challenge','TargetsCheck'):
            for r in rows: decls[mod,r['name']]=dict(r,module=mod)
    warnings=[w for mod in sorted(errors) for w in errors[mod]]
    dist,q={},collections.deque()
    for m in sorted(imports.get('TargetsCheck',())):
        if m in imports: dist[m]=0; q.append(m)
        elif m.startswith(('Sheaf.','WeilConjectures.')): warnings.append('missing target module '+m)
    while q:
        m=q.popleft()
        for n in sorted(imports.get(m,())):
            if n in imports and n not in dist: dist[n]=dist[m]+1; q.append(n)
            elif n.startswith(('Sheaf.','WeilConjectures.')) and n not in imports:
                warnings.append(m+': missing import '+n)
    return dict(decls=decls,imports=imports,dist=dist,warnings=sorted(set(warnings)),errors=errors,
                holes={k:r for k,r in decls.items() if r['markers']})


def holes(s,closure=False):
    h=s.get('holes')
    if h is None: h={k:r for k,r in s['decls'].items() if r['markers']}
    return {k:r for k,r in h.items() if k[0] in s['dist']} if closure else h


def delta(a,b,closure=False):
    ah,bh=holes(a,closure),holes(b,closure)
    closed=sorted(k for k in ah if k in b['decls'] and not b['decls'][k]['markers'])
    added=sorted(k for k in bh if k not in a['decls'] or not a['decls'][k]['markers'])
    return dict(closed=closed,added=added,net=len(closed)-len(added),
                changed=sorted(k for k in ah.keys() & bh.keys() if ah[k]['signature']!=bh[k]['signature']),
                deleted=sorted(k for k in ah if k not in b['decls']),
                pruned=sorted(a['dist'].keys()-b['dist'].keys()),entered=sorted(b['dist'].keys()-a['dist'].keys()))


def classify(d,a,b):
    if d['changed']: return 'moved'
    if d['closed'] and d['added'] and d['net']<=0:
        targets=set(d['added']); closed=set(d['closed'])
        helpers={k for k,r in b['decls'].items() if not r['markers'] and
                 (k not in a['decls'] or r['proof']!=a['decls'][k]['proof'])}
        def depends(k,seen):
            if k in seen: return False
            seen=seen|{k}; proof=b['decls'][k]['proof']
            reachable=li.closure(k[0],b['imports'],{})|{k[0]}
            for n in sorted(targets|closed|helpers):
                if n[0] in reachable and re.search(r"(?<![\w'])"+re.escape(n[1].split('.')[-1])+r"(?![\w'])",proof):
                    if n in targets or depends(n,seen): return True
            return False
        if all(depends(k,set()) for k in d['closed']): return 'moved'
    if any(k[0] in d['pruned'] for k in holes(a)): return 'pruned'
    if d['closed'] and d['added']: return 'decomposed'
    if d['closed'] and not (d['added'] or d['changed'] or d['deleted']): return 'proved'
    return 'other'


def history(since,head):
    files=tree(since); a=snapshot(files); out=[]
    logs=git('log','--first-parent','--reverse','--format=%H%x09%s',since+'..'+head).decode()
    for line in logs.splitlines():
        commit,subject=line.split('\t',1); touched=set()
        for raw in git('diff-tree','--no-commit-id','--raw','-r','--no-renames',commit+'^',commit).decode().splitlines():
            meta,p=raw.split('\t',1)
            if relevant(p):
                touched.add(p); oid=meta.split()[3]
                if set(oid)=={'0'}: files.pop(p,None)
                else: files[p]=oid
        b=snapshot(files,a,touched) if touched else a
        if subject.startswith('Prove '):
            d=delta(a,b); m=re.search(r'\(([^,()]+)(?:, reviewed by ([^()]+))?\)',subject)
            out.append(dict(commit=commit,subject=subject,group=m[1] if m else '<unknown>',
                            reviewer=(m[2] or '<unspecified>') if m else '<unknown>',
                            classification=classify(d,a,b),delta=d,closure_delta=delta(a,b,True),warnings=sorted(set(b['warnings'])-set(a['warnings']))))
        a=b
    return out


def census(s):
    h,c=holes(s),holes(s,True)
    return dict(unit='one per holed declaration; deleted is not proved',library=len(h),closure=len(c),
                definitions=sum(r['kind'] in DEFECT for r in h.values()),
                roots={root:dict(library=sum(k[0].split('.')[0]==root for k in h),
                                 closure=sum(k[0].split('.')[0]==root for k in c)) for root in ('Sheaf','WeilConjectures')},
                rows=sorted(h.values(),key=lambda r:(r['kind'] not in DEFECT,r['module'],r['name'])),warnings=s['warnings'])


def report(head, output=None):
    output=output or ROOT/'coord'
    s=snapshot(tree(head)); now=census(s); baselines=[]
    try: landings=history(BASELINES[0][0],head)
    except subprocess.CalledProcessError:
        landings=[]; now['warnings'].append('landing history unavailable: stage-3 baseline missing')
    for ref,reason in BASELINES:
        try:
            old=snapshot(tree(ref)); row=dict(ref=ref,reason=reason,library=delta(old,s))
            if ref==BASELINES[1][0]: row['closure']=delta(old,s,True)
            baselines.append(row)
        except subprocess.CalledProcessError: baselines.append(dict(ref=ref,reason=reason,unavailable='commit unavailable'))
    groups={}; classes=collections.Counter(l['classification'] for l in landings)
    for l in landings:
        g=groups.setdefault(l['group'],collections.Counter()); g['landings']+=1
        g['moved']+=l['classification']=='moved'
        for key in ('closed','added'): g[key]+=len(l['delta'][key])
    lines=['# Sorry ledger','','Source scan; one hole per declaration, regardless of token count. Deleted declarations are not proofs.',
           'Closure is the queue’s import upper bound. Classes use source references, not elaborated dependencies.',
           'Progress = closed − added in the closure, with pruning reported separately.','',
           f"Holes now: library **{now['library']}**, closure **{now['closure']}**, in definitions **{now['definitions']}**.",'',
           '| root | library | closure |','|---|---:|---:|']
    for root,r in now['roots'].items(): lines.append(f"| {root} | {r['library']} | {r['closure']} |")
    lines+=['','| baseline | scope | closed | added | net | deleted | changed holed statements |','|---|---|---:|---:|---:|---:|---:|']
    for r in baselines:
        if 'unavailable' in r:
            lines.append(f"| {r['ref']} | unavailable: {r['unavailable']} | | | | | |"); continue
        for scope in ('library','closure'):
            if scope in r:
                d=r[scope]; lines.append(f"| {r['ref']} ({r['reason']}) | {scope} | {len(d['closed'])} | {len(d['added'])} | {d['net']} | {len(d['deleted'])} | {len(d['changed'])} |")
    lines+=['','No closure delta is quoted across 660345513: proof-dependency imports changed the reached set.','',
            '| landing class | count |','|---|---:|']
    for cl in ('proved','decomposed','moved','pruned','other'): lines.append(f'| {cl} | {classes[cl]} |')
    lines+=['','Per group: whole-library closed/added/net since stage 3; landing count is not progress. Closure progress is shown only after the imports baseline.','',
            '| group | landings | closed | added | net | moved share |','|---|---:|---:|---:|---:|---:|']
    for g,r in sorted(groups.items()):
        lines.append(f"| {g} | {r['landings']} | {r['closed']} | {r['added']} | {r['closed']-r['added']} | {r['moved']}/{r['landings']} ({r['moved']/r['landings']:.1%}) |")
    claims={}
    for raw in git('ls-tree','-r',head,'coord/claims').decode().splitlines():
        meta,p=raw.split('\t',1)
        if not p.endswith('.lock'): continue
        try: claims[pathlib.Path(p).stem]=json.loads(read_blob(meta.split()[2])).get('who','—')
        except (ValueError,TypeError): now['warnings'].append('unreadable claim: '+p)
    modules=collections.Counter(k[0] for k in holes(s,True))
    lines+=['','Nearest targets (claims from the scanned git tree; live leases may differ):','',
            '| module | distance | holes | group |','|---|---:|---:|---|']
    for m in sorted(modules,key=lambda m:(s['dist'][m],m))[:20]:
        lines.append(f"| {m} | {s['dist'][m]} | {modules[m]} | {claims.get(m,'—')} |")
    lines+=['','Definitions with holes (def/instance/structure field):','']
    defects=[f"- `{r['module']}::{r['name']}` ({r['kind']}, line {r['line']})" for r in now['rows'] if r['kind'] in DEFECT]
    lines+=defects or ['None.']
    pruned=sorted(set(m for r in baselines if 'closure' in r for m in r['closure']['pruned']))
    lines+=['','Modules pruned since the imports baseline:','']+([f'- `{m}`' for m in pruned] or ['None.'])
    lines+=['','Scanner limitations: macro-generated declarations, elaborated anonymous/private names, and tactic dependencies cannot be recovered from source. Synthetic names are source keys, not elaborated names.','','Diagnostics:','']
    lines+=['- '+w for w in sorted(set(now['warnings']))] or ['None.']
    machine=['record\tscope\tmodule\tdeclaration\tkind\tvalue\tdetail']
    def add(*cols): machine.append('\t'.join(str(c).replace('\t',' ').replace('\n',' ') for c in cols))
    for r in now['rows']:
        add('hole','closure' if r['module'] in s['dist'] else 'library',r['module'],r['name'],r['kind'],1,','.join(r['markers']))
    for r in baselines:
        for scope in ('library','closure'):
            if scope in r:
                for key in ('closed','added','changed','deleted','pruned','entered'):
                    for k in r[scope][key]: add('baseline',scope,k[0] if isinstance(k,tuple) else k,k[1] if isinstance(k,tuple) else '',key,1,r['ref'])
        if 'unavailable' in r: add('unavailable','','','','',r['ref'],r['unavailable'])
    for l in landings: add('landing','library','',l['commit'],l['classification'],l['delta']['net'],json.dumps(l,sort_keys=True,ensure_ascii=False))
    for w in sorted(set(now['warnings'])): add('diagnostic','','','','','',w)
    (output/'sorry-ledger.tsv').write_text('\n'.join(machine)+'\n')
    (output/'sorry-ledger.md').write_text('\n'.join(lines)+'\n')
    return dict(now={k:v for k,v in now.items() if k!='rows'},baselines=baselines,classes=dict(sorted(classes.items())),groups=groups)


def post_build():
    """Generate without locks; commit only if the green build and input tree
    remain unchanged. Later landings do not change the pinned green input.
    Only the two generated files are staged. Lock covers verification + commit.
    """
    last=ROOT/'local/builds/last.json'
    try: build=json.loads(last.read_text())
    except (OSError,ValueError): return {'skipped':'no build result'}
    if build.get('result')!='green': return {'skipped':'last build is not green'}
    head=build.get('commit')
    if not head: return {'skipped':'green build has no commit'}
    # Pin to the green snapshot: autoland may start writing the next batch while
    # scanning. Newer landings are reported after their own green build.
    with tempfile.TemporaryDirectory(prefix='sorry-ledger-',dir=ROOT/'local') as tmp:
        output=pathlib.Path(tmp); result=report(head,output)
        with (ROOT/'coord/.merge.lock').open('a') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX)
            if json.loads(last.read_text())!=build:
                return {'skipped':'build moved while scanning; next green cycle retries'}
            paths=['coord/sorry-ledger.tsv','coord/sorry-ledger.md']
            changed=False
            for p in paths:
                dest=ROOT/p; data=(output/dest.name).read_bytes()
                if not dest.exists() or dest.read_bytes()!=data:
                    os.replace(output/dest.name,dest); changed=True
            if changed:
                subprocess.run(['git','-C',str(ROOT),'add','--',*paths],check=True)
                # --only excludes unrelated staged changes from a live checkout.
                subprocess.run(['git','-C',str(ROOT),'commit','--only','-m',
                    'Refresh source sorry ledger after green build\n\n'
                    'Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>',
                    '--',*paths],check=True)
            return {'changed':changed,'summary':result}


def main():
    p=argparse.ArgumentParser(description=__doc__); sub=p.add_subparsers(dest='command',required=True)
    c=sub.add_parser('census'); c.add_argument('commit',nargs='?',default='HEAD')
    d=sub.add_parser('delta'); d.add_argument('base'); d.add_argument('head')
    l=sub.add_parser('landings'); l.add_argument('--since',default=BASELINES[0][0])
    r=sub.add_parser('report'); r.add_argument('--commit',default='HEAD'); r.add_argument('--post-build',action='store_true')
    args=p.parse_args()
    if args.command=='census': result=census(snapshot(tree(args.commit)))
    elif args.command=='delta': result=delta(snapshot(tree(args.base)),snapshot(tree(args.head)))
    elif args.command=='landings': result=history(args.since,'HEAD')
    else: result=post_build() if args.post_build else report(args.commit)
    print(json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2))


if __name__=='__main__': main()
