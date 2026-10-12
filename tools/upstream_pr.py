#!/usr/bin/env python3
"""Cut second-level blueprint units into reviewable upstream trees; never push.

Mapping: Sheaf.<topic>.<name> -> WeilConjectures/<topic>/<name>.lean.
Counts are source evidence from sorry_ledger, not transitive axiom certification.
"""
from __future__ import annotations
import argparse, collections, json, pathlib, re, shutil, subprocess, sys, tempfile
import sorry_ledger as ledger
import stage2_delivery as parser
ROOT = pathlib.Path(__file__).resolve().parent.parent
IMPORT = re.compile(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)', re.M)
BASE = '7d675a263'
HEADER = '''/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/'''


def path(module):
    return pathlib.Path(module.replace('.', '/') + '.lean')


def mapped(module):
    return 'WeilConjectures.' + module.removeprefix('Sheaf.') if module.startswith('Sheaf.') else module


def scan(text):
    rows, warnings = ledger.scan_text(text)
    if warnings:
        raise ValueError('ledger scanner: ' + '; '.join(warnings))
    return rows


def git(tree, *args):
    p = subprocess.run(['git', '-C', str(tree), *args], capture_output=True, text=True)
    if p.returncode:
        raise ValueError(p.stderr.strip())
    return p.stdout


def inventory(upstream):
    units = {p.stem: json.loads(p.read_text()) for p in sorted((ROOT/'dag/units').glob('*.json'))}
    nodes = [json.loads(p.read_text()) for p in sorted((ROOT/'dag/nodes').rglob('*.json'))]
    modules = {}; owners = collections.defaultdict(set)
    for n in nodes:
        m = (n.get('lean') or {}).get('module')
        if m and isinstance(m, str) and (ROOT/'lean'/path(m)).is_file() and m.startswith(('Sheaf.', 'WeilConjectures.')):
            modules.setdefault(m, (ROOT/'lean'/path(m)).read_text())
            if n.get('unit') in units:
                owners[m].add(n['unit'])
    # Imports may include support files not explicitly attached to nodes.
    todo = list(modules)
    while todo:
        for m in IMPORT.findall(modules[todo.pop()]):
            p = ROOT/'lean'/path(m)
            if m.startswith('Sheaf.') and m not in modules and p.is_file():
                modules[m] = p.read_text(); todo.append(m)
    available = {'.'.join(p.relative_to(upstream).with_suffix('').parts) for p in (upstream/'WeilConjectures').rglob('*.lean')}
    destinations = {}
    # A merged mapping is authoritative only when the destination really exists.
    mapfile = ROOT/'coord/upstream-pr-map.tsv'
    if mapfile.exists():
        for line in mapfile.read_text().splitlines()[1:]:
            m, p, _, state = line.split('\t')
            if state == 'merged' and (upstream/p).is_file():
                available.add(m); destinations[m] = p[:-5].replace('/', '.')
    out = {}
    for u, unit in sorted(units.items()):
        ns = [n for n in nodes if n.get('unit') == u]
        ms = sorted({(n.get('lean') or {}).get('module') for n in ns} & modules.keys())
        ms = [m for m in ms if m.startswith('Sheaf.') and m not in available or
              m.startswith('WeilConjectures.') and (upstream/path(m)).is_file() and
              modules[m] != (upstream/path(m)).read_text()]
        rows = [r for m in ms for r in scan(modules[m])]
        deps = sorted({d for m in ms for d in IMPORT.findall(modules[m])
                       if d.startswith(('Sheaf.', 'WeilConjectures.')) and d not in available and d not in ms})
        out[u] = dict(section=u, chapter=unit.get('chapter'), title=unit.get('title'),
                      nodes=[dict(id=n['id'], module=(n.get('lean') or {}).get('module'),
                                  declaration=(n.get('lean') or {}).get('declaration'),
                                  existing=(n.get('lean') or {}).get('existing', False),
                                  upstream=n.get('lean_audit', {}).get('slopmaster2', {})) for n in ns],
                      modules=ms, declarations=len(rows), proved=sum(not r['markers'] and r['kind'] != 'structure field' for r in rows),
                      fields=sum(r['kind'] == 'structure field' for r in rows),
                      holes=sum(bool(r['markers']) for r in rows),
                      lines=sum(len(modules[m].splitlines()) for m in ms),
                      import_modules=deps, dependencies=sorted({v for d in deps for v in owners[d] if v != u}),
                      unassigned_imports=[d for d in deps if not owners[d]])
    emitted=set(); order=[]
    while True:
        ready=[u for u in sorted(out) if u not in emitted and not out[u]['unassigned_imports'] and
               all(d in emitted for d in out[u]['dependencies'])]
        if not ready: break
        for u in ready:
            out[u]['ready']=True; out[u]['order']=len(order); order.append(out[u]); emitted.add(u)
    for u in sorted(set(out)-emitted):
        out[u]['ready']=False; out[u]['order']=None; order.append(out[u])
    # A module attached to multiple blueprint units is exported only by its
    # earliest unit in dependency order. Persisted assignment wins on later scans.
    rank = {s['section']: i for i, s in enumerate(order)}
    assigned = {}
    if mapfile.exists():
        for line in mapfile.read_text().splitlines()[1:]:
            fields = line.split('\t')
            if len(fields) == 4 and fields[2] in out:
                assigned[fields[0]] = fields[2]
    for m, units_for_module in owners.items():
        assigned.setdefault(m, min(units_for_module, key=lambda u: (rank.get(u, len(rank)), u)))
    for s in order:
        s['modules'] = [m for m in s['modules'] if assigned.get(m, s['section']) == s['section']]
        rows = [r for m in s['modules'] for r in scan(modules[m])]
        s.update(declarations=len(rows),
                 proved=sum(not r['markers'] and r['kind'] != 'structure field' for r in rows),
                 holes=sum(bool(r['markers']) for r in rows),
                 fields=sum(r['kind'] == 'structure field' for r in rows),
                 lines=sum(len(modules[m].splitlines()) for m in s['modules']))
    owners = {m: {u} for m, u in assigned.items()}
    return order, modules, owners, available, destinations


def rewrite(text, mapping, header=False):
    if header:
        text = re.sub(r'\A/-.*?-/\s*', HEADER+'\n', text, count=1, flags=re.S)
    # Only module references, including comments containing module names.
    text = re.sub(r'\bSheaf\.[A-Za-z0-9_.\u0027]+', lambda m: mapping.get(m[0], m[0]), text)
    # Remove operational comments, but retain mathematical source docstrings.
    parts = list(ledger.segments(text))
    for kind,a,b in reversed(parts):
        if kind in ('line','block') and re.search(r'\b(?:SHEAF|sheaf-dag|stage [123]|landing|sandbox|worker|pipeline|group [A-Z][0-9]|STATEMENT-DISPUTED)\b',text[a:b]):
            raise ValueError('operational comment requires manual mathematical rewrite: '+text[a:b][:180])
    return text


def merge_file(upstream, module, ours, selected, mapping):
    """Apply changed declaration bodies only when upstream still equals the historical base.

    Refuse changed signatures, missing declarations and unclassified non-import changes.
    A declaration changed upstream is retained and explicitly reported.
    """
    p = path(module); theirs=(upstream/p).read_text()
    try: base=git(upstream,'show',BASE+':'+str(p))
    except ValueError as e: raise ValueError(f'{p}: historical base {BASE} unavailable; use a git checkout with history') from e
    bd={d['name']:d for d in parser.declarations(ledger.mask(base))}
    od={d['name']:d for d in parser.declarations(ledger.mask(ours))}
    td={d['name']:d for d in parser.declarations(ledger.mask(theirs))}
    def residual(text, decls):
        chars=list(ledger.mask(text))
        for d in decls.values(): chars[d['kw_pos']:d['end']]=' '*(d['end']-d['kw_pos'])
        return ' '.join(re.sub(r'^\s*(?:(?:public|private|meta)\s+)*import[^\n]*', '', ''.join(chars), flags=re.M).split())
    if residual(ours, od) != residual(base, bd):
        raise ValueError(f'{p}: non-declaration/non-import changes need manual review')
    edits=[]; kept=[]; accepted=[]
    for name,d in od.items():
        if name not in bd:
            raise ValueError(f'{p}: new declaration {name} needs a separate module')
        b=bd[name]; old=base[b['kw_pos']:b['end']]; new=ours[d['kw_pos']:d['end']]
        if old == new: continue
        if name not in td: kept.append(name+' (removed upstream)'); continue
        t=td[name]; current=theirs[t['kw_pos']:t['end']]
        if current != old: kept.append(name+' (changed upstream)'); continue
        if ledger.mask(base[b['kw_pos']:b['sig_end']]).strip() != ledger.mask(ours[d['kw_pos']:d['sig_end']]).strip():
            raise ValueError(f'{p}: signature changed: {name}')
        edits.append((t['kw_pos'],t['end'],new)); accepted.append(name)
    for a,b,new in sorted(edits,reverse=True): theirs=theirs[:a]+new+theirs[b:]
    # Only selected imports enter this PR; imports for unrelated proofs stay out.
    added=[m for m in IMPORT.findall(ours) if m in selected|set(mapping) and m not in IMPORT.findall(theirs)]
    if added and (accepted or not kept):
        last=list(IMPORT.finditer(theirs))[-1].end()
        theirs=theirs[:last]+''.join('\nimport '+mapping[m] for m in sorted(added))+theirs[last:]
    return rewrite(theirs,mapping), kept, accepted


def cut(args):
    up=args.upstream.resolve(); out=args.out.resolve()
    order,mods,owners,available,destinations=inventory(up); sections={s['section']:s for s in order}
    if args.section not in sections: raise ValueError('unknown section '+args.section)
    s=sections[args.section]
    unit_names = [args.section] + (getattr(args, 'also', None) or [])
    if any(u not in sections for u in unit_names): raise ValueError('unknown grouped section')
    if any(sections[u]['chapter'] != s['chapter'] for u in unit_names):
        raise ValueError('cannot group across blueprint chapters')
    selected = {m for u in unit_names for m in sections[u]['modules']}
    module_file = getattr(args, 'modules_file', None)
    if module_file:
        requested = {l.strip() for l in module_file.read_text().splitlines() if l.strip()}
        if not requested <= selected:
            raise ValueError('module filter contains modules outside assigned sections: ' + ', '.join(sorted(requested-selected)))
        selected = requested
    todo=list(selected)
    while todo:
        m=todo.pop()
        for d in IMPORT.findall(mods[m]):
            if d.startswith(('Sheaf.', 'WeilConjectures.')) and d not in available and d not in selected:
                if not args.with_deps: raise ValueError('missing dependency: '+d+' (use --with-deps)')
                if d not in mods: raise ValueError('missing source: '+d)
                selected.add(d);todo.append(d)
    mapping={m:destinations.get(m, mapped(m)) for m in selected|available if m.startswith('Sheaf.')}
    collisions=sorted(str(path(mapping[m])) for m in selected if m.startswith('Sheaf.') and (up/path(mapping[m])).exists())
    if collisions: raise ValueError('path collisions (nothing written):\n'+'\n'.join(collisions))
    if out.exists(): raise ValueError('output already exists: '+str(out))
    # Prepare everything before creating the output tree.
    files={}; retained=[]; accepted=[]
    for m in sorted(selected):
        if m.startswith('Sheaf.'):
            files[str(path(mapping[m]))]=rewrite(mods[m],mapping,True)
        else:
            t,keep,take=merge_file(up,m,mods[m],selected,mapping)
            if t != (up/path(m)).read_text(): files[str(path(m))]=t
            retained.extend(m+': '+n for n in keep);accepted.extend(m+': '+n for n in take)
    # Apply our proofs in upstream files associated with this unit, not unrelated consumers.
    root=(up/'WeilConjectures.lean').read_text()
    imports=set(IMPORT.findall(root))|{p[:-5].replace('/','.') for p in files}
    root=root.split('\npublic import ',1)[0].rstrip()+'\n\n'+''.join('public import '+m+'\n' for m in sorted(imports))
    files['WeilConjectures.lean']=root
    shutil.copytree(up,out,ignore=shutil.ignore_patterns('.git','.lake','.sandbox'))
    for p,t in files.items():
        dest=out/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(t)
    rows=[r for p,t in files.items() if p!='WeilConjectures.lean' for r in scan(t)]
    ns=sorted({n['id']:n for unit in order for n in unit['nodes'] if n['module'] in selected}.values(), key=lambda n:n['id'])
    omitted=[n['id'] for n in s['nodes'] if not n['module'] and n['upstream'].get('state') != 'closed']
    tags=sorted(set(re.findall(r'(?:Tag|tag/)\s*([0-9A-Z]{4})','\n'.join(files.values()))))
    description=(f"feat({s['chapter'].removeprefix('sec-')}): {s['title']}\n\n"
                 f"Add definitions and statements for blueprint sections {', '.join('`'+u+'`' for u in unit_names)} ({s['title']}).\n\n"
                 f"Covers {len(selected)} modules and {len(rows)} declarations: "
                 f"{sum(not r['markers'] and r['kind'] != 'structure field' for r in rows)} without direct holes, "
                 f"{sum(bool(r['markers']) for r in rows)} with `sorry`, "
                 f"{sum(r['kind'] == 'structure field' for r in rows)} structure fields. Definitions count as stated "
                 "declarations; these counts do not certify transitive proof dependencies.\n\n"
                 'Blueprint nodes: '+', '.join('`'+n['id']+'`' for n in ns)+'.\n\n'
                 'Stacks tags: '+(', '.join(tags) or 'none')+'.\n\n'
                 'Deliberately left: other blueprint sections'+(' and nodes without Lean declarations: '+', '.join(omitted) if omitted else '')+'.\n')
    if retained:description+='\nUpstream declarations retained: '+ '; '.join(retained)+'.\n'
    description+='\n🤖 Generated with [Claude Code](https://claude.com/claude-code)\n'
    (out/'PR.md').write_text(description)
    metadata=dict(section=args.section,sections=unit_names,base_files=sorted(str(p.relative_to(up)) for p in up.rglob('*') if p.is_file() and '.git' not in p.relative_to(up).parts and '.lake' not in p.relative_to(up).parts),files=sorted(files),new_files=sorted(p for p in files if not (up/p).exists()),
                  retained=retained,accepted=accepted,mapping={m:str(path(mapping[m])) for m in sorted(selected) if m in mapping})
    # Metadata stays outside the prospective PR tree.
    out.with_suffix('.cut.json').write_text(json.dumps(metadata,indent=2)+'\n')
    mapfile=ROOT/'coord/upstream-pr-map.tsv';mapfile.parent.mkdir(exist_ok=True)
    existing={}
    if mapfile.exists():
        for line in mapfile.read_text().splitlines()[1:]:existing[line.split('\t')[0]]=line
    for m,p in metadata['mapping'].items():existing[m]='\t'.join((m,p,next(iter(owners.get(m,{args.section}))), 'prepared'))
    mapfile.write_text('module\tupstream_path\tsection\tpr_state\n'+'\n'.join(existing[m] for m in sorted(existing))+'\n')
    print(json.dumps(metadata,indent=2))


def check(directory):
    directory=directory.resolve(); metadata=directory.with_suffix('.cut.json')
    if metadata.exists():
        data=json.loads(metadata.read_text()); files=data['files']
        if 'base_files' in data:
            allowed=set(data['base_files'])|set(files)|{'PR.md'}
            extra=[str(p.relative_to(directory)) for p in directory.rglob('*') if p.is_file()
                   and not any(x in p.relative_to(directory).parts for x in ('.git','.lake','.lbuild'))
                   and str(p.relative_to(directory)) not in allowed]
            if extra:
                print('unexpected PR files: '+', '.join(sorted(extra))); return True
    else:
        files=git(directory,'diff','--name-only','HEAD^','HEAD').splitlines()
    errors=[]; root=set(IMPORT.findall((directory/'WeilConjectures.lean').read_text()))
    for p in sorted((directory/'WeilConjectures').rglob('*.lean')):
        if '.'.join(p.relative_to(directory).with_suffix('').parts) not in root: errors.append(f'{p.relative_to(directory)}: missing root import')
    for rel in files:
        if rel != 'WeilConjectures.lean' and (not rel.startswith('WeilConjectures/') or not rel.endswith('.lean')):
            errors.append(rel+': forbidden PR file');continue
        t=(directory/rel).read_text(); code=ledger.mask(t);rows=scan(t)
        for r in rows:
            if 'axiom' in r['markers']:errors.append(f"{rel}:{r['line']}: axiom")
            if r['markers'] and r['kind'] not in ('theorem','lemma'):errors.append(f"{rel}:{r['line']}: hole in {r['kind']}")
            sig=r['signature'];proof=r['proof']
            if re.search(r':\s*True\s*$',sig) or re.search(r'[({⦃][^)}⦄]*:\s*False\s*[)}⦄]',sig) or re.search(r'∃[^,]*,\s*True\s*$',sig):
                errors.append(f"{rel}:{r['line']}: obviously vacuous statement")
            if r['kind'] in ('theorem','lemma') and re.fullmatch(r'\s*(?::=)?\s*(?:by\s+)?trivial\s*',proof):
                errors.append(f"{rel}:{r['line']}: trivial body requires statement review")
        for pattern,label in [(r'(?<![\w.])Sheaf\.', 'old module reference'),
          (r'\b(?:SHEAF|DAG|sheaf-dag|pipeline|sandbox|landing|worker|stage[- ][123]|group [A-Z][0-9]+|STATEMENT-DISPUTED)\b|(?:coord|dag|tools|stages)/','process vocabulary'),
          (r'(?:\b(?:\d{1,3}\.){3}\d{1,3}\b|BEGIN .*PRIVATE KEY|[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}|gh[pousr]_[A-Za-z0-9]+|ssh-(?:rsa|ed25519))','address/key pattern')]:
            if re.search(pattern,t):errors.append(rel+': '+label)
        for i,l in enumerate(t.splitlines(),1):
            if len(l)>100 and not IMPORT.match(l): errors.append(f'{rel}:{i}: line exceeds 100 columns ({len(l)})')
    print('\n'.join(errors) if errors else f'PASS: root coverage and static checks ({len(files)} affected files)')
    return bool(errors)


def main():
    p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='command',required=True)
    q=sub.add_parser('sections');q.add_argument('--upstream',type=pathlib.Path,required=True);q.add_argument('--json',action='store_true')
    q=sub.add_parser('cut');q.add_argument('section');q.add_argument('--also',action='append',default=[],help='another section of the same chapter');q.add_argument('--modules-file',type=pathlib.Path,help='exact module subset for a planned layer');q.add_argument('--with-deps',action='store_true');q.add_argument('--upstream',type=pathlib.Path,required=True);q.add_argument('--out',type=pathlib.Path,required=True)
    q=sub.add_parser('check');q.add_argument('directory',type=pathlib.Path)
    a=p.parse_args()
    try:
        if a.command=='cut':cut(a)
        elif a.command=='check':return check(a.directory)
        else:
            rows=inventory(a.upstream)[0]
            if a.json: print(json.dumps(rows,indent=2,ensure_ascii=False))
            else:
                print('section\tready\tmodules\tproved\tholes\tfields\tlines\tdependencies\tnodes\tmodule_names\timport_modules\texisting_upstream')
                for s in rows:
                    print('\t'.join(map(str,[s['section'],s['ready'],len(s['modules']),s['proved'],s['holes'],s['fields'],s['lines'],','.join(s['dependencies']+s['unassigned_imports']), ','.join(n['id'] for n in s['nodes']), ','.join(s['modules']), ','.join(s['import_modules']), ','.join(n['id']+':'+str(n['existing'])+'/'+n['upstream'].get('state','none') for n in s['nodes'])])))
    except (ValueError, OSError) as e: print(str(e),file=sys.stderr);return 2
    return 0


if __name__=='__main__':sys.exit(main())
