#!/usr/bin/env python3
"""Turn the sheaf DAG into text-only blueprint changes."""
from __future__ import annotations
import argparse, collections, json, pathlib, re, shutil, sys
try:
 import tomllib
except ImportError: tomllib=None
ROOT=pathlib.Path(__file__).resolve().parents[1]
DAG=ROOT/'dag'/'nodes'
FORBIDDEN=re.compile(r'(?i)(delivery|landing|stage\s*[0-9]|sheaf-dag|blueprint_pr|upstream-bp|43\.131\.49\.250|weil_formal|noreply@|token|secret)')

def nodes():
 out={}
 for f in DAG.rglob('*.json'):
  try:
   d=json.loads(f.read_text()); out[d['id']]=d
  except Exception: continue
 return out

def treepath(tree):
 t=pathlib.Path(tree)
 if (t/'.git').exists(): return t
 # accept bare repositories
 if (t/'HEAD').exists() and not (t/'blueprint').exists():
  import subprocess
  x=pathlib.Path('/tmp/bp-tree-'+str(__import__('os').getpid())); x.mkdir(exist_ok=True)
  subprocess.run(['git','--git-dir',str(t),'archive','blueprint-main'],stdout=open(x/'a.tar','wb'),check=True)
  shutil.unpack_archive(str(x/'a.tar'),str(x)); return x
 return t

def bpindex(tree):
 r={}; base=tree/'blueprint'
 for f in base.rglob('*'):
  if f.suffix not in ('.md',): continue
  if f.name.endswith('.proof.md'): continue
  m=re.search(r'(?m)^id\s*=\s*"([^"]+)"', f.read_text(errors='ignore'))
  if m:r[m.group(1)]=f
 return r

def sketch_of(d): return d.get('unit') or ''
def layer2(path):
 try:
  rel=path.relative_to(path.parents[2])
 except Exception:return False
 parts=path.parts
 return path.name=='_section.md' or any(p.startswith('sk-') for p in parts[-2:]) and path.name=='_section.md'

def diff(args):
 ns=nodes(); bp=bpindex(treepath(args.blueprint)); counts=collections.Counter(); rows=[]
 for i,d in sorted(ns.items()):
  ch=d.get('chapter','unknown'); p=bp.get(i)
  if d.get('blueprint',{}).get('is') is None: counts[(ch,'new:'+d.get('kind','?'))]+=1; rows.append((ch,sketch_of(d),'new',i,d.get('kind','')))
  elif d.get('statement_change'):
   if p and layer2(p): counts[(ch,'statement-correction-ASK')]+=1; rows.append((ch,sketch_of(d),'ask-statement',i,d.get('kind','')))
   else: counts[(ch,'statement-correction')]+=1; rows.append((ch,sketch_of(d),'statement',i,d.get('kind','')))
  elif d.get('proof') and p: counts[(ch,'changed-proof')]+=1; rows.append((ch,sketch_of(d),'proof',i,d.get('kind','')))
 print('COUNTS')
 for (ch,k),n in sorted(counts.items()): print(f'{ch}\t{k}\t{n}')
 print('TOTAL\t',sum(counts.values()))
 for r in rows: print('\t'.join(r))

def fm(fields):
 lines=['+++']
 for k,v in fields:
  if isinstance(v,list): lines.append(f'{k} = ['+', '.join(json.dumps(x) for x in v)+']')
  else: lines.append(f'{k} = {json.dumps(v,ensure_ascii=False)}')
 lines += ['+++','']; return '\n'.join(lines)

def link(i): return f'[{i}]({i})'
def render_node(d, proof=False):
 fields=[('id',d['id']),('kind','proof' if proof else ('theorem' if d.get('kind') in ('statement','lemma') else d.get('kind','definition')))]
 if proof: fields=[('kind','proof'),('of',d['id'])]
 else:
  if d.get('title'): fields.append(('title',d['title']))
  if d.get('lean',{}).get('declaration'): fields.append(('lean',[d['lean']['declaration']]))
  uses=d.get('stmt_deps') or []
  if uses: fields.append(('uses',uses))
 s=fm(fields)
 if proof:
  for st in d.get('proof',[]):
   text=st.get('text','')
   for u in st.get('uses',[]): text += f' ({link(u)})'
   s+=text+'\n\n'
 else:
  s+=d.get('statement','').strip()+'\n'
  if d.get('source'):
   src=d['source']; s+='\nSource: '+str(src.get('document',''))+' ('+str(src.get('place',''))+').\n'
  if d.get('proof'): s+='\n'
 return s

def cut(args):
 ns=nodes(); tree=treepath(args.blueprint); bp=bpindex(tree); out=pathlib.Path(args.out); out.mkdir(parents=True,exist_ok=True)
 chapters={args.chapter}; selected=[]
 for i,d in ns.items():
  if d.get('chapter')!=args.chapter: continue
  if args.sketch and sketch_of(d)!=args.sketch: continue
  selected.append((i,d))
 # copy blueprint chapter into output so check sees complete tree
 src=tree/'blueprint'
 if src.exists(): shutil.copytree(src,out/'blueprint',dirs_exist_ok=True)
 ask=[]
 for i,d in sorted(selected):
  b=d.get('blueprint',{}); p=bp.get(i)
  if b.get('is') and d.get('statement_change'):
   if p and layer2(p): ask.append(f'{i}: statement correction requested — {d.get("statement_change")}'); continue
   if p:
    rel=p.relative_to(tree/'blueprint'); dest=out/'blueprint'/rel.parent/i/'_section.md'; dest.parent.mkdir(parents=True,exist_ok=True)
    text=render_node(d); 
    if dest.exists() and dest.read_text()==text: continue
    dest.write_text(text)
  elif b.get('is') and d.get('proof') and p and not layer2(p):
   pr=p.with_name(p.stem+'.proof.md')
   if pr.exists():
    rel=pr.relative_to(tree/'blueprint'); dest=out/'blueprint'/rel; dest.parent.mkdir(parents=True,exist_ok=True); text=render_node(d,True)
    if not dest.exists() or dest.read_text()!=text: dest.write_text(text)
  elif b.get('is') is None:
   anc=b.get('from',{}).get('node'); ap=bp.get(anc) if anc else None
   if ap:
    rel=ap.relative_to(tree/'blueprint'); parent=rel.parent/(anc if d.get('blueprint',{}).get('from',{}).get('via') else '')
    if parent.name=='': parent=rel.parent
   else: parent=pathlib.Path(args.chapter)/(sketch_of(d) or 'unplaced')
   dest=out/'blueprint'/parent/f'{i}.md'; dest.parent.mkdir(parents=True,exist_ok=True); text=render_node(d)
   if not dest.exists() or dest.read_text()!=text: dest.write_text(text)
   if d.get('proof'):
    pr=dest.with_name(i+'.proof.md'); pt=render_node(d,True)
    if not pr.exists() or pr.read_text()!=pt: pr.write_text(pt)
 if ask:
  (out/'ASK.md').write_text('\n'.join(ask)+'\n')
 print('WROTE',len(selected),'DAG NODES to',out)

def check(args):
 root=pathlib.Path(args.dir); base=root/'blueprint'; ids={}; errs=[]
 files=[]
 for f in base.rglob('*.md'):
  if f.name.endswith('.proof.md'): continue
  txt=f.read_text(errors='replace'); m=re.search(r'(?m)^id\s*=\s*"([^"]+)"',txt)
  if not m: continue
  i=m.group(1); files.append((f,txt,i))
  if i in ids: errs.append(f'duplicate id {i}')
  ids[i]=f
 for f,txt,i in files:
  if FORBIDDEN.search(txt): errs.append(f'forbidden text in {f}')
  if txt.count('$$')%2 or txt.count('$')%2: errs.append(f'unbalanced TeX in {f}')
  for key in ('uses','of'):
   mm=re.search(rf'(?m)^{key}\s*=\s*(\[[^\n]*\]|"[^"]+")',txt)
   if mm:
    vals=re.findall(r'"([^"]+)"',mm.group(1))
    for v in vals:
     if v not in ids: errs.append(f'{f}: missing {key} target {v}')
 # all paths confined by construction
 if errs:
  for e in errs: print('ERROR',e)
  return 1
 print(f'OK {len(ids)} ids; no duplicate, missing dependency, forbidden text, or TeX errors')
 return 0

def main():
 ap=argparse.ArgumentParser(); sub=ap.add_subparsers(dest='cmd',required=True)
 p=sub.add_parser('diff'); p.add_argument('--blueprint',required=True); p.set_defaults(fn=diff)
 p=sub.add_parser('cut'); p.add_argument('chapter'); p.add_argument('--sketch'); p.add_argument('--blueprint',required=True); p.add_argument('--out',required=True); p.set_defaults(fn=cut)
 p=sub.add_parser('check'); p.add_argument('dir'); p.set_defaults(fn=check)
 a=ap.parse_args(); return a.fn(a)
if __name__=='__main__':sys.exit(main())
