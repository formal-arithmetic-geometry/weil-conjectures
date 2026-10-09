import csv,collections,os,re,sys
L='/home/bwucc/weil-conjectures-sheaf/literature'; SP=L+'/stacks-project'
tags={}
for l in open(SP+'/tags/tags'):
    l=l.strip()
    if l and not l.startswith('#'):
        t,lab=l.split(',',1); tags[t]=lab
texs=sorted((f[:-4] for f in os.listdir(SP) if f.endswith('.tex')),key=len,reverse=True)
def split(lab):
    for f in texs:
        if lab==f: return f,'chapter',''
        if lab.startswith(f+'-'):
            rest=lab[len(f)+1:]; kind=rest.split('-')[0]; return f,kind,rest
    return '?','?',lab
nodes=collections.defaultdict(set); other=collections.defaultdict(set)
for r in csv.DictReader(open(L+'/CITATIONS.tsv'),delimiter='\t',quoting=csv.QUOTE_NONE):
    t=r['stacks_tag']
    if not t: continue
    if r['node_id']!='-': nodes[t].add(r['node_id'])
    else: other[t].add(r['source'])
alltags=sorted(set(nodes)|set(other)); unresolved=[t for t in alltags if t not in tags]
kinds=collections.Counter(); files=collections.Counter(); nolabel=[]
with open(L+'/stacks-tags-cited.tsv','w') as o:
    o.write('tag\tlabel\ttex_file\tkind\tlabel_found_in_tex\tn_nodes\tnode_ids\tnon_node_sources\n')
    cache={}
    for t in alltags:
        if t not in tags: o.write(f'{t}\tUNRESOLVED\t\t\t\t{len(nodes[t])}\t{",".join(sorted(nodes[t]))}\t{",".join(sorted(other[t]))}\n'); continue
        f,k,rest=split(tags[t]); kinds[k]+=1; files[f]+=1
        if f not in cache: cache[f]=open(f'{SP}/{f}.tex',errors='replace').read() if os.path.exists(f'{SP}/{f}.tex') else ''
        found='yes' if (k=='chapter' or ('\\label{'+rest+'}') in cache[f]) else 'no'
        if found=='no': nolabel.append(t)
        o.write(f'{t}\t{tags[t]}\t{f}.tex\t{k}\t{found}\t{len(nodes[t])}\t{",".join(sorted(nodes[t]))}\t{",".join(sorted(other[t]))}\n')
print('tags cited',len(alltags),'unresolved',unresolved,'cited by md/tex-mapped nodes',len(nodes),'only non-node sources',len(set(other)-set(nodes)))
print('label not found in tex',nolabel); print(kinds.most_common()); print(files.most_common(12))
