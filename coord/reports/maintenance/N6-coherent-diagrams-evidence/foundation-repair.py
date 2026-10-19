import json, pathlib, shutil, subprocess, sys
root=pathlib.Path(sys.argv[1]); tag='maint-N6-1792191600-durable'
ndir=root/'dag/nodes/sec-six-functors'

def write(n,d):
 p=ndir/(n+'.json')
 if p.exists():
  backup=p.with_name(p.name+'.'+tag+'.bak')
  if not backup.exists():shutil.copy2(p,backup)
 p.write_text(json.dumps(d,indent=1,ensure_ascii=False)+'\n')

def load(n):return json.loads((ndir/(n+'.json')).read_text())

foundation='lem-coef-cat-infinity-colimits-cartesian-closure'
node=json.loads(pathlib.Path('/tmp/n6-cat-infinity-node.json').read_text())
node['title']='Small limits, colimits and cartesian closure of the infinity category of quasicategories'
node['statement']=node['statement'].replace('It admits all $\\mathcal U$-small colimits','It admits all $\\mathcal U$-small limits and colimits')
node['source']['place']='Definition 3.0.0.1 and Section 3.3.3, introductory paragraph, printed p. 214: Cat_infinity has small limits and colimits computed as homotopy (co)limits in the marked cartesian model. Sections 3.1.3-3.1.4, especially Proposition 3.1.4.2 and Corollary 3.1.4.3, give cartesian compatibility and the marked internal Hom. The exponential formula is the degreewise exponential law. Corollary 4.2.4.8 gives the model presentation of small (co)limits. All constructions are relative to the chosen universes. No Stacks tag states this result.'
write(foundation,node)

n='lem-coef-infinity-functor-pushout';d=load(n)
s=d['proof'][1]
s['uses']=['lem-coef-marked-point-cartesian-model',foundation,'lem-cbc-enhanced-functor-cone-calculus']
s['text']=(r'By [lem-coef-cat-infinity-colimits-cartesian-closure], $\mathrm{Cat}_\infty$ admits all small limits and colimits, including the empty ones, and coherent functor categories are its internal Homs. Its universe clause lets us form a colimit of the small input in its input universe and test its universal property after enlarging to contain $E$. Thus the pushout $P$ and the pullback $R$ below exist independently of any enriched diagram-model theorem. The actual exponential comparison and pushout-to-pullback argument are written in Steps 3--6; they retain the given cocones and all transformations.')
s=d['proof'][6]
s['uses']=[x for x in s['uses'] if x!='lem-coef-simplicial-model-coherent-diagrams']
a=s['text'].index('Apply the fibrant-cospan clause') if 'Apply the fibrant-cospan clause' in s['text'] else s['text'].index('By [lem-coef-marked-point-cartesian-model], the endpoint map')
b=s['text'].index('Its vertices are the two functors',a)
s['text']=s['text'][:a]+r'''Put $R=\operatorname{Fun}(B,E)\times_{C,\operatorname{ev}_0}V\times_{\operatorname{ev}_1,C}\operatorname{Fun}(D,E)$. To verify directly that it is the pullback in $\mathrm{Cat}_\infty$, test a quasicategory $Q$. The functor $\operatorname{Map}^{\sharp}(Q^\natural,-)$ preserves the displayed strict pullback and takes fibrant marked objects to Kan complexes, by the marked-model simplicial axiom. The exponential adjunction identifies
$$\operatorname{Map}^{\sharp}(Q^\natural,V^\natural)=\operatorname{Fun}(\Delta^1,\operatorname{Map}^{\sharp}(Q^\natural,C^\natural)).$$
Indeed the tensor is product with $(\Delta^n)^\sharp$ and $V^\natural=(C^\natural)^{(\Delta^1)^\sharp}$, so both sides in degree $n$ consist of the same marked maps. Thus $\operatorname{Map}_{\mathrm{Cat}_\infty}(Q,R)$ is exactly the path-space homotopy pullback of the three mapping Kan complexes into $\operatorname{Fun}(B,E),C,\operatorname{Fun}(D,E)$. The mapping-space cone criterion proves that this is the pullback, with its displayed cone. '''+s['text'][b:]
# Preserve TeX commands verbatim; raw multiline text already contains real newlines.
d['proof_deps']=list(dict.fromkeys(x for s in d['proof'] for x in s.get('uses',[])))
write(n,d)

n='lem-coef-space-geometric-descent';d=load(n)
s=d['proof'][1]
start=s['text'].index('Now take $K=')
s['text']=s['text'][:start]+r'''Now take the ordinary category $I=\Delta^{\mathrm{op}}$. Apply [lem-coef-small-diagram-model-rectification] to the Kan model category and this ordinary index. It identifies the localization of strict $I$-diagrams at objectwise weak homotopy equivalences with the full coherent diagram category $\operatorname{Fun}(N(I),\mathcal S)$, including transformations and constants. Here $\mathcal S$ is the infinity category of simplicial sets up to weak homotopy equivalence, equivalently spaces, in the conventions of the statement. Each strict diagram may be replaced objectwise by Kan complexes without changing its localized diagram. By [lem-coef-model-colimit-localization-comparison], its coherent colimit is computed by the ordinary colimit of a projectively cofibrant replacement. Products of strict Kan-valued diagrams represent pointwise products: Kan products are homotopy products and their function complexes are the products of the function complexes. This uses only ordinary-index rectification, not a projective or injective structure for enriched index categories.'''
s['uses']=[x for x in s['uses'] if x!='lem-coef-simplicial-model-coherent-diagrams']+['lem-coef-small-diagram-model-rectification','lem-coef-model-colimit-localization-comparison']
s=d['proof'][2]
s['text']=s['text'].replace('The free-diagram generators and projective-model description in [lem-coef-simplicial-model-coherent-diagrams] make every such free map a projective cofibration (decompose its underlying monomorphism into boundary cells and apply the free functor).',r'The projective-model description in [lem-coef-model-colimit-localization-comparison] makes every such free map a projective cofibration: evaluation preserves objectwise trivial fibrations, and the free-evaluation adjunction identifies each lifting square against one with a lifting square for the given monomorphism of simplicial sets.')
s['uses']=['lem-coef-model-colimit-localization-comparison' if x=='lem-coef-simplicial-model-coherent-diagrams' else x for x in s['uses']]
for step in [d['proof'][1],d['proof'][2]]:
 step['source']['place']='HTT ordinary-diagram rectification and model-colimit comparison; existing independent DAG inputs lem-coef-small-diagram-model-rectification and lem-coef-model-colimit-localization-comparison. This replaces the circular use of enriched diagram models.'
d['proof_deps']=list(dict.fromkeys(x for s in d['proof'] for x in s.get('uses',[])))
write(n,d)

names=[foundation,'lem-coef-infinity-functor-pushout','lem-coef-space-geometric-descent']
for n in names:
 d=load(n)
 assert 'lem-coef-simplicial-model-coherent-diagrams' not in d['proof_deps']
print('updated',root,','.join(names))
subprocess.run(['git','diff','--check'],cwd=root,check=True)
