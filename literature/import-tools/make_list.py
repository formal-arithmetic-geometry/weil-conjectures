import csv,collections,os,re,subprocess
L='/home/bwucc/weil-conjectures-sheaf/literature'
D='2026-10-08'
rows=list(csv.DictReader(open(L+'/CITATIONS.tsv'),delimiter='\t',quoting=csv.QUOTE_NONE))
nodes=collections.defaultdict(set); places=collections.defaultdict(list); nonnode=collections.Counter(); cnt=collections.Counter()
for r in rows:
    k=r['document_key']; cnt[k]+=1
    if r['node_id']!='-': nodes[k].add(r['node_id'])
    else: nonnode[k]+=1
    p=r['place_as_cited']
    if p!='(no place given)' and p not in places[k]: places[k].append(p)
def tidy(p):
    p=p.replace('~',' ').replace('\\S','§').replace("\\'e",'é').replace('--','–').replace('|','/')
    p=re.sub(r'^[^*]{0,60}\*,?\s*','',p).replace('$','').replace('*','')
    p=re.sub(r'^(?:An Introduction to Homological Algebra|Introduction to Affine Group Schemes|Central Simple Algebras and Galois Cohomology|Alg\. comm\. V|Algebraic Geometry),?\s*','',p)
    if p.count('(')>p.count(')'): p=p[:p.rfind('(')]
    if re.fullmatch(r'(?:19|20)\d\d',p.strip()): p=''
    return re.sub(r'\s+',' ',p).strip(' .,:')
def placestr(k,cap=14):
    ps=[]
    for p in places[k]:
        p=tidy(p)
        if p and p not in ps: ps.append(p)
    if not ps: return 'no place given in the blueprint'
    s='; '.join(ps[:cap])
    return s+(f'; … ({len(ps)} distinct places, see CITATIONS.tsv)' if len(ps)>cap else '')
def nodestr(k):
    ns=sorted(nodes[k]); extra=f' (+{nonnode[k]} citations in LaTeX units with no node id)' if nonnode[k] else ''
    if not ns: return 'no node cites it directly'+extra+f'; see `CITATIONS.tsv`, document_key `{k}`'
    if len(ns)>15: return f'{len(ns)} nodes; see `CITATIONS.tsv`, document_key `{k}`'+extra
    return ', '.join('`%s`'%n for n in ns)+extra
def size(f):
    p=L+'/'+f
    if os.path.isdir(p):
        n=sum(os.path.getsize(os.path.join(dp,x)) for dp,_,fs in os.walk(p) for x in fs); return f'{n/1e6:.1f} MB'
    return f'{os.path.getsize(p)/1e6:.1f} MB'
commit=subprocess.run(['git','-C',L+'/stacks-project','rev-parse','HEAD'],capture_output=True,text=True).stdout.strip()
OBT=[ # (file, what, where, key)
('blueprint/','The project\'s existing natural-language blueprint: 2,943 node files (`master/blueprint/`), LaTeX versions (`master/wholeblueprint-final.tex`, `slopmaster2/`). Source of the node ids.','already present before the import; commits in `blueprint/COMMITS.txt`',None),
('stacks-project/',f'The Stacks project, TeX source; every tag is looked up through `tags/tags` (tag,label; label = `<file>-<kind>-<name>` in `<file>.tex`). All 652 tags cited in the blueprint resolve; index in `stacks-tags-cited.tsv`.',f'git clone --depth 1 https://github.com/stacks/stacks-project, commit `{commit}` (2026-07-28), {D}','Stacks'),
('deligne-weil-I_PMIHES-1974-43.pdf','P. Deligne, La conjecture de Weil I, Publ. Math. IHÉS 43 (1974), 273–307','http://www.numdam.org/item/PMIHES_1974__43__273_0.pdf','WeilI'),
('deligne-weil-II_PMIHES-1980-52.pdf','P. Deligne, La conjecture de Weil II, Publ. Math. IHÉS 52 (1980), 137–252','http://www.numdam.org/item/PMIHES_1980__52__137_0.pdf','WeilII'),
('laumon-transformation-de-fourier_PMIHES-1987-65.pdf','G. Laumon, Transformation de Fourier, constantes d\'équations fonctionnelles et conjecture de Weil, Publ. Math. IHÉS 65 (1987), 131–210','http://www.numdam.org/item/PMIHES_1987__65__131_0.pdf','Laumon'),
('bbd-faisceaux-pervers_Asterisque-100-1982.pdf','Beilinson–Bernstein–Deligne, Faisceaux pervers, Astérisque 100 (1982)','https://www.numdam.org/item/AST_1982__100__1_0.pdf','BBD'),
('conrad-deligne-notes-on-nagata-compactifications.pdf','B. Conrad, Deligne\'s notes on Nagata compactifications (author\'s final version). Also the source for the citations "Deligne, Lemme 0.2 / 0.3".','https://math.stanford.edu/~conrad/papers/nagatafinal.pdf','ConradNagata'),
('conrad-etale-cohomology-notes.pdf','B. Conrad, Étale cohomology (seminar notes, chapter 1 of an unpublished book)','https://math.stanford.edu/~conrad/Weil2seminar/Notes/etnotes.pdf','ConradEtale'),
('stanford-weil2-seminar/','Stanford Number Theory Learning Seminar 2016–17 (Weil II), lecture notes L18, L19, L20, L22, L23, L24 (the six lectures in the blueprint bibliography)','https://math.stanford.edu/~conrad/Weil2seminar/Notes/L{18,19,20,22,23,24}.pdf','StanfordSeminar'),
('milne-lectures-on-etale-cohomology_LEC.pdf','J. S. Milne, Lectures on Étale Cohomology, v2.21 (2013)','https://www.jmilne.org/math/CourseNotes/LEC.pdf','MilneLEC'),
('milne-abelian-varieties_AV.pdf','J. S. Milne, Abelian Varieties, v2.0 (2008). The blueprint cites "Milne, Abelian Varieties, Ch. I / Ch. 12" without edition; this may instead mean his chapters in Cornell–Silverman, *Arithmetic Geometry* (see README-import.md).','https://www.jmilne.org/math/CourseNotes/AV.pdf','MilneAV'),
('milne-algebraic-groups_iAG2017.pdf','J. S. Milne, Algebraic Groups (2017), the author\'s posted version, at the URL the blueprint itself links','https://www.jmilne.org/math/Books/iAG2017.pdf','MilneAG'),
('bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf','B. Bhatt, P. Scholze, The pro-étale topology for schemes, arXiv:1309.1198v2 (the version the blueprint cites)','https://arxiv.org/pdf/1309.1198','BhattScholze'),
('varshavsky-lefschetz-verdier-trace-formula_arXiv-math0505564.pdf','Y. Varshavsky, Lefschetz–Verdier trace formula and a generalization of a theorem of Fujiwara, arXiv:math/0505564v2','https://arxiv.org/pdf/math/0505564','Varshavsky'),
('hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf','T. Hemo, T. Richarz, J. Scholbach, Constructible sheaves on schemes, arXiv:2305.18131v1','https://arxiv.org/pdf/2305.18131','HRS'),
('ruimy-tubach-wolf-proetale-motives-solid-rigidity_arXiv-2601.07358.pdf','R. Ruimy, S. Tubach, S. Wolf, Pro-étale motives and solid rigidity, arXiv:2601.07358v1','https://arxiv.org/pdf/2601.07358','RuimyTubachWolf'),
('haine-et-al-condensed-homotopy-type_arXiv-2510.07443.pdf','P. Haine et al., The condensed homotopy type of a scheme, arXiv:2510.07443v1','https://arxiv.org/pdf/2510.07443','HaineEtAl'),
('zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf','W. Zheng, Six operations and Lefschetz–Verdier formula for Deligne–Mumford stacks, arXiv:1006.3810v5','https://arxiv.org/pdf/1006.3810','Zheng'),
('bergfalk-lambie-hanson_arXiv-2412.19605.pdf','J. Bergfalk, C. Lambie-Hanson, Infinitary combinatorics in condensed mathematics and strong homology, arXiv:2412.19605v2','https://arxiv.org/pdf/2412.19605','BergfalkLH'),
('juteau-mautner-williamson-perverse-sheaves-modular-rep_arXiv-0901.3322.pdf','D. Juteau, C. Mautner, G. Williamson, Perverse sheaves and modular representation theory, arXiv:0901.3322v1','https://arxiv.org/pdf/0901.3322','JMW'),
('illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf','Illusie–Laszlo–Orgogozo (eds.), Travaux de Gabber sur l\'uniformisation locale et la cohomologie étale des schémas quasi-excellents, arXiv:1207.3648 (published as Astérisque 363–364)','https://arxiv.org/pdf/1207.3648','ILO'),
('scholze-six-functor-formalisms.pdf','P. Scholze, Six-Functor Formalisms (lecture notes)','https://people.mpim-bonn.mpg.de/scholze/SixFunctors.pdf','ScholzeSix'),
('charles-poonen-bertini-irreducibility.pdf','F. Charles, B. Poonen, Bertini irreducibility theorems over finite fields (linked from node `sk-i-dl-general-real`)','https://math.mit.edu/~poonen/papers/bertini_irred.pdf','Poonen'),
('tate-residues-of-differentials-on-curves_ASENS-1968.pdf','J. Tate, Residues of differentials on curves, Ann. Sci. ÉNS (4) 1 (1968), 149–159','http://www.numdam.org/item/ASENS_1968_4_1_1_149_0.pdf','TateResidues'),
('spaltenstein-resolutions-of-unbounded-complexes_CM-1988.pdf','N. Spaltenstein, Resolutions of unbounded complexes, Compositio Math. 65 (1988), 121–154','http://www.numdam.org/item/CM_1988__65_2_121_0.pdf','Spaltenstein'),
('balmer-schlichting-idempotent-completion.pdf','P. Balmer, M. Schlichting, Idempotent completion of triangulated categories, J. Algebra 236 (2001) (author\'s copy)','https://www.math.ucla.edu/~balmer/Pubfile/IdempCompl.pdf','BalmerSchlichting'),
('grothendieck-groupe-de-brauer-II_SemBourbaki-297.pdf','A. Grothendieck, Le groupe de Brauer II: théorie cohomologique, Séminaire Bourbaki exp. 297 (1965–66). Part II only; part III is Wanted.','https://www.numdam.org/item/SB_1964-1966__9__287_0.pdf','GrothBrauer'),
('sga/SGA1_arXiv-math0206203.pdf','SGA 1, Revêtements étales et groupe fondamental (SMF re-typeset edition, Documents Mathématiques 3)','https://arxiv.org/pdf/math/0206203','SGA1'),
('sga/SGA4-expose-{05..18}_reedition.pdf','SGA 4, exposés V–XVIII (the range the blueprint cites: IX, XIV–XVIII, and "V–XII"), the TeX re-edition by Y. Laszlo and F. Orgogozo, one file per exposé (05–18). Page and paragraph numbers follow the original; exposés I–IV, Vbis and XIX were not fetched.','http://www.normalesup.org/~forgogozo/SGA4/NN/NN.pdf, linked from the editors\' page http://fabrice.orgogozo.perso.math.cnrs.fr/SGA4/','SGA4'),
('ega/EGA-II_PMIHES-8-1961.pdf','EGA II, Publ. Math. IHÉS 8 (1961)','https://www.numdam.org/item/PMIHES_1961__8__5_0.pdf','EGA'),
('ega/EGA-III-1_PMIHES-11-1961.pdf','EGA III, première partie, Publ. Math. IHÉS 11 (1961)','https://www.numdam.org/item/PMIHES_1961__11__5_0.pdf','EGA'),
('ega/EGA-IV-1_PMIHES-20-1964.pdf','EGA IV, première partie (contains 0_IV), Publ. Math. IHÉS 20 (1964)','https://www.numdam.org/item/PMIHES_1964__20__5_0.pdf','EGA'),
('ega/EGA-IV-2_PMIHES-24-1965.pdf','EGA IV, seconde partie, Publ. Math. IHÉS 24 (1965)','https://www.numdam.org/item/PMIHES_1965__24__5_0.pdf','EGA'),
('ega/EGA-IV-3_PMIHES-28-1966.pdf','EGA IV, troisième partie, Publ. Math. IHÉS 28 (1966)','https://www.numdam.org/item/PMIHES_1966__28__5_0.pdf','EGA'),
]
WANT=[ # key, document, note
('SGA4.5','P. Deligne, *Cohomologie étale* (SGA 4½), Lecture Notes in Math. 569, Springer 1977','Not located on Numdam (its search was not completed; Numdam does not appear to carry the Springer Lecture Notes); the IAS page the blueprint bibliography gives (https://publications.ias.edu/node/378) answered HTTP 403 (bot challenge) to curl.'),
('SGA5','*Cohomologie ℓ-adique et fonctions L* (SGA 5), Lecture Notes in Math. 589, Springer 1977','No download attempted: no free copy hosted by its editors is known to the import agent.'),
('KiehlWeissauer','R. Kiehl, R. Weissauer, *Weil Conjectures, Perverse Sheaves and ℓ-adic Fourier Transform*, Springer 2001','Book, no free legal copy.'),
('FreitagKiehl','E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Springer 1988','Book, no free legal copy.'),
('MilneEC','J. S. Milne, *Étale Cohomology*, Princeton Univ. Press 1980','Book, no free legal copy (distinct from the Lectures, which are obtained).'),
('Hartshorne','R. Hartshorne, *Algebraic Geometry*, GTM 52','Book, no free legal copy.'),
('MumfordAV','D. Mumford, *Abelian Varieties*','Book, no free legal copy.'),
('Weibel','C. Weibel, *An Introduction to Homological Algebra*','Book, no free legal copy.'),
('SerreLF','J.-P. Serre, *Local Fields*, GTM 67','Book, no free legal copy.'),
('SerreGACC','J.-P. Serre, *Groupes algébriques et corps de classes*','Book, no free legal copy.'),
('Bourbaki','N. Bourbaki, *Algèbre commutative*, Ch. V','Book, no free legal copy.'),
('Waterhouse','W. Waterhouse, *Introduction to Affine Group Schemes*, GTM 66','Book, no free legal copy.'),
('Jacobson','N. Jacobson, *Lie Algebras*','Book, no free legal copy.'),
('GilleSzamuely','P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*','Book, no free legal copy.'),
('Greenberg','M. Greenberg, *Lectures on Forms in Many Variables*','Book, no free legal copy.'),
('MilnorMoore','J. Milnor, J. Moore, On the structure of Hopf algebras, Ann. of Math. 81 (1965), 211–264 (the blueprint writes "Ann. of Math. 68 (1958)")','Journal article behind a paywall; no download attempted.'),
('GrothBrauer','A. Grothendieck, Le groupe de Brauer III: exemples et compléments, in *Dix exposés sur la cohomologie des schémas*, North-Holland 1968 (part II is obtained)','Part III was not a Bourbaki talk and is not on Numdam.'),
('LangQAC','S. Lang, On quasi algebraic closure, Ann. of Math. 55 (1952)','Journal article behind a paywall; no download attempted.'),
('Tsen','C. Tsen, Divisionsalgebren über Funktionenkörpern, Nachr. Ges. Wiss. Göttingen (1933)','Cited as "Tsen, 1933" only; no download attempted.'),
('Olivier','J.-P. Olivier, Fermeture intégrale et changements de base absolument plats (Colloque d\'algèbre commutative, Rennes 1972), as cited through Stacks Tag 092Z','No download attempted; the Stacks text of 092Z is obtained.'),
('RaynaudGruson','M. Raynaud, L. Gruson, Critères de platitude et de projectivité, Invent. Math. 13 (1971)','No download attempted (journal). Named in the LaTeX Nagata chapter only, without place.'),
('KatzLang','N. Katz, S. Lang, Finiteness theorems in geometric classfield theory, Enseign. Math. 27 (1981)','Identified by inference from "the rank-one Katz–Lang theorem"; no download attempted.'),
('CompleteNotes','`weil_conjectures_complete_notes.pdf`, the blueprint authors\' own notes, linked from two section files but absent from the blueprint repository','Not a published document; must come from the blueprint authors.'),
('Zavyalov','Zavyalov, "5.7.7" (work not named in the blueprint; probably B. Zavyalov\'s Poincaré-duality/six-functor paper)','Unidentified; the citing node says the result is not used.'),
]
missing=[f for f,_,_,_ in OBT if '{' not in f and not os.path.exists(L+'/'+f)]
head=open(L+'/LIST.md').read().split('## Wanted')[0]
o=[head.rstrip('\n'),'','## Wanted','','| Document, with the place needed (theorem, section, page) | Nodes waiting for it | Asked by, date |','|---|---|---|']
for k,doc,note in WANT:
    pl=placestr(k)
    if k=='GrothBrauer': pl='part III as a whole (cited "Le groupe de Brauer II–III" and "III", no finer place)'
    o.append(f'| {doc}. Places: {pl}. {note} | {nodestr(k)} | import agent, {D} |')
o+=['','## Obtained','','| File | What it is | Where it came from |','|---|---|---|']
for f,what,where,k in OBT:
    if f in missing: continue
    if '{' in f: sz=f"{sum(os.path.getsize(L+'/sga/'+x) for x in os.listdir(L+'/sga') if x.startswith('SGA4-'))/1e6:.1f} MB, {len([x for x in os.listdir(L+'/sga') if x.startswith('SGA4-')])} files"
    else: sz=size(f)
    w=where if (k is None or k=='Stacks') else f'{where}, {D}'
    o.append(f'| `{f}` | {what} ({sz}) | {w} |')
open(L+'/LIST.md','w').write('\n'.join(o)+'\n')
print('missing',missing)
