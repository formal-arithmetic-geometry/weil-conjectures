#!/usr/bin/env python3
"""Citation inventory for the Weil-conjectures blueprint. Writes CITATIONS.tsv rows:
node_id, source, document, place, tag, pattern."""
import re,glob,os,sys,collections
LIT='/home/bwucc/weil-conjectures-sheaf/literature'
BP=LIT+'/blueprint'
OUT=sys.argv[1]
# ---------- documents: key -> (display name, [name regexes]) ----------
SP=r'[\s~]*'
DOCS=[
('SGA4.5',"Deligne, SGA 4 1/2 (Cohomologie etale, LNM 569)",[r'SGA'+SP+r'(?:\\\()?\$?4\$?'+SP+r'(?:\\\()?(?:\$?\\t?frac\{?1\}?\{?2\}?\$?|1/2|½|\.5)',r'SGA4half']),
('SGA1',"SGA 1 (Revetements etales et groupe fondamental)",[r'SGA'+SP+r'1\b']),
('SGA4',"SGA 4 (Theorie des topos et cohomologie etale des schemas)",[r'SGA'+SP+r'(?:4|IV)\b(?!'+SP+r'(?:\$?\\t?frac|\\\(|1/2|½|\.5|\$))']),
('SGA5',"SGA 5 (Cohomologie l-adique et fonctions L)",[r'\$?SGA'+SP+r'5\$?']),
('SGA-other',"SGA (other volume)",[r'SGA'+SP+r'(?:2|3|6|7)\b']),
('EGA',"EGA (Elements de geometrie algebrique)",[r'\bEGA\b']),
('WeilI',"Deligne, La conjecture de Weil I",[r'Weil'+SP+r'I\b(?!I)',r'La conjecture de Weil\.?'+SP+r'I\b(?!I)',r'DeligneWeilI\b']),
('WeilII',"Deligne, La conjecture de Weil II",[r'Weil'+SP+r'II\b',r'DeligneWeilII\b']),
('BBD',"Beilinson-Bernstein-Deligne, Faisceaux pervers (Asterisque 100)",[r'\bBBD\b',r'Faisceaux pervers',r'Be[iĭ]linson\W{1,3}Bernstein\W{1,3}Deligne(?!, \*?Faisceaux)']),
('MilneLEC',"Milne, Lectures on Etale Cohomology",[r"Lectures on (?:\\'E|[EÉ])tale Cohomology"]),
('MilneEC',"Milne, Etale Cohomology (Princeton 1980)",[r"Milne, \*?(?:\\'E|[EÉ])tale Cohomology",r'MilneEtale']),
('MilneAV',"Milne, Abelian Varieties",[r'Milne, \*?Abelian Varieties',r'Mumford and Milne',r'Milne(?= I\b)']),
('MilneAG',"Milne, Algebraic Groups (2017)",[r'Milne, \[?\*?Algebraic Groups']),
('MumfordAV',"Mumford, Abelian Varieties",[r'Mumford, \*?Abelian Varieties',r'Mumford and Milne',r'Mumford(?= II\b)',r'Mumford(?=, Abelian)']),
('ConradNagata',"Conrad, Deligne's notes on Nagata compactifications",[r"Deligne's notes on Nagata",r'ConradNagata',r'\bConrad\b(?! additionally| does| we)']),
('ConradEtale',"Conrad, Etale cohomology notes (Stanford)",[r'ConradEtaleNotes']),
('Varshavsky',"Varshavsky, Lefschetz-Verdier trace formula and a generalization of a theorem of Fujiwara (arXiv:math/0505564)",[r"Varshavsky(?!'s (?:theorem|convention|contracting))",r'\\cite(?:\[[^\]]*\])?\{varsh\}']),
('BhattScholze',"Bhatt-Scholze, The pro-etale topology for schemes (arXiv:1309.1198)",[r'Bhatt\W{1,3}Scholze',r'BhattScholzeProEtale',r'\\cite(?:\[[^\]]*\])?\{(?:bs|proetale)\}']),
('Hartshorne',"Hartshorne, Algebraic Geometry",[r'Hartshorne']),
('Weibel',"Weibel, An Introduction to Homological Algebra",[r'Weibel']),
('SerreLF',"Serre, Local Fields",[r'Serre, \*?Local Fields']),
('SerreGACC',"Serre, Groupes algebriques et corps de classes",[r'Groupes alg[ée]briques et corps de classes']),
('Bourbaki',"Bourbaki, Algebre commutative",[r'Bourbaki']),
('Waterhouse',"Waterhouse, Introduction to Affine Group Schemes",[r'Waterhouse']),
('Jacobson',"Jacobson, Lie Algebras",[r'Jacobson, \*?Lie Algebras']),
('MilnorMoore',"Milnor-Moore, On the structure of Hopf algebras (Ann. of Math. 1965)",[r'Milnor\W{1,3}Moore']),
('GilleSzamuely',"Gille-Szamuely, Central Simple Algebras and Galois Cohomology",[r'Gille\W{1,3}Szamuely']),
('GrothBrauer',"Grothendieck, Le groupe de Brauer I-III (Dix exposes)",[r'Le groupe de Brauer']),
('Tsen',"Tsen (1933)",[r'Tsen, 1933']),
('LangQAC',"Lang, On quasi algebraic closure (1952)",[r'Lang, On quasi algebraic closure']),
('Greenberg',"Greenberg, Lectures on Forms in Many Variables",[r'Greenberg, Lectures']),
('BalmerSchlichting',"Balmer-Schlichting, Idempotent completion of triangulated categories",[r'Balmer\W{1,3}Schlichting']),
('Spaltenstein',"Spaltenstein, Resolutions of unbounded complexes",[r'Spaltenstein']),
('Olivier',"Olivier, Fermeture integrale et changements de base absolument plats",[r'\bOlivier\b',r'\{oli72\}']),
('Zavyalov',"Zavyalov (reference '5.7.7'; document not named)",[r'Zavyalov']),
('Zheng',"Zheng, Six operations and Lefschetz-Verdier formula for Deligne-Mumford stacks (arXiv:1006.3810)",[r'Zheng, arXiv']),
('BergfalkLH',"Bergfalk-Lambie-Hanson (arXiv:2412.19605)",[r'Bergfalk']),
('Laumon',"Laumon, Transformation de Fourier, constantes d'equations fonctionnelles et conjecture de Weil",[r'Transformation de Fourier',r'LaumonFourier',r'\\cite(?:\[[^\]]*\])?\{Laumon\}']),
('KiehlWeissauer',"Kiehl-Weissauer, Weil Conjectures, Perverse Sheaves and l-adic Fourier Transform",[r'Kiehl\W{1,3}Weissauer',r'KiehlWeissauer']),
('FreitagKiehl',"Freitag-Kiehl, Etale Cohomology and the Weil Conjecture",[r'Freitag\W{1,3}Kiehl',r'FreitagKiehl']),
('KatzLang',"Katz-Lang, Finiteness theorems in geometric classfield theory (named only as 'the rank-one Katz--Lang theorem')",[r'Katz\W{1,3}Lang']),
('Ekedahl',"Ekedahl, On the adic formalism",[r'Ekedahl']),
('Jannsen',"Jannsen, Continuous etale cohomology",[r'Jannsen|\{jannsen\}']),
('KashiwaraSchapira',"Kashiwara-Schapira, Categories and sheaves",[r'Kashiwara|kashiwara-shapira']),
('HRS',"Hemo-Richarz-Scholbach, Constructible sheaves on schemes (arXiv:2305.18131)",[r'HRSConstructible',r'Hemo\W{1,3}Richarz']),
('ScholzeSix',"Scholze, Six-Functor Formalisms (lecture notes)",[r'ScholzeSixFunctors',r'Six-Functor Formalisms']),
('HaineEtAl',"Haine et al., The Condensed Homotopy Type of a Scheme (arXiv:2510.07443)",[r'HaineEtAlCondensedHomotopy']),
('RuimyTubachWolf',"Ruimy-Tubach-Wolf, Pro-etale Motives and Solid Rigidity (arXiv:2601.07358)",[r'RuimyTubachWolfSolid']),
('ILO',"Illusie-Laszlo-Orgogozo, Travaux de Gabber (Asterisque 363-364)",[r'ILOTravauxGabber',r'Travaux de Gabber']),
('Juteau',"Juteau, Decomposition numbers for perverse sheaves",[r'JuteauPerverse']),
('StanfordSeminar',"Stanford Number Theory Learning Seminar 2016-17 (Weil II) lecture notes",[r'StanfordWeilIISeminar',r'StanfordL\d+']),
('TateResidues',"Tate, Residues of differentials on curves",[r'Residues of differentials on curves']),
('Poonen',"Charles-Poonen, Bertini irreducibility theorems over finite fields (math.mit.edu/~poonen/papers/bertini_irred.pdf)",[r'math\.mit\.edu/~poonen[^)\s]*']),
('Lurie',"Lurie (HTT/HA/SAG)",[r'\bLurie\b',r'Higher Topos Theory',r'Higher Algebra\b']),
('Matsumura',"Matsumura, Commutative Ring Theory",[r'Matsumura']),
('Fulton',"Fulton, Intersection Theory",[r'Fulton, ']),
('RaynaudGruson',"Raynaud-Gruson, Criteres de platitude et de projectivite",[r'Raynaud\W{1,3}Gruson']),
('Lutkebohmert',"Lutkebohmert, On compactification of schemes",[r'L(?:ü|\\"u|u)tkebohmert']),
('DeligneNagata',"Deligne, unpublished notes on Nagata compactification (cited by Lemme number; reproduced in Conrad's paper)",[r'Deligne, \*?Lemme\*?']),
('JMW',"Juteau-Mautner-Williamson, Perverse sheaves and modular representation theory (arXiv:0901.3322)",[r'Juteau\W{1,3}Mautner']),
('nLab',"nLab",[r'ncatlab\.org[^)\s}]*',r'nlab:\w+']),
('Fujiwara',"Fujiwara, Rigid geometry, Lefschetz-Verdier trace formula and Deligne's conjecture",[r'Fujiwara(?!\'s theorem)']),
('CompleteNotes',"weil_conjectures_complete_notes.pdf (internal notes of the blueprint authors; not in the repository)",[r'weil_conjectures_complete_notes\.pdf\`?\]?(?:\([^)]*\))?',r'Complete notes']),
]
BIBKEYS={'SGA4':'SGA4','SGA5':'SGA5','SGA1':'SGA1','sga4':'SGA4','sga5':'SGA5','sga4half':'SGA4.5','SGA4half':'SGA4.5','bs':'BhattScholze','varsh':'Varshavsky',
 'stacks-project':'Stacks','DeligneWeilI':'WeilI','DeligneWeilII':'WeilII','LaumonFourier':'Laumon','Laumon':'Laumon','BBD':'BBD','Deligne':'WeilII','BhattScholze':'BhattScholze',
 'FreitagKiehl':'FreitagKiehl','KiehlWeissauer':'KiehlWeissauer','MilneEtale':'MilneEC','ConradEtaleNotes':'ConradEtale','ConradNagata':'ConradNagata',
 'BhattScholzeProEtale':'BhattScholze','proetale':'BhattScholze','HRSConstructible':'HRS','ScholzeSixFunctors':'ScholzeSix','HaineEtAlCondensedHomotopy':'HaineEtAl',
 'RuimyTubachWolfSolid':'RuimyTubachWolf','ILOTravauxGabber':'ILO','JuteauPerverse':'Juteau','EkedahlAdic':'Ekedahl','Hartshorne':'Hartshorne','Weibel':'Weibel',
 'StanfordWeilIISeminar':'StanfordSeminar','oli72':'Olivier','kashiwara-shapira':'KashiwaraSchapira','jannsen':'Jannsen','nlab:coherent_object':'nLab'}
for n in (18,19,20,22,23,24): BIBKEYS['StanfordL%d'%n]='StanfordSeminar'
NAME=dict((k,n) for k,n,_ in DOCS); NAME['Stacks']='The Stacks project'; NAME['UNIDENTIFIED-NUMBERED']='(numbered reference with no document named nearby)'; NAME['arXiv:0901.3322']='arXiv:0901.3322'
ARX={'0901.3322':'JMW','math/0505564':'Varshavsky','1309.1198':'BhattScholze','1006.3810':'Zheng','2412.19605':'BergfalkLH','2305.18131':'HRS','2510.07443':'HaineEtAl','2601.07358':'RuimyTubachWolf'}
RX=[(k,re.compile('|'.join('(?:%s)'%p for p in ps))) for k,_,ps in DOCS]
PLACEHINT=re.compile(r'\d|§|\\S\b|\b[IVX]+\b|Ch\.|Chap|Expos|Exp\.|Appendix|Rapport|Section|Lecture')
def clean(s):
    s=re.sub(r'\s+',' ',s).strip(' ,:;*`~')
    s=re.sub(r'^[\]\[,:;*`~. ]+','',s)
    while s.endswith(('(','[',' ',',','$','*','`')) : s=s[:-1]
    if s.count('(')>s.count(')') and s.startswith('('): s=s[1:]
    if s.count('$')%2: s=s.rstrip('$') if s.endswith('$') else s
    return s.strip()
ALLOW=set('and with proof the for see also part parts loc cit his her its form case used text esp especially statement paragraph formula item items line lines page pages chapter chapters chapitre section sections sect lemma lemmas lemme theorem theorems proposition propositions corollary definition remark example appendix rapport lecture lectures expos exposé expose exposition dualité finitude théorème theoreme théorèmes etc que des les sur dans'.split())
TEXCUT=re.compile(r'\\\\|\\end\b|\\begin\b|\\\[|\$\$|\\bottomrule|\\item\b|\\bibitem|\\qquad|\\tag\b|\n\s*\n|\\par\b|\\medskip|\\noindent')
def tail(text,end,lim=150):
    t=text[end:end+lim]
    t=re.sub(r"^'s\s+",'',t)
    t=re.sub(r'^[^*\n]{0,70}\*(?=[,. )]|$)','',t) if re.match(r'[,:]?\s*\[?\*',text[end-2:end+3]) or text[end-1:end]=='*' or re.match(r'\s*\*?[A-Z][a-z]+[^*]{0,60}\*',t) else t
    cuts=[m.start() for m in [TEXCUT.search(t),OTHER.search(t,1),re.search(r'\||\]\(http|\\cite|\\emph|%|&|\\href|Stacks|Tag|,? for (?:\$|the |a |its )|, with |, where |, together |, translated |: ',t)] if m]
    if cuts: t=t[:min(cuts)]
    depth=0
    for i,c in enumerate(t):
        if c in '([{': depth+=1
        elif c in ')]}':
            if depth==0: t=t[:i]; break
            depth-=1
        elif c==';' or (c=='*' and t[i+1:i+2] in (')','.')) : t=t[:i]; break
        elif c=='.' and re.match(r'\s+(?:[A-Z][a-z]|\$|\*\(|\\)|\s*$',t[i+1:i+8] or ' ') and not re.search(r'(?:Ch|Th|Thm|Prop|Exp|no|cit|Sect|Def|Cor|Lem|pp?|Alg|comm|Math|cf|loc)$',t[:i]): t=t[:i]; break
    toks=t.split(' '); out=[]; run=0
    for w in toks:
        core=re.sub(r'[^A-Za-zÀ-ÿ]','',w)
        prose=bool(core) and w[:1].islower() and not re.search(r'\d',w) and core.lower() not in ALLOW and len(core)>=2 and not re.fullmatch(r'[ivxIVX]+',core)
        run=run+1 if prose else 0
        out.append((w,prose))
        if run>=2: out=out[:-2]; break
    while out and out[-1][1]: out.pop()
    t=clean(' '.join(w for w,_ in out))
    for _ in range(3): t=re.sub(r'[,:]?\s+(?:and|with|the|for|see|also|in|of|as|is|by|proof|together|where|so|while|both|a|especially|its|his|or)$','',t).rstrip(' ,:(')
    return t if PLACEHINT.search(t) else ''
OTHER=re.compile('|'.join('(?:%s)'%p for k,_,ps in DOCS for p in ps if k not in('Poonen','nLab','Lurie')))
TAGTOK=r'[0-9][0-9A-Z]{3}'
STX=[('url',re.compile(r'stacks\.math\.columbia\.edu/tag/('+TAGTOK+r')\b')),
     ('Tag',re.compile(r'\b[Tt]ags?'+r'[\s~:]*(?:\\texttt\{|\\href\{[^}]*\}\{|\[|`)*('+TAGTOK+r')\b')),
     ('macro',re.compile(r'\\stacks\{('+TAGTOK+r')\}')),
     ('tt',re.compile(r'(?:`|\\texttt\{(?:Stacks\s+)?)('+TAGTOK+r')(?:`|\})')),
     ('Stacks-bare',re.compile(r'Stacks(?:\s+[Pp]roject)?[\s~]+(?:\\texttt\{)?('+TAGTOK+r')\b')),
     ('bare',re.compile(r'(?<![\w/.:\-`{])(0(?=[0-9A-Z]{0,2}[A-Z])[0-9A-Z]{3})(?![\w}`\-])')),
     ('paren-digits',re.compile(r'\((0\d{3})\)')),
     ('see-bare',re.compile(r'\bsee\s+('+TAGTOK+r')\b(?![.\d])'))]
NUM=re.compile(r'((?:Lemma|Proposition|Theorem|Definition|Section|Remark|Example|Lemmas|Situation|Equation)[\s~]+\d+\.\d+(?:\.\d+)?(?:\s*\([^)]{1,12}\))?)')
STNOTAG=re.compile(r'Stacks(?:\s+[Pp]roject)?(?:\s+references)?[,:]?\s+(?!Project)([A-Z][^;*\n]{3,140})')
NUM3=re.compile(r'(?:Lemma|Proposition|Theorem|Definition|Section|Remark|Example)[\s~]+(\d{1,3}\.\d+\.\d+)')
NUM2=re.compile(r'(?:Lemma|Proposition|Theorem|Definition|Corollary|Remark|Example)[\s~]+(\d{1,2}\.\d{1,3})(?![\d.])')
ARXIV=re.compile(r'arxiv\.org/(?:abs|pdf|html)/((?:math/)?\d{4}\.?\d{3,5})|arXiv:((?:math/)?\d{4}\.?\d{3,5})',re.I)
LINK=re.compile(r'\[([^\]\[]{1,80})\]\((https?://[^)\s]+)\)')
URL=re.compile(r'https?://[^\s)}\]>"`]+')
CITE=re.compile(r'\\cite[tp]?\*?(?:\[([^\]]*)\])?\{([^}]*)\}')
URLMAP=[('jmilne.org/math/Books/iAG2017','MilneAG'),('scholze/proetale.pdf','BhattScholze'),('AST_2014__363-364','ILO'),('978-3-662-04576-3','KiehlWeissauer'),('grothendiecksga.com/read/sga4','SGA4'),('github.com',''),('github.io','')]
def scan(text,ismd=False):
    text=re.sub(r'(?<!\n)\n(?!\n)',' ',text)
    """yield (dockey, place, tag, pattern)"""
    rows=[]; seen_tagpos={}
    for name,rx in STX:
        for m in rx.finditer(text):
            tag=m.group(1); pos=m.start(1)
            if any(abs(pos-p)<60 and t==tag for p,t in seen_tagpos.items()): continue
            seen_tagpos[pos]=tag
            back=text[max(0,pos-110):pos]; nm=NUM.findall(back)
            place='Tag '+tag+((' ('+clean(nm[-1])+')') if nm else '')
            rows.append(('Stacks',place,tag,'stacks:'+name))
    LISTC=re.compile(r'\s*(?:/|,|and|or|–|--)\s*(?:Tags?\s*)?[\[`(]*('+TAGTOK+r')\b(?![.\d])')
    for pos,tag in sorted(seen_tagpos.items()):
        e=pos+4
        while True:
            e2=re.match(r'[`\]})]*(?:\(https?://[^)]*\))?\)?',text[e:]).end()+e
            m=LISTC.match(text,e2)
            if not m: break
            t2=m.group(1); e=m.end()
            if not re.search('[A-Z]',t2) and not t2.startswith('0'): break
            if m.start(1) not in seen_tagpos and not any(abs(m.start(1)-q)<60 and tt==t2 for q,tt in seen_tagpos.items()):
                seen_tagpos[m.start(1)]=t2; rows.append(('Stacks','Tag '+t2,t2,'stacks:list'))
    tagpos=sorted(seen_tagpos)
    for m in STNOTAG.finditer(text):
        seg=m.group(1); a,b=m.start(),m.end()
        if any(a-5<=p<=b+70 for p in tagpos): continue
        seg=clean(re.split(r'\)\s|\.\s+[A-Z]|\*\)',seg)[0])[:120]
        if len(seg.split())<2 or re.match(r"(?:Project|entry|entries|tag|tags|form|amplitude)\b",seg,re.I): continue
        rows.append(('Stacks',seg,'','stacks:notag'))
    hasst=bool(tagpos) or 'Stacks' in text
    for m in NUM3.finditer(text):
        if any(m.start()-10<=p<=m.end()+90 for p in tagpos): continue
        if not hasst or int(m.group(1).split('.')[0])<10: continue
        rows.append(('Stacks',clean(m.group(0))+' (number only, no tag)','','stacks:number-only'))
    nocite=CITE.sub(lambda m:' '*len(m.group(0)),text)
    for k,rx in RX:
        for m in rx.finditer(nocite):
            pl=tail(text,m.end())
            if k in('Poonen','nLab'): pl=m.group(0)
            rows.append((k,pl,'','name'))
    for m in CITE.finditer(text):
        for key in m.group(2).split(','):
            key=key.strip(); k=BIBKEYS.get(key)
            opt=clean(m.group(1) or '') or (tail(text,m.end(),90) if ',' not in m.group(2) else '')
            if k is None: rows.append(('UNKNOWN-CITEKEY:'+key,opt,'','cite'))
            elif k!='Stacks': rows.append((k,opt,'','cite'))
            elif not re.search(TAGTOK,m.group(1) or '') : rows.append(('Stacks',clean(m.group(1) or ''),'','cite'))
    if ismd:
        for m in NUM2.finditer(text):
            ctx=nocite[max(0,m.start()-160):m.start()]
            if OTHER.search(ctx) or 'Stacks' in ctx or re.search(r'https?://|arXiv',text[max(0,m.start()-200):m.end()+60]): continue
            rows.append(('UNIDENTIFIED-NUMBERED',clean(m.group(0)),'','number2'))
    for m in LINK.finditer(text):
        a=ARXIV.search(m.group(2))
        if a:
            i=(a.group(1) or a.group(2)); k=ARX.get(i,'arXiv:'+i)
            rows.append((k,re.sub(r'^(?:[A-Z][\w–-]+,\s+|arXiv:\S+$|loc\. cit\.$)','',clean(m.group(1))),'','arxiv-link'))
    for m in ARXIV.finditer(text):
        i=(m.group(1) or m.group(2)); k=ARX.get(i,'arXiv:'+i); rows.append((k,'','', 'arxiv-id'))
    for m in URL.finditer(text):
        u=m.group(0).rstrip('.,;')
        if re.search(r'stacks\.math\.columbia\.edu|arxiv\.org|ncatlab|poonen',u): continue
        k=next((d for pat,d in URLMAP if pat in u),'URL:'+u)
        if k: rows.append((k,'','','url'))
    return rows
def dedupe(rows):
    # drop empty-place rows of a doc when a non-empty place row exists for the same doc; drop places that are prefixes of longer ones
    by=collections.defaultdict(list)
    for r in rows: by[r[0]].append(r)
    out=[]
    if 'Stacks' in by:
        best={}
        for r in by['Stacks']:
            if r[2] and len(r[1])>len(best.get(r[2],'')): best[r[2]]=r[1]
        by['Stacks']=[(r[0],best[r[2]],r[2],r[3]) if r[2] else r for r in by['Stacks']]
    for k,rs in by.items():
        places=sorted({(r[1],r[2]) for r in rs},key=lambda x:-len(x[0]))
        keep=[]
        for p,t in places:
            if p=='' and keep: continue
            if not t and any(q.startswith(p) or p in q for q,_ in keep if not _): continue
            keep.append((p,t))
        for p,t in keep:
            pat=sorted({r[3] for r in rs if r[1]==p and r[2]==t})
            out.append((k,p,t,'+'.join(pat)))
    return out
# ---------- sources ----------
ids={}; units=[]
for f in sorted(glob.glob(BP+'/master/blueprint/**/*.md',recursive=True)):
    t=open(f,encoding='utf8').read()
    m=re.match(r'\+\+\+\n(.*?)\n\+\+\+\n',t,re.S)
    fm=m.group(1) if m else ''; body=t[m.end():] if m else t
    im=re.search(r'^id = "([^"]+)"',fm,re.M); nid=im.group(1) if im else ''
    tm=re.search(r'^title = "(.*)"\s*$',fm,re.M)
    if tm: body=tm.group(1)+'\n\n'+body
    ids[nid]=f
    units.append((nid,os.path.relpath(f,LIT),body,True))
def mapid(l):
    for c in (l,l.replace(':','-'),'sk-'+l.replace(':','-'),l.replace(':','-').replace('lemma-','lem-')):
        if c in ids: return c
    return ''
texfiles=[BP+'/master/wholeblueprint-final.tex']+sorted(glob.glob(BP+'/slopmaster2/**/*.tex',recursive=True))+sorted(glob.glob(BP+'/slopmaster2/**/*.lean',recursive=True))+sorted(glob.glob(BP+'/slopmaster2/**/*.md',recursive=True))
for f in texfiles:
    t=open(f,encoding='utf8',errors='replace').read()
    t=re.sub(r'(?m)^(?:import|open|set_option)\s.*$','',t) if f.endswith('.lean') else t
    bib=re.search(r'\\begin\{thebibliography\}',t)
    if bib: t=t[:bib.start()]
    rel=os.path.relpath(f,LIT)
    parts=re.split(r'\\label\{([^}]+)\}',t)
    units.append(('',rel+'#(preamble)',parts[0],False))
    for i in range(1,len(parts),2):
        lab=parts[i]; units.append((mapid(lab),rel+'#'+lab,parts[i+1],False))
n=0
with open(OUT,'w',encoding='utf8') as o:
    o.write('node_id\tsource\tdocument_key\tdocument\tplace_as_cited\tstacks_tag\textraction_pattern\n')
    for nid,src,body,ismd in units:
        for k,p,t,pat in sorted(dedupe(scan(body,ismd))):
            o.write('\t'.join([nid or '-',src,k,NAME.get(k,k),p or '(no place given)',t,pat])+'\n'); n+=1
print('rows',n,'units',len(units))
