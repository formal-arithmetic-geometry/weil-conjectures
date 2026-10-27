## Worker report

Files written (only in this sandbox):

- dag/nodes/sec-trace-formula/lem-trf-etale-affine-quotient-representable.json: unchanged statement; shorter five-step assembly.
- dag/nodes/sec-trace-formula/lem-trf-quotient-map-fppf-local-models.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-quotient-diagonal-fppf-local-models.json: statement, unsplit; no Mathlib match.
- citations.json and this report.

Attachments: none. The project theorem AlgebraicGeometry.AlgebraicSpace.etale_affine_quotient_representable in lean/Sheaf/AlgebraicGeometry/EtaleAffineQuotientRepresentable.lean:70 has sorry, and searching WeilConjectures by the blueprint tag and quotient/relation concepts found no completed declaration. No Lean was written or compiled.

WANTED: none.

The sandbox was empty when this repair began, so I copied the current live item, which has exactly the seven returned steps. There was no earlier sandbox report or search log to reuse. No git command was run in the read clone. The live statement, lean attachment, imported fields, and existing maintainer fields are retained verbatim. The repair addresses the one return point: distribute the proof into at least two comparable independent local-model tasks, delivered statement-only, and leave at most 3000 characters of assembly in the parent. Each new node stops before descent and neither restates a global clause of the item.

## Argument allocation and retained argument

Old step 1 stays parent step 1. Old steps 2 and 3 and the sheaf check at the beginning of old step 4 are allocated to the quotient-map local-model node. The descent-data correspondence and effectivity from old step 4 remain parent step 3. Old steps 5 and 6 and the sheaf check at the beginning of old step 7 are allocated to the diagonal local-model node. The remaining descent in old step 7 remains parent step 5. The two children explicitly conclude natural local representations and separated locally quasi-finite projections, and carry no proof steps or proof dependencies. Their proof tasks are preserved below, rather than discarded or blurred.

Old step 1: Put $j=(s,t)$ and $q:h_U\to F$. Here $h_Z(W)=\operatorname{Mor}_S(W,Z)$ for every $S$-scheme $Z$. Apply [lem-trf-affine-etale-relation-separated-lqf] to obtain that $s,t$ and $j$ are separated and locally quasi-finite. The hypotheses are precisely that $U$ is affine and $(s,t)$ is an etale equivalence relation; $S$ need not be separated.

Old step 2: Fix a scheme $T$ over $S$ and a map $a:h_T\to F$. Write $Q(W)=U(W)/R(W)$. By [lem-weil-pbc-site-sheafification-sections-local], the section $a_T(\mathrm{id}_T)\in Q^\#(T)$ has representatives in $Q(T_i)$ on an fppf covering $\{T_i\to T\}$. Choose representatives $a_i:T_i\to U$ of these equivalence classes. Naturality gives $a_W(g)=F(g)(a_T(\mathrm{id}_T))$ for every $g:W\to T$, so $q a_i=a|_{T_i}$ as natural transformations. This uses only the existence of local representatives, not representability or etaleness of $q$.

Old step 3: Let $G=h_T\times_F h_U$. The kernel-pair identity [lem-trf-etale-relation-kernel-pair] identifies its pullback to $T_i$ with $h_{X_i}$, where $X_i=T_i\times_{a_i,U,s}R$ and the map $X_i\to U$ is $t$ on the second factor. Explicitly, on a test scheme $W\to T_i$, a point of $G$ is a map $u:W\to U$ with $q(u)=q(a_i|_W)$; the kernel-pair identity gives a unique $r:W\to R$ with $s(r)=a_i|_W$ and $t(r)=u$. This is a natural bijection, so it gives the asserted representation. The structure map $X_i\to T_i$ is a base change of $s$ and is separated and locally quasi-finite by [lem-weil-pbc-separated-lqf-base-change] and step 1.

Old step 4: Regard $G$ on the big fppf site of $T$ by $G(W)=\{u:W\to U\mid q(u)=a|_W\}$. The kernel-pair statement [lem-trf-etale-relation-kernel-pair] is an identity of fppf sheaves, so in particular $h_U$ is an fppf sheaf. Hence $G$ is a sheaf: the maps to $U$ glue uniquely on a cover, and their required equality in $F$ can be checked on that cover. Apply [lem-trf-fppf-sheaf-representability-descent-data] to the local schemes $X_i$. Its overlap comparison maps give a scheme descent datum with these very $X_i$. They are separated and locally quasi-finite over $T_i$ by step 3, so [lem-trf-separated-lqf-fppf-effective-descent] makes this datum effective. The representability-if-effective clause of the former lemma then represents $G$ by a scheme over $T$. This proves the first assertion.

Old step 5: Now fix $a:h_T\to F\times F$, with components $a_1,a_2$. Apply [lem-weil-pbc-site-sheafification-sections-local] separately to these two quotient sections. Use pullback stability and composition of coverings, which are the site axioms in [def-weil-pbc-sites-and-cohomology], to take a common fppf refinement $\{T_i\to T\}$. There are maps $u_i,v_i:T_i\to U$ with $q(u_i)=a_1|_{T_i}$ and $q(v_i)=a_2|_{T_i}$. Hence $(u_i,v_i)$ is a map to $U\times_SU$.

Old step 6: Set $H=h_T\times_{F\times F,\Delta}F$. On $W\to T$, its sections are pairs consisting of the structure map and a section $z\in F(W)$ with $z=a_1|_W=a_2|_W$. Thus the fibre is a singleton exactly when $a_1|_W=a_2|_W$, and otherwise empty. On $T_i$ this sheaf is represented by $Y_i=T_i\times_{(u_i,v_i),U\times_SU,j}R$: the kernel-pair identity [lem-trf-etale-relation-kernel-pair] says that $q(u_i|_W)=q(v_i|_W)$ holds exactly when there is a unique $r:W\to R$ with $(s(r),t(r))=(u_i|_W,v_i|_W)$. This describes inverse natural maps on sections. The structure map $Y_i\to T_i$ is a base change of $j$, so it is separated and locally quasi-finite by step 1 and [lem-weil-pbc-separated-lqf-base-change].

Old step 7: The functor $H$ on the big fppf site of $T$ is a sheaf: equality of the two fixed sections of $F$ is local, with a unique section whenever they agree. By [lem-trf-fppf-sheaf-representability-descent-data] the representing schemes $Y_i$ of step 6 carry the corresponding descent datum. By [lem-trf-separated-lqf-fppf-effective-descent] it is effective, since every $Y_i\to T_i$ is separated and locally quasi-finite. The representability-if-effective clause of the former lemma represents $H$ by a scheme over $T$. As $a$ was arbitrary, the diagonal of $F$ is representable.

## Source and search review

I read literature/stacks-project/spaces.tex, Tag 0265, label lemma-presentation-quasi-compact, lines 1466-1600: the first descent calculation and the diagonal cartesian square are the sources of the two child statements. For the second child I use the already approved direct common-fppf-refinement variant: lift the two quotient sections and take fibre products of the two covering families; this avoids needing representability of q to construct a diagonal cover. The source instead first establishes that q is etale and surjective. Both variants use the same kernel-pair model and separated locally quasi-finite descent. The new nodes do not need affineness: separated local quasi-finiteness of s, respectively j, is an explicit hypothesis, supplied in the parent by its existing affine-geometry lemma.

I read the existing statements of lem-trf-etale-relation-kernel-pair (Tag 045Y), lem-weil-pbc-site-sheafification-sections-local (00WB/00WK), and lem-weil-pbc-separated-lqf-base-change (01KU/01TM). The local-model tasks use their actual conclusions: existence of local representatives; unique relation arrows for equality in the sheaf quotient; permanence of both morphism properties. The common refinement uses exactly the covering base-change and composition axioms in def-weil-pbc-sites-and-cohomology. The children inline the equivalence-relation and representable-presheaf notions and cite definitions for scheme, fibre products, topology, sheafification, etale, separated, locally quasi-finite, sheaf, and size. Their statement dependencies introduce notions only; no hidden proof dependency was inserted there.

Searches of the whole DAG by 0265 and quotient/relation/local-model concepts, blueprint_refs.py searches by quotient, equivalence relation, local models, fppf, quotient scheme and diagonal fppf, and project Lean searches found no existing node with either local-model statement. General quotient nodes are global theorems above this item, so citing them would also risk circularity. The existing kernel-pair statement gives the equality identification but neither local lifts nor the geometric local models and their properties. The existing finding-opens lemma concerns saturated opens, not these local models.

Every Mathlib search in the children was run through msearch.py and is in searches.jsonl. Two semantic phrasings were tried, with both quotient-map and diagonal queries. LeanFinder returned etale base-change/pullback facts for the first query and scheme-diagonal restriction/pullback formulas for the second; neither states these quotient-sheaf local-model assertions. LeanSearch's diagonal query was rate-limited and is recorded unavailable; its quotient-map query returned ideal-quotient scheme lifts and universal sheafification lifts, which do not construct these local models. A valid Scheme/pullback Loogle pattern returned open-immersion pullback results, not a quotient-sheaf result; the earlier IsRepresentable identifier query was unrecognized, and is recorded verbatim. Both grep patterns and subdirectory restrictions are in the log. I read Mathlib/AlgebraicGeometry/EffectiveEpi.lean:50-105: its kernel-pair hits concern descent of morphisms along flat surjective affine maps, not the two claims here. No new node is declared a Mathlib leaf.

## Review by Q151

I checked the returned re-split requirement against the actual seven steps, not merely their lengths. The two new tasks each include a genuine lifting plus natural-identification argument and have comparable sizes; neither is elementary in two lines, and neither proves global representability. The exact former text is retained above to make coverage auditable. The five new parent steps have total text length below 3000 characters, with no step over 2000.

Parent step 1 cites the affine-geometry statement, which explicitly supplies all three morphisms s,t,j with both separatedness and local quasi-finiteness and explicitly excludes any assumption that S be separated. Step 2 cites the first child: its s hypothesis was just obtained and its conclusion gives G as a sheaf, the cover, the actual schemes X_i, their natural identifications, and their morphism properties. Step 3 cites the precise descent-data/sheaf correspondence, which supplies comparison isomorphisms for these very local schemes and the representability-if-effective equivalence; the effective-descent statement applies because the cover is fppf and each X_i is separated locally quasi-finite. Step 4 uses the second child with j from step 1; its conclusion gives H as a sheaf and the simultaneous-lift local models Y_i, including both required properties. Step 5 uses the same two descent statements on this new cover and these Y_i. I read descent.tex Tag 02W5 label lemma-descent-data-sheaves, including clauses (1) and (2), and more-morphisms.tex Tag 02W8 label lemma-separated-locally-quasi-finite-morphisms-fppf-descend; neither requires quasi-compactness or local finite presentation of the descended local schemes. All families and test objects stay in the stated size convention. citations.json quotes the exact part of each cited statement used at each parent step.

For the quotient-map child, I checked the orientation X_i=T_i times_(a_i,U,s) R: a test point r maps to t(r), and the kernel pair supplies the inverse uniquely when q(t(r))=q(a_i). Naturality identifies a as the section evaluated at id_T; no use of Yoneda full faithfulness alone replaces the section formula. For the diagonal child, the fibre on W has a unique section when the two a's agree and none otherwise; the relation monomorphism makes the relation witness unique. Both maps u_i,v_i are S-maps, so their pair lands in U times_S U. Refining both covering families by fibre products preserves the fppf-covering condition. The sheaf assertions follow respectively by unique gluing of maps to U with equality checked in F, and by locality of equality in the sheaf F. The represented h_U is an fppf sheaf as already asserted in the existing kernel-pair node.

Small cases checked: for the diagonal relation R=U both local models reduce to ordinary fibre products/equality subfunctors; for U empty a map h_T to its quotient can occur only over empty T, where the empty-cover formulation works; for the pair relation R=U times_S U with U etale separated locally quasi-finite over S the formulas still give the correct possibly empty local fibres. No separatedness of S, quasi-compactness of R, or nonemptiness of T was used. Singleton diagonal fibres rely on monomorphism, not merely on surjectivity onto the relation. I found no statement dispute and changed no statement of the parent. The only correction is the required decomposition and allocation of all old arguments. I checked B1-B10 (statement-only children, self-contained hypotheses, TeX, tags/labels, honest searches, blueprint placement), C1-C8 (actual statement citations and no parent cycle), D1-D5 (strict intermediate tasks and no wholesale relabelling), E1-E7 (hypotheses, objects, natural maps, and small cases).

## Not duplicates

lem-trf-quotient-map-fppf-local-models vs lem-coef-cartesian-grothendieck-colimit-formula: the existing node is about Colimits of Cartesian Grothendieck diagrams inverting transport arrows, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-a1-separated-etale-space-scheme: the existing node is about A separated etale algebraic space over a scheme is a scheme, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-trf-fppf-covering-base-change: the existing node is about Base change of an fppf covering is an fppf covering, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-trf-etale-affine-quotient-representable: the existing parent concludes global representability of both maps; this child supplies only local models for one pullback, prior to effective descent.

lem-trf-quotient-map-fppf-local-models vs lem-trf-fppf-family-affine-effectivity-reduction: the existing node is about Reduction of effective fppf descent for a morphism property to affine singleton covers, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-trf-quasi-affine-fpqc-effective-descent: the existing lemma concerns descent or its reduction, whereas this child supplies the local quotient-sheaf models before applying descent.

lem-trf-quotient-map-fppf-local-models vs lem-trf-separated-lqf-fppf-effective-descent: the existing lemma concerns descent or its reduction, whereas this child supplies the local quotient-sheaf models before applying descent.

lem-trf-quotient-map-fppf-local-models vs lem-trf-etale-relation-quotient: the existing theorem concludes an algebraic-space quotient and etale surjective atlas; this child is an intermediate local-model construction used below that theorem.

lem-trf-quotient-map-fppf-local-models vs lem-trf-affine-etale-relation-separated-lqf: the existing lemma proves separated local quasi-finiteness of s,t,j from affineness; this child assumes one such property and constructs lifts and local representing schemes.

lem-trf-quotient-map-fppf-local-models vs lem-trf-fppf-sheaf-representability-descent-data: the existing lemma concerns descent or its reduction, whereas this child supplies the local quotient-sheaf models before applying descent.

lem-trf-quotient-map-fppf-local-models vs lem-pc-finite-free-stalk-chain-map-lift: the existing node is about Hereditary local extension of one finite free stalk chain map, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-pc-flat-module-descent-affine-charts: the existing lemma concerns descent or its reduction, whereas this child supplies the local quotient-sheaf models before applying descent.

lem-trf-quotient-map-fppf-local-models vs lem-pc-finite-free-stalk-chain-map-pair-lift: the existing node is about Lifting a prescribed pair of finite free chain maps, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-pc-affine-cover-module-tensor-flat-criterion: the existing node is about Affine-cover criterion for tensor module flatness after base change, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs def-pc-stalk-restriction-complex-iso: the existing node is about Canonical restriction-to-stalk comparison on complexes, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-sfb-ringed-derived-tensor-diagrams: the existing node is about Coherence equations for explicit canonical derived comparison maps, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-sfb-ringed-derived-tensor-lift: the existing node is about Symmetric monoidal coherence of a canonical derived tensor lift, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-sfb-internal-tensor-composition-unit-normalization: the existing node is about Internal tensor multiplication is the unit-normalized composition comparison, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-sfb-ringed-derived-two-iso-comparison: the existing node is about Specified geometric 2-isomorphism comparison on derived modules, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-sfb-ringed-derived-adjoint-lift: the existing node is about Normalized ordinary and derived adjoint lifts of ringed-topos morphisms, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-sfb-supplied-tensor-adjunction-normalization: the existing node is about Scalar-extension adjunction with normalized underlying Hom bijection, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs def-sfb-ringed-derived-comparison-data: the existing node is about Data of normalized derived monoidal comparisons of ringed topoi, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-sfb-ringed-derived-composition-comparison: the existing node is about Composition comparison with normalized representative formulas, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-sfb-resolving-derived-adjunction-normalization: the existing node is about Derived adjunction normalized by a left resolving class and K-injectives, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-sfb-ringed-derived-identity-comparison: the existing node is about Identity comparison with normalized representative formulas, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-sfb-ringed-derived-monoidal-comparisons: the existing node is about Monoidal and adjunction normalization of derived ringed-topos comparisons, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-sc-structure-sheaf-cohomology-pullback-composition-pointwise: the existing node is about Pointwise composition law for structure-sheaf cohomology pullback, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-per-noetherian-prime-power-smooth-duality: the existing node is about Prime-power diagonal smooth orientation over a Noetherian base, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-weil-pbc-finite-ring-map-quasi-finite: the existing node is about A finite ring map is of finite type and quasi-finite at every prime, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-weil-pbc-spectral-closed-clopen-decomposition-lift: the existing node is about Decompositions of a closed subset meeting point closures connectedly lift to the spectral space, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs new-node-finite-closed-cover-cohomology-vanishing: the existing node is about Finite closed cover cohomology vanishing, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-sc-closed-union-cohomology-vanishing: the existing node is about Universal cohomology vanishing over a binary closed union, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-sc-empty-space-cohomology-vanishing: the existing node is about Cohomology of an empty topological space, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-sc-whole-closed-subtype-cohomology-vanishing: the existing node is about Vanishing transfer from the whole closed subtype, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-coef-cartesian-grothendieck-colimit-formula: the existing node is about Colimits of Cartesian Grothendieck diagrams inverting transport arrows, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-a1-separated-etale-space-scheme: the existing node is about A separated etale algebraic space over a scheme is a scheme, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-trf-fppf-covering-base-change: the existing node is about Base change of an fppf covering is an fppf covering, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-trf-etale-affine-quotient-representable: the existing parent concludes global representability of both maps; this child supplies only local models for one pullback, prior to effective descent.

lem-trf-quotient-diagonal-fppf-local-models vs lem-trf-fppf-family-affine-effectivity-reduction: the existing node is about Reduction of effective fppf descent for a morphism property to affine singleton covers, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-trf-quasi-affine-fpqc-effective-descent: the existing lemma concerns descent or its reduction, whereas this child supplies the local quotient-sheaf models before applying descent.

lem-trf-quotient-diagonal-fppf-local-models vs lem-trf-separated-lqf-fppf-effective-descent: the existing lemma concerns descent or its reduction, whereas this child supplies the local quotient-sheaf models before applying descent.

lem-trf-quotient-diagonal-fppf-local-models vs lem-trf-etale-relation-quotient: the existing theorem concludes an algebraic-space quotient and etale surjective atlas; this child is an intermediate local-model construction used below that theorem.

lem-trf-quotient-diagonal-fppf-local-models vs lem-trf-affine-etale-relation-separated-lqf: the existing lemma proves separated local quasi-finiteness of s,t,j from affineness; this child assumes one such property and constructs lifts and local representing schemes.

lem-trf-quotient-diagonal-fppf-local-models vs lem-trf-fppf-sheaf-representability-descent-data: the existing lemma concerns descent or its reduction, whereas this child supplies the local quotient-sheaf models before applying descent.

lem-trf-quotient-diagonal-fppf-local-models vs lem-pc-finite-free-stalk-chain-map-lift: the existing node is about Hereditary local extension of one finite free stalk chain map, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-pc-flat-module-descent-affine-charts: the existing lemma concerns descent or its reduction, whereas this child supplies the local quotient-sheaf models before applying descent.

lem-trf-quotient-diagonal-fppf-local-models vs lem-pc-finite-free-stalk-chain-map-pair-lift: the existing node is about Lifting a prescribed pair of finite free chain maps, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-pc-affine-cover-module-tensor-flat-criterion: the existing node is about Affine-cover criterion for tensor module flatness after base change, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs def-pc-stalk-restriction-complex-iso: the existing node is about Canonical restriction-to-stalk comparison on complexes, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-sfb-ringed-derived-tensor-diagrams: the existing node is about Coherence equations for explicit canonical derived comparison maps, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-sfb-ringed-derived-tensor-lift: the existing node is about Symmetric monoidal coherence of a canonical derived tensor lift, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-sfb-internal-tensor-composition-unit-normalization: the existing node is about Internal tensor multiplication is the unit-normalized composition comparison, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-sfb-ringed-derived-two-iso-comparison: the existing node is about Specified geometric 2-isomorphism comparison on derived modules, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-sfb-ringed-derived-adjoint-lift: the existing node is about Normalized ordinary and derived adjoint lifts of ringed-topos morphisms, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-sfb-supplied-tensor-adjunction-normalization: the existing node is about Scalar-extension adjunction with normalized underlying Hom bijection, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs def-sfb-ringed-derived-comparison-data: the existing node is about Data of normalized derived monoidal comparisons of ringed topoi, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-sfb-ringed-derived-composition-comparison: the existing node is about Composition comparison with normalized representative formulas, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-sfb-resolving-derived-adjunction-normalization: the existing node is about Derived adjunction normalized by a left resolving class and K-injectives, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-sfb-ringed-derived-identity-comparison: the existing node is about Identity comparison with normalized representative formulas, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-sfb-ringed-derived-monoidal-comparisons: the existing node is about Monoidal and adjunction normalization of derived ringed-topos comparisons, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-sc-structure-sheaf-cohomology-pullback-composition-pointwise: the existing node is about Pointwise composition law for structure-sheaf cohomology pullback, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-per-noetherian-prime-power-smooth-duality: the existing node is about Prime-power diagonal smooth orientation over a Noetherian base, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-weil-pbc-finite-ring-map-quasi-finite: the existing node is about A finite ring map is of finite type and quasi-finite at every prime, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-weil-pbc-spectral-closed-clopen-decomposition-lift: the existing node is about Decompositions of a closed subset meeting point closures connectedly lift to the spectral space, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs new-node-finite-closed-cover-cohomology-vanishing: the existing node is about Finite closed cover cohomology vanishing, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-sc-closed-union-cohomology-vanishing: the existing node is about Universal cohomology vanishing over a binary closed union, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-sc-empty-space-cohomology-vanishing: the existing node is about Cohomology of an empty topological space, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-diagonal-fppf-local-models vs lem-sc-whole-closed-subtype-cohomology-vanishing: the existing node is about Vanishing transfer from the whole closed subtype, whereas this child concerns local models for an etale equivalence-relation quotient; the whole-file 0265 hit does not give this statement.

lem-trf-quotient-map-fppf-local-models vs lem-trf-quotient-diagonal-fppf-local-models: the first models a quotient-map pullback with a free U-section and one local lift; the second models the equality subfunctor for two fixed sections and needs simultaneous lifts. Neither local conclusion implies the other.
