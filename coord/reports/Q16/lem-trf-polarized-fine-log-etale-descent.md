# Worker report: lem-trf-polarized-fine-log-etale-descent

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-polarized-fine-log-etale-descent.json`: statement unchanged; four assembly steps, 2055 characters total, replacing the returned eight-step 5450-character proof.
- `dag/nodes/sec-trace-formula/lem-trf-log-structure-fixed-scheme-enhancement.json`: statement-only, status unsplit, no Mathlib match. Fine log enhancement on a prescribed scheme over a fine log base, including descent of local Noetherianity, the structural log morphism and conditional fs charts.
- `dag/nodes/sec-trace-formula/lem-trf-log-morphism-fixed-map-etale-lifting.json`: statement-only, status unsplit, no Mathlib match. Logarithmic lifting of a prescribed scheme morphism, including equality detection, the equation over a log base and inverse comparisons. This applies to arbitrary log structures, not only fine ones.
- `citations.json`: a verbatim quotation for every use in every assembly step.
- `searches.jsonl`, `search-results.json`: actual search log and full returned search results. `repair.py` and `write_report.py` are sandbox-only reproducibility scripts; they are not project files.

## Attachments

None. A search of `lean/WeilConjectures/` for the blueprint tag and polarized/fine-log notions gives no declaration proving the item. The current `lean/Sheaf/AlgebraicGeometry/PolarizedFineLogEtaleDescent.lean:212` theorem has `sorry` at line 224. Its docstring still records the same eight arguments, so it is material for this repair, not a finished attachment.

## WANTED

None. All source documents used here are present. No SGA source was used.

## What was wrong and what changed

This repairs the human's 2026-10-21 batch5 re-split return: the retained proof was too large to leave as a single proof task. At session start the sandbox had only dispatcher marker files, with no node, report or search log; I therefore copied the current read-only repository item, which has exactly the eight step sizes in the return (515, 508, 528, 761, 256, 1385, 569, 928). Its statement, source, old Mathlib searches, provenance, blueprint ancestry, Lean metadata and review metadata are retained. No old search was invented or rerun as if new. The new searches belong to the two new statements.

The argument is now divided into two substantive obligations of comparable size. The first must construct a log structure and structural morphism on an already supplied scheme, accounting for Noetherianity and saturated charts. The second must glue the inverse-image log sheaf map of an already supplied scheme map, check the base equation, and construct inverse comparisons after changing the source cover. Neither supplies scheme effectivity or polarized scheme descent. Neither restates the parent or all its clauses. The assembly retains the independent existing polarized scheme theorem and underlying scheme-map descent.

No statement dispute or source correction was found. No open work is omitted: the new nodes are deliberately unsplit, with no proof, proof dependency or proof sketch embedded in their statements. The entire previous argument is preserved below as the handoff material for those later workers.

## Allocation of every old argument

| Old step | New location | Mathematical obligation retained |
| --- | --- | --- |
| 1 | Assembly step 1; existing polarized-scheme node | Both normalized cocycles, affine-local relative ampleness, scheme and invertible-module effectivity. |
| 2 | Assembly step 2 and lem-trf-log-structure-fixed-scheme-enhancement | Base-change identifies the actual covering of X; local Noetherianity is proved before log descent. |
| 3 | Assembly step 2 and lem-trf-log-structure-fixed-scheme-enhancement | Identify X_i times_X X_j by the fibre-product universal property, then glue the fine log structures over the structure sheaf with normalized cocycle. |
| 4 | lem-trf-log-structure-fixed-scheme-enhancement | Use A=f^(-1)M_S, not an assumed log structure, to construct the base morphism; its compatibility is part of the conclusion. |
| 5 | lem-trf-log-structure-fixed-scheme-enhancement | Transport saturated charts on the same etale cover. |
| 6 | Assembly step 3; polarized scheme uniqueness; lem-trf-log-morphism-fixed-map-etale-lifting | The unique polarized scheme comparison over S, its line-bundle map and inverse, gluing of the log comparison, inverse equations, base equations and uniqueness of every component. |
| 7 | Assembly step 4; existing fpqc lemmas | Descend the underlying map first; uniqueness with target S proves its scheme-level base equation. |
| 8 | Assembly step 4 and lem-trf-log-morphism-fixed-map-etale-lifting | Strictness identifies the actual source sheaf; construct the log lift from arbitrary inverse-image sheaves; compare both composites from M_S and prove uniqueness. |

## Full retained argument for future workers

The following is the previous item proof, copied verbatim, not shortened. These are handoff notes in this report; the two new nodes remain statement-only.

### Old step 1

Forget the log structures and apply [lem-trf-polarized-scheme-etale-descent]. The underlying $\theta_{ij}$ have the identity and cocycle conditions; the specified $\theta_{ij}^*L_j\simeq L_i$ have their own identity and cocycle conditions, so the line-bundle datum meets the corrected child hypothesis. Relative ampleness is exactly ampleness after restriction to every affine open of $U_i$. Obtain $f:X\to S$, an invertible module $L$, and compatible identifications $X\times_SU_i\simeq X_i$ carrying $L$ to $L_i$.

Cited statements: lem-trf-polarized-scheme-etale-descent.

### Old step 2

Under these identifications the maps $p_i:X_i\to X$ are the base changes of $U_i\to S$ along $f$. Thus [lem-weil-pbc-etale-covering-base-change] makes $\{p_i:X_i\to X\}$ a jointly surjective etale cover of the descended $X$. Each $X_i$ is locally Noetherian, since it is a fine log scheme in the sense of [def-trf-fs-log-blowup]. Apply [lem-trf-etale-local-noetherian-descent] to this cover: $X$ is locally Noetherian. This establishes the underlying-scheme hypothesis of fine-log descent before applying it.

Cited statements: lem-weil-pbc-etale-covering-base-change, def-trf-fs-log-blowup, lem-trf-etale-local-noetherian-descent.

### Old step 3

Use the cover $\{X_i\to X\}$ of Step 2. The overlap $X_i\times_XX_j$ identifies with $X\times_SU_{ij}$ by the fibre-product universal property. The log parts of $\theta_{ij}$ therefore identify the restrictions of $M_{X_i}$ and $M_{X_j}$ on precisely these overlaps, over the structure sheaf. Their identity and triple cocycle follow from those of the given log isomorphisms. By [lem-trf-fine-log-structure-etale-descent] they glue to a fine log structure $M_X$ on $X$ with compatible identifications $M_X|_{X_i}\simeq M_{X_i}$.

Cited statements: lem-trf-fine-log-structure-etale-descent, def-pc-fibre-product.

### Old step 4

Construct the log structure map for $f$. Let $A=f^{-1}M_S$, equipped with $f^{-1}M_S\to f^{-1}\mathcal O_S\to\mathcal O_X$, and let $B=M_X$. On $X_i$, the given log morphism $X_i\to U_i$ followed by the strict log morphism $U_i\to S$ gives $A|_{X_i}\to M_{X_i}=B|_{X_i}$. These maps agree on $X_i\times_XX_j$ because $\theta_{ij}$ is a log isomorphism over $U_{ij}$. The arbitrary-monoid-sheaf clause of [lem-trf-fine-log-structure-etale-descent] gives a unique $f^\flat:f^{-1}M_S\to M_X$ compatible with the structure maps. Together with $f$ this is a log morphism by [def-trf-fs-log-blowup]. Its restrictions are the specified log morphisms, so the identifications of Step 1 are now over the log base $S$ and induce the original polarization and overlap data.

Cited statements: lem-trf-fine-log-structure-etale-descent, def-trf-fs-log-blowup.

### Old step 5

If every $X_i$ is fs, its log structure has etale-local charts by fine saturated monoids. Apply the saturated-chart clause of [lem-trf-fine-log-structure-etale-descent] to the same cover of $X$. It gives saturated charts for $M_X$, and therefore $X$ is fs.

Cited statements: lem-trf-fine-log-structure-etale-descent.

### Old step 6

For two descents $(X,M_X,L)$ and $(X\prime,M_{X\prime},L\prime)$ with the specified identifications, let $h_i:X_i\to X\prime$ be the underlying comparison isomorphisms followed by projection to $X\prime$. They agree on $X_i\times_XX_j$. By [lem-weil-pbc-fpqc-finer-than-etale] the cover of Step 2 is fpqc, and [lem-weil-pbc-fpqc-representable-descent] descends the $h_i$ to a unique $h:X\to X\prime$. Its two composites to $S$ agree on the cover, so uniqueness of that same descent with target $S$ shows $h$ is over $S$. Applying the same argument on $X\prime$ descends the inverse comparisons; the two inverse equations hold globally by uniqueness after restriction. The uniqueness clause of [lem-trf-polarized-scheme-etale-descent] gives the compatible invertible-module isomorphism for this same underlying $h$. The local log comparisons are maps $h^{-1}M_{X\prime}|_{X_i}\to M_X|_{X_i}$. Apply the arbitrary-monoid-sheaf clause of [lem-trf-fine-log-structure-etale-descent] to descend them and their inverse comparisons. Its uniqueness makes their composites identities and makes the resulting log isomorphism commute with the maps from $M_S$, since both assertions hold locally. Every compatible log isomorphism has this underlying scheme map and this monoid-sheaf map by the same two uniqueness assertions. This proves unique compatible isomorphism of the polarized log descents.

Cited statements: lem-weil-pbc-fpqc-finer-than-etale, lem-weil-pbc-fpqc-representable-descent, lem-trf-polarized-scheme-etale-descent, lem-trf-fine-log-structure-etale-descent.

### Old step 7

For the final assertion write $q_a:T_a\to T$ and $g_a:T_a\to Z$ for the given strict etale cover and compatible log $S$-morphisms. The underlying $g_a$ agree on $T_a\times_TT_b$. By [lem-weil-pbc-fpqc-finer-than-etale] this is an fpqc cover, so [lem-weil-pbc-fpqc-representable-descent] produces a unique scheme map $g:T\to Z$ with $gq_a=g_a$. If $t:T\to S$ and $z:Z\to S$ are the structure maps, then $(zg)q_a=zg_a=tq_a$ for every $a$. The uniqueness in representable descent, now with target $S$, implies $zg=t$; hence the underlying descended map is an $S$-morphism.

Cited statements: lem-weil-pbc-fpqc-finer-than-etale, lem-weil-pbc-fpqc-representable-descent.

### Old step 8

Equip $A=g^{-1}M_Z$ with the composite $g^{-1}M_Z\to g^{-1}\mathcal O_Z\to\mathcal O_T$ and put $B=M_T$. Strictness of $q_a$ identifies $M_{T_a}$ with $M_T|_{T_a}$, so the log parts of $g_a$ give maps $u_a:A|_{T_a}\to B|_{T_a}$ over $\mathcal O_{T_a}$. They agree on overlaps because the given $g_a$ agree as log morphisms. Apply the arbitrary-monoid-sheaf clause of [lem-trf-fine-log-structure-etale-descent] on the locally Noetherian scheme $T$: it gives a unique $g^\flat:g^{-1}M_Z\to M_T$ over $\mathcal O_T$. By [def-trf-fs-log-blowup], $(g,g^\flat)$ is a log morphism. It is over the log base $S$: the maps $t^{-1}M_S\to M_T$ obtained from $t$ and from the composite $zg$ agree after every $q_a$, since the $g_a$ are log $S$-morphisms, and the uniqueness in the same sheaf clause makes them equal. The scheme-map uniqueness in Step 7 and the monoid-map uniqueness here give the required uniqueness of the log $S$-morphism.

Cited statements: lem-trf-fine-log-structure-etale-descent, def-trf-fs-log-blowup.

## Suggested separate proof tasks

For lem-trf-log-structure-fixed-scheme-enhancement, start with the actual cover of the fixed X. Apply `lem-trf-etale-local-noetherian-descent` before using `lem-trf-fine-log-structure-etale-descent`. The latter's statement supplies a fine log structure with the labelled comparisons, plus its conditional saturated-chart conclusion. The prescribed f_a maps produce maps from A=f^(-1)M_S to the glued M_X on each V_a; the hypothesis phi_ab f_a^flat=f_b^flat is exactly the overlap equation. Equip A with the composite structure map through f^(-1)O_S and O_X. The arbitrary-monoid-sheaf clause of the same existing lemma gives F^flat, so the log morphism F has precisely the given underlying map f and labelled restrictions. The construction does not descend a scheme and cannot prove the parent without the polarized-scheme theorem.

For lem-trf-log-morphism-fixed-map-etale-lifting, retain the arbitrary inverse-image sheaf A=g^(-1)M_Z and B=M_T, with composite structural map to O_T. Strictness identifies each local source sheaf with the restriction of B. Apply the arbitrary-monoid-sheaf clause of `lem-trf-fine-log-structure-etale-descent` to the given maps. For the base assertion, the two maps from t^(-1)M_S to M_T agree after every q_a; the same clause's uniqueness applied with that source makes them equal globally. Equality detection uses its uniqueness with source g^(-1)M_Z. For inverses, when g is a scheme isomorphism, use the etale cover gq_a of Z. The inverses of the local sheaf isomorphisms give log lifts of the fixed inverse scheme map k=g^(-1) on that cover. Glue them by the same arbitrary-sheaf clause. After restriction, the composites in both orders are the identity monoid maps, so uniqueness gives the two inverse equations. The base equation for the inverse follows either by composing zG=t with the inverse or by the same local test. This includes the change of domain of the inverse, which cannot be suppressed as a mere identification. No fine/fs assumption is needed for this task.

The two tasks take the same existing sheaf-descent theorem as a black box but construct different data: one glues the object and its map to S; the other glues maps between fixed objects and checks inverse/base identities. Their simultaneous proof work does not depend on one another. These are structured expansions of ILO's descent sentence, not separately stated numbered results of ILO. Their source fields explicitly indicate this.

## Searches read

I searched the whole DAG by statement text for log structures/log schemes/log morphisms combined with descent, gluing or strict etale locality; searched the current blueprint by `log descent`, `log structure`, `log morphism`, `strict etale`, `polarized` and `logarithmic`; and ran `blueprint_refs.py ancestor lem-trf-polarized-fine-log-etale-descent`. The only blueprint matches for `logarithmic` are tensor traces and the zeta definition, which do not state either new result. The nearest ancestor is `lem-trf-local-term-locality`; each new node has the item's full via chain with the item prepended and a specific place in the ILO chart-descent branch. Both proposed new ids are absent from the entire DAG. A grep of upstream project declarations finds no completed logarithmic result covering either statement.

Each new node has LeanFinder, Loogle, grep and LeanSearch queries, plus a second phrasing and a second grep. I read the hits: the first node's natural-language searches find scheme etale categories, etale morphism properties and their descent; none constructs a log structure or its map from f^(-1)M_S. The second node's first semantic search finds valuative criteria and etale morphisms; the second finds Zariski scheme/sheaf gluing. Its Loogle sheaf hom_ext hits are extensionality for underlying natural transformations or sections, not logarithmic lifting with base/inverse clauses. Grep finds no LogStructure/FineLog/LogScheme API; the sole logarithmic-text hit is the unrelated elliptic-curve logarithmic height. The second node's LeanSearch request returned unavailable and is recorded with that verdict, not no match. Every recorded query is copied exactly from a real msearch invocation and its full answer remains in search-results.json. The unchanged item already records its earlier complete Mathlib searches, which are preserved.

## Not duplicates

lem-trf-log-structure-fixed-scheme-enhancement vs lem-trf-etale-local-noetherian-descent: shared Tag 034C; the existing node proves only local Noetherianity, while the new node constructs a fine log structure, specified overlap identifications and a structural log map on a prescribed scheme. It uses that existing result in the future proof rather than duplicating its conclusion alone.
lem-trf-log-structure-fixed-scheme-enhancement vs lem-trf-fine-log-structure-etale-descent: the existing result has an already locally Noetherian base scheme and no map to a fixed log base; the new result first descends local Noetherianity and then constructs the prescribed scheme map's logarithmic lift from compatible local maps to S. Its conclusion includes that relative construction, not only the descended monoid sheaf.
lem-trf-log-structure-fixed-scheme-enhancement vs lem-trf-polarized-fine-log-etale-descent: the new node starts with the scheme and underlying map already given, has no invertible modules or relative ampleness, and asserts no effectivity of the scheme datum, no polarized uniqueness and no source locality of morphisms.
lem-trf-log-morphism-fixed-map-etale-lifting vs lem-trf-fine-log-structure-etale-descent: its arbitrary-sheaf clause glues homomorphisms over O_T; the new node applies that to the inverse image of a fixed target log structure, checks composites from a log base and constructs the inverse log morphism on the cover gq_a of the target. It asserts the resulting log morphism and inverse/base equations, which the existing statement does not state.
lem-trf-log-morphism-fixed-map-etale-lifting vs lem-trf-polarized-fine-log-etale-descent: the new node presupposes the global scheme map g, allows arbitrary log structures, and proves neither existence of g nor any polarized object descent. The parent still has to descend g and its scheme-level equation over S using the existing fpqc lemmas.
lem-trf-log-structure-fixed-scheme-enhancement vs lem-trf-coherent-log-ideal-chart-construction: that node constructs chart blowups for coherent ideals and invokes polarized descent; it does not give fixed-scheme relative log enhancement for arbitrary compatible local structures.
lem-trf-log-morphism-fixed-map-etale-lifting vs def-trf-fine-log-scheme-morphisms: that is a definition of maps and their relative-test presentations, not an existence or local-isomorphism theorem.

## Review by Q16

I read the item and every statement used in its new assembly, and the fine-log-structure and etale-local-Noetherianity statements underlying the extracted work. For the source, I read ILO VI 1.1 on printed p.69 (PDF p.75), where fine/fs means etale-local fine/fs charts and the locally Noetherian convention is explicit; and VIII 3.3.4(ii), 3.3.8--3.3.9 on printed pp.107--108 (PDF pp.113--114), where strict etale charts and the final descent sentence supply this branch. Neither new node changes that convention. I also read Stacks descent.tex Tag 034C, `lemma-Noetherian-local-fppf`, and Tag 023Q, `lemma-fpqc-universal-effective-epimorphisms`; topologies.tex Tag 022C, `lemma-zariski-etale-smooth-syntomic-fppf-fpqc`, and Tag 022D, `lemma-fpqc`; spaces.tex Tag 02WW, `theorem-presentation`; spaces-descent.tex Tag 04W8, `proposition-fpqc-descent-quasi-coherent`, and Tag 0D3C, `lemma-descending-property-ample`. These justify precisely the original scheme/polarization and sheaf route, without introducing another route. The new statements make explicit the fixed-object and fixed-map logarithmic arguments in ILO's descent sentence; they are not attributed to a more specific theorem than the source contains.

Assembly step 1 uses the actual statement of `lem-trf-polarized-scheme-etale-descent`: its theta and lambda identity/cocycle hypotheses and affine-open ampleness condition are exactly the item hypotheses. It supplies the scheme and module, including every labelled identification. I did not cite the definition of polarization for an effectivity theorem.

Assembly step 2 uses the statement of `lem-weil-pbc-etale-covering-base-change` for the actual scheme projections X_i to X. `def-pc-fibre-product` states the universal property, so identifying the double overlaps is a direct application, not a new non-elementary comparison. The new fixed-scheme-enhancement statement explicitly takes a scheme map f and a cover by locally Noetherian fine log schemes; that hypothesis follows from the item's fine-log convention. Its required over-base equation follows from the given theta being log isomorphisms over U_ij and the strict maps U_i to S. Its conclusions supply local Noetherianity before log descent, the fine log structure, its structural map to S, and the conditional fs property. All these are in the new statement, not merely in the handoff sketch.

Assembly step 3 uses polarized scheme descent's unique compatible isomorphism over S, including the line-bundle component. Thus the underlying h and its inverse are obtained without a second scheme construction. The new fixed-map-lifting statement supplies the unique log lift of this h, its base equation, and its log inverse because the local comparisons are isomorphisms of the restricted monoid sheaves. This avoids treating the local scheme maps X_i to X' themselves as isomorphisms: the scheme isomorphism is the global h, while its local log sheaf comparisons are isomorphisms. Uniqueness of the line-bundle comparison is inherited from the polarized statement, and log-lift uniqueness is explicitly a conclusion of the new node.

Assembly step 4 uses `lem-weil-pbc-fpqc-finer-than-etale` only to convert the given jointly surjective etale covering to the fpqc condition in `lem-weil-pbc-fpqc-representable-descent`. That latter statement really gives existence and uniqueness of the underlying morphism with arbitrary scheme target. Applying its uniqueness to target S proves zg=t. The fixed-map-lifting node is then applied to that now prescribed g; strictness is essential for replacing M_Ta by the restriction of M_T. Its relative clause proves the equation of log maps, and its uniqueness combined with scheme uniqueness proves the final assertion. The off-unit fpqc results remain declared generic tools in split_report.tool_uses, as in the retained item; no new off-unit proof route is introduced.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 with the node statements open. New nodes are statement-only with empty proof/proof_deps, introduce every object and hypothesis, and cite definitions actually defining log structures, schemes, fine log schemes, etale coverings, local Noetherianity and fibre products. Sources name the Stacks tag and label where a Stacks fact is involved. No source tag is being used to define a notion. All stored TeX has single mathematical escapes after JSON parsing. The original item statement is identical. The extracted nodes are neither mere individual clauses of the parent nor the whole parent under another id: the fixed underlying scheme/map hypotheses cut out the independent log arguments, and the parent still performs polarized scheme effectivity and underlying-map descent. Proof lengths are comparable (old steps 2--5: 2053 characters; old steps 6 and 8: 2313 characters), and the new parent has no step over 2000 characters.

Small cases: an empty jointly surjective cover forces X or T empty, so both enhancements and maps are unique on the empty site. An identity cover gives the given log structure/map directly. Repeated cover indices require the diagonal identity and triple cocycle, which remain explicit in the first new node. Trivial log structures recover ordinary scheme maps. A fine nonsaturated chart such as the additive monoid generated by 2 and 3 in N remains permitted; saturation is concluded only when the local charts are saturated. For the second node I checked a nontrivial base log point and the identity scheme map with local log automorphisms: the equation over S is an additional hypothesis on the local maps and cannot be inferred just from the equation of underlying schemes. The statement retains it. For the inverse clause, a scheme isomorphism alone is insufficient (multiplication by 2 on a standard-log-point N chart is not a log isomorphism); the new statement also requires the local inverse-image monoid maps to be isomorphisms. The target cover gq_a is then etale and jointly surjective because g is an isomorphism. No affine-intersection, quasi-compactness or unmentioned noetherian hypothesis was added.

The return's size defect is repaired by adding exactly two independent unsplit proof tasks and replacing the parent proof with a short assembly, retaining all previous reasoning in this report. The citations file quotes every cited statement verbatim. No agents were started, no Lean files were written, and no compiler, Lake or build command was run.

## Unfinished work

Only the deliberate future proof tasks in the two new unsplit nodes. The requested stage-1 repair itself is complete subject to the required server dry run and delivery.
