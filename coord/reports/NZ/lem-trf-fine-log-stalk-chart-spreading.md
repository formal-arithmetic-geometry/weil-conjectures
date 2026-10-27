# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fine-log-stalk-chart-spreading.json`: repaired item; unchanged statement and statement dependencies, four assembly steps, 1888 proof-text characters.
- `dag/nodes/sec-trace-formula/lem-trf-finite-monoid-stalk-data-spreading.json`: new statement-only node, status `unsplit`, no Mathlib match. A finite-presentation/filtered-colimit argument for monoid homomorphisms, simultaneous finite equations, affine refinements and canonical stalks.
- `dag/nodes/sec-trace-formula/lem-trf-charted-log-map-local-right-inverse.json`: new statement-only node, status `unsplit`, no Mathlib match. A finite-chart-generator lift of the stalk inverse and its extension across all units.

The sandbox initially contained only dispatcher markers, with no retained node, report or searches. I copied the returned seven-step split from the current read repository. Its seven lengths agree with the return (1403, 841, 595, 834, 421, 738, 489), so it supplies the returned baseline. The exact old proof is retained below and in `original-proof.json`. Existing citations, source metadata, searches and maintainer-owned records are retained in the item. Delivery tooling rebases the permitted split fields on current server main and preserves its maintainer fields. I ran no git command in the read repository and no compiler, Lean, Lake or build command. Only sandbox files were written.

## Attachments

None. I searched `lean/WeilConjectures/` by the exact blueprint tag and by log-structure/chart/stalk notions. No project declaration states the assertion. I also read `lean/Sheaf/AlgebraicGeometry/FineLogStalkChartSpreading.lean`: `AlgebraicGeometry.EtaleLogStructure.exists_affine_chart_of_isStalkChart` has the correct complete statement but its proof is `sorry`, so it is not an attachment. No source was edited.

## Wanted literature

WANTED: Kazuya Kato, “Logarithmic structures of Fontaine–Illusie” (1988), section 1, for the associated-log construction cited in the existing node `lem-trf-associated-log-universal-stalks` and the chart-extension background for this item. It is not among the local literature files. The present proof remains marked agent-written; ILO explicitly refers to that reference and omits this extension argument. No download was made and no SGA source is used.

## What the return required and what changed

The sole return requires spreading the 5321-character proof into at least two new comparable statement-only tasks, keeping this item's statement, keeping every argument and reducing only the assembly to at most 3000 characters. This delivery adds exactly two such tasks, rather than replacing the whole item by a renamed chart-spreading assertion. Neither child asserts that a prescribed stalk chart becomes a chart. The first is about arbitrary monoid sheaves and finite data, with no log structure or chart in its conclusion. The second starts with an actual chart on the target of a log map and constructs only a right inverse, without claiming that the map is a neighbourhood isomorphism; it does not assume that the source has a finite chart. The left-inverse argument remains explicit in the assembly.

The first child's workload comprises the old small-index/cofinality/finite-data argument (old 1), monoid-presentation lifting (the first part of old 2), and simultaneous equality plus affine restriction from old 6–7. The second comprises the generator-relation inverse lift (old 4) and its associated-log extension and right-inverse identity (old 5). These are comparable multi-part arguments, each with a useful standalone statement. The existing associated-log theorem carries the old 3 construction and the universal-property arguments of old 5–7. The choice of an existing fine chart from old 2 remains in assembly step 1. No old argument has been removed: the original texts and their new assignments are below.

The four assembly steps are all below 2000 characters and their sum is 1888. Both children have empty `proof`, empty `proof_deps` and null `proof_origin`; their statements contain conclusions, not proof sketches. Their proof tasks remain for other workers. I found no statement error in the item and have changed neither its hypotheses nor its conclusion. In particular the specified homomorphism into the full log stalk, rather than only its characteristic quotient, is preserved.

## Searches and blueprint route

Read `dag/chapters/sec-trace-formula.json`, `dag/units/sk-i-curve-zero.json`, and current main-20261015 `lem-trf-local-term-locality.md`. This is a subsidiary chart argument in its monoidal-resolution ancestry, through `lem-trf-log-regular-sharp-chart`; no unit/chapter route is changed. `tools/blueprint_refs.py ancestor` gives `lem-trf-local-term-locality`. New `from.via` records prepend this item to its existing ancestry; each exact `from.place` identifies the chart-extension sentence and the argument extracted. The item keeps its filled place and `same_as=[]`.

Whole-blueprint searches ran for “monoid stalk”, “log chart”, “finite presentation monoid”, “monoid homomorphism”, “log structure”, and the broader “chart”, “monoid”, “logarithm”. None states either child. Whole-DAG searches used monoid/stalk/presentation/inverse/relations keywords on statements, and source tags 03PQ, 002W, 01T6. I opened the two existing monoid/associated-log nodes, the geometric-stalk/cofiltered/affine-cofinal/essential-smallness nodes, and candidate general finite-data nodes, rather than relying on their titles. `lem-sfb-site-fp-stalk-realization` concerns finitely presented modules and construction of a module sheaf; `lem-weil-pbc-finite-structure-algebra-operations-lift` concerns complete Noetherian algebra sheaves along infinitesimal thickenings. Neither is a monoid homomorphism into an arbitrary étale sheaf stalk. The finite-free matrix/germ nodes likewise require modules and do not state the monoid result.

All new-node Mathlib queries were executed with the mandated `msearch.py`, and the exact tool/query pairs are in `searches.jsonl` and the nodes. Each child has LeanFinder, LeanSearch, Loogle and source grep records, with distinct semantic phrasings. Both semantic services answered, as did Loogle. For the finite-data child a second targeted source grep searched `FinitelyPresentable|FinitePresentation|Presentation` under `Algebra/Category/MonCat`, finding no such result. I read the actual candidate source in `Mathlib/CategoryTheory/Presentable/Finite.lean` (Hom preserves colimits assuming categorical finite presentability) and `Mathlib/Algebra/Category/MonCat/FilteredColimits.lean` (construction and underlying-set preservation of filtered colimits). They do not give the conversion from a finitely generated commutative monoid to the needed finite presentation or the geometric-stalk neighbourhood identifications. Thus this is not a one-line specialization. Ring `exists_lift_of_germInjective` assumes ring data and germ injectivity and does not apply. The inverse-lift searches return standard étale rings, locally ringed-space isomorphisms or individual monoid unit maps, not logarithmic structures or their charts. No exact/generalizing match was found; neither child is a Mathlib leaf.

## Review by NZ

I read ILO Exposé VI 1.1 at PDF page 75 / printed p. 69, and VI 3.7(a) at PDF page 81 / printed p. 75. Section 1.1 specifies étale log structures, locally Noetherian schemes, and the distinction between fine and saturated; the end of 3.7(a) says that the restriction of the splitting gives a chart near the point. It supplies no finite-presentation or inverse-lifting proof. Thus both new statements are explicitly agent extractions of that omitted argument, not attributed as verbatim ILO lemmas. For the first child I also read Stacks `etale-cohomology.tex`, Tag 03PQ `lemma-cofinal-etale`, the adjacent `definition-stalk` and representative/equality description, `categories.tex` Tag 002W `lemma-directed-commutes`, and `morphisms.tex` Tag 01T6 `lemma-finite-type-noetherian`. These support exactly the filtered-neighbourhood and Noetherian inputs; the remaining monoid argument is recorded in full below. The existing finite-monoid-presentation node supplies finite relations for the chosen generating tuple, including the empty tuple. I read its whole statement, not its proof, and did not promote the general categorical candidate to a Mathlib leaf.

Assembly step 1 cites the first child's actual Hom-colimit bijection to lift the precise h and its affine/local-Noetherian/refinement clauses to retain germs. The log-definition node supplies exactly the chart notion; fineness itself is an item hypothesis. The geometric-cover-lift statement explicitly gives a lift from the same algebraically closed field to the chosen cover member, so there is no unnoticed residue-field extension. I added `lem-trf-associated-log-universal-stalks` here for its restriction compatibility: the existing q remains a chart after taking the affine refinement. This corrects a potentially implicit restriction citation in my initial assembly. No saturation or freeness of P or Q is used.

Assembly step 2 uses the existing associated-log node's universal property and its pushout stalk formula, including compatibility with R and units. Its statement is exactly what identifies f at the marked stalk with the item's specified pushout map. U is locally Noetherian by the first child, as required by that associated-log theorem. Elementary inversion of the structure-map identity implies that the stalk inverse fixes units and respects alpha; no independent non-elementary lemma is hidden here.

Assembly step 3 uses the second child's displayed equations for k, its unique extension g and its right-inverse identity, not any construction hidden in its future proof. Its hypotheses are checked: q is a global chart on the current U, Q is finitely generated, f is over the identity, and step 2 proved the relevant stalk map invertible. The child deliberately allows an arbitrary log N, so there is no circular assumption that P is already a chart on M.

Assembly step 4 uses the first child's same-germ equality of homomorphisms with finitely generated source, applied to gf composed with iota and to iota in the monoid sheaf N. The equality is on all of P after the refinement. It then uses exactly the associated-log theorem's uniqueness and restriction clauses: the two log endomorphisms agreeing on iota are equal, and the already established fg=id persists. These yield an actual two-sided inverse on W; one stalk being invertible alone is not taken as a general neighbourhood-isomorphism principle. The chart conclusion is the existing associated-log chart clause, and its restriction/stalk compatibility together with the first child preserves the entire h. W is affine and pointed by construction. `citations.json` copies the cited statements verbatim, giving a quote for every use in every step.

For the new finite-data statement I checked all objects and the slice indexing: affine refinements of a fixed pointed U need not be the whole neighbourhood category, but common refinements and equalizers make them cofinal for the stalk and their small skeleton exists from affine essential smallness plus the set of lifts. Étale neighbourhoods are locally of finite presentation, hence locally of finite type by their affine polynomial quotient presentations; 01T6 gives local Noetherianity. No affine intersections are assumed affine. Empty tuples, empty finite families and zero defining relations cause no difficulty: the category is nonempty and the unique map out of the trivial monoid exists. A nonempty marked neighbourhood is automatic from its geometric point. The nonintegral idempotent monoid generated by e with e^2=e is allowed and its single relation must be imposed; the claim does not rely on cancellation. For a finite cyclic group viewed as a monoid its torsion relation is also imposed. Neither units nor the sheaf's section monoids are assumed finitely generated.

For the new right-inverse statement I tested Q the trivial monoid (M is then the unit log structure), Q a group (again its chart only supplies units), and a rank-one chart with its generator a nonunit. In the first two cases g is the canonical unit map; in the last case the lifted generator must satisfy alpha_N(t)=alpha_M(q(1)) and f(t)=q(1) on the actual neighbourhood, and these equations are explicitly in the conclusion. Repeated generators and relations are handled by finite presentation, not by freeness. No global chart on N is asserted and no saturation or integrality is needed for the lemma. Agreement on Q extends over every unit by the log universal property, which is why no finite list of units needs to be shrunk. The source and target maps have the correct direction f:N→M and g:M→N.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 against the actual files: both children are self-contained, cited notions have definition nodes or inline meanings, the colimit and filtered-category terminology explicitly cites `def-weil-pbc-category-colimit`, TeX has one backslash per mathematical command after JSON decoding, new IDs have no pre-existing DAG/blueprint declaration, and there is no proof inside either child. The item cites both children, and neither cites the item or any parent. The existing associated-log and finite-presentation statements are reused without cloning. The only off-unit proof tool in the item is the same geometric-cover lift already used by the returned proof; it is a Mathlib leaf and is explained in `split_report.tool_uses`. I changed no maintained `tool_uses` field. No long non-elementary assembly step remains and no unit realization is fabricated for this non-key subsidiary node. No claim of a completed Lean proof is made.

## Not duplicates

- lem-trf-finite-monoid-stalk-data-spreading vs lem-sbc-composite-fibre-local-models: the existing statement local Noetherian fibre-ring triples for finite-type maps, rather than homomorphisms from arbitrary finitely generated monoids into etale sheaf stalks.
- lem-trf-finite-monoid-stalk-data-spreading vs pqf-def-locnoeth: the existing statement defines local Noetherianity and records its preservation; it does not state monoid Hom spreading or simultaneous germ equations.
- lem-trf-finite-monoid-stalk-data-spreading vs lem-trf-proper-base-change-coherent-conservative: the existing statement coherence and conservativity of oriented-nearby-cycle topoi, not finite monoid data in pointed neighbourhoods.
- lem-trf-finite-monoid-stalk-data-spreading vs lem-trf-fibre-component-relative-associated: the existing statement associated generic points of flat finite-type fibres, not monoid stalk homomorphisms.
- lem-trf-finite-monoid-stalk-data-spreading vs pqf-lem-locnoeth-lft: the existing statement supplies only preservation of local Noetherianity, one input; it has no monoid Hom or finite-data conclusion.
- lem-trf-finite-monoid-stalk-data-spreading vs lem-weil-pbc-etale-local-ring-triples: the existing statement identifies pointed etale ring neighbourhoods with algebraic ring triples; no homomorphisms from finitely generated monoids to arbitrary sheaves are asserted.
- lem-trf-finite-monoid-stalk-data-spreading vs lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered: the existing statement supplies only cofilteredness of neighbourhoods, not the finite-presentation monoid Hom bijection or simultaneous finite data.
- lem-trf-finite-monoid-stalk-data-spreading vs lem-weil-pbc-finite-type-over-noetherian: the existing statement finite-type schemes over Noetherian bases are Noetherian, with a quasi-compactness conclusion absent from and unnecessary for the new lemma.
- lem-trf-finite-monoid-stalk-data-spreading vs lem-weil-pbc-sets-inverse-image-colimits-finite-products: the existing statement inverse image of sheaves on topological spaces preserves colimits and finite limits; not etale neighbourhood lifting from a finite monoid.
- lem-trf-finite-monoid-stalk-data-spreading vs lem-weil-pbc-filtered-colimits-commute-finite-limits: the existing statement abstract finite-limit/filtered-colimit commutation is an input; it does not identify finite monoid presentations or etale stalk refinements.
- lem-trf-finite-monoid-stalk-data-spreading vs lem-weil-pbc-presheaf-pullback-left-exact: the existing statement left adjoint to presheaf pullback for abelian groups, not finite monoid Hom spreading at a geometric point.
- lem-trf-finite-monoid-stalk-data-spreading vs lem-weil-pbc-finite-presieve-filtered-colimit: the existing statement preservation of a finite-presieve sheaf condition under filtered colimits, not Hom from a finitely generated monoid into a stalk.
- lem-trf-finite-monoid-stalk-data-spreading vs aux-weil-pbc-affine-sections-colimit: the existing statement affine evaluation of a filtered colimit of etale sheaves, rather than finite-presentation Hom into the stalk of one arbitrary monoid sheaf.
- lem-trf-finite-monoid-stalk-data-spreading vs lem-weil-pbc-presheaf-pullback-sets-left-exact: the existing statement general presheaf left Kan extension and finite-limit preservation, not finite monoid presentations or pointed etale stalk lifting.
- lem-trf-finite-monoid-stalk-data-spreading vs lem-weil-pbc-finite-algebra-noetherian: the existing statement a module-finite algebra over a Noetherian ring is Noetherian; no etale sheaf or monoid Hom assertion.
- lem-trf-finite-monoid-stalk-data-spreading vs lem-weil-pbc-graded-finiteness-cohomology: the existing statement finite generation of graded coherent cohomology over an algebra, not finite monoid data at a geometric point.
- lem-trf-finite-monoid-stalk-data-spreading vs lem-weil-pbc-constant-sheaf-geometric-stalk: the existing statement the stalk of a constant abelian sheaf is its value, not Hom lifting for arbitrary monoid sheaves.
- lem-trf-finite-monoid-stalk-data-spreading vs lem-pur-affine-line-support-geometry: the existing statement Noetherianity and quasi-compactness for an affine line and its punctured complement; no monoid Hom spreading.

- lem-trf-finite-monoid-stalk-data-spreading vs lem-trf-fine-log-stalk-chart-spreading: the child concerns arbitrary monoid sheaves and has no chart conclusion; the item is a prescribed-chart theorem for a fine log structure.
- lem-trf-charted-log-map-local-right-inverse vs lem-trf-fine-log-stalk-chart-spreading: the child assumes an already charted target and proves a local right inverse for a log map, whereas the item starts with a stalk chart and must construct a two-sided neighbourhood isomorphism.
- lem-trf-charted-log-map-local-right-inverse vs lem-trf-associated-log-universal-stalks: that theorem constructs logification and extends a GIVEN compatible monoid homomorphism; the child must first lift the inverse germ and impose its finite relations and equations.
- lem-trf-finite-monoid-stalk-data-spreading vs lem-trf-fg-commutative-monoid-finite-presentation: that theorem gives finite relations for an abstract monoid; the child realizes prescribed homomorphisms and their equalities on pointed etale neighbourhoods.

## Full retained argument and allocation of the work

The following is the old proof verbatim. These texts are the argument briefs for the new statement-only tasks; they are intentionally in the report rather than disguised as proof inside a new node statement. They also record the exact work preserved by the repair.

### Old step 1

Assignment: New node lem-trf-finite-monoid-stalk-data-spreading: small index category, finite representatives/equalities, local Noetherianity, canonical stalk identifications.

Use a small skeleton of affine pointed etale neighbourhoods: affine etale objects form an essentially small category, and the possible lifts of the fixed geometric point to each object form a set. Affine neighbourhoods are cofinal for stalks, and pointed neighbourhoods are cofiltered; affine refinements of their common sources and equalizers show that the opposite of this skeleton is filtered. For any finite family of sheaves, stalks are their section colimits. Commutation with finite products and equalizers implies the following finite-data rule: finitely many germs have representatives on one common pointed neighbourhood, and finitely many equations between these representatives which hold as germs hold after a further pointed refinement. All later refinements use this rule, allowing the several sheaves to be $M$, $\mathcal O$ or an associated log sheaf. Every such neighbourhood is locally Noetherian: an etale morphism is locally of finite presentation, whose affine polynomial quotient presentations show it is locally of finite type, and the locally-Noetherian finite-type lemma applies to its map to $X$. Neighbourhoods factoring through a fixed pointed etale neighbourhood compute the same stalk: a common refinement with any other neighbourhood exists by cofilteredness, and parallel arrows can be equalized there. Thus subsequent stalk identifications preserve the specified germs.

Original citations: lem-weil-pbc-affine-etale-essentially-small-cover, lemma-weil-pbc-affine-neighbourhood-cofinal, lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered, lem-weil-pbc-filtered-colimits-commute-finite-limits, def-weil-pbc-geometric-stalks, def-weil-etale-morphism, def-sbc-locally-finite-presentation, pqf-lem-locnoeth-lft.

### Old step 2

Assignment: New node lem-trf-finite-monoid-stalk-data-spreading: finite generators and defining relations lift the prescribed h. Assembly step 1 retains the fine-chart choice and the cover-point lift.

Choose a finite generating tuple $p_1,\ldots,p_n$ of $P$. The finite-presentation lemma supplies finitely many defining relations for this tuple. Represent each $h(p_i)$ by a section of $M$ on a common pointed neighbourhood. Each defining relation holds at the specified stalk because $h$ is a homomorphism; impose the finitely many relations by step 1. The presentation's universal property now gives a homomorphism $\widetilde h:P\to M(U)$ with precisely the germ $h$. By fineness of $M$, refine once more to a pointed etale neighbourhood admitting a chart $q:Q\to M(U)$ with $Q$ finitely generated and integral. Such a refinement exists because an etale chart covering has a member through the geometric point, and that member is itself pointed by a lift of the geometric point. No saturation or freeness is assumed for either $P$ or $Q$.

Original citations: lem-trf-fg-commutative-monoid-finite-presentation, def-trf-fs-log-blowup, lem-weil-pbc-etale-cover-geometric-point-lift.

### Old step 3

Assignment: Assembly step 2, using existing lem-trf-associated-log-universal-stalks: construction of N, f and the exact pushout stalk map.

Put $\beta=\alpha\widetilde h$ and let $N=L_U(P,\beta)$, with canonical generator map $\iota:P\to N(U)$. The associated-log universal property extends $\widetilde h$ uniquely to a homomorphism $f:N\to M|_U$ over the identity of $U$. By its stalk formula, $N_{\bar u}=P\oplus_E A^\times$, and $f_{\bar u}$ is exactly $[p,u]\mapsto h(p)u$. The hypothesis of the item says this map is an isomorphism. In particular its inverse fixes $A^\times$ and is compatible with the structure maps to $A$. This proves a stalk assertion only; an inverse on a neighbourhood will be constructed in the next steps.

Original citations: lem-trf-associated-log-universal-stalks.

### Old step 4

Assignment: New node lem-trf-charted-log-map-local-right-inverse: lift inverse Q-generators and impose relations, alpha-compatibility and f-image equations.

Choose a finite generating tuple $q_1,\ldots,q_s$ of $Q$ and finitely many defining relations using the finite-presentation lemma. For each $q_j$ take $n_j=f_{\bar u}^{-1}(q(q_j)_{\bar u})\in N_{\bar u}$, and represent these by sections $t_j$ of $N$ on a common pointed refinement. At the stalk, these sections satisfy every defining relation of $Q$, as well as the finitely many equations $\alpha_N(t_j)=\alpha_M(q(q_j))$ in $\mathcal O$ and $f(t_j)=q(q_j)$ in $M$. The relations hold because $f_{\bar u}^{-1}$ is a monoid homomorphism compatible with the structural maps. Impose all these equations simultaneously by the finite-data rule of step 1. The resulting tuple defines a homomorphism $k:Q\to N(V)$ with $\alpha_N k=\alpha_M q$ and $fk=q$. The identities on the finite generators imply the displayed identities on all of $Q$.

Original citations: lem-trf-fg-commutative-monoid-finite-presentation, lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered, lem-weil-pbc-filtered-colimits-commute-finite-limits, def-weil-pbc-geometric-stalks.

### Old step 5

Assignment: New node lem-trf-charted-log-map-local-right-inverse: extend k across the associated-log structure and all units; obtain fg=id by uniqueness.

Since $q:Q\to M|_V$ is a chart, the chart form of the associated-log universal property extends $k$ uniquely to a log homomorphism $g:M|_V\to N|_V$. Both $fg$ and the identity of $M|_V$ restrict to $q$ on $Q$, since $fk=q$. Uniqueness in that same universal property gives $fg=\mathrm{id}_{M|_V}$. This equality is on the whole neighbourhood, including its unit sheaf; no finite generation of the unit groups is asserted.

Original citations: lem-trf-associated-log-universal-stalks, def-trf-fs-log-blowup.

### Old step 6

Assignment: New node lem-trf-finite-monoid-stalk-data-spreading supplies eventual equality of the two P-homomorphisms; assembly step 4 then applies associated-log uniqueness to get gf=id and the chart conclusion.

At the marked stalk, $f_{\bar v}$ is the isomorphism of step 3. Taking stalks in $fg=\mathrm{id}$ therefore gives $g_{\bar v}=f_{\bar v}^{-1}$ and $(gf)_{\bar v}=\mathrm{id}$. Consequently, for each of the finitely many $p_i$ from step 2, the two sections $gf(\iota(p_i))$ and $\iota(p_i)$ of $N$ have equal germs. Refine once more so that all these equalities hold as sections, using step 1. They then hold for every $p\in P$ by generation. Uniqueness in the universal property of $N=L(P,\beta)$ shows $gf=\mathrm{id}_N$. Thus $f$ and $g$ are inverse isomorphisms on this neighbourhood. The map $P\to M$ is a chart because its induced associated-log homomorphism $f$ is an isomorphism, and its germ is still the originally specified $h$.

Original citations: lem-trf-associated-log-universal-stalks, lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered, lem-weil-pbc-filtered-colimits-commute-finite-limits, def-weil-pbc-geometric-stalks.

### Old step 7

Assignment: New node lem-trf-finite-monoid-stalk-data-spreading supplies affine refinement and canonical stalks; the existing associated-log restriction clause in assembly steps 1 and 4 preserves the chart and full specified germ.

Finally take an affine pointed etale refinement $(W,\bar w)$ using cofinality of affine neighbourhoods. The restriction compatibility of associated log structures restricts the two inverse maps, so $P\to M|_W$ remains a chart. Step 1 identifies its marked stalk canonically with $M_{\bar x}$, and every generator has the original germ $h(p_i)$; hence the whole monoid homomorphism has germ $h$. This gives the affine pointed neighbourhood and the specified chart required in the statement.

Original citations: lemma-weil-pbc-affine-neighbourhood-cofinal, lem-trf-associated-log-universal-stalks, lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered, def-weil-pbc-geometric-stalks.

## Unfinished work and validation

Only the proofs of the two explicitly statement-only children remain for their later workers, as required by this re-split. No proof of the item or of a new child is being represented as Lean-complete. The server `review_split` preliminary check passed. The first full delivery dry run passed at d501cecccaf. I then added an explicit definition citation for colimits/filtered categories to the first child, without changing its mathematical statement, and refreshed the verbatim citation quotes. The final dry run and push terminal outputs are the authoritative delivery evidence.
