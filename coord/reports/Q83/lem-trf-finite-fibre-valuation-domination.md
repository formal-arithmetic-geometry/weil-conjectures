# Q83 worker report: lem-trf-finite-fibre-valuation-domination

## Files written

- dag/nodes/sec-trace-formula/lem-trf-finite-fibre-valuation-domination.json: item, statement, now split in nine steps; no exact project attachment or Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-modification-fibre-centre-finite.json: new statement-only unsplit lemma; no Mathlib match.
- citations.json: exact statement quotes for every step/node pair.
- searches.jsonl: actual msearch records, including the retained earlier searches and new searches for the repaired support statement.

The two draft nodes lem-trf-modification-centre-dominance and lem-trf-curve-valuation-centre-generic-or-closed were removed before delivery. The item now carries their arguments.

## Attachments

None. The exact blueprint tag and the modification/fibre/valuation terminology did not reveal a finished declaration under the read-only project source WeilConjectures/. Mathlib's proper valuative criterion supplies individual lifts but not the finite test set or domination criterion.

## Literature wanted

WANTED: Temkin, Stable modification of relative curves, arXiv:0707.3953v3, Section 4.2 (printed pp. 26--27), for lem-trf-finite-fibre-valuation-domination and lem-trf-modification-fibre-centre-finite.
WANTED: the same paper, Section 4.1 (printed p. 25) and the opening reduction in Proposition 4.3.1 (printed pp. 27--28), for the reduced-source formulation and the finite-test application.

I read the public author PDF at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf. No PDF was downloaded into the shared repository. The item retains proof_origin.by = agent because the local archival document is absent.

## Corrections and scope

The imported item statement is unchanged. The proof is expanded from the schematic graph argument in Proposition 4.2.3 rather than citing a newly named version of the item's conclusion.

My first sandbox draft confused points on different models with elements of the common valuation space. It also placed the neighbourhood-isomorphism assertion at exceptional source centres. Both are corrected: Gamma sets now consist of specified centred valuations in a common space, and the support lemma asserts that the modification locus in the normal target is quasi-finite over the valuation base. The item deduces avoidance of target fibre-generics from this assertion.

I also removed the unjustified inference that a point closed in C must lie over the closed point of T. A nonproper curve can have a closed point over a nonclosed base point. Step 8 instead works in the closed inverse image of the original centre and uses the intermediate residue field. This proves the imported dichotomy without adding a base-closed hypothesis.

No work remains on this one-level split. The new support node is intentionally statement-only for a later worker. The reduced-source version of the finite-centre lemma uses finite normalization from Section 4.1: a finite surjective normalization does not change whether a valuation centre is generic in its fibre. This is the extension of the normal-source formulation of Lemma 4.2.2, not a claim that a singular generic centre has a unique valuation branch.

## Not duplicates

- lem-trf-modification-fibre-centre-finite vs lem-trf-finite-fibre-valuation-domination: the support lemma gives finite Gamma sets, their generation by generalizations, and a quasi-finite modification locus. It gives no comparison morphism between two modifications, no centre dichotomy, and no persistence conclusion; those are proved in the item's steps.
- lem-trf-modification-fibre-centre-finite vs def-trf-multipointed-curve: the existing node only defines a flat finitely presented curve with a marking; it proves no theorem about valuation sets or modification loci.
- lem-trf-modification-fibre-centre-finite vs lem-trf-abhyankar-finite-type-field-height: the existing node bounds valuation height over an absolutely finitely generated field; the new node concerns finite fibre-generic centre sets on relative curve modifications.
- lem-trf-modification-fibre-centre-finite vs lem-trf-birational-quasi-modification-common-cover: the existing node constructs an open-covered common refinement from a valuative cover, without identifying finite Gamma sets or modification loci.
- lem-trf-modification-fibre-centre-finite vs lem-trf-birational-riemann-zariski-neighbourhoods: the existing node gives topology, quasi-compactness and local filtered rings for a valuation space; it has no relative one-dimensional finite-centre or locus theorem. Its definition of the valuation-space topology is reused.
- lem-trf-modification-fibre-centre-finite vs lem-trf-geometrically-reduced-eta-normal: the existing node proves eta-normality for geometrically reduced fibres over a normal base, not finiteness or generation of Gamma sets.
- lem-trf-modification-fibre-centre-finite vs lem-trf-marked-curve-finite-type-model: the existing node descends a marked curve to a finite-type integer model, not a finite set of fibre-generic valuations.
- lem-trf-modification-fibre-centre-finite vs lem-trf-marked-nodal-dualizing-degrees: the existing node constructs a dualizing line and computes degrees on components; it says nothing about Gamma generation or modification loci.
- lem-trf-modification-fibre-centre-finite vs lem-trf-no-isolated-contracted-fibre-component: the existing node excludes a proper isolated contracted component for a nodal curve over a Noetherian base; it does not cover arbitrary reduced modifications over valuation bases or finite valuation sets.
- lem-trf-modification-fibre-centre-finite vs lem-trf-nodal-normalization-adjunction: the existing node concerns normalization and the adjunction line on a nodal curve over a field, without the valuation-space assertions.
- lem-trf-modification-fibre-centre-finite vs lem-trf-normal-approximation-finite-eta-modification: the existing node spreads a finite eta-modification to a Noetherian model with reduced geometric fibres; the new lemma allows nonfinite modifications and concerns their fibre-generic valuations and locus.
- lem-trf-modification-fibre-centre-finite vs lem-trf-riemann-zariski-finite-refinement: the existing node gives finite refinements of separable-field models over a finite-type integer scheme; it does not state the finite Gamma theorem for a relative curve over a valuation ring.
- lem-trf-modification-fibre-centre-finite vs lem-trf-valuation-exceptional-closed-image-criterion: the existing node assumes a semistable modification and characterizes stability using exceptional rational components. The new lemma allows arbitrary reduced modifications and asserts the Gamma generalization formula and the quasi-finite modification locus, without a stability assertion.

- lem-trf-modification-fibre-centre-finite vs lem-trf-abhyankar-inequality: the existing node bounds rational rank plus residue transcendence degree for a valued field extension; it gives neither finite centre sets on a model nor their generalization formula or a modification-locus theorem.

## Review by Q83

I read Temkin's definitions before Lemma 4.2.1, both Lemmas 4.2.1--4.2.2, the entire graph proof of Proposition 4.2.3, Section 4.1's finite-normalization observation, and Proposition 4.3.1's finite-test reduction. The new node isolates those finite-set and locus facts. Its normal-source bijection is stated only under normality; the reduced-source version asserts surjectivity, not uniqueness of branches. I read the existing candidate statements listed in Not duplicates and searched the DAG, blueprint, and project source before retaining this one new node.

Step 1 uses the explicit reduced-modification clause of lem-trf-valuation-horizontal-curve-models with empty marking. Its smooth-generic, finite-height separably closed valuation-base hypotheses are exactly available here. The proper-separated valuation-extension statement then gives the unique lift of the specified generic morphism, without needing the curve itself to be proper or separated over T.

Steps 2 and 3 use the new lemma's finite Gamma_0, residual transcendence degree, generation formula and generalization-stability, exactly as quoted in citations.json. The hypothesis on the proposed dominating model says F is contained in Gamma(C'), which yields Gamma(W) contained in Gamma(C'). This avoids the incorrect inclusion of point sets on different models.

Step 4 uses the first clause of sk-lem-nagata-sketch-closure for the quasi-compact common isomorphism open in the quasi-separated product. Proper base change gives proper ambient projections; the closed-immersion/proper-composite statement gives proper graph projections. Reducedness follows on affine opens because a kernel into a reduced ring is radical. The horizontal-curve lemma applies again to these reduced modifications.

Step 5 is the source's final contradiction written explicitly. I checked that lem-kun-closed-points-of-product applies to the two finite-type fibres over the same residue field. The map from the graph fibre to their product is injective on points by the fibre-product universal property and its closed immersion. Thus a point projecting to two closed fibre points is closed, contradicting its being generic in a one-dimensional component. No normality of W is used.

Step 6 uses the new lemma's surjectivity to choose a valuation over every fibre-generic graph point. This prevents contracted components. Over a closed target-fibre point, a positive-dimensional inverse image would contain a source-fibre component; over a generic target-fibre point, the residue-field criterion lem-kun-closed-point-field excludes nongeneric source points. The remaining finite set of source generics is zero-dimensional. The existing relative-dimension-zero/local-quasi-finite equivalence applies because the projection is proper and hence locally of finite type. pqf-lem-proper-lqf-finite has no Noetherian-base assumption, which is essential here.

Step 7 uses finite-birational-normal-iso componentwise. I checked reducedness, the shared dense isomorphism open, and target normality. Finitely many components of a normal scheme are disjoint and open, so the integral version applies on each component; the graph construction has not added a vertical component. The final uniqueness uses the second clause of sk-lem-nagata-sketch-closure and separatedness of W over C.

Step 8 uses lem-kun-closed-point-field twice: first for the nongeneric point in its finite-type one-dimensional fibre over kappa(s), then for the finite-type fibre over kappa(c). Finiteness over kappa(s) implies finiteness over the intermediate field kappa(c). Since c is closed in C its inverse image is closed, giving global closedness. No closedness assumption on s is inserted.

Step 9 uses only the new lemma's quasi-finite-locus assertion: a closed locus containing a fibre-generic point would contain its one-dimensional component, impossible for a quasi-finite T-scheme. The complement is the required isomorphism neighbourhood; the unique valuation lift from step 1 gives persistence there.

For B--E I checked that the new node introduces every object, uses TeX, has inline notion references, contains only a statement, and carries the exact blueprint ancestry. Every proof citation has an exact quote, and proof_deps is the union of uses. The proof carries the graph and dichotomy arguments rather than transferring conclusion clauses to new nodes. No step exceeds 2000 characters. Small cases checked: identity modification (no new contracted valuations), valuation height zero (smooth curves over a field have no nontrivial reduced proper birational modification), reducible normal C (disjoint components), a singular reduced W (multiple valuation branches allowed), a closed original centre over a nonclosed point of T, and the empty curve. No SGA route is used. No Lean, compiler, Lake, or project build was run.

The generic geometry tools used outside the item's unit are the proper valuative criterion, scheme-theoretic closure/dense-open uniqueness, proper base change and closed-immersion properness, the closed-point residue-field and product criteria, and proper locally-quasi-finite finiteness. They expand the paper's graph argument and do not replace the unit's Temkin semistable-reduction route.
