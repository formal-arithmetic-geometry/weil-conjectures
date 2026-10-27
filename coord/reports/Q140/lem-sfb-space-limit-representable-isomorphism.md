## Worker report

Group Q140, stage 1, 2026-10-23. Item: lem-sfb-space-limit-representable-isomorphism.

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-space-limit-representable-isomorphism.json: five-step split; statement and statement dependencies preserved.
- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-limit-isomorphism-descent.json: statement-only supporting theorem, Stacks Tag 081E; unsplit, no Mathlib match.
- citations.json: one verbatim cited-statement entry for every dependency of every proof step.

Attachments: none. Searches in lean/WeilConjectures for the blueprint tag, descent of isomorphisms, and algebraic-space/limit terminology produced no project declaration stating this item. No Lean was written and no compiler or build was run.

WANTED: none.

The imported item had an empty proof. Its source, spaces-limits.tex Tag 084S, has two explicit “details omitted” passages. The split now checks the scheme objects to which 081E applies and gives the inverse gluing argument at the end. The statement already includes the assumptions of Situation 084R, and is unchanged. No source error or statement dispute was found. I corrected the supporting node's draft situation reference to Tag 081D after checking tags/tags; 07C6 was not its tag. I also checked decoded TeX for doubled literal backslashes.

Unfinished work: the new scheme theorem is intentionally statement-only, as required for a one-level split. Its later worker can follow limits.tex Tag 081E: descend etaleness and closed immersion, obtain a flat finitely presented closed immersion and thus an open-and-closed subscheme, and use constructible containment to obtain eventual surjectivity. This proof sketch is kept here, not in the node's statement or proof fields.

## New nodes

lem-sfb-scheme-limit-isomorphism-descent — statement; unsplit; 0 Mathlib leaves. This is the scheme theorem invoked by 084S, not a restatement for algebraic spaces. The item still proves the reduction: a common affine etale chart, qcqs chart pullbacks, compatibility with the scheme limit, and descent of the inverse through a cover.

Mathlib searches were made through msearch.py and recorded in searches.jsonl. They comprise Loogle, LeanSearch, two different LeanFinder phrasings, and two source grep patterns. All services answered. The semantic hits included Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType and Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType (AffineTransitionLimit.lean, lines 635 and 690), existence of a map at a stage, global-section descent, and finite-presentation base-change declarations. I read the equality declarations and the locally-finitely-presented factorization/yoneda section of that file: eventual equality of already given maps does not itself give an inverse, and constructing an inverse and both identities requires an argument. No exact declaration or one-line specialization states 081E. The grep on a single file printed numerical labels in its file column; those are preserved in its recorded result, with the searched file identified. The broader directory grep supplies ordinary file names. No returned hit was promoted to a leaf. The item's earlier Q108 searches and their results were retained; the Q140 scheme searches were appended.

## Not duplicates

No existing node has source Tag 081E. Searches for 081E, lemma-descend-isomorphism, isomorphism/limit/stage terminology, and descent of isomorphisms were made over the whole DAG; the whole-blueprint searches included 081E, descend-isomorphism, isomorphism stage, isomorphism limit, representable limit, and a broad isomorphism search. No existing blueprint node states the scheme theorem. The module sources were also searched before introducing the new id.

lem-sfb-scheme-limit-isomorphism-descent vs lem-sfb-space-limit-representable-isomorphism: the new result is the scheme input 081E; the item concerns algebraic spaces and proves the affine-etale reduction and inverse descent. They do not have the same source tag.

lem-sfb-scheme-limit-isomorphism-descent vs lem-sfb-space-affine-limits-schematic-stages: the latter gives existence of space limits and eventual schematicity/affineness, not eventual invertibility of a specified morphism. It already depends on the item, so using it for the chart limit would be circular; step 2 instead computes the chart limit directly from the universal property and the existing scheme limit theorem.

lem-sfb-scheme-limit-isomorphism-descent vs lem-sfb-lfp-space-scheme-limit-test: the latter descends maps into a fixed locally finitely presented space. It does not assert that a specified relative morphism becomes an isomorphism at a stage.

The existing finite affine atlas refinement, qcqs fibre-product theorem, chart property test and local-lifting lemma were reused. No new node was made for any of these, for restriction to a cofinal tail, for commuting a pullback with this limit, or for the elementary gluing of unique lifts.

The dry-run duplicate checker also detected the shared setup tag 081D. I opened and read all twelve statements it listed. None asserts the isomorphism conclusion of 081E:

lem-sfb-scheme-limit-isomorphism-descent vs lem-weil-pbc-finite-family-joint-surjectivity-stage: descends joint surjectivity of a finite family of maps between finitely presented objects; it asserts neither injectivity nor eventual invertibility of a specified map, and assumes finite presentation over the base.

lem-sfb-scheme-limit-isomorphism-descent vs def-weil-pbc-flat-descent-chart: defines affine ring-chart data and flatness predicates, and contains no theorem about eventual isomorphisms.

lem-sfb-scheme-limit-isomorphism-descent vs lem-weil-pbc-descend-affine: descends the property affine, which does not imply invertibility (for example the affine-line projection).

lem-sfb-scheme-limit-isomorphism-descent vs lem-weil-pbc-descend-closed-immersion: descends only a closed immersion; it need not be flat or surjective and hence need not be an isomorphism.

lem-sfb-scheme-limit-isomorphism-descent vs lem-weil-pbc-descend-etale: descends only etaleness; a nontrivial finite etale cover is not an isomorphism.

lem-sfb-scheme-limit-isomorphism-descent vs lem-weil-pbc-descend-finite-locally-free: descends finite local freeness and its degree; it does not assert invertibility of a general locally finitely presented morphism or supply the other conditions making a morphism finite locally free of degree one.

lem-sfb-scheme-limit-isomorphism-descent vs lem-weil-pbc-descend-finite: descends finiteness under a local-finite-type assumption; a finite map is not in general an isomorphism.

lem-sfb-scheme-limit-isomorphism-descent vs lem-weil-pbc-descend-flat-finite-presentation: descends flatness under local finite presentation; a flat finitely presented map need not be invertible.

lem-sfb-scheme-limit-isomorphism-descent vs lem-weil-pbc-descend-monomorphism: descends the monomorphism property under local finite type; it does not assert surjectivity or invertibility.

lem-sfb-scheme-limit-isomorphism-descent vs lem-weil-pbc-descend-quasifinite-affine: descends quasi-finiteness of an affine finitely presented algebra chart, not invertibility of arbitrary qcqs scheme morphisms.

lem-sfb-scheme-limit-isomorphism-descent vs lem-weil-pbc-descend-separated: descends separatedness with no local finiteness assumption; separated morphisms need not be invertible.

lem-sfb-scheme-limit-isomorphism-descent vs lem-weil-pbc-descend-surjective: descends only surjectivity under local finite presentation; a surjective morphism need not be an isomorphism.

## Review by Q140

I read spaces-limits.tex, lemma-descend-equality (Tag 084S), together with situation-descent (084R), and compared every hypothesis: small nonempty directed indexing, affine transitions, qcqs stages, representability of both objects over the fixed stage, qcqs objects, locally finitely presented g_0 and invertibility after limit base change. The source uses 0 for the chosen stage; our i_0 is the same after restriction to its directed tail. There is no finite-presentation hypothesis on Y_0 or T_0 over X_{i_0}; none is inserted. The chapter/unit records and the current latest blueprint's sk-thm-sf-ctf-stability and direct-images proof were read; this is the supporting space-limit reduction on the inherited route, not a change to its six-functor claims. blueprint.from.node is null, exactly as the ancestor tool reports for this created-item chain; its inherited place and via chain are preserved and extended on the new node, with same_as=[] from the searches.

For the new node I read limits.tex, lemma-descend-isomorphism (081E) and situation-descent-property (081D). The base, two objects, fixed stage, map and both base changes are all introduced in its statement. Its qcqs scheme and affine-transition meanings cite the existing conventions; the base-change objects cite the fibre-product definition, local finite presentation cites its definition, and smallness cites the size convention. Requiring qcqs at every base stage is harmless here: the source's qcqs initial stage and affine transitions already give that property on the tail. The new node contains no proof, proof dependencies or hidden proof sketch.

Step 1 uses the full statement of lem-trf-space-qc-finite-affine-atlas-refinement, in particular its final assertion giving one affine surjective etale chart. I checked its source spaces-properties.tex, lemma-quasi-compact-affine-cover (03H6). The item has the required quasi-compactness. lem-trf-space-fibre-products-etale-covers explicitly preserves joint surjectivity and etaleness under arbitrary base change; its statement was read, so this is not taken merely from a definition. def-trf-algebraic-space supplies the scheme-test meaning of representable. Affineness of U_i and of U_i to U_j uses the item's explicit definition of affine applied to its given affine transitions, not an unstated affineness of an atlas. Cofinality is established by the common-upper-bound argument written in this step, without assuming a least element in the original I.

Step 2 uses exactly the existence of a scheme limit asserted by lem-weil-pbc-limit-affine-transition; I read limits.tex 01YX and the affine case 01YW. The identification with U=X times_{X_{i_0}} U_0 is proved on test schemes by describing both sets of points. The description is natural, so gives the claimed projection-compatible identification of sheaves by the definitions in def-trf-algebraic-space. It neither uses the proof of the cited node nor invokes the parent space-limit theorem. This is a routine universal-property computation, marked elementary after the cited limit exists.

Step 3 uses representability from def-trf-algebraic-space to obtain actual schemes P_0 and Q_0. It uses lem-weil-pbc-affine-scheme-qcqs for U_0, and the explicit final clause of lem-sfb-space-qcqs-source-products for both products over the qcqs X_{i_0}. I read spaces-morphisms.tex lemma-quasi-compact-quasi-separated-permanence, Tag 073B, clause (3). All three spaces in each product are qcqs; no separatedness of the atlas over the space is assumed. The existing cover-base-change node gives Q_0 to T_0 surjective etale. Finally lem-sfb-space-local-properties-chart-test says, for each of the listed properties, that the morphism has the property exactly when the indicated two-chart scheme morphism does. I read its statement and spaces-morphisms.tex lemma-finite-presentation-local, Tag 0410. Choosing Q_0 as the target chart and the identity of P_0 as the source chart gives precisely local finite presentation of h_0. Thus a scheme-only base-change lemma is not being applied to non-schemes.

Step 4 uses the same affine qcqs node for every U_i and exactly the conclusion stated by the new 081E node. The initial base is U_0, not X_{i_0}. The preceding steps provide qcqs P_0,Q_0 and local finite presentation of h_0. Its limit base change is invertible because it is the base change of the given invertible morphism. Associating the fibre products identifies h_i with the chart pullback of g_i; this follows from their universal properties, with both projections fixed, so does not add a comparison lemma without an argument.

Step 5 uses lem-a1-representable-etale-fppf-local-lifting for precisely the asserted fppf covering lift of a test-scheme point of X_i to the scheme U_i. I read its statement and spaces.tex lemma-space-presentation, Tag 0262, proof of (3), plus the fppf covering definition 021M in topologies.tex. Its hypothesis is a representable surjective etale map from a scheme; step 1 supplies it, even though X_i need not be a scheme. The rest is written out: the local inverse yields preimages, invertibility over the chart makes any two preimages equal on the double overlap, the fppf sheaf condition for Y_i glues, uniqueness gives naturality, and the inverse natural transformation is an algebraic-space morphism by def-trf-algebraic-space. These are applications of the definition of a sheaf and inverse, rather than an uncited descent theorem. Each cited node's statement, including the new node, is quoted verbatim in citations.json; the quotes have been checked as substrings of the actual statement fields.

Small cases: if I is a singleton, the limit and the fixed stage coincide and both assertions reduce to the given isomorphism. If the base stage is empty, its affine chart may be Spec(0), both representable pullbacks are empty, and all the arguments still apply. If the limit is empty but some stages are not, I did not assume a projection is surjective or that all stages are empty: 081E is applied with its empty limit case intact. Empty Y_0 or T_0 are permitted; any pointwise gluing assertion over the empty scheme uses the sheaf axiom for the empty covering. The proof does not use etale atlases as monomorphisms, does not assume Y_0 or T_0 are themselves schemes before the base change, and does not exclude a nonseparated qcqs space.

Against delivery-errors B–E: the new node is self-contained statement-only TeX, with definition citations and source tag/label; searches preceded creation; existing results were reused; every non-elementary input is a cited statement rather than a fact hidden in its proof; the item carries a genuine reduction rather than only applying a restated node. There is no induction or suppressed spreading-out argument in the assembly. Each step is under 2000 characters. I checked the dependency union and reachable acyclicity, all citation substrings, the fresh id, and decoded TeX locally, and the required server review_split check passed. The generic cross-unit atlas/cover/local-lifting tools are declared with their purpose in split_report.tool_uses; no top-level tool_uses or maintainer field was set.

The first full dry run exited before any push because the shared situation tag 081D triggered its duplicate gate. All twelve flagged node statements were then opened and compared, and their distinctions are recorded above. No mathematical change was needed.
