## Worker report

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-quasi-affine-open-finite-subalgebras.json (item, statement unchanged, split, not a Mathlib leaf); citations.json (eleven verbatim statement quotations). No new nodes or unit edits.

Attachments: none. The project search for the exact blueprint tag returned no declaration; concept searches found the specialized PreStage.exists_finset_hgen/mkStage construction in WeilConjectures/Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean:1006–1097, whose hypotheses are extension-stage fibre-product data and which does not state this item. It is not an attachment. No compiler was run.

WANTED: none.

The imported node had no proof. Stacks limits.tex Tag 01Z7, lemma-quasi-affine-finite-type-over-Z, gives the numerator construction and ends with “Details omitted.” The delivery supplies those details, retains the chosen principal elements, includes the prescribed finite set E, and proves the exact open image. In particular localization injectivity here follows from A being a subring of R, not from any nonzerodivisor assumption. Nothing in the statement or the source was disputed or weakened.

All work is finished subject to the mandatory dry run and push. No Lean files, build commands, repository edits, launcher edits or agents were used.

## New nodes

None. An initially considered auxiliary statement that the R_h are finitely generated was unnecessary: the existing lem-weil-pbc-lft-affine-pairs supplies it directly. Denominator choices, the generated subring, and the elementary kernel calculation stay as proof steps, not new nodes.

## Sources and searches

Read limits.tex Tag 01Z7 statement and proof (lines 1038–1058); morphisms.tex Tag 01T2, lemma-locally-finite-type-characterize (the all-affine-pairs equivalence at lines 2673 onward); schemes.tex Tag 01I3, lemma-standard-open-affine (lines 966 onward). For morphism gluing, read schemes.tex lemma-glue, especially its mapping property Mor(X,Y) in lines 2562–2566, and lemma-glue-schemes; also sheaves.tex Tag 00AN, lemma-mapping-property-glue, with its reference to Tag 04TN, lemma-glue-maps. These support the existing scheme-morphism-gluing node actually cited.

Read the chapter record, the recorded unit, and the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability unit and direct-images proof. This is a commutative-algebra input far below the approximation branch recorded in blueprint.from, not a replacement of the unit's compactification/direct-image route. The inherited blueprint ancestor is null (confirmed by tools/blueprint_refs.py ancestor); its explicit place and via chain are retained. Whole-blueprint searches for quasi-affine, finite subalgebras, finite type affine open, generators of R, localizations, principal, affine pairs and isomorphism local found no imported duplicate of the item's ambient-subring assertion. DAG statement searches led to the three existing leaves used; all their full statements were read. No new nodes require a same-tag duplicate comparison.

The required msearch commands ran and are logged in searches.jsonl. LeanFinder was queried twice, first geometrically and then in terms of finitely generated localized rings. Loogle queried Subalgebra.FG together with IsOpenImmersion. LeanSearch queried descent to a finite integer subalgebra. The Mathlib grep covered quasi-affine and finite-subring names in AlgebraicGeometry. Read Mathlib/AlgebraicGeometry/QuasiAffine.lean:30–70, Morphisms/FiniteType.lean:35–100, and RingTheory/RingHom/FiniteType.lean:70–91. Hits concern canonical quasi-affine embeddings or finite-type locality, not the requested subring of this R. All queries in the new search records are exactly those logged; historical searches already in the item were retained. No unavailable service was counted as a negative result.

## Review by NH

I checked B–E of delivery-errors with the item and the cited statements open. There are no new statement-only nodes to audit under B, and no hidden restatement of the item's clauses. Its unchanged hypotheses include arbitrary commutative rings, a finite type structure morphism to Spec Z, arbitrary specified principal-open cover, and arbitrary prescribed finite E. The stronger-looking localization conclusion is exactly what the numerator construction in 01Z7 yields; no finite presentation or noetherian hypothesis on R is inserted.

Step 1 uses the full principal-localization-open-immersion statement, which identifies Spec(R_h) with D_R(h), and the full lft-affine-pairs criterion, which applies to EVERY affine open of Q, not only a selected defining cover. Q_l is affine because its image is D_R(h_l); the target is the whole affine Spec Z, and finite type implies locally finite type. Thus the criterion provides finite integer algebra generators of each R_h. I corrected the initial plan to cite this existing criterion instead of creating an unnecessary node.

Step 2 uses only the localization definition's fraction description, plus the definition of an algebra generated by a finite set. Each denominator is an explicit power h_l^n, and including its numerator puts every selected x_lj in the localization image. The image is an integer subalgebra containing a generating set, hence is the whole target. No common-denominator lemma, finiteness descent or unrecorded geometric theorem is being invoked.

Step 3 uses exactly the zero-fraction equality in the same localization definition. If h_l^k a vanishes in R it vanishes in the subring A. This checks injectivity without assuming h_l is regular. It would be wrong to cite lem-pc-affine-localization-injective, whose nonzerodivisor hypothesis is absent; that node was deliberately not used.

Step 4 uses the affine-spectrum node's contravariant functoriality, the principal-localization node's specified image, the morphism-gluing node's existence AND uniqueness, and the definition of open immersion as an isomorphism onto an open subscheme. All four statements are quoted verbatim in citations.json. The maps are those induced by the natural localization maps, not arbitrary isomorphisms. The equation g^{-1}D_A(h_l)=Q_l follows by prime contraction. It ensures an inverse chart lands in every required overlap; the inverse uniqueness on that chart proves compatibility. The morphism-gluing node then supplies the global inverse. This avoids falsely treating a source-local isomorphism as automatically globally injective. The routine factorization of a scheme morphism with image in an open is restriction of its continuous map and sheaf map, hence follows directly from the open-subscheme definition. The step is 1146 characters; none exceeds the 2000-character long-step threshold.

Step 5 checks empty family, zero ring and nilpotent h_l explicitly. When the family is empty Q is empty and the unital subring generated by E suffices. If h_l is nilpotent the principal opens are empty and both localizations are zero. As further small cases I checked h=1 (the chosen generators then give A=R), R=Z[x], h=x with E arbitrary finite, and R=Z[x,y]/(xy) with h=x: the same numerator and kernel arguments hold, so no hidden domain assumption was used.

C1 and C4 hold step by step: the only non-elementary geometric inputs are precisely the named existing nodes above, and the elementary parts are written out. There is no citation of a proof-only construction, no definition cited for a theorem about it, no added recursive dependency and no SGA route. All proof dependencies equal the union of step citations; the citations file includes one exact statement quote per use. The statement and import/history fields are preserved, the item is split by one level, and no existing node outside this item was modified.
