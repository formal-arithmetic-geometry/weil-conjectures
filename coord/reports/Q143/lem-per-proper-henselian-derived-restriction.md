# Q143 stage-1 report: lem-per-proper-henselian-derived-restriction

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-proper-henselian-derived-restriction.json`: item split into seven steps, statement unchanged; no new nodes and no Mathlib leaves.
- `citations.json`: one verbatim statement quote for every step/node citation. Full statements are retained so that hypotheses and the precise derived clauses remain visible.
- `searches.jsonl`: actual msearch output records, including exploratory searches for a comparison lemma that was ultimately found already in the DAG.
- `report.md`: this report. `prepare.py` is sandbox-only preparation code, not a delivery node.

## Attachments

None. Searching the live WeilConjectures source for the item tag and for henselian derived restriction found no declaration giving this whole statement. `Etale.bijective_pullSection_of_henselianRing` gives degree-zero sections for proper schemes; `Etale.bijective_cohomologyMap_of_henselianRing` in Gabber.lean gives the affine pair theorem. Neither states the present derived proper theorem and its derived coefficient-map square. The general `DerivedCategory.Plus.isIso_app_of_forall_homology` in PlusDevissage.lean is an input, already represented by `lem-weil-pbc-heart-test-bounded-below`, not an attachment of this item.

## WANTED

None. The needed Stacks source is available locally.

## Corrections and scope

The statement is correct as imported and was kept exactly. The node had no proof. The gap was the derived extension of the affine henselian-pair comparison and its identification with the canonical proper restriction, not a new relative affine Gabber theorem. I deliberately used `prop-weil-pbc-gabber-pair-comparison`, whose statement warns against extending Gabber to arbitrary affine finite-type schemes. The parent source mentions the derived torsion conclusion of 0DDD; the DAG already has its sheaf-level generalization `lem-sbc-qcqs-higher-images-prime-torsion`. Step 2 derives the needed complex version from that existing lemma and finite truncation convergence, without a duplicate node.

The blueprint ancestor and current proof were read from `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.{md,proof.md}`. This node is a descendant furnishing the proper-base-change input in the completion branch already recorded by its parent; it is not the key node of the unit. No unit or chapter file changes are needed. No SGA source was used.

## What remains

No unfinished part of this one-level split. Existing cited nodes remain responsible for their own proofs. The item is delivered only after the server dry run passes.

## Not duplicates

No new nodes. The contemplated general hypercohomology restriction criterion was dropped when the whole-DAG search found the strictly more general heart-test statement. The existing sheaf higher-image torsion lemma supplies 0DDD(1); its derived consequence is a proof step, not another node. The item itself is not duplicated by the affine pair comparison or the degree-zero proper sections theorem.

## Review by Q143

I read Stacks `etale-cohomology.tex` at the full statement and relevant proof of Tag 09ZI (`theorem-gabber`), Tag 0DDD (`lemma-torsion-direct-image`), and Tag 0DDE (`lemma-proper-base-change`). Gabber assumes only a henselian pair and arbitrary torsion abelian sheaves; proper base change assumes precisely properness and bounded-below torsion cohomology, with no restriction on torsion primes. I also read `derived.tex` Tags 015J (`lemma-two-ss-complex-functor`, including its finite convergence), 05TC (`lemma-negative-vanishing`), and 015M (`lemma-compose-derived-functors`), `cohomology.tex` Tags 01F8/01F9/01FB for the canonical arrow, and `sites-cohomology.tex` Tag 07A7 for the exchange mate. The proof is marked agent assembly because the sources do not state this entire assembled theorem with its coefficient-map square in one place. There are no new-node sources to review.

Step 1 uses the actual properness, finite-type, quasi-separatedness and closed-immersion definitions, and affine quasi-compactness. It writes the finite-type and diagonal arguments: no general morphism permanence lemma is silently assumed. A closed immersion is affine locally Spec of a quotient, so its preimage of an affine is quasi-compact even for an infinitely generated defining ideal. This is a few-line elementary step from the cited statements.

Step 2 uses the Grothendieck property of abelian etale sheaves, negative vanishing, the precise truncation spectral-sequence statement, and the fixed-set-of-primes higher-image torsion statement with the set of all primes. I checked that this last node is about sheaves, not complexes: the finite-filtration argument is therefore explicitly supplied. Exactness of geometric stalks and the equivalence between torsion stalks and torsion sheaves are separately cited. Every stalk subquotient is torsion and every finite extension is torsion, by the displayed annihilator multiplication argument. The bounds a <= q <= n make this finite even when a is negative; no infinite extension or common annihilator is asserted.

Step 3 uses the derived-unit comparison for the actual restriction map, the derived-section unit-pasting statement for naturality in derived objects, triangulatedness of right-derived functors and of exact inverse image, and negative vanishing for lower-bound preservation. I checked the full statement of the heart test before applying it: it needs shift compatibility, not just naturality. The proof verifies this on the actual section-pullback chain map and shifted resolutions, invoking the resolution-independence clause of the pullback-functoriality node. The module-form unit-pasting node is used with the constant ring Z, i.e. precisely the abelian sheaf case of the derived-category convention. It supplies naturality and derived composition, unlike the cohomology-degree-only pullback laws node, which I did not substitute for it.

Step 4 applies only the affine pair theorem to each torsion cohomology sheaf of E. The canonical chain map on injective resolutions is a quasi-isomorphism because Gabber gives its nonnegative cohomology maps and negative vanishing gives the other degrees; localization then inverts that chain map by the definition of the derived category. The heart test's hypotheses were verified in step 3, so it yields the derived comparison for E, without a new node restating this clause of the item.

Step 5 reads `thm-weil-pbc-bounded-below` literally: its conclusion is the canonical exchange isomorphism in the cartesian square, exactly what the step needs. The square is Y_0 -> Y over Spec(A/I) -> Spec A, and K is the originally assumed bounded-below torsion object. The Leray identification is quoted from the statement of the derived-unit node, not inferred from its proof. I checked this dependency and the other major inputs for a path back to the item; none was found.

Step 6 uses the definition's full three-arrow mate formula and the derived adjunction's counit, natural unit and triangle identity. Unit-Leray pasting rewrites the base change composite, naturality moves the counit, and the displayed triangle identity cancels it. I checked the types: E = Rf_*K lives on X; epsilon_f has source f^{-1}E on Y; its i-inverse image lives on Y_0. The intermediate composite is RΓ(Y_0,i^{-1}epsilon_f) T_i(f^{-1}E) T_f(E), so naturality gives T_i(K) RΓ(Y,epsilon_f) T_f(E). This last factor is lambda_f,K, leaving exactly rho. This is a routine mate calculation from the cited statements, marked elementary; it is not an extra canonical-map comparison asserted without an argument.

Step 7 uses the derived, not degreewise, naturality and composition of the section maps. I wrote the maps with the specified a:h^{-1}K -> L and its restricted coefficient map a_0, and both paths in the square. The map of ideals gives h_0 and hj = ih_0 even without a cartesian h. No claim of properness of h is made or needed. Naturality of restriction follows at the derived level, so equality on cohomology is not being mistaken for equality of derived morphisms.

I checked the small cases I=0 (the closed fibre and restriction are identity), empty Y (both sides zero), K=0, a single torsion sheaf in an arbitrary degree (the heart test shifts it correctly), complexes with arbitrarily high nonzero cohomology (only finite diagonals are used in each fixed degree), and residue-characteristic torsion (no invertibility is invoked). None requires finite generation of I, excellence or Noetherianity. The statement and all coefficient categories remain unchanged. Every proof step is under 2000 characters, and none hides a separate unrecorded comparison. All cited node statements were opened and read; citations.json copies their actual text. Searches were made only through msearch and are logged verbatim; the exploratory comparison search was not fabricated into a new node. Definitions used as inputs are cited for their actual content; theorems supplying exactness, torsion, convergence and coherence are cited separately.

Generic tools from other units are declared in `split_report.tool_uses` for maintainer review. They supply algebraic geometry, sheaf cohomology and formal derived-category facts for the existing completion input; they do not replace the unit's perverse argument with a different route.
