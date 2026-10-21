# Worker report

Item: lem-sfb-integral-residue-class-triangle-closure. Group: Q24. Stage 1 only. Direct delivery, 2026-10-21.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-residue-class-triangle-closure.json: existing statement, split into seven steps; no exact Mathlib match.
- citations.json: all thirteen step/node pairs, with verbatim statements containing the clauses used.
- report.md: this report. searches.jsonl contains the unmodified search-wrapper records. prepare.py is sandbox-only preparation code, not a delivery file.

New nodes: 0. New Mathlib leaves: 0. The item statement and its statement dependencies are unchanged. No unit record is changed: this item is a subsidiary stability lemma, not the unit's key statement.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and the residue/complete/triangle notions. LocalizationIntegral.lean has ordinary étale integral constructibility lemmas with additional coefficient conditions and a reduction/Tor predicate. Those are not the present arbitrary-scheme pro-étale ordinary-module predicate and do not supply an exact attachment. No declaration was treated as complete merely from a sorry declaration's existence.

## Literature wanted

None. WANTED: none.

## Original gaps and changes

The item had no proof. Its blueprint source, paragraph (1) of sk-lem-int-integral-heart-triangulated.proof.md, says that exact reduction preserves constructibility because bounded constructible étale complexes form a triangulated category. That requires explaining why an *ambient pro-étale* morphism between étale-origin residues has an étale-origin cone. I supplied this argument through the already existing global constructible sheaf comparison, bounded reconstruction, and intrinsic pro-étale triangulation nodes. The split does not infer essential-image cone closure just from exactness.

For completeness I used the already stated canonical completion map as a morphism of distinguished triangles. This avoids equating the canonical-map completeness predicate with a different ringed-local completeness definition without a comparison theorem. The statement's ordinary derived category and residue scalar structure are maintained throughout.

There is no statement dispute. In particular the lemma makes no assertion that the integral complex itself is bounded or locally perfect; such assertions elsewhere need geometric conditions and are not used here.

## Existing nodes and blueprint search

Read the chapter and the sk-lem-int-integral-heart unit, and the current main-20261015 item source and derived-Nakayama completion source. The proof realizes only the completeness/reduction closure assertions in paragraph (1); it does not replace the integral-model comparison or the later boundedness/local-model arguments of the unit.

Searched the whole DAG for completion-triangle, constructible/Serre, finite-coefficient origin, bounded classical comparison and ring-object encoding statements. Read the statements and dependency lists of the candidates. The Noetherian finite-discrete constructible model comparison and the finite-type unbounded comparison were deliberately not applied, because their hypotheses are absent here. The fixed-module sheaf and bounded reconstruction nodes, in contrast, state the arbitrary-scheme results needed. Read-only blueprint_refs searches included classical, complete, bounded constructible, residue, residue class, triangle closure, and the conjunction derived complete / triangulated. No imported node states this exact conjunction. Ancestor is det-lem-int-integral-heart-triangulated, already correctly recorded by the item.

The item's inherited searches were retained. Additional actual wrapper searches used LeanFinder twice, Loogle, LeanSearch and grep; they are copied exactly from searches.jsonl. LeanFinder/LeanSearch returned general derived categories, triangles and ordinary adic completion. Loogle returned ObjectProperty.instIsTriangulatedInverseImage, which I read at Mathlib/CategoryTheory/Triangulated/Subcategory.lean:580: it assumes the target object property is already triangulated and does not establish the pro-étale finite étale-origin class or the completion comparison. It is an ingredient, not an exact match for this item. The valid Mathlib grep returned zero results for the specialized pattern. No search result is recorded as an attachment or a new leaf.

## Not duplicates

No new nodes were created. All substantive inputs are existing nodes. In particular the completion functor comparison and bounded finite-coefficient reconstruction are reused rather than restated as children of this item.

## Tool uses

The split_report.tool_uses declares the generic completion-triangle comparison, derived change of rings, constant-module encoding, sheaf origin comparison, bounded reconstruction and finite-coefficient pro-étale triangulation. Each is an input implementing the unit's exact-completion/exact-reduction argument, not a change to its route. The other inputs are definitions or existing Mathlib leaves.

## Review by Q24

I read delivery-errors B through E, including the second retained copy, against the node and source text. There are no new statement-only nodes to audit or same-tag pairs to distinguish. I kept the original statement, blueprint lineage and creation metadata, used single-backslash mathematical TeX through JSON serialization, and created no Lean or compiler output.

For step 1 I opened lem-pe-completion-triangle-comparison and read its entire statement and its source, the Cones and shifts paragraphs of the current derived-Nakayama proof. It uses the same R = p_X^* underline(O_E), the same arbitrary scheme and the same canonical-map completeness predicate. Its statement supplies an additive functor, a natural completion map and all integer-shift comparisons. The zero and isomorphism arguments are explicitly written. This is not an application of the different locally derived ringed-ideal completeness predicate.

For step 2 I checked that the same completion node expressly supplies a distinguished image triangle AND the last square of the map of triangles. The statement of lem-sf-triangle-morphism-iso (read with derived.tex Tag 014A, lemma-third-isomorphism-triangle) applies to any two vertical isomorphisms, which gives all three completeness implications, not only closure of cones of complete pairs. Neither statement requires boundedness or a Noetherian scheme.

For step 3 I opened lem-pur-derived-change-of-rings. Clause (2) says the derived scalar extension is an exact functor to D(O'), computed by K-flat resolutions. I read sites-cohomology.tex Tag 06YY, lemma-derived-base-change, and the corresponding source specification. Taking the underlying topos map to be the identity and the ring map R_X to kappa_X meets its hypotheses. This proves exactness in the residue module category, not merely after forgetting residue scalars. No flatness of kappa over R_X is asserted or needed.

For step 4 I read def-weil-pbc-proetale-modules, lem-weil-pbc-proetale-constant-module-encoding, lem-sf-exact-functor-derived-triangulated and lem-weil-pbc-exact-functor-complex-cohomology. Their statements give precisely the ordinary finite constant-ring category, the equivalence by restriction to constant scalars with unchanged underlying additive sheaf, and the termwise triangulation/cohomology facts for an exact functor. I wrote out why the scalar action after pullback is the same (it is determined locally by constant sections), why an equivalence is exact, and why finite stalks and the same strata are retained. This is a short unpacking of the recorded equivalence, not a comparison with a new condensed constructibility predicate. The relevant constant sheaf/module construction sources are sites-modules.tex Tags 03CY and 093I; the exact cohomology source is homology.tex Tag 010N.

For step 5 I opened both fixed-module origin nodes and checked their statements independently. The sheaf node gives the equivalence with *global finite-stratification* constructibility for any scheme and finite commutative ring. The bounded reconstruction node says that a bounded pro-étale complex with a globally constructible étale antecedent for every cohomology sheaf has a bounded constructible étale antecedent. Thus this step does not replace global finite partitions with affine-local partitions on a non-quasi-compact scheme, does not use only the fully faithful sheaf Yoneda-style part, and does not invoke an unbounded comparison theorem. The exact cohomology statement supplies the forward implication and the same cohomological interval. I read proetale.tex Tags 09AK and 09AL (lemma-compare-constructible and lemma-compare-constructible-derived) and the nearby bounded-below comparison proof. The stronger global convention used here is supplied by the explicitly global existing nodes; I do not claim that the affine-local Stacks definition alone supplies it.

For step 6 I read lem-weil-proetale-dbc-triangulated: its statement is exactly zero/isomorphism/shift and extension stability of the intrinsic globally constructible bounded class for ANY scheme and finite commutative coefficient ring. The residue field is such a ring. I checked the two explicit rotations against TR2 in def-weil-triangulated-category. In particular when only the last two vertices are known, the twice-rotated middle vertex is N_1[1], and the inverse shift gives N_1. This proves the positions absent from the displayed extension clause without inventing another node. Its source is proetale.tex Tag 09AL with Tag 09B5; both were read.

Step 7 just combines the proved assertions about the two factors of P and the exact reduction functor. It invokes no uncited non-elementary theorem. I checked each of the thirteen citations against its node statement, and citations.json contains those statements verbatim. I also checked the existing dependencies for paths back to this item; none of these tools introduces a cycle.

Small cases checked: X empty (zero module categories and an allowed empty stratum), zero objects and arbitrary isomorphic representatives, positive and negative integer shifts, the three possible known pairs in a triangle, and an unbounded integral complex (only its finite residue is bounded). No residue-characteristic invertibility on X is used. The finite field condition is used only to apply the finite constant-coefficient comparison and constructibility closure, so characteristic-ell schemes are allowed. Infinite unions of components cause no need to choose a uniform integral cohomological bound: boundedness is required only at the given residue objects and is supplied for a third residue by the existing triangulation theorem.

No step exceeds 2000 characters. In particular the coefficient bookkeeping and the origin reconstruction have separate steps with named existing theorem inputs; there is no hidden long lemma or clause-restating new node. Nothing remains unfinished in the mathematical split. The required dry run and delivery are performed after this report is written.

## Dry-run repair

The first preflight rejected the phrase “the item's statement” in step 5 as a self-containment violation. Replaced it with the explicit bounded constructible étale-origin condition. No object, hypothesis, conclusion or citation changed.
