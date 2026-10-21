# Worker report — Q140

Item: lemma-nagata-separate-closed-data-exists. Stage 1 only; direct delivery.

## Files written

- dag/nodes/sec-nagata-compactification/lemma-nagata-separate-closed-data-exists.json: statement node, split into seven steps; no Mathlib match.
- citations.json: 17 verbatim statement quotes, one for every citation of every step.
- searches.jsonl: six actual msearch.py results, retained unchanged.
- report.md: this report and the signed self-review below.

New nodes: 0. New Mathlib leaves: 0. No Lean files, compiler calls, library builds, repository edits, or agents.

## Attachments

None. I did not repeat the rejected attachment. I searched the supplied WeilConjectures source by blueprint id and the separation notions. BoundarySeparationData.lean now has preparation declarations, but disjoint_range_inclusion_inter_preimage_and_subset (line 161) states a partition of underlying sets, not the scheme isomorphism required by this item. The proof here explicitly verifies the quotient ideals that give that scheme isomorphism. No source declaration is being treated as evidence of a completed attachment.

## Literature wanted

None.

## What needed repair

The statement is retained verbatim. Its word “components” means the two clopen summands, which can be empty or disconnected; it does not assert that either is a connected component.

The imported proof left the scheme decomposition unjustified and used an unnecessary assertion that powers of the complement ideals “vanish on the boundary.” A vanishing-set identity must not be read as vanishing of boundary stalks. For example, with X = Spec k[t], Z_1 = X, Z_2 empty, U = D(t), one can choose K_1 = (t), K_2 = 0: no positive power of K_1 vanishes in the local ring at (t). Restriction to a separately specified reduced closed subscheme is a different assertion. The replacement uses only V(K_i) = Z minus P_i, nilpotence of K_1 K_2, and the equality V(K_1 + K_2) = Z minus U_Z. It does not need any scheme structure on that boundary.

The imported last step had elementary = null, no strict-transform-definition citation, and no citation of closure minimality. These are repaired. The new chart step cites the actual chart cover, generator regularity and principalization statements. The following step explains the global opens directly, including intersections of charts over different affine base opens; there is no unproved “these local decompositions glue.”

The chapter and unit route remain unchanged: preparation of complement ideals, nilpotent product, blow-up charts, and confinement of the scheme-theoretic strict transforms. This is not the alternative Deligne disjointness blow-up route.

## Mathlib and blueprint searches

The six searches in searches.jsonl were read and are recorded with precisely their actual tool and query text in the item. The first Loogle query was invalid because AlgebraicGeometry is a namespace rather than a constant; this is reported as an invalid query, not evidence of absence. The second, valid quoted-name query returned no hits. Two different semantic phrasings returned only separation/quasi-separation properties of schemes and morphisms, not blow-ups or strict-transform separation. LeanSearch likewise returned proper/separated-morphism results. The logged grep of Mathlib/AlgebraicGeometry for blow.?up|strictTransform returned zero hits. Thus the item is not a Mathlib leaf.

I searched all dag/nodes by the relevant ideals, clopen/closed decomposition, chart-cover, closure, and Stacks-tag notions; I also ran blueprint_refs.py ancestor and searches for separate closed, Chinese, blowup chart, closed complement, unit off support, separation, and disjoint opens. The neighboring separation nodes concern the later ambient-X blow-up or constructible-boundary closures; none duplicates this preparation on Z. Existing complement-ideal existence, nilpotence, chart, and closure nodes suffice. No new statement node is needed for the elementary quotient-ideal, ideal-product, local-ring, or clopen arguments.

## Not duplicates

No new nodes. The preparation item is not the ambient-X separation theorem lemma-nagata-separate-closed-subschemes, whose datum already depends on this item; that node was not cited, avoiding a cycle.

## Unfinished work

None in the stage-1 split. Dependencies remain existing DAG items, as allowed by the one-level split contract. Delivery validation is recorded after the required tool exits.

## Review by Q140

I read coord/delivery-errors.md B–E in full, the worker brief, the three levels in SETUP.md, GOAL.md, the chapter and unit records, the current main-20261015 statement and the imported blueprint_update proof. For the mathematical argument I read Stacks divisors.tex Tag 080P, label lemma-separate-disjoint-opens-by-blowing-up, including its omitted gluing sentence; Tag 0804, label lemma-blowing-up-affine; Tag 02OS, label lemma-blowing-up-gives-effective-Cartier-divisor; properties.tex Tag 01PH, label lemma-quasi-coherent-finite-type-ideals; and morphisms.tex label lemma-scheme-theoretic-image. These give the complement-ideal/chart argument and the smallest-closed-subscheme property used at the end. There are no new nodes whose statements need a separate literature comparison.

1. Step 1 uses lemma-nagata-ideal-unit-off-support, whose statement really says the ideal becomes the unit ideal on the complement of its vanishing locus. The disjointness hypothesis on U supplies the covering by the two unit-ideal loci. The equalities I_1 I_2 = I_1 or I_2 on those loci are equalities of ideals, so the quotients identify the schemes themselves. The overlap is the empty scheme. This is an elementary explicit check, not just an underlying-set partition.

2. Step 2 uses the affine quotient description stated in def-weil-closed-immersion, and pqf-lem-qs-intersection-qc for quasi-compact intersections in the quasi-separated X. The restricted affine cover verifies qcqs for Z. The closed-in-U description verifies quasi-compactness of U_Z; each clopen P_i is closed in that quasi-compact space and open in Z. I then checked the exact hypotheses of lemma-nagata-qc-open-complement-ideal-exists: the ambient scheme is qcqs, and the chosen open P_i is quasi-compact. Its statement supplies finite-type quasi-coherent ideals with the exact vanishing sets needed. I cite this existence theorem, not the choice-definition node as a substitute for existence.

3. Step 3 uses precisely the statement of lemma-nagata-finite-type-nil-ideal-nilpotent. Its ambient Z is quasi-compact by step 2, the product ideal is finite type by products of local generators, and its vanishing set is all of Z by disjointness of the P_i. The positive exponent N, unchanged supports of powers, and K_1^N K_2^N = (K_1 K_2)^N are written out. No regularity of Z or Noetherian hypothesis is introduced.

4. Step 4 uses the explicit finite-algebra-presentation meaning in def-sbc-locally-finite-presentation; A/(c_1,...,c_r) is the displayed presentation of the center on every affine open. Since the immersion is affine and separated it is also quasi-compact and quasi-separated, so this is finite presentation, not merely locally finite presentation. The unit-off-support node supplies the unit restrictions; zero product supplies the opposite zero restrictions. The definition def-nagata-admissible-blowup asks for exactly a finite-type ideal with unit restriction and the indicated blow-up datum. thm-nagata-global-blowup-complement actually states the isomorphism over the complement. V(J) is exactly the complement of U_Z, not just a subset of it, so the strict-transform open in the final step is the required one.

5. Step 5 uses the statements of def-nagata-global-blowup and def-nagata-global-blowup-local-model for the affine pieces of the construction, prop-nagata-affine-blowup-chart-cover for their finite open covering, lemma-nagata-chart-generator-regular for injectivity of multiplication by the generator, and lemma-nagata-chart-extended-ideal-principal for J becoming the principal ideal generated by it. Each cited statement was opened. The zero opposite ideal is derived by multiplying its generators by that regular element; it is not asserted from a definition of blow-up.

6. Step 6 applies the same regularity statement at stalks and explicitly proves regularity persists under localization. It takes unions of the actual open charts in Z', rather than constructing a new gluing datum. At a point in opposite charts, one computation makes the regular generator zero, contradicting the nonzero local ring at a point. This also handles charts over distinct affine opens. The chart cover then makes both global opens clopen. Unit versus zero for the opposite extended ideal proves containment of the inverse images of P_i. These are elementary deductions from step 5; they are not new node candidates.

7. Step 7 cites def-nagata-strict-transform for the scheme-theoretic construction inside B_i, and lemma-nagata-scheme-theoretic-closure-minimal, whose statement says it factors through every closed subscheme through which the initial immersion factors. The inverse image of Z'_i is clopen, hence a closed subscheme, so that statement applies directly. I did not use only the topological closure or the unrelated claim that the defining image node says “largest.” The conclusion is scheme-theoretic disjointness, since the two ambient clopen opens have empty intersection. Closure minimality is declared as a generic tool from another unit, as is the quasi-separated intersection fact in step 2; neither replaces the boundary unit's proof route.

For the small cases, if one P_i is empty its complement ideal can be 0 and its corresponding charts can be empty; the other charts give the result. If U_Z is empty, take both complement ideals 0: blowing up the zero ideal is the empty scheme, and both strict transforms are empty, as required. If U_Z = Z, the construction still works and the blow-up is an isomorphism on all of Z. The example Z = Spec(k[x,y]/(xy)) with P_1 = D(x), P_2 = D(y) has K_1 = (x), K_2 = (y); the charts separate the punctured axes while the origin is the center. Nilpotent thickening does not invalidate the argument: the explicitly cited finite-type nilpotence theorem supplies a uniform exponent, and regularity of a chart generator is used only on the blow-up chart, never assumed in the original ring.

All seven steps are shorter than 2000 characters. The elementary steps spell out their deductions and introduce no hidden lemma. Every non-elementary ingredient is an existing node whose statement is quoted verbatim in citations.json. The only corrections are to the proof and its dependencies, not the imported statement. I preserved the blueprint_update, import_flags, and other maintainer-owned fields.
