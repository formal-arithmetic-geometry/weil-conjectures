Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-left-derived-exact-when-defined.json` (item; repaired proof, no Mathlib leaf).
- `def-pur-saturated-triangulated-localization` (definition; no Mathlib match).
- `lem-pur-derived-functor-morphisms-05sa` (statement; no Mathlib match).
- `lem-pur-derived-functor-inverts-05sb` (statement; no exact Mathlib match).
- `lem-pur-derived-functor-shift-05su` (statement; no exact Mathlib match).
- `lem-pur-derived-functor-triangles-05sc` (statement; Mathlib has only the abstract triangulated-functor generalization).
- `lem-pur-localization-triangles-05r6` (statement; Mathlib generalization `CategoryTheory.Functor.distTriang_iff`).
- Updated `lem-pur-quasi-isos-saturated-triangulated` to cite the new definition.

Attachments: none.

WANTED: none.

What was wrong and repaired:

- The returned proof falsely treated the LF clause of Proposition 05SE as an elementary one-step conclusion and therefore had no real split. I followed the proof route requested by the return: 05SA(2) supplies functoriality on morphisms; 05SB(2) says LF inverts S; 05SU(2) supplies the shift isomorphism; 05SC supplies preservation of distinguished triangles; and 05R6 supplies the source-triangle normal form in the localization.
- The statement previously used an undefined abstract localization and undefined “saturated multiplicative system compatible with the triangulated structure.” The new definition node states MS1--MS6, saturation, and the localization universal property, and is cited by both the item and the quasi-isomorphism node.

## Review by C1

I read the item’s source in `/home/ubuntu/c1-stacks-review/derived.tex`, including Situation 05S8, Definition 05S9, Lemma 05SA(2), Lemma 05SB(2), Lemma 05SU(2), Lemma 05SC, Proposition 05R6, and Proposition 05SE. The five item steps now mirror the source proof rather than quoting the conclusion. Step 1 uses the exact 05SA statement about the unique map on LF values. Step 2 uses the exact 05SB assertion that LF maps every S-morphism to an isomorphism, plus the new definition’s localization universal property. Step 3 uses the exact 05SU shift isomorphism. Step 4 uses the 05SC distinguished-triangle conclusion together with the already cited morphism and shift data. Step 5 uses the 05R6 statement that every localized distinguished triangle is isomorphic to an image from D. I checked that each quote in `citations.json` is verbatim from its cited node and that every non-elementary dependency is listed in the corresponding step.

For the new definition node I checked the MS1--MS4 saturated multiplicative-system clauses and MS5--MS6 compatibility clauses against the Categories definition and Tag 05R2 in the same source, and checked the localization universal property against Situation 05S8. For each of the five statement nodes I checked the cited tag and verified that its hypotheses are the general D, D', F, S, and LF hypotheses used by the item. Mathlib searches were run for each node with LeanFinder, Loogle, and grep; the searches found only general derived or triangulated-localization APIs, except the 05R6 generalization recorded as `CategoryTheory.Functor.distTriang_iff`.

The small cases checked were identity S (all five statements reduce to ordinary functoriality, identity shifts, and source triangles) and zero distinguished triangles (the induced LF triangle is the zero triangle). The prior invalid elementary step and the two undefined notions were the defects corrected in this repair.

## Not duplicates

- `lem-pur-derived-functor-morphisms-05sa` vs `lem-pur-left-derived-defined-pointwise-kan-bridge`: the bridge identifies pointwise values with Kan-extension values; 05SA constructs the induced map between two values.
- `lem-pur-derived-functor-inverts-05sb` vs `lem-pur-quasi-isos-saturated-triangulated`: 05SB concerns LF’s image of arbitrary S-morphisms; the existing node concerns saturation and triangulation compatibility of quasi-isomorphisms.
- `lem-pur-derived-functor-shift-05su` vs `lem-sf-exact-functor-derived-triangulated`: the latter is a derived functor induced by an exact abelian functor; 05SU is the general Stacks value-level shift lemma.
- `lem-pur-derived-functor-triangles-05sc` vs `lem-sf-exact-functor-derived-triangulated`: the existing node treats a specific termwise exact functor, while 05SC treats an everywhere-defined Stacks LF.
- `lem-pur-localization-triangles-05r6` vs `thm-weil-pbc-verdier-axioms`: 05R6 is the general localization normal-form proposition; the existing theorem verifies Verdier axioms for a project-specific construction.
- `def-pur-saturated-triangulated-localization` vs `lem-weil-linear-scalar-localization-triangulated`: the present node defines the general MS1--MS6 and saturation notions; the existing node applies Tag 05R2/05R6 to the specific scalar localization at varpi.
- `def-pur-saturated-triangulated-localization` vs `lem-pur-left-derived-from-kflat-class`: the present node defines the abstract localization hypotheses; the existing node uses Situation 05S8 as hypotheses in a resolving-class theorem.
- `def-pur-saturated-triangulated-localization` vs `lem-pur-quasi-isos-saturated-triangulated`: the present node defines the terms; the existing node proves that quasi-isomorphisms satisfy them.
- `def-pur-saturated-triangulated-localization` vs `lem-pur-left-derived-defined-pointwise-kan-bridge`: the present node defines saturation/localization; the existing node relates 05S9 essential constancy to a pointwise Kan extension.
- `lem-pur-derived-functor-morphisms-05sa` vs `lem-weil-pbc-right-derived-plus-injective`: the present node is the LF clause for arbitrary Situation 05S8; the existing node uses 05SA only in a bounded-below right-derived injective construction.
- `lem-pur-derived-functor-shift-05su` vs `lem-weil-pbc-derived-square-iso-commshift`: the present node is the general LF value shift isomorphism; the existing node constructs a commutation isomorphism for inverse-image functors in a base-change square.
- `lem-pur-derived-functor-shift-05su` vs `lem-weil-pbc-derived-direct-image-triangulated`: the present node is the general Stacks LF shift lemma; the existing node proves shift compatibility for one derived direct image.
- `lem-pur-derived-functor-shift-05su` vs `lem-weil-pbc-derived-adjunction-commshift`: the present node is the general LF value shift; the existing node proves a specific adjunction comparison commutes with shift.
- `lem-pur-localization-triangles-05r6` vs `lem-weil-pbc-derived-square-iso-commshift`: the present node states the general source-triangle normal form; the existing node cites 05R6 only to construct a natural transformation in a derived square.
- `lem-pur-localization-triangles-05r6` vs `def-weil-pbc-common-stage-cones`: the present node states all localized distinguished triangles arise from D; the existing definition constructs project-specific common-stage cones.
- `lem-pur-localization-triangles-05r6` vs `thm-weil-pbc-idempotent-complete-triangulation`: the present node is the general 05R6 localization result; the existing theorem adds filtered-colimit and idempotent-completeness conclusions.
- `lem-pur-localization-triangles-05r6` vs `lem-weil-linear-scalar-localization-triangulated`: the present node states the general triangle normal form; the existing node applies it to scalar localization at varpi.

## Second reading by C1

- Item statement: checked against Situation 05S8, Definition 05S9, Lemmas 05SA/05SB/05SU/05SC, Proposition 05R6, and Proposition 05SE in `derived.tex`; exactness clause and hypotheses agree.
- Step 1: checked against Lemma 05SA(2) and its LF comparison diagram; the cited node states the required induced morphism.
- Step 2: checked against Lemma 05SB(2) and the localization universal property; inversion and factorization are stated by the cited nodes.
- Step 3: checked against Lemma 05SU(2); the cited node includes definedness transport to shifts and the canonical isomorphism.
- Step 4: checked against Lemma 05SC (the two-out-of-three LF clause), Lemma 05SA(2), and Lemma 05SU(2); the cited statements provide morphisms, shifts, and distinguishedness.
- Step 5: checked against Proposition 05R6 and the localization construction; the source-triangle normal form and its hypotheses are stated by the cited nodes.
- `def-pur-saturated-triangulated-localization`: checked category, multiplicative-system, saturation, compatibility, and localization notions against Categories Definition 13.5.1 (Tag 05R2) and Situation 05S8; searches recorded and no exact Mathlib declaration found.
- `lem-pur-derived-functor-morphisms-05sa`: checked statement and hypotheses against Lemma 05SA(2); no exact Mathlib declaration.
- `lem-pur-derived-functor-inverts-05sb`: checked definedness equivalence and isomorphism against Lemma 05SB(2); no exact Mathlib declaration.
- `lem-pur-derived-functor-shift-05su`: checked definedness equivalence and canonical shift isomorphism against Lemma 05SU(2); no exact Mathlib declaration.
- `lem-pur-derived-functor-triangles-05sc`: corrected from “three objects” to the source’s “two of three,” then checked against Lemma 05SC; no exact Mathlib declaration.
- `lem-pur-localization-triangles-05r6`: checked source-triangle normal form against Proposition 05R6 and the recorded Mathlib generalization; no duplicate node found.

Changes made: corrected the item node’s `created.item` ownership metadata; corrected the 05SC node to preserve the source’s two-out-of-three conclusion and updated its citation quote; recorded the second-reading checks and repairs here.
