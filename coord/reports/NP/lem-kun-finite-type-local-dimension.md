## Files written

- dag/nodes/sec-smooth-purity/lem-kun-finite-type-local-dimension.json: statement, split using existing Mathlib leaves; no new nodes.
- citations.json: verbatim statement quotations for every citation of every proof step.

## Attachments

None. Searched the project source for the exact blueprint tag and for local dimension, finite type and ringKrullDim. The project extension IsAffineOpen.topologicalKrullDim_ne_top in WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:163 proves affine-open topological finiteness, not precisely this stalk assertion. It was not attached. Master is reference material only.

## Wanted

None.

## Corrections and route

The mathematical statement is unchanged. Added def-weil-field, which was named in the statement but missing from stmt_deps. The old source 00P1 is the local-dimension formula, not a direct finiteness theorem. Read that lemma (algebra.tex, lemma-dimension-at-a-point-finite-type-field) and replaced the source pointer with the actual inputs 00KQ, 01T6, 01HV and 00FN. This is not a statement dispute.

The blueprint ancestor lem-kun-dimension-finite-type.md, first proof sentence, explicitly uses the Noetherian local ring argument; the split expands precisely that sentence. Chapter and unit records were read, and neither is changed. All imported flags and blueprint provenance are retained. No units are realized by this auxiliary lemma itself.

## Mathlib and duplicate searches

Ran the required msearch.py searches for the item, using two localization/finite-type phrasings, Loogle and source grep. The second semantic search found instFiniteRingKrullDimOfIsNoetherianRingOfIsLocalRing; read KrullsHeightTheorem.lean:276, where Noetherianity is a section hypothesis. Further stalk queries found the Noetherian-stalk instance at Noetherian.lean:349; read its proof, which uses exactly an affine stalk localization and localization-Noetherianity. LeanSearch returned Internal Server Error and is recorded unavailable. The item has a scheme finite-type hypothesis, rather than an already established Noetherian-stalk hypothesis, so these results do not make it a one-line Mathlib leaf under the delivery rule.

Searched the entire DAG statements for finite local dimension, Noetherian stalks, localization-Noetherianity and the tags; searched the whole blueprint with blueprint_refs.py for finite local dimension, finite-type algebra local-ring finiteness, Noetherian stalks and 00FN. Existing lem-weil-pbc-localization-noetherian and lem-weil-pbc-noetherian-local-system-of-parameters supply the algebra facts. Existing affine-open-stalk-localization supplies the geometric fact. Creating new Noetherian-stalk or local-finiteness nodes would be unnecessary. No new nodes or duplicate pairs.

## Unfinished

Nothing for this one-level split. No Lean was written and no compiler or build tool was run. Delivery is reserved for the second reader.

## Review by NP

I read Stacks Algebra 00P1 (lemma-dimension-at-a-point-finite-type-field), 00FN (lemma-Noetherian-permanence), and 00KQ (proposition-dimension), Properties 01OV (definition-noetherian), Morphisms 01T6 (lemma-finite-type-noetherian), and Schemes 01HV (lemma-spec-sheaves), parts (1) and (6). There are no new node sources to audit. The statement requires neither separatedness nor reducedness nor irreducibility, and none is used.

Step 1 uses the actual field definition and Noetherian-ring definition: the inverse of a nonzero ideal element proves the ideal is the whole ring. The spectrum definition states both that its global ring is K and that it has one point. The locally-Noetherian definition therefore applies to the single chart, and the Noetherian-scheme convention is explicitly in the finite-type-over-Noetherian node. Quasi-compactness of a singleton is elementary: select one member of any open cover. No general theorem about spectra being compact is being silently used.

Step 2 uses the exact statement of lem-weil-pbc-finite-type-over-noetherian. Its finite-type morphism is the given structure morphism, its base is Spec K established in step 1, and its conclusion expressly includes locally Noetherian. It is not being used merely as a definition of that property.

Step 3 chooses a chart from the covering furnished by pqf-def-locnoeth, so its ring is Noetherian without invoking the stronger assertion that every affine ring is Noetherian. Clause (c) of lem-weil-pbc-affine-open-stalk-localization gives all three localization conditions required by lem-weil-pbc-localization-noetherian for the germ map itself. The prime complement is multiplicative by the explicit short argument in the step. The latter node concludes the actual stalk is Noetherian, so no unstated transport theorem is needed. Locality of the stalk is part of the locally ringed space in the scheme definition.

Step 4 uses the first clause of lem-weil-pbc-noetherian-local-system-of-parameters, which explicitly asserts finite dimension for every Noetherian local ring. This is a general algebraic tool, not a clause restatement for finite-type schemes. Its two hypotheses were established in step 3. The other conclusions concerning parameters, Artinian quotients and powers are not used. All three substantive tools are existing Mathlib leaves, so their off-unit use preserves the blueprint route.

I checked B1–B10: no statement-only child carries a hidden proof because there are no children; sources have tags and labels; existing source provenance and flags are kept; searches are actual logged queries, and unavailable LeanSearch is identified. For C1–C8 every non-elementary fact is in a cited statement, all of which I opened; citations.json contains verbatim quotations, and no source proof is used as a black-box node statement. The dependencies descend to general Mathlib leaves and definitions and introduce no edge to this item or its ancestor. D1–D5 are avoided by writing the entire scheme reduction in this item's steps and creating no surrogate conclusion node. For E1–E7, checked the structure morphism's finite type, the Noetherian affine-cover choice, primality needed for the multiplicative set, and the locality required at the final step. Test cases: X empty has no x, so the universal assertion is vacuous; Spec K has a dimension-zero field stalk; the generic and closed points of affine space both fit; a nonreduced finite-type ring such as K[t]/(t^2) is still Noetherian and its sole stalk has dimension zero. Corrected only the missing field dependency and indirect source pointer; the mathematical statement and unit route survive unchanged.

## Second reading by NP

- Item statement: checked against Algebra Tag 00KQ (proposition-dimension), with the finite-type-over-a-field hypotheses and the conclusion that each specified local ring has finite Krull dimension; no hypothesis is added or dropped.
- Step 1: checked the field ideal argument against the field and Noetherian-ring definitions, and the one-point affine spectrum and quasi-compact affine cover against the affine-spectrum and locally-Noetherian statements; the finite-type theorem is cited only for its stated Noetherian-scheme conclusion.
- Step 2: checked that the given structure morphism has the required finite-type source and the target `Spec K` is Noetherian by step 1; the cited finite-type-over-Noetherian node states exactly that the source is Noetherian, hence locally Noetherian.
- Step 3: checked the affine chart choice against the locally-Noetherian definition, the localization data against every clause of affine-open-stalk-localization, multiplicativity from primality, and the Noetherian conclusion against localization-Noetherian; locality comes from the scheme definition.
- Step 4: checked both hypotheses of the Noetherian-local-system-of-parameters node (Noetherian and local stalk) and used only its finite-dimension clause; no parameter or Artinian conclusion is smuggled in.
- New nodes: none. Therefore B1–B7, source tags, self-contained statements, and duplicate-node checks are vacuous for children; all existing dependencies were read by statement rather than by proof.
- Citations: citations.json was checked for one verbatim quotation per cited node, and every non-elementary fact in the four steps has a corresponding existing node. No step relies on a tag without a node or on a cited node's proof.
- Edge cases: the empty scheme makes the universal assertion vacuous; `Spec K` has a zero-dimensional field stalk; affine-space generic and closed points satisfy the same argument; `K[t]/(t^2)` confirms nilpotents do not invalidate Noetherianity or local finiteness.
- Changes retained: added the missing `def-weil-field` statement dependency and corrected the source metadata from 00P1 to the direct finiteness inputs 00KQ, 00FN, 01T6, and 01HV. No mathematical statement or proof step required alteration.
