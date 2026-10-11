Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-left-derived-from-kflat-class.json` (repaired split).
- `dag/nodes/sec-smooth-purity/lem-pur-total-left-derived-localization.json` (repaired Mathlib leaf).
- `dag/nodes/sec-smooth-purity/lem-pur-left-derived-exact-when-defined.json` (new Tag 05SE statement node).
- `citations.json` (verbatim quotes for steps 2 and 3).

Attachments:

- None. No sorry-free project declaration states the arbitrary resolving-class criterion.

WANTED:

- None.

What was wrong and repaired:

- The returned split's only step cited Tag 06XN, which is the item's own criterion, and its Mathlib leaf assumed `HasLeftDerivedFunctor`, the existence being proved. Step 1 now writes the elementary cofinality and essential-constancy argument, and Step 2 cites the actual pointwise-to-right-Kan-extension declarations.
- Exactness was asserted from Proposition 05SE without a DAG node. The new `lem-pur-left-derived-exact-when-defined` statement records the LF part of Tag 05SE and Step 3 cites it.

## Review by M1

I reread Tag 06XN in `derived.tex`, including its dual resolving-class proof and computation clause, and Tag 05SE in Situation 05S8. Step 1 uses only the two item hypotheses: cofinal P-resolutions and invariance of F on quasi-isomorphisms between P-objects; the resulting essential constancy is the short elementary argument requested by the return. Step 2 cites the repaired leaf, whose statement is exactly the pointwise-left-derived-to-left-derived/right-Kan-extension implication, and whose source was read at `PointwiseLeftDerived.lean` lines 86 and 98. Step 3 cites the new node, whose statement is precisely the LF exactness clause of 05SE, and separately spells out the identity-resolution computation for objects of P.

I searched the whole DAG and blueprint for a generic 05SE exactness node and found no duplicate statement; existing right-derived and exact-functor nodes concern different hypotheses or constructions. I ran LeanFinder, Loogle, grep, and LeanSearch for the new exactness node; the searches and unavailable results are recorded in its `mathlib_searches`. I checked the zero complex and a class containing all complexes; the cofinality and computation claims reduce to the identity resolution. The circular leaf and uncited exactness assertion identified in the return are both removed.

## Not duplicates

- `lem-pur-left-derived-exact-when-defined` vs `lem-pur-left-derived-from-kflat-class`: the new node isolates only the generic exactness implication from Tag 05SE, while the item additionally constructs the derived functor from a resolving class and proves its computation on P; the new node is required to cite that non-elementary clause.
- `lem-pur-left-derived-exact-when-defined` vs `lem-weil-pbc-derived-direct-image-triangulated`: the new node is the generic LF clause of Tag 05SE, while the existing node is a specific RF/direct-image triangulated result on a bounded-below domain.

## Second reading by M1

- Item statement: checked against Stacks Tag 06XN (dual resolving-class clause), Situation Tag 05S8, Definition Tag 05S9, and Proposition Tag 05SE; the hypotheses and conclusions agree, including the direction of the resolution maps, quasi-isomorphism invariance, the right Kan extension universal property, exactness, and computation on the resolving class.
- Step 1: checked against the proof of Tag 06XN; hypothesis (1) gives cofinality and hypothesis (2) gives essential constancy. The identity resolution gives computation for an object of the class. This is elementary from the hypotheses and the definition of the left-derived pro-object.
- Step 2: checked against Mathlib `PointwiseLeftDerived.lean` lines 86 and 98 and the statement of `lem-pur-total-left-derived-localization`; it uses only pointwise existence and localization, and the cited node states the resulting right Kan extension and universal property.
- Step 3: checked against Proposition Tag 05SE (LF part) and the identity-resolution argument in Tag 06XN; exactness is supplied by the cited statement, while computation is the elementary counit calculation from Step 1. The zero complex, a field, the empty indexing case, and one-term complexes reduce to the identity resolution and add no hypotheses.
- `lem-pur-total-left-derived-localization`: checked as a statement-only Mathlib leaf against `hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor` (line 86) and `isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor` (line 98); its notions are supplied by its dependencies and its recorded searches were rerun.
- `lem-pur-left-derived-exact-when-defined`: checked as a statement-only node against Proposition Tag 05SE in Situation Tag 05S8; its triangulated-category and localization notions are explicitly referenced, and the recorded Mathlib searches found no generic declaration.
- No duplicate or circular node was found: the DAG search contains no generic Tag 05SE exactness node, and the Mathlib leaf is strictly the pointwise-to-global construction rather than the resolving-class criterion.

Changes made: corrected the item node's `created.item` ownership field, which incorrectly named `lem-pur-derived-change-of-rings`; no mathematical statement or proof step required alteration.

Repair update: added `lem-pur-left-derived-defined-pointwise-kan-bridge` for the 05S9/pro-object to pointwise-Kan equivalence, added `lem-pur-quasi-isos-saturated-triangulated` for the 05RT saturation and triangulation hypotheses, made the exactness node self-contained, and expanded the item proof to four steps with updated verbatim citations. The Mathlib leaf metadata points to `PointwiseLeftDerived.lean` lines 86 and 98.

## Not duplicates

- `lem-pur-left-derived-defined-pointwise-kan-bridge` vs `lem-pur-left-derived-from-kflat-class`: the bridge identifies two notions of being defined at one object; the item constructs an everywhere-defined LF from resolving data and proves exactness and computation.
- `lem-pur-left-derived-defined-pointwise-kan-bridge` vs `lem-pc-derived-adjoint-functors`: the existing node proves an adjunction from globally defined derived functors; the bridge has no adjunction conclusion and concerns one pointwise value.
- `lem-pur-left-derived-defined-pointwise-kan-bridge` vs `lem-weil-pbc-right-derived-plus-injective`: the existing node is a bounded-below right-derived-plus-injective construction; the bridge is the general left-derived Stacks/pointwise-Kan equivalence.
- `lem-pur-quasi-isos-saturated-triangulated` vs `lem-pur-left-derived-from-kflat-class`: the new node supplies localization hypotheses; the item uses them to derive LF exactness and computation.
- `lem-pur-quasi-isos-saturated-triangulated` vs `def-weil-abstract-derived-category`: the definition node defines `D(A)` and its triangulation, but does not state saturation or cone detection of quasi-isomorphisms.
- `lem-pur-quasi-isos-saturated-triangulated` vs `lem-pc-quasi-isomorphisms-multiplicative-system`: the existing Mathlib leaf states fraction calculi and localization; the new node adds saturation, cone characterization, and triangulation compatibility.
- `lem-pur-quasi-isos-saturated-triangulated` vs `def-weil-derived-category-cohomology-functor`: the existing node concerns factoring cohomology through localization; the new node concerns the multiplicative system itself.
- `lem-pur-quasi-isos-saturated-triangulated` vs `lem-weil-pbc-derived-direct-image-triangulated`: the existing node proves a specific direct-image functor is triangulated; the new node is the generic 05RT property in `K(A)`.
- `lem-pur-left-derived-exact-when-defined` vs `lem-pc-derived-adjoint-functors`: the existing node concludes an adjunction from two already globally defined derived functors; the new node concludes exactness of one LF under 05SE hypotheses.
- `lem-pur-left-derived-exact-when-defined` vs `lem-weil-pbc-right-derived-plus-injective`: the existing node constructs a specific right-derived functor on a bounded-below category using injectives; the new node is the generic exactness implication for an everywhere-defined left-derived functor.
