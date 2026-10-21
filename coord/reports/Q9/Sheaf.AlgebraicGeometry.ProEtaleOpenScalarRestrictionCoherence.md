## What changed

Filled the seven theorem proofs in `Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence`, without changing their statements or the six published definitions. Added proved private helpers for fixed-scalar unit normalization, realization composition, and adjunction mates. The canonical open comparison is proved normalized and unique; its specified coefficient composition and identity equations are then proved for sheaves, complexes, and unbounded derived categories.

The proof uses the existing open adjunction, restriction/coextension of scalars, the section-normalized realization comparison, and Mathlib's mate-pasting theorems. The derived cocycle uses `Functor.mapDerivedCategorySquareIso_comp` from `Sheaf.CategoryTheory.DerivedExactSquareComposition`; the derived identity uses the existing exact derived-square identity theorem. Updated the item's DAG proof, proof dependencies and proof origin to record this route. No source-library file, public signature, definition body, consumer, or target statement changes. The added scoped notation and local irreducibility commands are documented in `coord/changes/proetale-open-scalar-coherence-proof-environment.md`, because preflight classifies proof-environment commands conservatively as interface changes. The downstream scan reports zero importers and no adaptation is needed. The full proof file compiled successfully in 38.6 seconds; import-direction checks pass for both added private proof imports. All 13 existing declaration signatures and the six definition bodies were checked byte-for-byte against the original.

## Proved and sorry left

Closed all seven original holes (namespace `AlgebraicGeometry.Scheme`):

- `sfOpenRestriction_normalized_unique`
- `sfOpenRestriction_coefficient_comp`
- `sfOpenRestriction_coefficient_id`
- `sfOpenRestriction_cochain_comp`
- `sfOpenRestriction_cochain_id`
- `sfOpenRestriction_derived_comp`
- `sfOpenRestriction_derived_id`

All belong to `lem-sf-open-extension-scalar-restriction-coherence`. Holes left in the item: zero. Holes added elsewhere: zero. New split statements: zero. The proof uses existing declarations as permitted by stage 3, including `sfRealizationRestriction_existsUnique`; its unfinished proof remains a dependency rather than a new hole in this packet.

## No longer needed

Removed private imports `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`, `Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`, and `Mathlib.CategoryTheory.Localization.Predicate`. Direct sheafification and ordinary coefficient-adjunction proofs are unnecessary here: the published comparison is already defined using adjunction uniqueness, and its unit equation suffices. Scalar exactness instances are already available through existing public dependencies. The derived APIs encapsulate localization extensionality, so no direct localization proof is needed.

Removed direct proof dependencies `def-weil-presheaf-modules-sheafification` and `lem-pur-sheaf-ring-coefficient-ordinary-adjunction` from this node. Their mathematics may remain necessary below imported definitions; this packet withdraws no module or declaration and claims no global pruning of those dependencies. Added the existing proved node `lem-pod-derived-exact-square-composition` to the proof route. The blueprint unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original direct sheafification argument is valid but longer than necessary for the comparison actually published in Lean. Its fixed-scalar middle square is constructed by uniqueness of left adjoints, so the corresponding unit equation and the mate correspondence supply normalization directly. The sectionwise realization property identifies the transported scalar compositors. No false statement, mathematical interface repair, forced consumer adaptation, or new node was needed. The first preflight required the proof-environment change record named above; the packet now includes it.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
