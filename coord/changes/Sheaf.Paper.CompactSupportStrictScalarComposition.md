# Compact support strict scalar composition repair

## Reason

The returned review rejected the `_core` split because it was equivalent to the
parent theorem after cancelling an isomorphism, and required the image-tower
comparison plus support realization. The published comparison hole is restored.
The preparatory declarations are split into a Prelude because the original item
compile took 52.9 seconds; the Prelude took 23.1 seconds in import order.

## Old

The item source contained the rejected `_core` declaration and its node. The
published `compactSupportStrictScalarComparison` declaration was absent from the
delivered source, and the item proof depended only on `_core`.

## New

The `_core` declaration and node are removed. The published comparison theorem is
present with its original statement and hole. The item is proved by the new
`supportRealization_coherence` theorem in
`Sheaf.Paper.CompactSupportStrictScalarCompositionSupportRealization`, applied to
the equation supplied pointwise by `compactSupportStrictScalarComparison`. The
`constantMap_composition` preparatory
declaration is in the Prelude module with its own node.

## Users

The item proof passes the published comparison equation as an explicit hypothesis
to the smaller support-realization theorem. The support node cites the Prelude;
the item node cites the support node. This keeps the DAG acyclic because the
published comparison node already reaches this item through the integral
coefficient comparison route. No existing importer is adapted and no
source-library interface is changed.

## Status

Closed: the repaired item and its new support-realization module compile. The comparison,
identity, and support-realization statements retain their intended proof holes;
the item composition hole is closed. The `_core` theorem was equivalent to the
item, rather than strictly weaker.

## Reviewer corrections (cc review of c5fcbe083d86, 2026-10-28)

- `supportRealization_coherence`: the unused hypothesis `hcomparison` was removed. Its
  conclusion does not mention the E-level comparison, and the item proof still uses
  `compactSupportStrictScalarComparison` directly (`hcomp`). A docstring proof in words
  was added. The module now imports only the Prelude (`public import`).
- Prelude: four unused imports were dropped (CompactSupportCompleteRestrictionFaithful,
  ConstantCompletedScalarAssociativity, ScalarLimitTensorComposition,
  ScalarLimitTensorRestriction). The item drops `import Mathlib.CategoryTheory.Adjunction.CompositionIso`
  and `import Sheaf.Paper.StrictProperRestrictionComposition`; only the moved Prelude declarations used them.
- Nodes: the Prelude node now records all twelve moved public declarations in
  `lean.declarations`, with proof steps and proof_deps for compositionProper and compositionOpen.
  Their owners are added to its stmt_deps. The item node keeps its sixteen earlier proof
  steps and proof_deps, because its remaining declarations still use them. It adds Step 17
  (the support node) and the stmt_dep on the Prelude node, since its statement uses
  compositionTower, compositionRamification, compositionSelection, compositionRetained and
  compositionCompleted. The support node gets the owners of the names in its statement as stmt_deps.
- Users: the one importer, Sheaf.Paper.CompactSupportCompletedScalarArrow, compiles
  against the corrected files.

