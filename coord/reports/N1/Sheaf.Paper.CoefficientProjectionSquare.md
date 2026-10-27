## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.coefficientProjectionSquare` with its
statement and public imports unchanged. The proof imports the declared scalar-tensor
realization and ringed-square normalization, identifies their path comparison with the
specified derived pull comparison, identifies the push comparison with its geometric mate,
and applies the existing categorical projection-mate square.

All auxiliary calculations are proved private lemmas in the item module. The comparison
calculation is performed for abstract abelian categories before specializing, to avoid
expanding the concrete sheaf and derived constructions. No definition or existing signature
was changed and no consumer adaptation was needed. Local proof commands are documented in
`coord/changes/N1-coefficient-projection-private-proof.md`.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.coefficientProjectionSquare`
(node `lem-sfb-coefficient-projection-square`). Zero holes remain in the delivered module;
zero holes and zero public declarations were added elsewhere; zero statements split off.
The imported scalar realization theorem remains a declared dependency of this stage.

## No longer needed

Removed direct proof imports `Sheaf.Paper.ModuleRingedToposDerivedComparison`,
`Sheaf.Paper.RingedComparisonTensorAdjunction`, and
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`. Their work is already
encapsulated in the declared realization/normalization dependencies. This does not withdraw
those modules or their DAG nodes: other consumers and the retained dependencies may need
them. No module is claimed globally pruned. The declared proof dependencies and the unit
route are retained.

## Where the brief, the DAG or earlier work was wrong

The first DAG step treated the realization path as the normalization path immediately.
Their current Lean definitions use independently constructed left-derived and conjugate
right-derived comparisons. The proof supplies the missing identification: composition of
right-derived functors respects conjugation, and transport through the exact-functor
comparisons gives precisely the left-derived square used by the realization. The node's
first proof step now records this calculation. No mathematical statement needed repair.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
