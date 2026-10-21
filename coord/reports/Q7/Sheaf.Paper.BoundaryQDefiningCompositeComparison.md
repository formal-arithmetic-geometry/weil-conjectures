## What changed

Proved `boundary_q_defining_composite_comparison` by the DAG's input-symmetry,
inverse-projection, and final-arrow calculation. Private helpers prove naturality and
braiding compatibility for the exact native comparison tensor isomorphism, using its
left-derived counit normalization on K-flat representatives and doctrinal adjunction
for the comparison pullback. The diagram calculation is proved for an abstract coefficient
category and instantiated at `ModuleCat A`; local irreducibility attributes prevent
repeated unfolding of the canonical comparison isomorphisms. No target, existing
statement, or definition changed.

The import/interface change record is
`coord/changes/boundary-q-defining-composite-native-proof.md`. The downstream source
check reports zero current Lean importers; all existing public declarations and the
DAG attachment remain, for the unfinished parent that needs this item.

## Proved and sorry left

Closed the single hole in
`AlgebraicGeometry.ProEtale.BoundaryComparisonOfCoefficients.boundary_q_defining_composite_comparison`
(node `lem-weil-boundary-q-defining-composite-comparison`). No holes added or split off.
No `sorry` remains in the delivered module.

## No longer needed

Removed proof imports `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons` and
`Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`; their general ringed-module
presentations are unnecessary for the existing constant-coefficient functor. Removed
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`,
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, and
`Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed` as direct imports: the public
statement uses the already recorded native ordinary comparison, pullback square and
derived tensor functors. The last import is already public through
`BoundaryExceptionalComparisonData`.

The proof does not use nodes
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-sfb-ringed-derived-monoidal-comparisons`, or
`lem-sf-ringed-derived-closed-symmetric-monoidal`; its node's proof dependencies and
obsolete tool-use entries are updated accordingly. Those nodes remain available to
other consumers, and none of their modules or declarations is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned categorical calculation is correct. Its first step can be proved directly
for the actual native comparison isomorphism, without identifying a separate ringed-site
module presentation. The public theorem retains all input hypotheses and its exact
conclusion. The unit has no realized route steps to bypass. Small cases checked in the
argument: identity comparison, zero final arrow, arbitrary (including zero) input
objects, and odd cochain degrees; the braiding used throughout is the same native
Koszul braiding, so no sign is discarded.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
