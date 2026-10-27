## What changed

Proved `AlgebraicGeometry.Etale.SupportedTrace.secondExtraction` with its existing
statement and canonical maps. The proof inverts the native compact-support
projection/exchange square, uses projection associativity to extract the two
coefficients, applies the common-coefficient braid, and finishes by naturality.
The existing `extractionShuffle` construction and all public imports are preserved.

Added `Sheaf.AlgebraicGeometry.SfSupportedCoefficientBraid`, which proves
`coefficientBraid`, and `Sheaf.AlgebraicGeometry.SfSupportedCoordinateTensor`,
which constructs `coefficientSplit`, `cyclicShuffle`, `coefficientCoordinate`
and `tensorCoordinate` and proves `coordinateTensor`. The latter two generic
constructions specialize definitionally to the existing coordinate and
coordinateTwisted maps. This isolates the inverse-image tensor calculation,
without any direct image or projection formula. The braid proof transports
identity self-symmetry through the two pullbacks, then uses the hexagons and
naturality. Both new modules use generic coefficient categories to keep
concrete derived-category comparisons small. Their public imports provide the
statement and construction APIs; all added proof imports are private.
No other existing Lean module is changed.

Updated the item's proof plan and dependency list to follow these native maps.
The unit's second coordinate calculation before the trace is preserved.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.SupportedTrace.secondExtraction`
(`lem-sf-supported-second-extraction`).

Added no holes. The new theorem
`AlgebraicGeometry.Etale.SupportedTrace.coefficientBraid`
(`lem-sf-supported-coefficient-braid`) and all private helpers have complete proofs.
The new `AlgebraicGeometry.Etale.SupportedTrace.coordinateTensor` theorem
(`lem-sf-supported-coordinate-tensor`) is also fully proved. There are zero
`sorry` declarations in the three delivered Lean modules. All three modules compiled together in the delivery check: extraction in
57.2 seconds, coordinate tensor in 11.0 seconds, and coefficient braid in
36.0 seconds. The two reported unused-argument warnings were then corrected. Profiling options and diagnostic
modules were removed before delivery. Generic component equations and explicit
normalization of composite-functor evaluation avoid costly kernel conversions;
no shared definition was changed.

## No longer needed

The revised proof does not use these former proof dependencies as additional
inputs; it uses the native supported square directly:

- `lem-weil-pbc-ringed-exchange-tensor-coherence` /
  `Sheaf.Paper.RingedExchangeTensorCoherence`.
- `def-sp-unbounded-proper-shriek-star-comparison` /
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar`.
- `lem-asd-source-proper-projection-coincidence` /
  `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaCoherence`.
- `lem-kun-proper-base-change-torsion-ring` /
  `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`.
- `lem-sfb-ringed-projection-tensor-composition` /
  `Sheaf.Paper.RingedProjectionTensorComposition`.
- `lem-sfb-ringed-derived-monoidal-comparisons` /
  `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.

The original item imported only its statement-data module, which stays. None of
these old proof-dependency modules needed an added import. A trial broad private
import of `ProjectionFormulaCoherence` was replaced with the precise native
`LowerShriekProjectionExchange` module. These are dependency-plan removals for
this proof, not withdrawals of adopted source declarations or claims that the
modules have no other consumers. Existing public imports and their transitive
support for the canonical data remain intact. `lem-kun-tensor-sym` remains needed.

## Where the brief, the DAG or earlier work was wrong

The planned detour through ringed-topos coherence and proper forget-supports
comparisons is unnecessary. The source library already proves
`projectionMap_rightDerivedLowerShriekBaseChangeMap` for the actual canonical
supported maps in the statement, and `projectionMapAssociativity` for the same
projection maps. The remaining geometric comparison is an elementary tensor
calculation using monoidality of the pullback square comparison and the even
self-symmetry hypothesis. No disputed statement, weakened hypothesis, arbitrary
comparison, trace normalization, or new adjunction assumption is used.

## New nodes

`lem-sf-supported-coefficient-braid` states the coefficient-only identity needed
between projection associativity and inverse ordered-projection naturality. It
is strictly a part of the extraction argument and is fully proved here. Its
statement does not assume properness or finiteness.

`lem-sf-supported-coordinate-tensor` isolates monoidality of the coordinate
comparison conjugated by the coefficient isomorphism. It does not require
self-symmetry, a direct image or a projection formula. This generic coefficient
step is fully proved, and its separate module keeps the tensor compatibility
calculation within the per-file compilation budget.

Zero objects and the zero
ring require no separate hypothesis. There are no change records because no
existing definition or statement was changed.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
