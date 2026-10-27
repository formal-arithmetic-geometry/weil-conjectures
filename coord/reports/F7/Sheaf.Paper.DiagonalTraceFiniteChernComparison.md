## What changed

Filled `diagonalTrace_finite_chern_comparison` without changing its signature.
The proof evaluates the tower adjunct using the existing normalized geometry
unit equation, composes the finite push comparison with the positive-line
comparison, and transports the adjunct by naturality and the finite unit
identity. Both categorical transport arguments are proved private helpers.

Added `FiniteP1CoefficientAdjunctionCoordinates` for the missing finite
coefficient comparisons and `FiniteP1KummerChernRealization` for the scalar
Kummer comparison on X before direct image. The latter defines its positive
class as the actual comparison image of `geoP1EtaleChern`, and proves that
its ordinary adjunct is the second component of `geoP1TwistedMap` directly
from the specified etale decomposition component and direct-image mate.

The existing constant/root-section `SpTowerP1.CoefficientCoordinates` is reused.
Its type is already declared, but there was no theorem constructing it from
the hypotheses here. No arbitrary data are chosen from a sorried existence
theorem: the main proof eliminates the existence proposition directly, and
all new definitions are explicit composites of published canonical maps.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finite_chern_comparison`
(node `lem-sfb-diagonal-trace-finite-chern-comparison`). This is a decomposition,
not a net hole reduction: one original hole is closed and two holes are added.

The two remaining holes, each in its own new module, are:

- `AlgebraicGeometry.ProEtale.DiagonalTrace.finiteP1_coefficient_adjunction_coordinates`
  (`lem-sfb-finite-p1-coefficient-adjunction-coordinates`): constructs normalized
  finite coefficient coordinates and pull/push comparisons with their unit
  and coefficient equations. It has no Chern data or Chern conclusion.
- `AlgebraicGeometry.ProEtale.DiagonalTrace.finiteP1_kummer_chern_realization`
  (`lem-sfb-finite-p1-kummer-chern-realization`): compares the scalar Chern arrow
  on X with the actual ordinary etale Kummer class, given any normalized
  coordinates. It has no tower base, geometry, coefficient pullback, or
  tower direct-image adjunct.

Also proved `finiteP1PositiveClass_adjunct`, showing the ordinary component
identity without assuming invertibility of the decomposition. The private
helpers `evaluation_adjunct`, `realization_adjunct`, `comparison_adjunct`,
and `ordinary_positive_adjunct` contain complete categorical proofs.

Validation: all three delivered modules pass remote compilation. The three
generic adjunction helpers also passed an isolated Mathlib-only compilation.
The delivery tool runs the full packet compilation, axiom probe, and preflight
before pushing.

## No longer needed

No existing module is withdrawn and no public import is removed. No existing
mathematical dependency is globally pruned. The original direct proof edges
to the diagonal, finite-normalization, intrinsic-adjunction, and G2 nodes are
replaced by the two explicit finite substeps and adjunction evaluation; those
notions remain needed transitively and in the theorem's statement. In
particular the proof needs the defining G2 Chern component, not its
invertibility or cohomology computation. No negative Tate cancellation,
projection formula, or cohomology-vanishing result is imported for this proof.

The new proof imports are exactly `FiniteP1KummerChernRealization` and
`TowerGeometryAdjunctionEvaluation`. Their statement imports retain the
existing coefficient and ordinary projective-line definitions.

## Where the brief, the DAG or earlier work was wrong

The old three-step plan correctly describes the mathematics but its cited
interfaces do not themselves state the normalized coefficient-coordinate
existence or the scalar Chern realization equality. `CoefficientCoordinates`
is a structure, not an existence theorem. These are now separate concrete
statements. The reduction does not rename the commuting square: the first
new statement is independent of Chern classes, the second is independent of
tower geometry and direct-image adjuncts, and the original square is assembled
by proved naturality and unit calculations.

The new proof uses the existing `def-sp-p1-coefficient-coordinates` interface
from the smooth-purity unit as a tool for constant/root-normalized coefficient
coordinates; it does not replace or bypass any realized step of the diagonal
tower unit. The unit's realized statement/step lists are empty, and its route
through the normalized finite G2 component is retained.

Edge checks: the finite exponent is always n+1, so n=0 has exponent one.
All coordinate isomorphisms and adjunction equations make sense for empty
schemes and the zero ring. No nonzero generator, inverse decomposition, or
choice of primitive root is assumed. The class sign stays the specified
positive Kummer sign.

## New nodes

`lem-sfb-finite-p1-coefficient-adjunction-coordinates` owns the explicit unit
coordinate definitions, the over-e realization functor, and the Chern-free
coefficient/adjunction comparison theorem. Its module is
`Sheaf.Paper.FiniteP1CoefficientAdjunctionCoordinates`.

`lem-sfb-finite-p1-kummer-chern-realization` owns the actual positive ordinary
Chern class definition, its proved adjunct identity, and the remaining scalar
Kummer realization theorem. Its module is
`Sheaf.Paper.FiniteP1KummerChernRealization`.

Both nodes cite paragraph (1) of the current diagonal-tower trace proof,
record the reused definitions and searches, and supply full proof plans.
No existing interface is changed, so no change record or consumer adaptation
is required.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
