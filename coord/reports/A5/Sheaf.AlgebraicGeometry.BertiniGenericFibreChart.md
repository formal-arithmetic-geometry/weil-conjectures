## What changed

Proved `AlgebraicGeometry.exists_bertiniIncidenceChart` with its original statement and public
imports unchanged. Four new proved support modules carry the geometric chart construction,
basis-coordinate change, base-change compatibility, and polynomial generic residue-field
comparison. The target combines the dominant adapted chart with the existing
`Algebra.bertini_independent_functions` and transports the resulting residue-field arrow.

The construction handles nonreduced Y by quotienting each affine coordinate ring by its
nilradical. It uses universal homeomorphisms rather than global nilpotence. The base-locus
codimension bound proves each affine incidence chart irreducible; the zero-parameter section
makes these charts pairwise intersect. This proves the density required for the adapted chart.
The chosen three vectors are proved independent by the principal ideal theorem and extended
to a basis. Polynomial evaluation verifies the actual parameter projection after changing
coordinates and eliminating the first variable. No existing definition or signature changed.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.exists_bertiniIncidenceChart`.
Added zero holes. Every declaration in the five delivery modules is proved or is a real
construction. In particular, the following supporting results are proved:

- `Algebra.exists_bertiniBasisCoordinateChange`;
- `AlgebraicGeometry.isPullback_bertiniIncidenceBaseChange` and its tensor-unit, local-generator,
  ideal-pullback, ambient-pullback and projection compatibility API;
- `AlgebraicGeometry.exists_bertiniIncidenceAdaptedChart`;
- `AlgebraicGeometry.bertiniPolynomialResidueArrow`.

There are no remaining `sorry` declarations in this packet and no unfinished split.

## No longer needed

The target's direct proof no longer needs these imports (some remain used through the new
adapted-chart module): `Mathlib.AlgebraicGeometry.Noetherian`,
`Sheaf.AlgebraicGeometry.BertiniUniversalZeroSection`,
`WeilConjectures.AlgebraicGeometry.Curve.ReductionNilradicalNilpotence`,
`Sheaf.AlgebraicGeometry.BertiniAffineIncidenceIrreducible`,
`Sheaf.AlgebraicGeometry.BertiniIncidenceElimination`,
`WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRing`,
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`,
`Sheaf.AlgebraicGeometry.GenericPointGeometricIrreducibility`, and
`Sheaf.AlgebraicGeometry.BertiniAffineIncidenceChart`.

The route does not use `lem-sc-reduction-nilradical-nilpotent`: a surjective closed immersion
is a universal homeomorphism, which gives the required topology and field comparisons without
a global nilpotence bound. It does not use
`lem-weil-pbc-finite-type-domain-dimension-local-ring`: the dimension-at-point and
transcendence-degree formulas give the needed quotient dimension identity directly. It does
not use `lem-weil-pbc-noetherian-height-quotient-bound`: Mathlib's principal ideal theorem gives
the height-one contradiction directly. The global integral-scheme and locally-Noetherian
steps (`def-pc-integral-scheme`, `pqf-lem-locnoeth-lft`, `pqf-lem-affine-open-locnoeth`) are also
unnecessary for this route, which works directly with reduced finite type affine domains.
These are removals from this proof's dependency route; no existing module is withdrawn, and
no claim is made that other target routes do not still use them.

## Where the brief, the DAG or earlier work was wrong

The planned affine and residue-field argument is valid, but the existing interfaces did not
supply the necessary change-of-base incidence square or the compatible change of coefficient
coordinates. Both are now constructed and proved. The global nilpotence reduction is stronger
than needed. The original three-vector independence and dimension arguments can use existing
Mathlib and source-library results directly. No statement was disputed or weakened.

## New nodes

`lem-zl-bertini-basis-coordinates`: compatible polynomial coordinate changes for two bases.
Module `Sheaf.AlgebraicGeometry.BertiniBasisCoordinates`.

`lem-zl-bertini-incidence-naturality`: tensor-unit compatibility and the cartesian incidence
base-change square. Module `Sheaf.AlgebraicGeometry.BertiniIncidenceNaturality`.

`lem-zl-bertini-incidence-adapted-chart`: the actual dominant, stalk-surjective polynomial chart,
component dimension and fraction-field geometric irreducibility.
Module `Sheaf.AlgebraicGeometry.BertiniIncidenceAdaptedChart`.

`lem-zl-bertini-polynomial-residue-arrow`: the generic residue-field arrow for the eliminated
polynomial projection. Module `Sheaf.AlgebraicGeometry.BertiniPolynomialResidueArrow`.

No change record is needed: no existing statement, definition, or public import was changed.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
