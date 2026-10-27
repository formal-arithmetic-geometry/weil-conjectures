## What changed

Proved `AlgebraicGeometry.ProEtale.SpFiniteOrientation.canonical_purity_at_unit` in
`Sheaf.Paper.FiniteOrientationReduction`, retaining its exact statement and all definitions.
Added proved private helpers for tensor-mate naturality and the single-complex coefficient
unit. The proof uses the existing coefficient-unit mate calculation, the specified ordinary
presentation of `diagonalDualizingObject`, and naturality of the comparison tensor constraint.
Added the private proof import
`WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence` for
`projectionMap_app_app_naturality_right`. Updated the existing node's proof description.

## Proved and sorry left

Closed one of the six original holes:
`AlgebraicGeometry.ProEtale.SpFiniteOrientation.canonical_purity_at_unit`.
Added zero holes and zero new statements with `sorry`.

Five existing holes remain, all attached to `lem-sp-finite-orientation-reduction`:

- `AlgebraicGeometry.ProEtale.SpFiniteOrientation.uniformizer_orientation_agreement`
- `AlgebraicGeometry.ProEtale.SpFiniteOrientation.finite_orientation_reduction`
- `AlgebraicGeometry.ProEtale.SpFiniteOrientation.uniformizer_purity_agreement`
- `AlgebraicGeometry.ProEtale.SpFiniteOrientation.unit_tower_mem`
- `AlgebraicGeometry.ProEtale.SpFiniteOrientation.unit_tower_reduction`

The existing proofs `coefficient_ideal` and `coefficient_unit_purity` are retained.

## No longer needed

None. No imports, modules, declarations or planned dependencies are withdrawn.
The five remaining holes retain their original proof dependencies. The proved unit
calculation needs no new intermediate theorem with a postponed proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The existing ordinary coefficient-unit
proof concerns the tensor unit, whereas the canonical pro-etale statement is presented at
the single-complex coefficient unit. Its proof therefore also needs naturality along
`smoothPurityUnitIso`, followed by the specified comparison-unit identifications.
The general reduction theorem presently uses a common annihilating exponent and pro-etale
coordinates; applying it directly to the unequal-exponent ordinary equation would still
require the exponent and presentation comparisons. Those five original holes are unchanged.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
