## What changed

Filled the two remaining proofs in `Sheaf.Paper.ConstantCoefficientScalarNormalization`.
`constantCoefficientScalarUnit_existsUnique` specializes
`ConstantScalarStrictUnit.regular_scalar_strict_unit`, converting its full quotient-coordinate
normalization to the equivalent unit-only normalization and transporting uniqueness back.
`constantCoefficientScalarUnit_isIso` recovers the chosen map's normalization, converts it to
full coordinates, and applies
`ConstantScalarUnitQuasiIsomorphism.regular_scalar_unit_quasi_isomorphism`; the derived-category
localization inverts that quasi-isomorphism.

A proved private helper constructs a finite-field datum of prime characteristic greater than l
using `ZMod p` and its algebraic closure. This discharges the auxiliary datum parameters of the
existing dependencies without adding hypotheses to either theorem. Their regular complexes,
boundaries and unit sections agree definitionally with the existing concrete constructions.
No public statement, definition, visibility, or public import changes. Added only private proof
imports of `Sheaf.Paper.ConstantScalarStrictUnit` and
`Sheaf.Paper.ConstantScalarUnitQuasiIsomorphism`. The proof follows the node's existing route,
so its proof dependencies and unit route require no changes.

## Proved and sorry left

Closed 2 of 2 existing holes, both attached to
`lem-weil-constant-coefficient-objects-constructible`:

- `WeilConjectures.constantCoefficientScalarUnit_existsUnique`.
- `WeilConjectures.constantCoefficientScalarUnit_isIso`.

Added holes: none. Remaining holes in the delivered module: none. Split off: none.
The two already-stated dependency theorems are used as requested by stage 3; their existing
proof obligations remain with their modules and are not claimed closed by this delivery.
The already-proved rational isomorphism argument is preserved.

## No longer needed

Removed the following direct private imports, whose results are either already available from
the retained public interfaces or belong to the internal proofs of the two scalar-unit
inputs rather than this assembly:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`.
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`.
- `Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`.
- `Sheaf.Paper.DerivedCompleteOnSlices`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`.
- `Sheaf.Paper.ProEtaleConstructibleSheaf`.
- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`.
- `Sheaf.Paper.SfCommonStageWeilCohomology`.
- `Sheaf.Paper.SfIntegralConstructible`.
- `Sheaf.Paper.SfRationalizationKaroubi`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`.

No node or module is withdrawn. In particular, the strict-unit and quasi-isomorphism nodes
remain necessary, and the parent node's finite constructibility/stalk dependencies are still
needed for its other Lean realizations. Removing these direct private import lines is not a
claim that the corresponding modules leave the global targets' closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy. The two extracted scalar-unit dependencies have a finite-field
datum parameter while this module's scalar normalization statements quantify over arbitrary
schemes without such a datum. A finite field of an auxiliary prime characteristic supplies
it, with no effect on the normalized maps. The stated results apply also to the empty scheme,
disconnected schemes, identity coefficient extensions and ramified extensions.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
