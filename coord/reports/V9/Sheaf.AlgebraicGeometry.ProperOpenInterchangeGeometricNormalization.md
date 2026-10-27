## What changed

The original theorem is proved as a conjunction. The entire ordinary support cube is proved
by monic support inclusions and ordinary mate pasting; the derived base-change conjunct
then follows from `Functor.rightDerivedFunctorPlusBaseChange_cube`. The refinement conjunct
uses the existing proved `properOpenIdentification_unit`, cancellation of the invertible
derived open unit, and the open adjunction hom-equivalence. Only the algebraic derived
unit equation is split off. No existing statement, definition, or public import changes.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Etale.properOpenInterchangeGeometricNormalization_of_normalization`
(node `lem-cbc-normalized-proper-open-geometric-normalization`). Its proof is complete from
the named dependency below; there is no `sorry` in the item module.

Added hole: `AlgebraicGeometry.Etale.properOpenDerivedUnitNormalization`
(node `lem-cbc-proper-open-derived-unit-normalization`), in the new module
`Sheaf.AlgebraicGeometry.ProperOpenDerivedUnitNormalization`. This is the unit/counit equation
for one ordinary triangle and its canonical derived lift; it has no properness, finite-ring,
invertibility, global families, gamma, properOpenIdentification, properOpenComparison,
Cartesian cube, or geometric component-restriction hypothesis/conclusion.

This delivery is a decomposition: 1 original hole closed and 1 strictly simpler hole added,
net 0 holes. The Cartesian base-change conjunct is proved in full. The remaining equation
has been checked on identity triangles, empty opens, zero coefficients, and the zero map
(the latter satisfies the normalization only in its degenerate zero situation).

## No longer needed

Removed direct private imports:
- `Sheaf.AlgebraicGeometry.ClopenSectionDirectImage`;
- `Sheaf.AlgebraicGeometry.DerivedOpenRestriction`;
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`;
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`;
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`;
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.

The last two APIs remain available through the used public imports of
`Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange` and
`Sheaf.AlgebraicGeometry.ProperSupportSheafComposition`; this is import cleanup, not
withdrawal of their mathematics. Direct clopen-component and geometric open-restriction
calculations are replaced by the proved identification-unit theorem. Their nodes
`lem-weil-pbc-clopen-section-direct-image`, `lem-weil-pbc-derived-open-restriction`, and
`lem-weil-pbc-exchange-forget-coefficients` are removed from this node's direct proof route;
they remain needed transitively by existing definitions/theorems. No module is withdrawn.
All original public imports and target statements are preserved. No blueprint unit route
is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or tool failure was found. The original refinement plan repeated a
geometric component calculation already encapsulated by the proved
`properOpenIdentification_unit`; using its unit characterization substantially reduces
that part of the argument. The ordinary support cube available in the unbounded comparison
module unnecessarily carried Noetherian hypotheses: its proof works verbatim without them.
Only its proved private argument is reused here; no source-library declaration is edited.

## New nodes

`lem-cbc-proper-open-derived-unit-normalization` records exactly the remaining algebraic
passage from the ordinary support normalization to the derived unit/counit equation.
Its standalone module is `Sheaf.AlgebraicGeometry.ProperOpenDerivedUnitNormalization`.
The statement has one natural transformation and one triangle; the docstring gives the
ordinary transpose calculation and the bounded-below localization proof. The original
node now records the actual three-step proof and its declared dependencies.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
