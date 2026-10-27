## What changed

Closed the unit, generator, and degree-zero exchange criteria using the canonical derived
adjunction, the exact pullback homology comparison, and `DerivedCategory.isIso_iff`.
The proofs use only the direct derived-category API and remove the obsolete scalar-forgetting
and bounded-below imports. The edge theorem remains the one unresolved declaration.

## Proved and sorry left

Closed 3 of the 4 original holes:

- `AlgebraicGeometry.Etale.relativeKummerExchange_unit`
- `AlgebraicGeometry.Etale.relativeKummerExchange_generators`
- `AlgebraicGeometry.Etale.relativeKummerExchange_degreeZero`

One `sorry` remains in `AlgebraicGeometry.Etale.relativeKummerExchange_edge`. Its
natural-language proof is recorded in that declaration's docstring and follows the canonical
mate, constant-sheaf, homology, and shift comparisons. No new split-off statements were added.

## No longer needed

Removed proof imports and their unused proof dependencies:

- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`
- `WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
- `WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget`
- `Sheaf.AlgebraicGeometry.CommutativeExchangeChart`
- `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`
- `Mathlib.Algebra.Homology.DerivedCategory.Plus`

The corresponding unused DAG dependencies are the scalar-forgetting, resolution-comparison,
commutative-chart, and bounded-below-plus nodes listed by the original plan. No module is
withdrawn; those upstream declarations remain available to other consumers.

## Where the brief, the DAG or earlier work was wrong

The original route through scalar-forgetting and bounded-below derived categories is longer
than needed for the three closed criteria. The direct ordinary derived-category homology
criterion suffices for the unit and vanishing degrees. The edge route is still pending.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
