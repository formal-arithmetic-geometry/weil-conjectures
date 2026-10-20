## What changed

Pruned unused proof imports and decomposed `compatibility` into the strictly smaller
named results `compatibility_data` and `compatibility_triangle`.  The latter is proved
completely from the supplied exactness, shift-commutation, and object-property data;
the original theorem now combines both results with a complete Lean proof.  The module
compiles through `lcompile.py`.

## Proved and sorry left

Closed the original `compatibility` hole and the `compatibility_triangle` helper hole.
The split theorem `compatibility_data` remains a single named `sorry`, as do the
pre-existing `slice_compatibility`, `subcategory_linearity`, and
`scalar_compatibility` holes.  No definitions contain `sorry`.

## No longer needed

Removed these unused proof imports: `Sheaf.Algebra.Homology.SignedDoubleHomCone`,
`Mathlib.Algebra.Homology.BifunctorShift`,
`Mathlib.Algebra.Homology.HomotopyCategory.KInjective`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses`,
`Sheaf.Algebra.Homology.KInjectiveHomComplex`,
`WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`,
`WeilConjectures.Algebra.Homology.HomComplex`,
`WeilConjectures.Algebra.Homology.HomTensorTotal`,
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`, and
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled the explicit signed comparison data with the routine
assembly of `TriangleCompatibility`.  The assembly is independently provable from its
local hypotheses, so it is now a complete helper; only the genuinely mathematical
signed-comparison data remains split off.

## New nodes

- `lem-coef-rational-bidual-data`
- `lem-coef-rational-bidual-triangle-assembly`

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
