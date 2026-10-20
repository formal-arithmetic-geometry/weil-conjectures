## What changed

Repaired the compile timeout in `Sheaf.Paper.CoefficientExtensionReductionModel`.
The five concrete records now specialize four generic records with exactly the original
field types and equations. Two large model predicates cache the original finite-evaluation
and Roos-projection equations. The chain association has an explicit result type, and
comparison definitions restrict automatic unfolding while retaining exposed bodies.
No source-library module or target statement changes.

The item compiled cleanly at 22.6 and 41.8 seconds on the final source. The original
`DerivedPullbackTensorIso` consumer compiled against the repair in 54.2 seconds.
`ScalarExtensionTowerCoherence` timed out both against the repair and against the
published baseline; it is unchanged, and its field usages remain identical.
`IntegralPullbackComparisonRealization` likewise timed out against both the repair and
the published baseline; it mentions none of the changed declarations. No consumer is
adapted. The public-import graph audit found only the two deliberately removed modules
lost from this item's public closure, and found no downstream use losing visibility.

Proved `WeilConjectures.coefficientExtensionQuotient_naturality` by faithful forgetting,
constant-sheaf functoriality and `integralScalarQuotientMap_transition`. Its small proved
ring calculation is a private helper in the same module. The earlier attempt's separate
helper module and new node are not retained; no proof or file is split to meet the limit.

Change record: `coord/changes/z9-coefficient-extension-record-cache.md`.

## Proved and sorry left

Closed one of the four original holes:
`WeilConjectures.coefficientExtensionQuotient_naturality`.
Added zero holes; zero results split off.

Three original named theorem holes remain, all attached to
`lem-pur-coefficient-extension-reduction-model` with their existing source and proof plans:

- `WeilConjectures.coefficientExtensionReductionModel`;
- `WeilConjectures.coefficientExtensionReduction_composition`;
- `WeilConjectures.coefficientExtensionReduction_identity`.

The delivered change repairs the previously blocking definition/elaboration cost and
retains the proved quotient-naturality result. It does not claim to prove these three
major coherent-model results.

## No longer needed

Removed unused private imports:

- `Sheaf.Paper.NormalizedDVREffectivity`;
- `Sheaf.Paper.NormalizedDVRTower`;
- `Sheaf.Paper.IntegralScalarExtensionWellDefined`;
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`;
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`;
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`;
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`;
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`;
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.

Removed unused public imports `Sheaf.Paper.IntegralReductionTowerCanonical` and
`Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`.
The remaining public interfaces expose every name used by the module's statements and
definitions. No existing node/module is withdrawn or claimed mathematically unnecessary:
the dependency plan of the three remaining major holes is preserved in the DAG.
No source-library declaration is removed or changed to sorry.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped on a compilation timeout and tried moving a tiny ring
calculation into another file. The actual cost was the repeated elaboration and checking
of concrete coefficient record types and comparison definitions. Caching their types and
large propositions repairs that cost within this module. The finite quotient calculation
is now retained in the same module. No mathematical statement discrepancy was found.

The original eight-step plan remains for the three unfinished theorems; the node also
records the completed elementary quotient-naturality step. The packet adds no new nodes.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
