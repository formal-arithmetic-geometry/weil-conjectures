# clopen tensor support declarations

## Reason

The finite-clopen theorem is decomposed into independently imported component statements. A support module under a separate namespace provides the same construction bodies to those modules, while the item module retains each original public declaration as a wrapper. Every original public name and signature is preserved.

## Old

`clopenTensorModules`, `clopenTensorRings`, `clopenTensorRestriction`, `clopenTensorRestrictionAdditive`, `clopenTensorComplexRestriction`, `clopenTensorComparison`, `clopenTensorUnitComparison`, `clopenTensorPure`, and `clopenTotalTensorSummand` were defined directly in `Sheaf.AlgebraicGeometry.ProEtaleClopenTotalTensorKFlatDetection.lean`.

## New

The support bodies are also available as `ClopenData.clopenTensorModules`, `ClopenData.clopenTensorRings`, `ClopenData.clopenTensorRestriction`, `ClopenData.clopenTensorRestrictionAdditive`, `ClopenData.clopenTensorComplexRestriction`, `ClopenData.clopenTensorComparison`, `ClopenData.clopenTensorUnitComparison`, `ClopenData.clopenTensorPure`, and `ClopenData.clopenTotalTensorSummand` in `Sheaf.AlgebraicGeometry.ProEtaleClopenTotalTensorKFlatDetectionData.lean`. The original nine declarations remain in the item module with unchanged signatures and names, and their bodies delegate to these support constructions.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedModelNormalization` | unclaimed | original public names and signatures remain available |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarCompositor` | unclaimed | original public names and signatures remain available |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarData` | unclaimed | original public names and signatures remain available |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenKFlatMonoidalDescent` | unclaimed | original public names and signatures remain available |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenOrdinaryScalarComparison` | unclaimed | original public names and signatures remain available |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenMonoidalNormalization` | unclaimed | original public names and signatures remain available |
| `Sheaf.Paper.ClopenCompletedOperationTowers` | unclaimed | original public names and signatures remain available |
| `Sheaf.Paper.FiniteClopenDerivedDecomposition` | unclaimed | original public names and signatures remain available |

## Status

landed 20261027T012938-L-2350552 2026-10-27 (merge of deliver/S7/Sheaf.AlgebraicGeometry.ProEtaleClopenTotalTensorKFlatDetection)
