# Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback

## Reason

The Sheaf module is an empty API shim: it declares no constants and only publicly
imports `WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullbackExtension`.
The upstream extension is the canonical source of `rawTriangleSource`,
`rawTriangleMap`, `higherDirectImageRawTrianglePullback`, and the restriction theorem.
The queue marks this item for retirement, and the upstream twin is intentionally kept
because its `rawTriangleMap` definition differs from the retired Sheaf history.

## Old

`lean/Sheaf/AlgebraicGeometry/HigherDirectImageRawTrianglePullback.lean` publicly
imports the upstream extension and declares no definitions or theorems.

`Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors` publicly imports the Sheaf shim.

## New

The empty Sheaf shim is withdrawn. `Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors`
publicly imports `WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullbackExtension`
directly, which supplies the same `rawTriangleSource` API it uses.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors | unclaimed | Required import retargeted to the canonical upstream extension; declarations and signatures unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas | unclaimed | Transitive import remains available through `RawModuleScalarSourceFactors`; no source change. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula | unclaimed | Transitive import remains available through `RawModuleScalarSourceFactors`; no source change. |

## Status

landed 20261021T002152-L-1495416 2026-10-21 (merge of deliver/U4/Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback)
