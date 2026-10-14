# AlgebraicGeometry.tensorPullbackComposition_localized_homotopy_counit

## Reason

The module has no downstream import in the current library and is outside the target import closure. The current parent proof route uses the localized counit interface directly, so retaining this standalone helper module is unnecessary.

## Old

`Sheaf.AlgebraicGeometry.TensorPullbackCompositionHomotopyCounit` publicly imports `Sheaf.AlgebraicGeometry.DerivedCompositionCounitApex` and exports `AlgebraicGeometry.tensorPullbackComposition_localized_homotopy_counit`.

## New

The module is withdrawn and replaced by an empty module. No importer or target statement changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| none | none | No downstream module imports the withdrawn module. |

## Status

landed 20261014T164023-L-2227390 2026-10-14 (merge of deliver/E2/Sheaf.AlgebraicGeometry.TensorPullbackCompositionHomotopyCounit)
