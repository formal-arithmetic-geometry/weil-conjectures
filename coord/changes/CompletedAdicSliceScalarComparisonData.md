# CompletedAdicSliceScalarComparisonData

## Reason
The slice scalar-extension definitions moved from the item module into a public data module so the lower statements of the derived proof can be stated against the universal witness.

## Old
The item module `Sheaf.Paper.CompletedAdicSliceScalarComparison` declared `completedAdicSliceChangeData` and `completedAdicSliceDerivedChange` (recorded by lem-weil-pbc-completed-adic-slice-scalar-comparison).

## New
`completedAdicSliceChangeData` and `completedAdicSliceDerivedChange` are moved verbatim (signatures and bodies unchanged) to `Sheaf.Paper.CompletedAdicSliceScalarComparisonData`, together with the new `completedAdicSliceChange` and the instance `completedAdicSliceChange_additive`. The three definitions are recorded by def-weil-pbc-completed-adic-slice-scalar-extension, the instance by def-weil-pbc-completed-adic-slice-scalar-extension-additive. The item module publicly imports the data module, so every name stays visible to its importers.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedAdicSliceScalarComparison | U1 | imports the data module; proves `completedAdic_slice_scalarComparison` from its lower statements |
| Sheaf.Paper.FiniteQuotientModelResidueComparison | unclaimed (written by K6) | uses `completedAdicSliceDerivedChange` through the item's public import; unchanged, compiles |

## Status

landed 20261027T180829-L-3906877 2026-10-27 (merge of deliver/U1/Sheaf.Paper.CompletedAdicSliceScalarComparison)
