# Scalar external cup module comparison

## Reason

Repair the landed global import collision while preserving all three theorem
statements and the external comparison proof.

## Old

`ScalarExternalCupModuleComparison` directly imported
`Sheaf.Paper.ModuleCohomologyCupProduct` while also importing
`ScalarCupModuleCupCompatibility`, which publicly imports that same module. In the
combined global environment this re-entered `ModuleCupKInjectiveTarget` after
`GlobalTensorPullbackMonoidalNormalization` and produced a duplicate exposed local
instance declaration.

## New

The direct cup-product import was removed from `ScalarExternalCupModuleComparison`.
The module now publicly imports `ScalarCupModuleCupCompatibility`, so the canonical
`IsModuleCupProduct` declaration remains available through one import path. No
statement, definition, or proof body was changed.

## Users

| module | effect |
| --- | --- |
| Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison | repaired global import |

## Status

landed 20261014T001712-L-2547236 2026-10-14 (merge of deliver/XRa2c5451bd4aff80a/Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison)
