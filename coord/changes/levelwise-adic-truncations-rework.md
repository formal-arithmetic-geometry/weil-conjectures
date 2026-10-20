# Sheaf.Paper.LevelwiseAdicTruncations

## Reason

The module was quarantined during the 2026-10-20 upstream rework because its
`pbc_levelwise_truncations_constructible` signature referenced the removed
`LocallyClosedStratification` identifier. Restoring it with the adopted
`AlgebraicGeometry.Scheme.Stratification` type is required for the module and its
preserved declarations to compile.

## Old

The quarantined module was absent from `lean/`; its archived source used
`∃ S : LocallyClosedStratification T` in the local-model hypothesis.

## New

The restored module uses `∃ S : Stratification T`, resolving to
`AlgebraicGeometry.Scheme.Stratification`, whose fields `domain`, `immersion`, and
`range_immersion` are the fields used by the hypothesis. Existing declarations and
proof signatures are otherwise unchanged. The module also retains its local elaboration
attributes and private helper from the previous accepted repair.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.AdicTorFlatCohomology` | quarantined/unclaimed | Imports the restored module; no signature adaptation is needed. |
| `Sheaf.Paper.IntegralCanonicalTruncations` | quarantined/unclaimed | Imports the restored module; no signature adaptation is needed. |
| `Sheaf.Paper.PbcUniformLocalModelCohomology` | quarantined/unclaimed | Imports and uses preserved theorem declarations; no signature adaptation is needed. |
| `Sheaf.Paper.PbcUniformReductionCriterion` | quarantined/unclaimed | Imports the restored module; no signature adaptation is needed. |

## Status

landed 20261020T230702-L-600251 2026-10-20 (merge of deliver/A2/Sheaf.Paper.LevelwiseAdicTruncations)
