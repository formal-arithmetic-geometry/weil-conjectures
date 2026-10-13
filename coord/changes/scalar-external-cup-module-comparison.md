# Scalar external cup module comparison

## Reason

The delivery adds proof imports and intermediate theorem modules required by the target proof.

## Old

The target module had no proof imports for these comparisons.

## New

The target module imports `ScalarCupModuleCupCompatibility` and `ScalarModuleCohomologyPullbackComparison`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison | U2 | imports added for proof |

## Status

landed 20261013T172659-L-2101278 2026-10-13 (merge of deliver/U2/Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison)
