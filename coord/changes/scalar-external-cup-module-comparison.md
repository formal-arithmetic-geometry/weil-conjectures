# Scalar external cup module comparison

## Reason

The target proof requires two proof-only comparison theorem imports. The current
branch omitted the target and these prerequisite modules after an earlier batch
revert, so this delivery restores them together.

## Old

The target module and the two prerequisite comparison modules were absent from the
current branch.

## New

The target imports `ScalarCupModuleCupCompatibility` and
`ScalarModuleCohomologyPullbackComparison`; the target theorem is proved by
composing those comparisons.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison | K4 | restored target and proof imports |

## Status

landed 20261013T190143-L-3217210 2026-10-13 (merge of deliver/K4/Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison)
