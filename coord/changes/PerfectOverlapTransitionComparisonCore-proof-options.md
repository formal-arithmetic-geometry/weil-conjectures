# PerfectOverlapTransitionComparisonCore proof options
## Reason
The proof needs a local linter suppression and an elevated heartbeat limit for the deeply nested dependent comparison expression.
## Old
No local linter suppression or final theorem heartbeat override.
## New
`set_option linter.unusedVariables false` and `set_option maxHeartbeats 1600000 in` on the final theorem.
## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore | S4 | proof elaboration only |
## Status
landed 20261014T001734-L-2555518 2026-10-14 (merge of deliver/S4/Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore)
