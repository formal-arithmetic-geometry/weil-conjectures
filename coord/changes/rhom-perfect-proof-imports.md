# rhom-perfect-proof-imports
## Reason
The proof requires additional proof-only imports and a new public helper theorem.
## Old
The item imported only `DerivedPullbackTensorQCoh` and `PerfectRHomTensorComparison`.
## New
The item also imports `DerivedTensorQCohClosure` and `PerfectImpliesQCoh`; the latter declares `schemeDerivedQCohProperty_of_isPerfect`.
## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart | X2 | proof imports and helper theorem |
## Status
landed 20261013T002359-L-2377297 2026-10-13 (merge of deliver/X2/Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart)
