# AlgebraicGeometry.Proj.twist_finiteLocal_representatives
## Reason
The original declaration emits a linter warning because its existential binder `hspan`
is intentionally present in the public target interface but does not occur in the
continuation type. The proof-only module option suppresses this warning.
## Old
The declaration had no module-level linter option.
## New
The module sets `set_option linter.unusedVariables false` before the unchanged declaration.
## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalizationData | unclaimed | Interface and meaning unchanged; no adaptation |
## Status
landed 20261012T194113-L-455918 2026-10-12 (merge of deliver/G3/Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalRepresentatives)
