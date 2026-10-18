# AdicLimitFiniteModules imports and scoped declarations
## Reason
The proofs use pointwise set operations and topology names internally. The module now opens these scopes.
## Old
The module did not open `Pointwise` or `Topology`.
## New
The module opens `Pointwise` and `Topology` in its public section.
## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.NumberTheory.Padics.AdicLimitFiniteModules | H3 | proof elaboration only |
## Status
landed 20261018T062805-L-654281 2026-10-18 (merge of deliver/H3/Sheaf.NumberTheory.Padics.AdicLimitFiniteModules)
