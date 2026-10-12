# AlgebraicGeometry.Etale.exists_resolutionSection_canonical_comparison

## Reason
The private represented-resolution helper is polymorphic in the category and additive-group universes, so Lean requires universe parameters `v` and `w` in addition to the module's existing `u`.

## Old
```lean
universe u
```

## New
```lean
universe u v w
```
The two added imports are non-public proof imports. Existing public signatures and definitions are unchanged; the transparency option is scoped to the private helper.

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleResolutionSectionHomology | unclaimed | Existing signatures and visibility unchanged; no adaptation needed. |


## Status

landed 20261012T223418-L-1641583 2026-10-12 (merge of deliver/T2/Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalData)
