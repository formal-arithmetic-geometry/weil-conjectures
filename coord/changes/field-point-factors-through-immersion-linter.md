# linter.style.haveILetI in FieldPointFactorsThroughImmersion

## Reason
The proof requires local typeclass instances with `letI`; Mathlib's style linter reports these despite the instances being necessary.

## Old
No file-level setting for `linter.style.haveILetI`.

## New
`set_option linter.style.haveILetI false` in `FieldPointFactorsThroughImmersion.lean`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FieldPointFactorsThroughImmersion | V2 | suppresses style warnings in this proof |

## Status
landed 20261012T060758-L-2918037 2026-10-12 (merge of deliver/V2/Sheaf.AlgebraicGeometry.FieldPointFactorsThroughImmersion)
