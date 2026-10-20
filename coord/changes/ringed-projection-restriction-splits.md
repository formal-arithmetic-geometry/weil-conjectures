# Ringed projection restriction proof splits

## Reason
The original theorem proof had one large unresolved argument. Three named public
intermediate results make the global construction, local slice compatibility, and
local detection steps independently provable and let the main theorem combine them.

## Old
The module had only the theorem `AlgebraicGeometry.Scheme.ringedProjectionRestriction`
with proof `by sorry`.

## New
The module also declares `ringedProjectionRestriction_global`,
`ringedProjectionRestriction_local`, and `ringedProjectionRestriction_detection`.
The original theorem now combines these three results by ordinary existential
elimination and conjunction introduction.

## Users

| module | group holding it | effect |
|---|---|---|
| (none) | (none) | The new helper declarations have no downstream name users yet. |

## Status
landed 20261020T211834-L-3509315 2026-10-20 (merge of deliver/T9/Sheaf.Paper.RingedProjectionRestriction)
