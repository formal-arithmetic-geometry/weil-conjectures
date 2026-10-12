# linter option

## Reason
The target's existential binder is intentionally named `hn` by the fixed interface, which triggers an unused-variable warning. The local option suppresses only this cosmetic warning.

## Old
No local `linter.unusedVariables` option.

## New
`set_option linter.unusedVariables false`

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.FieldTheory.CrossedProductRealization | W2 | proof-only local option |

## Status
landed 20261012T150959-L-2232820 2026-10-12 (merge of deliver/W2/Sheaf.FieldTheory.CrossedProductRealization)
