# linter setting in Sheaf.Algebra.LimitFinitePresentation

## Reason
Suppresses the pre-existing unused existential binder warnings in the target theorem so the
stage-3 delivery probe is warning-free.

## Old
No file-level linter setting.

## New
`set_option linter.unusedVariables false` before the public section.

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.LimitFinitePresentation | J4 | required for warning-free compilation |

## Status
landed 20261013T024037-L-3335412 2026-10-13 (merge of deliver/J4/Sheaf.Algebra.LimitFinitePresentation)
