# Linter options in GlobalTensorPullbackMonoidalNormalization

## Reason
The proof file contains intentionally long mathematical signatures and local instance bindings that trigger style warnings under the delivery compiler. The options only suppress diagnostics and do not alter declarations or proofs.

## Old
No local linter options after `set_option autoImplicit false`.

## New
`set_option linter.style.longLine false`
`set_option linter.style.haveILetI false`
`set_option linter.unusedVariables false`
`set_option linter.unusedSectionVars false`

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization | D4 | suppresses local linter warnings |

## Status
landed 20261013T190137-L-3215064 2026-10-13 (merge of deliver/D4/Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization)
