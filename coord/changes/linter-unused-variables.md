# linter-unused-variables option

## Reason
The existing target theorem has an existential witness `q` which is intentionally not referenced by the proposition following it. The Lean linter emits a warning for this required unchanged signature; disabling this warning is necessary for the delivery compiler's warning-free check.

## Old
The target module used the default `linter.unusedVariables` setting.

## New
The target module sets `set_option linter.unusedVariables false` before the unchanged theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineAlternatingCechExchangeResolution | R3 | warning suppression only; theorem signature and visibility are unchanged |

## Status
landed 20261013T015611-L-3026025 2026-10-13 (merge of deliver/R3/Sheaf.AlgebraicGeometry.AffineAlternatingCechExchangeResolution)
