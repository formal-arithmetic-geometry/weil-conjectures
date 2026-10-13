# DerivedPullbackKFlatCounitData linter option

## Reason

The theorem's existential binder is required by the unchanged target signature,
but Lean's unused-variable linter reports its name while elaborating the proof.
Suppressing that linter keeps delivery output clean without changing any
declaration or definition.

## Old

The module had no explicit `linter.unusedVariables` option.

## New

The module sets `set_option linter.unusedVariables false`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitData | D2 | proof-only linter setting |

## Status

landed 20261013T201742-L-3966550 2026-10-13 (merge of deliver/D2/Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitData)
