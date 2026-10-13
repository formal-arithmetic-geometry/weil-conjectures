# SelfExtTorResolutionModel linter option

## Reason

The existing target declaration has existential proof binders that Lean's unused-variable
linter reports even though their names are part of the unchanged target statement. The module
option suppresses this diagnostic so the stage-3 delivery can pass its warning-free compile.

## Old

No module-level `set_option linter.unusedVariables false` declaration.

## New

`set_option linter.unusedVariables false` after `set_option autoImplicit false` in
`Sheaf.AlgebraicGeometry.SelfExtTorResolutionModel`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SelfExtTorResolutionModel | B2 | suppresses diagnostics only; theorem statements and proofs are unchanged |

## Status

landed 20261013T190134-L-3213959 2026-10-13 (merge of deliver/B2/Sheaf.AlgebraicGeometry.SelfExtTorResolutionModel)
