# linter option in ZeroDimensionalNoetherianFiniteDiscrete

## Reason
The proof necessarily introduces proposition-valued local instances with `letI`; Mathlib's style linter emits warnings that delivery tooling treats as failures. The local option only suppresses this stylistic warning.

## Old
No local linter option.

## New
`set_option linter.style.haveILetI false` in the module section.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete | F2 | proof-only linter configuration |

## Status
landed 20261012T113946-L-820369 2026-10-12 (merge of deliver/F2/Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete)
