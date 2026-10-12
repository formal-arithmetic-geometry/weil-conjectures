# moduleExtensionByZero_unit_isIso

## Reason
The proof uses local Mono and Epi instances and disables a proposition-instance style linter warning for this theorem.

## Old
The theorem had a `sorry` proof with no local instances.

## New
The theorem proves the result from `moduleExtensionByZero_unit_mono`, `moduleExtensionByZero_unit_epi`, and `isIso_of_mono_of_epi`, with the local linter option `linter.style.haveILetI` disabled.

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkInside | J3 | proof remains compatible |

## Status
landed 20261012T194137-L-463981 2026-10-12 (merge of deliver/S1/Sheaf.Algebra.Homology.ModuleExtensionByZeroUnitIsIso)
