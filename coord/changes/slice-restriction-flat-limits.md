# SheafOfModules.isFlat_over_preservesFiniteLimits

## Reason

The finite-limit part of the Stacks Tag 0E8J argument is isolated as a named public
intermediate theorem so the upper flatness theorem can be completed while the
extension-by-zero cone comparison remains an independent proof item. The item module
also adds proof-only imports and the new theorem is visible to downstream importers.

## Old

No declaration existed before this delivery.

## New

`SheafOfModules.isFlat_over_preservesFiniteLimits` states finite-limit preservation of
tensoring with the restricted flat module, for the canonical slice monoidal structure
(the explicit `hm` equality pins the supplied structure to that canonical one).

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat | Q3 | Uses the theorem to prove the finite-limit half of `isFlat_over`. |

## Status

landed 20261016T054838-L-158061 2026-10-16 (merge of deliver/Q3/Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat)
