# derived_exists_perfect_well_generators

## Reason
Suppress linter warnings for local proof instances; theorem signature and meaning are unchanged.

## Old
The original proof used local `letI` declarations and emitted style warnings.

## New
The same local instances are compiled under `set_option linter.style.haveILetI false`.

## Users
| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.GrothendieckDerivedPerfectWellGenerators | B4 | proof-only linter setting |

## Status
landed 20261018T002706-L-2157785 2026-10-18 (merge of deliver/B4/Sheaf.CategoryTheory.GrothendieckDerivedPerfectWellGenerators)
