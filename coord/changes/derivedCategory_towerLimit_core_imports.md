# derivedCategory_towerLimit_core imports

## Reason

The parent theorem needs DerivedCategory.Basic for its signature, not HomologySequence.
HomologicalComplexLimits is used only in the cone helper's proof, where it is imported
privately. Remove these unused public exports from the parent.

## Old

```
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
```

## New

```
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
```

The cone helper has the proof-only import
`import Mathlib.Algebra.Homology.HomologicalComplexLimits`.

## Users

`tools/downstream.py Sheaf.CategoryTheory.Triangulated.DerivedLimitTower --uses
CategoryTheory.derivedCategory_towerLimit_core` found the item itself and the one
direct importer below as users. That direct importer already publicly imports both
removed modules itself, so its re-exported environment is unchanged. Consequently
all its downstream modules retain the same imports as well. No target meaning changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Triangulated.DerivedLimitTower | K2 | Proof and imports change; signature unchanged. |
| Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence | unclaimed | Already imports HomologySequence and HomologicalComplexLimits; no adaptation. |

## Status

landed 20261012T184314-L-4008534 2026-10-12 (merge of deliver/K2/Sheaf.CategoryTheory.Triangulated.DerivedLimitTower)
