# Sheaf.Paper.RingedSiteIdeal public imports

## Reason

The completed proofs do not use these three public imports, so they were removed from the module.
This changes only the transitive import interface; all declarations of the module remain unchanged.

## Old

```lean
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.Grp.FilteredColimits
```

## New

The three lines are removed. The module retains the public imports required by its declarations and
uses `import Mathlib.CategoryTheory.Sites.Subsheaf` privately for the proof.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FlatRingedIdealCompleteEquivalence | M1 | Its existing direct imports provide all declarations it uses; no source change is needed. |
| Sheaf.Paper.RestrictionLocalCompleteness | A2 | Its existing direct imports provide all declarations it uses; no source change is needed. |

## Status

landed 20261018T062845-L-668248 2026-10-18 (merge of deliver/P2/Sheaf.Paper.RingedSiteIdeal)
