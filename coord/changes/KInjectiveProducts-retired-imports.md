# KInjectiveProducts retired imports

## Reason

Upstream review #1428's duplicate theorem and all three callers were already
repaired by U2 in landing 20261014T035546-L-888417. The unused compatibility
module has no declarations and no importers. Remove its remaining public
imports, retaining the module file. No theorem, definition or target changes.

## Old

```lean
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
```

## New

No imports. The compatibility module remains a module with no declarations.

## Users

There are no direct or transitive importers. The downstream.py result is empty.
No module needs adaptation and no target's interpretation changes.

| module | group holding it | effect |
| --- | --- | --- |

## Status

landed 20261014T090919-L-366279 2026-10-14 (merge of deliver/K4/Sheaf.Algebra.Homology.KInjectiveProducts)
