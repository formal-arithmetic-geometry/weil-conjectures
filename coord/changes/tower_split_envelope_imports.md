# tower_split_envelope imports

## Reason

OfSequence is used only to construct the private proof witnesses and is therefore
an ordinary import. Products is already publicly imported transitively through
Abelian.FunctorCategory and its Abelian.Basic dependency, so its direct import is
redundant. No declaration signature, definition used by a target, or theorem
meaning changes.

## Old

```lean
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Functor.OfSequence
```

## New

```lean
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Functor.OfSequence
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.TowerSplitComplexReplacement | unclaimed in the local claim snapshot | Sole direct importer, imports this module privately; uses tower_split_envelope unchanged, no OfSequence declarations. Compiled unchanged against the revised module. No adaptation needed. |

`tools/downstream.py --direct` and source inspection find this single direct
importer. Its import of TowerSplitEnvelope is ordinary, so the lost public export
of OfSequence was already not exported to its own downstream importers. Products
remains publicly available through Abelian.FunctorCategory. No downstream
statement changes meaning and no target requires re-review. No adapted modules.

## Status

landed 20261013T082414-L-1648425 2026-10-13 (merge of deliver/T1/Sheaf.CategoryTheory.TowerSplitEnvelope)
