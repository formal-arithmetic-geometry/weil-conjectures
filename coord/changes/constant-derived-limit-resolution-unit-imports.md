# Sheaf.Paper.ConstantDerivedLimitResolutionUnit public imports

## Reason

The proof only needs CompletedPullback and its existing public dependencies.
PbcQbarCompletedPullback belongs to the common-stage coefficient construction and is
unrelated to the projection-defined constant-tower unit. The remaining explicit
imports are redundant through CompletedPullback. Removing them reduces the import
closure while keeping every existing declaration and its signature unchanged.

The explicit natural-transformation witness is stored as private
`resolutionUnitMap`, with the proved application equation
`resolutionUnitMap_app`. The private definition is irreducible after this equation
is established, so the proof uses its API instead of repeatedly unfolding its
naturality data. This is the same constructed witness as the local record; no
public definition refers to the private helper.

## Old

```lean
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.CompletedPullback
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
```

## New

```lean
public import Sheaf.Paper.CompletedPullback
```

## Users

`python3 tools/downstream.py Sheaf.Paper.ConstantDerivedLimitResolutionUnit
--uses constantDerivedLimitResolutionUnit` reports zero downstream modules; its
only textual declaration use is in the item itself. A source search for importers
also found none. Pending DAG parents still require this node: the item is retained,
with exactly its original public statement. No target statement or definition changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantDerivedLimitResolutionUnit | U5 | Only the public import surface shrinks; the theorem signature and all mathematical definitions stay identical. |

## Status

landed 20261021T120742-L-3943013 2026-10-21 (merge of deliver/U5/Sheaf.Paper.ConstantDerivedLimitResolutionUnit)
