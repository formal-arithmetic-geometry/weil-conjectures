# ConstantDerivedLimitResolutionUnit public imports

## Reason

The theorem is proved using the existing ordinary and derived constant/limit adjunctions.
Its statement only needs CompletedPullback and that module's public dependencies. Remove
unrelated coefficient extensions and redundant direct public imports. The proof explicitly
imports the derived-adjunction API privately. All declaration signatures stay unchanged.

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
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
```

## Users

`tools/downstream.py Sheaf.Paper.ConstantDerivedLimitResolutionUnit --uses
constantDerivedLimitResolutionUnit` reports zero downstream modules. The only textual
use of the theorem name is its own declaration. No consumer adaptation is required.
The DAG parents still use this node; its declaration, attachment and statement stay.
No target statement or definition changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ConstantDerivedLimitResolutionUnit | Z7 | One proof filled; redundant imports removed. |

## Status

landed 20261021T151217-L-1185116 2026-10-21 (merge of deliver/Z7/Sheaf.Paper.ConstantDerivedLimitResolutionUnit)
