# CategoryTheory.ringedDerivedPushforward_linear

## Reason

Prune unused direct imports after proving the theorem. Its declaration and all
hypotheses and conclusions remain verbatim. Only the public import surface changes;
no definition, instance, theorem signature, or target meaning is changed.

## Old

```lean
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
public import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
```

## New

```lean
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
```

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.RingedDerivedPushforwardLinear
--uses ringedDerivedPushforward_linear` reports zero downstream modules. The single
textual declaration-name hit is the item itself. No consumer adaptation is required.
The DAG parents still need this theorem, whose statement is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.RingedDerivedPushforwardLinear | B9 | Proves its sole hole; minimal direct imports. |

## Status

landed 20261021T100827-L-4155872 2026-10-21 (merge of deliver/B9/Sheaf.CategoryTheory.RingedDerivedPushforwardLinear)
