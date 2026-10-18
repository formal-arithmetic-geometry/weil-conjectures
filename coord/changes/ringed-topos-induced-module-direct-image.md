# SheafOfModules.ringData_inducedModules

## Reason

The square transport theorem needs both an additive module direct image and its
scalar-action compatibility under the given adjunction. The existing
`geometric_module_construction` supplies concrete private operation constructions,
but its public conclusion does not include these two assertions. Add a theorem in
the same module to reuse those constructions, proving the extra assertions there.
The module is unclaimed in the repository claim snapshot. No existing declaration,
visibility, definition body, or target statement is changed.

## Old

The following new signature and import were absent. The original imports were:

```lean
public import Mathlib.Algebra.Category.Ring.Limits
public import Sheaf.CategoryTheory.RingedSiteModules
```

Every original declaration, including `geometric_module_construction`, remains
verbatim. In particular its hypotheses and conclusions are unchanged.

## New

```lean
public import Sheaf.CategoryTheory.RingedToposRingData
import Sheaf.CategoryTheory.AdjunctionRingOperations
```

```lean
theorem ringData_inducedModules
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (g : CategoryTheory.RingedToposMorphism.RingData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)) :
    Nonempty g.Modules
```

The fully proved theorem uses the existing `imageFunctor`, whose underlying sheaf
is the specified direct image, and its existing sectionwise module operations.
The functor is additive because a sum is pairing followed by addition. Counit
naturality, inverse product comparisons and the triangle identity prove the
required adjunction scalar-action equation.

## Users

`tools/downstream.py Sheaf.CategoryTheory.GeometricModuleConstruction --uses
SheafOfModules.ringData_inducedModules` reports zero existing uses. Its 723
transitive importers keep every original declaration unchanged. The only new user
is the item module. No existing consumer requires adaptation; no definition used
by a target changes its meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.GeometricModuleConstruction | unclaimed | Add one proved theorem and the imports above; all existing declarations unchanged. |
| Sheaf.CategoryTheory.RingedToposSquareTransport | F3 | Use the new theorem three times to supply the module fields. |

## Status

landed 20261018T062747-L-648550 2026-10-18 (merge of deliver/F3/Sheaf.CategoryTheory.RingedToposSquareTransport)
