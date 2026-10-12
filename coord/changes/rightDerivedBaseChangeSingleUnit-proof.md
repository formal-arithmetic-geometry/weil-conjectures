# rightDerivedBaseChange_single_unit proof interface

## Reason
The stage-3 proof adds local comparison lemmas and transparency options in the
module. The delivery tool classifies the module commands as an interface change;
recording this lets the independent reader verify that no public declaration
signature or target statement changed.

## Old
The unchanged public signature was:

```lean
theorem rightDerivedBaseChange_single_unit (e : G ⋙ γ ⟶ β ⋙ G') (Y : B) :
    γ.mapDerivedCategoryPlus.map (G.rightDerivedPlusSingleUnit Y) ≫
      (rightDerivedFunctorPlusBaseChange e).app
        ((DerivedCategory.Plus.singleFunctor B 0).obj Y) ≫
      G'.rightDerivedFunctorPlus.map
        ((β.mapDerivedCategoryPlusSingleFunctor 0).hom.app Y) =
    (γ.mapDerivedCategoryPlusSingleFunctor 0).hom.app (G.obj Y) ≫
      (DerivedCategory.Plus.singleFunctor C' 0).map (e.app Y) ≫
      G'.rightDerivedPlusSingleUnit (β.obj Y)
```

Its proof was `by sorry`; there were no local helper lemmas.

## New
The public signature remains, verbatim:

```lean
theorem rightDerivedBaseChange_single_unit (e : G ⋙ γ ⟶ β ⋙ G') (Y : B) :
    γ.mapDerivedCategoryPlus.map (G.rightDerivedPlusSingleUnit Y) ≫
      (rightDerivedFunctorPlusBaseChange e).app
        ((DerivedCategory.Plus.singleFunctor B 0).obj Y) ≫
      G'.rightDerivedFunctorPlus.map
        ((β.mapDerivedCategoryPlusSingleFunctor 0).hom.app Y) =
    (γ.mapDerivedCategoryPlusSingleFunctor 0).hom.app (G.obj Y) ≫
      (DerivedCategory.Plus.singleFunctor C' 0).map (e.app Y) ≫
      G'.rightDerivedPlusSingleUnit (β.obj Y)
```

The public theorem has a complete proof. Four helper theorems and two private
isomorphism definitions are added; all are private and occur only in the proof.
No public declaration, definition, notation, variable, or import is changed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.RightDerivedBaseChangeSingleUnitHomology | K1 | imports the public theorem's module; its statement is unchanged |

## Status
landed 20261012T112843-L-769240 2026-10-12 (merge of deliver/K1/Sheaf.CategoryTheory.RightDerivedBaseChangeSingleUnit)
