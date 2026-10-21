# AlgebraicGeometry.Scheme.localReductionComplexCounit

## Reason

The direct four-factor cochain expression repeatedly expands the coefficient-module
structures when the derived evaluation comparison is checked. Use the existing public
`CategoryTheory.derivedCochainCounit` constructor to share that expression. The proved
private generic lemma `complexCounit_formula` identifies this constructor with the
old four-factor formula, for every additive functor and derived counit.
The declaration's type and the normalized morphism are unchanged.

## Old

```lean
def localReductionComplexCounit (P : CochainComplex (pbcModules Y B) ℤ) :
    (localReductionDerived Y B R π).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((localReductionModuleTower Y B R π).mapHomologicalComplex (.up ℤ)).obj P) :=
  (localReductionDerived Y B R π).map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (localReductionCounit Y B R π).app ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map
      (((localReductionModuleTower Y B R π).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso (pbcTowers Y B)).hom.app
      (((localReductionModuleTower Y B R π).mapHomologicalComplex (.up ℤ)).obj P)
```

## New

```lean
def localReductionComplexCounit (P : CochainComplex (pbcModules Y B) ℤ) :
    (localReductionDerived Y B R π).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((localReductionModuleTower Y B R π).mapHomologicalComplex (.up ℤ)).obj P) :=
  (CategoryTheory.derivedCochainCounit (localReductionModuleTower Y B R π)
    (localReductionDerived Y B R π) (localReductionCounit Y B R π)).app P
```

## Users

`tools/downstream.py Sheaf.Paper.ReconstructionUniformTower --uses
localReductionComplexCounit` found no downstream modules. The module itself uses the
same morphism in its evaluation comparison. No other module requires adaptation.
The existing reconstruction node and its seven geometric steps are retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ReconstructionUniformTower | W4 | Reuse the public cochain constructor and prove the original evaluation statement. |

## Status

landed 20261021T011053-L-2034806 2026-10-21 (merge of deliver/W4/Sheaf.Paper.ReconstructionUniformTower)
