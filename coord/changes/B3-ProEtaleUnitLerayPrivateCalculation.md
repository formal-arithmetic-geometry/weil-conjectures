# AlgebraicGeometry.Scheme.proEtale_unit_leray_chain_formula

## Reason
The mechanical stage-3 interface checker requests a change record because this delivery
adds a scoped generic `variable` command in `section UnitLerayCalculation`. Those variables
parameterize three fully proved private helpers only. The section ends before the existing
public theorem. No existing declaration signature, visibility, definition, instance, public
import, or file-level option changes. The generic calculation prevents reduction of the
intrinsic module realization during the categorical proof.

## Old
The public theorem signature, verbatim:

```lean
theorem proEtale_unit_leray_chain_formula
    {X Y : Scheme.{u}} (h : X ⟶ Y)
    (I : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ)
    (J : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    [I.IsKInjective] [J.IsKInjective]
    (j : ((proEtaleConstantRingPullback A h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J) :
    ((proEtaleUnitLeraySections A Y).rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (proEtaleUnitLeraySectionUnit A h) (.up ℤ)).app I ≫
            ((proEtaleUnitLeraySections A X).mapHomologicalComplex (.up ℤ)).map j) ≫
      ((proEtaleUnitLeraySections A X).rightDerivedFunctorObjQIso J).inv =
    (proEtaleUnitLeraySections A Y).rightDerivedFunctor.map
        ((proEtaleConstantRingAdjunction A h).mapDerivedCategoryRightDerivedAdjunction.unit.app
          (DerivedCategory.Q.obj I)) ≫
      (proEtaleUnitLerayIso A h).hom.app
        ((proEtaleConstantRingDerivedPullback A h).obj (DerivedCategory.Q.obj I)) ≫
      (proEtaleUnitLeraySections A X).rightDerivedFunctor.map
        ((proEtaleConstantRingPullback A h).mapDerivedCategoryFactors.hom.app I ≫
          DerivedCategory.Q.map j)
```

## New
The public theorem signature is identical:

```lean
theorem proEtale_unit_leray_chain_formula
    {X Y : Scheme.{u}} (h : X ⟶ Y)
    (I : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ)
    (J : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    [I.IsKInjective] [J.IsKInjective]
    (j : ((proEtaleConstantRingPullback A h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J) :
    ((proEtaleUnitLeraySections A Y).rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (proEtaleUnitLeraySectionUnit A h) (.up ℤ)).app I ≫
            ((proEtaleUnitLeraySections A X).mapHomologicalComplex (.up ℤ)).map j) ≫
      ((proEtaleUnitLeraySections A X).rightDerivedFunctorObjQIso J).inv =
    (proEtaleUnitLeraySections A Y).rightDerivedFunctor.map
        ((proEtaleConstantRingAdjunction A h).mapDerivedCategoryRightDerivedAdjunction.unit.app
          (DerivedCategory.Q.obj I)) ≫
      (proEtaleUnitLerayIso A h).hom.app
        ((proEtaleConstantRingDerivedPullback A h).obj (DerivedCategory.Q.obj I)) ≫
      (proEtaleUnitLeraySections A X).rightDerivedFunctor.map
        ((proEtaleConstantRingPullback A h).mapDerivedCategoryFactors.hom.app I ≫
          DerivedCategory.Q.map j)
```

The following scoped commands are added before the private proof helpers:

```lean
section UnitLerayCalculation

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  {L : D ⥤ C} {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
  [L.Additive] [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [F.PreservesKInjectiveComplexes] (a : L ⊣ F) (e : F ⋙ G ≅ H)
```

The section is closed before the original public theorem. The new helpers are private
proved theorems; none occurs in a public signature or definition body. The existing
public theorem changes from `sorry` to a complete proof. The five removed imports are
private proof imports and provide no declarations required by the retained proof.

## Users
`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula --uses
proEtale_unit_leray_chain_formula proEtaleUnitLeraySections proEtaleUnitLerayIso
proEtaleUnitLeraySectionUnit` reports zero downstream modules; its textual name hits
are confined to the item itself. There are no consumers to adapt. The current unfinished
DAG parents retain this statement, with its unchanged Lean attachment.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula | B3 | One original hole proved; private generic helpers; unchanged public interface. |

## Status
landed 20261020T230716-L-603970 2026-10-20 (merge of deliver/B3/Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula)
