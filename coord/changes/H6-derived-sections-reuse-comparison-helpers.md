# AlgebraicGeometry.Etale derived-comparison helper interface

## Reason

Repair the return of head `4cf61d0d5f7`: the item re-proved three existing private
helpers. Their privacy prevented importing them. Expose `comp_fac` and `comp_unit_app`
in their existing unclaimed Sheaf module, and generalize its `derived_comp_eq` from
AddCommGrpCat to an arbitrary Grothendieck abelian coefficient category. The item
imports and uses these helpers instead of defining copies. No adopted source module
is edited. The original public `derivedLeray_comp` signature is unchanged.

## Old

```lean
private lemma derived_comp_eq {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    (rightDerivedLowerStarComp AddCommGrpCat.{u + 1} g f).hom =
      (Functor.rightDerivedFunctorCompIso'
        (lowerStar AddCommGrpCat.{u + 1} g) (lowerStar AddCommGrpCat.{u + 1} f)
        (lowerStarComp AddCommGrpCat.{u + 1} g f)).hom
```

```lean
private lemma comp_fac
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) :
    Functor.rightDerivedFunctorCompUnit F G ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedFunctorCompIso' F G e).hom =
    Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ)) DerivedCategory.Qh ≫
      H.rightDerivedFunctorUnit
```

```lean
private lemma comp_unit_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (T : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app T =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj T) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app T)
```

## New

```lean
lemma derived_comp_eq (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    (rightDerivedLowerStarComp A g f).hom =
      (Functor.rightDerivedFunctorCompIso'
        (lowerStar A g) (lowerStar A f)
        (lowerStarComp A g f)).hom
```

```lean
lemma comp_fac
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) :
    Functor.rightDerivedFunctorCompUnit F G ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedFunctorCompIso' F G e).hom =
    Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ)) DerivedCategory.Qh ≫
      H.rightDerivedFunctorUnit
```

```lean
lemma comp_unit_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (T : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app T =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj T) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app T)
```

The three proofs are retained, substituting the coefficient parameter in
`derived_comp_eq`. Its old abelian-valued caller now passes `AddCommGrpCat` explicitly.
Neither generic helper has a changed mathematical statement. The generalized compositor
is valid for all morphisms without boundedness, finiteness, or monoidal assumptions.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.DerivedLerayComp | unclaimed | Adapted: three helpers exposed; one generalized; its internal caller specialized explicitly. Public derivedLeray_comp unchanged. |
| Sheaf.TraceFormula.DerivedSectionsFinitePushforwardModules | H6 | Remove the three duplicate private helpers; import and apply the existing generalized API. |
| Sheaf.Paper.DerivedUnitLerayComp | unclaimed | Unchanged. Uses only the unchanged derivedLeray_comp. Textual comp_unit_app hit is Adjunction.comp_unit_app. |
| Sheaf.Paper.DerivedEtaleCohomologyPullbackLaws | unclaimed | Unchanged transitive consumer; no use of the changed helpers. |
| Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial | unclaimed | Unchanged transitive consumer; no use of the changed helpers. |

The table includes all three downstream modules and every --uses hit from
`tools/downstream.py`. Claims checked on 2026-10-24: only the item is held.
No target statement or definition changes meaning; all helper bodies are proofs.

## Status

landed 20261023T231430-L-3593856 2026-10-23 (merge of deliver/H6/Sheaf.TraceFormula.DerivedSectionsFinitePushforwardModules)
