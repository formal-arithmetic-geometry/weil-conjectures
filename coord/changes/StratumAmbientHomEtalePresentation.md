# AlgebraicGeometry.Etale.nonempty_stratumAmbientHomIso

## Reason

The expanded functor presentation caused kernel conversion to unfold the entire derived internal Hom, exceeding the 60-second file limit. The existing immersionLowerShriek and immersionUpperShriek are definitionally exactly those composites. Using their names preserves every binder, universe and mathematical conclusion, and the isolated etale proof compiled in 2.1 seconds. No definition is changed. The existing theorem immersionInternalHomIso supplies the isomorphism, with an extra evaluation equation that is discarded. Its import becomes public because the two existing names occur in the signature.

## Old

```lean
theorem Etale.nonempty_stratumAmbientHomIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty
      ((((Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor ⋙
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory).op.prod
          (𝟭 (Etale.DerivedCategoryModule A X))) ⋙
          Functor.uncurry.obj (Etale.derivedHom (ModuleCat.{u + 1} A) X) ≅
        ((𝟭 (Etale.DerivedCategoryModule A S)ᵒᵖ).prod
          ((Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
            (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.rightAdjoint)) ⋙
          Functor.uncurry.obj (Etale.derivedHom (ModuleCat.{u + 1} A) S) ⋙
            (Etale.lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).rightDerivedFunctor)
```

## New

```lean
theorem Etale.nonempty_stratumAmbientHomIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty
      ((Etale.immersionLowerShriek A i j).op.prod
          (𝟭 (Etale.DerivedCategoryModule A X)) ⋙
          Functor.uncurry.obj (Etale.derivedHom (ModuleCat.{u + 1} A) X) ≅
        (𝟭 (Etale.DerivedCategoryModule A S)ᵒᵖ).prod (Etale.immersionUpperShriek A i j) ⋙
          Functor.uncurry.obj (Etale.derivedHom (ModuleCat.{u + 1} A) S) ⋙
            (Etale.lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).rightDerivedFunctor)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.StratumAmbientHom | R4 | Definitionally identical presentation; both item holes closed; this etale statement has identical meaning. |

tools/downstream.py with --uses AlgebraicGeometry.Etale.nonempty_stratumAmbientHomIso lists only the defining module; no other source names this declaration. The current downstream query lists 479 modules in the import downstream closure. No downstream declaration changes meaning: both names unfold to the original functor composites. The eight direct importing modules were compiled unchanged against this delivery in an isolated sandbox. All passed; the slowest took 37.3 seconds. Nineteen redundant public imports were also removed; their required statement declarations remain publicly available through the retained imports. No consumer is adapted.

## Status

landed 20261019T231324-L-573996 2026-10-19 (merge of deliver/R4/Sheaf.Paper.StratumAmbientHom)
