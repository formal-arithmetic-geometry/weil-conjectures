# AlgebraicGeometry.Etale.nonempty_stratumAmbientHomIso

## Reason

Reuse the already proved evaluation-normalized immersion isomorphism. Expanding the
DerivedCategoryModule abbreviation in the statement and retaining the existing named
immersion functors avoids expensive kernel conversion through the expanded functors.
The formula, universes, binder order and hypotheses are unchanged mathematically.
This is not a correction of the mathematical statement or a change to any definition.

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
    Nonempty ((immersionLowerShriek A i j).op.prod
        (𝟭 (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))) ⋙
        Functor.uncurry.obj (derivedHom (ModuleCat.{u + 1} A) X) ≅
      (𝟭 (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)))ᵒᵖ).prod
        (immersionUpperShriek A i j) ⋙
        Functor.uncurry.obj (derivedHom (ModuleCat.{u + 1} A) S) ⋙
          R((i ≫ j)_*[ModuleCat.{u + 1} A]))
```

The named immersionLowerShriek is the abbreviation Ri_* followed by j_!;
immersionUpperShriek is defined as j^* followed by the right adjoint of Ri_*.
DerivedCategoryModule is the displayed DerivedCategory abbreviation. Thus this only
changes spelling. No target statement or data construction changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.StratumAmbientHom | J2 | Declaration itself; same mathematical formula |

The required downstream.py --uses scan found no external use of this declaration
among 351 downstream modules. A repository rg scan likewise finds only its declaration.
All original public imports are retained to preserve reexports for importers; the one
new public import supplies the two named functors now appearing in the statement.
No consumer is adapted and no target semantic review is reopened.

## Status

landed 20261020T221219-L-4158566 2026-10-20 (merge of deliver/J2/Sheaf.Paper.StratumAmbientHom)
