# Canonical smooth composition coordinates

## Reason

The separate composition equation needs the three existing comparison definitions without importing the theorem that uses the equation. Move their unchanged declarations to the new module, and publicly import that module from the item.

## Old

```lean
noncomputable def smoothCompactSupportCompIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)] :
    Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (f ≫ g) ≅
      Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g :=
  let c := HasCompactification.compactification g
  let b := (HasCompactification.compactification (f ≫ g)).ofComp c
  (Etale.rightDerivedLowerShriekIso Λ (c.comp b)).symm ≪≫
    (Etale.rightDerivedLowerShriekOfCompactificationCompIso Λ c b).symm ≪≫
    Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekIso Λ b.restrict) _ ≪≫
    Functor.isoWhiskerLeft _ (Etale.rightDerivedLowerShriekIso Λ c)

noncomputable def smoothExceptionalCompIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)] :
    Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) (f ≫ g) ≅
      Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) g ⋙
        Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f :=
  Adjunction.rightAdjointUniq
    ((Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (f ≫ g)).ofNatIsoLeft
      (smoothCompactSupportCompIso Λ f g))
    ((Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).comp
      (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) g))

noncomputable def smoothDualizingCompMap
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)] :
    ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) f)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj
          (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) g)) ⟶
      Etale.dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g) :=
  Etale.dualizingComplexTensorMap Λ f (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) g) ≫
    (smoothExceptionalCompIso Λ f g).inv.app (𝟙_ _)
```

## New

The three declarations above are verbatim in `Sheaf.Paper.SmoothTensorCompositionEquation`; their original module publicly imports it. No body or signature changes. The new module also states the separate unit-specialized composition equation.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | V8 | public import preserves all existing comparison declarations |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed; no edit | existing import continues to expose the same declarations |

## Status

landed 20261025T164617-L-1041161 2026-10-25 (merge of deliver/V8/Sheaf.Paper.CohomologicalSmoothnessTheorem)
