# AlgebraicGeometry.ProEtale.DiagonalTrace.completedSupportedUnit

## Reason

Move the existing construction to its own module so that the finite strict-class
calculation can use it without importing its parent theorem. The definition's
signature and body are unchanged; the item publicly imports the new module and
therefore preserves its existing public declaration.

## Old

```lean
def completedSupportedUnit (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    SheafOfModules.unit.{u, u + 1, u + 1}
      (Scheme.purTwistRing (diagonalSurface Y)
        (Scheme.purTwistZlCompletion (diagonalSurface Y) l)) ⟶
      diagonalCompletedSource l Y := by
  let unitToPushforwardRestrictedUnit
      {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
      {J : GrothendieckTopology C} {K : GrothendieckTopology D}
      {F : C ⥤ D} [F.IsContinuous J K]
      {R : Sheaf J RingCat.{u + 1}} {S T : Sheaf K RingCat.{u + 1}}
      (α : R ⟶ (F.sheafPushforwardContinuous RingCat J K).obj S) (φ : S ⟶ T) :
      SheafOfModules.unit.{u, u + 1, u + 1} R ⟶
        (SheafOfModules.pushforward.{u + 1} α).obj
          ((SheafOfModules.restrictScalars φ).obj (SheafOfModules.unit T)) := by
    exact SheafOfModules.unitToPushforwardObjUnit
      (α ≫ (F.sheafPushforwardContinuous RingCat J K).map φ)
  unfold diagonalCompletedSource Scheme.proEtaleRingedDirectImage
  let i := diagonalImmersion Y
  let R := Scheme.purTwistZlCompletion (diagonalSurface Y) l
  exact unitToPushforwardRestrictedUnit
    (C := (diagonalSurface Y).ProEt) (D := (ProjectiveLine Y).ProEt)
    (J := Scheme.ProEt.topology (diagonalSurface Y))
    (K := Scheme.ProEt.topology (ProjectiveLine Y))
    (F := Scheme.proEtaleBaseChange i)
    (R := Scheme.purTwistRing (diagonalSurface Y) R)
    (S := Scheme.proEtaleModuleCoefficients
      ((Scheme.proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R))
    (T := Scheme.purTwistRing (ProjectiveLine Y)
      (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))
    ⟨Functor.whiskerRight
      ((Scheme.proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    ((sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (diagonalCompletedCoefficientMap l i))
```

Previously declared in `Sheaf.Paper.DiagonalTraceFiniteCartierChern`.

## New

```lean
def completedSupportedUnit (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    SheafOfModules.unit.{u, u + 1, u + 1}
      (Scheme.purTwistRing (diagonalSurface Y)
        (Scheme.purTwistZlCompletion (diagonalSurface Y) l)) ⟶
      diagonalCompletedSource l Y := by
  let unitToPushforwardRestrictedUnit
      {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
      {J : GrothendieckTopology C} {K : GrothendieckTopology D}
      {F : C ⥤ D} [F.IsContinuous J K]
      {R : Sheaf J RingCat.{u + 1}} {S T : Sheaf K RingCat.{u + 1}}
      (α : R ⟶ (F.sheafPushforwardContinuous RingCat J K).obj S) (φ : S ⟶ T) :
      SheafOfModules.unit.{u, u + 1, u + 1} R ⟶
        (SheafOfModules.pushforward.{u + 1} α).obj
          ((SheafOfModules.restrictScalars φ).obj (SheafOfModules.unit T)) := by
    exact SheafOfModules.unitToPushforwardObjUnit
      (α ≫ (F.sheafPushforwardContinuous RingCat J K).map φ)
  unfold diagonalCompletedSource Scheme.proEtaleRingedDirectImage
  let i := diagonalImmersion Y
  let R := Scheme.purTwistZlCompletion (diagonalSurface Y) l
  exact unitToPushforwardRestrictedUnit
    (C := (diagonalSurface Y).ProEt) (D := (ProjectiveLine Y).ProEt)
    (J := Scheme.ProEt.topology (diagonalSurface Y))
    (K := Scheme.ProEt.topology (ProjectiveLine Y))
    (F := Scheme.proEtaleBaseChange i)
    (R := Scheme.purTwistRing (diagonalSurface Y) R)
    (S := Scheme.proEtaleModuleCoefficients
      ((Scheme.proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R))
    (T := Scheme.purTwistRing (ProjectiveLine Y)
      (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))
    ⟨Functor.whiskerRight
      ((Scheme.proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    ((sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (diagonalCompletedCoefficientMap l i))
```

Declared in `Sheaf.Paper.DiagonalTraceCompletedSupportedUnit` and publicly
re-exported by the original module.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DiagonalTraceFiniteCartierChern | D4 | Same declaration, signature and body; available through the original public import. |
| Sheaf.Paper.DiagonalTraceFiniteAdjunctionFactorization | unclaimed in the current claim records | Same declaration, signature and body; available through the original public import. |
| Sheaf.Paper.DiagonalTraceFiniteAdjunctionGeometric | C8 | Same declaration, signature and body; available through the original public import. |
| Sheaf.Paper.DiagonalTraceFiniteAdjunctionSupported | C9 | Same declaration, signature and body; available through the original public import. |
| Sheaf.Paper.DiagonalTraceFiniteAdjunctionSupportedAdditive | unclaimed in the current claim records | Same declaration, signature and body; available through the original public import (compiled OK against the delivery, packet §3b). |
| Sheaf.Paper.DiagonalTraceFiniteCanonicalSupported | unclaimed in the current claim records | Same declaration, signature and body; available through the original public import (compiled OK against the delivery, packet §3b). |
| Sheaf.Paper.DiagonalTraceSupportedUnitNormalization | unclaimed in the current claim records | Same declaration, signature and body; available through the original public import (compiled OK against the delivery, packet §3b). |

## Status

landed 20261027T233852-L-4126810 2026-10-27 (merge of deliver/D4/Sheaf.Paper.DiagonalTraceFiniteCartierChern)
