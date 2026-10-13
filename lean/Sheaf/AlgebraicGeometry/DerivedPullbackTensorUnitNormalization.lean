/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitCounit

/-! # Normalization of the explicit derived pullback unit comparison -/

@[expose] public section

universe uModel wModel

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

attribute [local instance]
  tensorDescentPullbackDescentModuleTensor
  tensorDescentModuleSymmetric
  tensorDescentModulePreadditive
  tensorDescentModuleClosed
  tensorDescentModuleGrothendieck
  tensorDescentModuleResolutions
  tensorDescentModuleDerivedMonoidal
  tensorDescentPullbackDescentQLax

/-- Normalize the explicitly constructed unit comparison before any tensor comparison is used.
Source: Stacks Project, Cohomology, Tag 079U, parent unit proof, step 1;
the explicit construction in `derivedPullback_tensorUnitIso`.
(blueprint: lem-pc-derived-pullback-tensor-unit-normalization).
Proof: Q is the homotopy quotient followed by Qh, transported along quotientCompQhIso.
The quotient unit comparison and this transport have identity components, hence
its lax unit morphism is the lax unit morphism of Qh. The latter is invertible by
DerivedCategory.isIso_ε_Qh, proving the first assertion. Write u for the single-image
unit comparison of F on complexes. The definition of tensorPullback_unitHomotopyIso
is the quotient image of u followed by the inverse functor-factorization comparison.
The latter has identity components, so Qh of its inverse is Q of u inverse.
Invert the four factors defining derivedPullback_tensorUnitIso: the result is
L of the source localization unit, then the supplied counit at U, then Q of u inverse,
then the inverse target localization unit. Compose with the target localization
unit and cancel its inverse. This proves the displayed formula. This calculation
uses no tensorator of L and no K-flatness or boundedness hypothesis. It applies
also to zero complexes, zero rings, and empty schemes. -/
theorem derivedPullback_tensorUnitIso_normalization {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace)) [F.Additive]
    (mF : F.CoreMonoidal)
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [IsIso (ε.app (𝟙_ (HomotopyCategory
      (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))))] :
    IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q
      (C := SheafOfModules.{uModel} (moduleRings T.toRingedSpace)))) ∧
    (let AX := SheafOfModules.{uModel} (moduleRings X.toRingedSpace)
     let AT := SheafOfModules.{uModel} (moduleRings T.toRingedSpace)
     let U : CochainComplex AX ℤ := 𝟙_ _
     let u := (HomologicalComplex.single AT (ComplexShape.up ℤ) 0).mapIso mF.εIso ≪≫
       ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app _).symm
     (derivedPullback_tensorUnitIso g F mF ε).inv ≫
         Functor.LaxMonoidal.ε (DerivedCategory.Q (C := AT)) =
       (derivedPullback g).map (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := AX))) ≫
         ε.app ((HomotopyCategory.quotient AX (ComplexShape.up ℤ)).obj U) ≫
           (DerivedCategory.Q (C := AT)).map u.inv) := by sorry

end AlgebraicGeometry
