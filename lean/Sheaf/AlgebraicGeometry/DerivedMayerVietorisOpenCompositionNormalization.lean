/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData

/-! # Composition normalization by derived units

Source: Stacks Project, Cohomology, Tags 08FE and 08BV.
(blueprint: lem-pc-derived-mayer-vietoris-open-composition-normalization).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

variable (X Y : Scheme.{u}) (h : X ⟶ Y)
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ T : X.Opens, HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
  [∀ T : Y.Opens, HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
  (U : Y.Opens)

attribute [local instance 2000] schemeMVModuleAbelian

/-- The composition square commutes with the right-derived units, before any counit
is applied. This holds on every homotopy object, without a K-injectivity hypothesis.
Source: Stacks Tag 0D5T; Tag 08FE, composition on inverse-image opens.
Proof: apply the determining unit equation of each chosen composition comparison.
Transport the middle unit along the equality jX followed by h = g followed by jY.
Naturality of the right-derived unit identifies this transport with the image of
the underived open-composition identification. Cancel the comparison for g followed
by jY and reassociate. The result is the equality of the two pasted units displayed
below. No restriction functor or adjunction counit enters this computation.
(blueprint: lem-pc-derived-mayer-vietoris-open-composition-normalization). -/
theorem schemeMVOpenComposition_unit_normalization
    (β : schemeDerivedDirectImage (h ⁻¹ᵁ U).ι ⋙ schemeDerivedDirectImage h ≅
      schemeDerivedDirectImage (h ∣_ U) ⋙ schemeDerivedDirectImage U.ι)
    (hβ : β = (schemeMVDirectImageComposition (h ⁻¹ᵁ U).ι h).symm ≪≫
      eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h U).symm) ≪≫
      schemeMVDirectImageComposition (h ∣_ U) U.ι)
    (K : HomotopyCategory
      (SheafOfModules.{u} (moduleRings (h ⁻¹ᵁ U).toScheme.toRingedSpace))
      (ComplexShape.up ℤ)) :
    let RX := RingedSpace.moduleDirectImage (h ⁻¹ᵁ U).ι.toLRSHom.toShHom
    let F := RingedSpace.moduleDirectImage h.toLRSHom.toShHom
    let G := RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom
    let RY := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
    F.rightDerivedFunctorUnit.app ((RX.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        F.rightDerivedFunctor.map (RX.rightDerivedFunctorUnit.app K) ≫
        β.hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
          ((schemeMVHomotopyOpenComposition h U).hom.app K) ≫
        RY.rightDerivedFunctorUnit.app ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        RY.rightDerivedFunctor.map (G.rightDerivedFunctorUnit.app K) := by sorry

end AlgebraicGeometry
