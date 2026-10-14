/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.MayerVietorisRestrictionLocalizationChain

/-! # Left-hand composition normalization

Source: Stacks Project, Tags 08FE and 0D5T.
(blueprint: lem-pc-mayer-vietoris-composition-left-normalization).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian

/-- Left-hand composition normalization to the complex-composition composite.
Source: Stacks Project, Tags 08FE, 0D5T and 079V.

Proof: Apply schemeMVOpenComposition_complex_localization to the termwise restriction J.
Naturality of the derived composition isomorphism along the inverse exact X-restriction
factor moves this factor from the source to the restricted direct image on the right.
Expand only the open-image localization and canonical open comparison. Postcompose the
unit equation with open direct image of that factor and the inverse derived restriction
comparison. Functoriality combines these three maps. This calculation involves no image
component, no exact Y-restriction factor, and no injectivity hypothesis.
The argument applies to arbitrary complexes, empty and full opens, and identity morphisms:
only functoriality, naturality and inverse-isomorphism equations are used.
(blueprint: lem-pc-mayer-vietoris-composition-left-normalization). -/
theorem schemeMV_composition_left_normalization
    (X Y : Scheme.{u}) (h : X ⟶ Y) (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)
    let R := schemeDerivedDirectImage W.ι
    (schemeMVDirectImageLocalization h).app (schemeOpenModuleImageComplex X (h ⁻¹ᵁ W) I) ≫
      (schemeDerivedDirectImage h).map (schemeMVOpenImageLocalization X (h ⁻¹ᵁ W) I) ≫
      (schemeMVOpenComparison h W (DerivedCategory.Q.obj I)).hom =
    (let LX := schemeOpenRestriction X (h ⁻¹ᵁ W)
     let J := (LX.mapHomologicalComplex (.up ℤ)).obj I
     let G := RingedSpace.moduleDirectImage (h ∣_ W).toLRSHom.toShHom
     let RY := RingedSpace.moduleDirectImage W.ι.toLRSHom.toShHom
     let b₀ := (Functor.mapHomologicalComplexCompIso
         (schemeMVUnderivedOpenComposition h W) (.up ℤ) ≪≫
       (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ RY)) (.up ℤ)).symm).hom.app J
     DerivedCategory.Q.map b₀ ≫
       (schemeMVDirectImageLocalization W.ι).app
         ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
       R.map ((schemeMVDirectImageLocalization (h ∣_ W)).app J ≫
         (schemeDerivedDirectImage (h ∣_ W)).map
           (LX.mapDerivedCategoryFactors.inv.app I) ≫
         (schemeMVOpenRestrictionComparison h W).inv.app (DerivedCategory.Q.obj I))) := by sorry

end AlgebraicGeometry
