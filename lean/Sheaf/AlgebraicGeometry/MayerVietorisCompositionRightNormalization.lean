/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.MayerVietorisRestrictionLocalizationChain

/-! # Right-hand image normalization

Source: Stacks Project, Tags 08FE and 0D5T.
(blueprint: lem-pc-mayer-vietoris-composition-right-normalization).
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

/-- Right-hand image normalization to the complex-composition composite.
Source: Stacks Project, Tags 08FE, 0D5T and 079V.

Proof: Apply schemeMVImageIso_composition_factor in every degree. Extensionality of chain
maps identifies the image component followed by open direct image of the underived
restriction comparison with the complex composition comparison b₀. Apply Q. Naturality
of schemeMVDirectImageLocalization for that underived comparison moves it past the open
direct-image unit. Expand the restriction-localization chain and open-image localization
on Y; cancel the inverse and hom of the exact Y-restriction factor inside R. Associativity
and functoriality give the displayed three-map composite. This calculation uses no
h-localization unit and no derived composition isomorphism.
The argument applies to arbitrary complexes, empty and full opens, and identity morphisms:
only functoriality, naturality and inverse-isomorphism equations are used.
(blueprint: lem-pc-mayer-vietoris-composition-right-normalization). -/
theorem schemeMV_composition_right_normalization
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
    DerivedCategory.Q.map (schemeMVImageComponent h W I (F.obj I) (𝟙 _)) ≫
      schemeMVOpenImageLocalization Y W (F.obj I) ≫
      R.map (schemeMVRestrictionLocalizationChain X Y h W I) ≫
      R.map ((schemeMVOpenRestrictionComparison h W).inv.app (DerivedCategory.Q.obj I)) =
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
