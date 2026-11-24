/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisRestrictionLocalizationChain
import WeilConjectures.AlgebraicGeometry.MayerVietorisCompositionLeftNormalization
import WeilConjectures.AlgebraicGeometry.MayerVietorisCompositionRightNormalization

/-! # Complex localization of the open composition square

## References

* Stacks Project, Tags 08FE, 08BV and 0D5T.
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

/-- Core composition identity before combining the final derived map factors: the unit-transport
calculation from the open-composition normalization. -/
theorem schemeMV_image_composition_localization_core
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
    DerivedCategory.Q.map (schemeMVImageComponent h W I (F.obj I) (𝟙 _)) ≫
      schemeMVOpenImageLocalization Y W (F.obj I) ≫
      R.map (schemeMVRestrictionLocalizationChain X Y h W I) ≫
      R.map ((schemeMVOpenRestrictionComparison h W).inv.app (DerivedCategory.Q.obj I)) := by
  have hleft := schemeMV_composition_left_normalization X Y h W I
  have hright := schemeMV_composition_right_normalization X Y h W I
  exact hleft.trans hright.symm

/-- Complex localization of the open composition square (Stacks, Tags 0D5T and 08FE). The
determining unit equations are those of `schemeMVOpenComposition_unit_normalization`. -/
theorem schemeMV_image_composition_localization
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
    DerivedCategory.Q.map (schemeMVImageComponent h W I (F.obj I) (𝟙 _)) ≫
      schemeMVOpenImageLocalization Y W (F.obj I) ≫
      R.map (schemeMVRestrictionLocalizationChain X Y h W I ≫
        (schemeMVOpenRestrictionComparison h W).inv.app (DerivedCategory.Q.obj I)) := by
  have hc := schemeMV_image_composition_localization_core X Y h W I
  dsimp only at hc ⊢
  simpa only [Functor.map_comp, Category.assoc] using hc

end AlgebraicGeometry
