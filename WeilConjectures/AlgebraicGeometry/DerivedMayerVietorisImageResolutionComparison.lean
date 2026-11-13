/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSplitTriangle
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisImageResolutionComparisonIntersection

/-! # Comparing the concrete Mayer--Vietoris sequences after direct image

Source: Stacks Project, Tags 08BV, 08FE and 0D5T.
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

/-- A map of concrete short complexes realizes the normalized first and intersection maps
(Stacks, Tags 08BV, 08FE and 0D5T). -/
theorem schemeMV_image_resolution_comparison
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U V : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X)
    [(schemeOpenModuleImageComplex X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))
      (schemeMVResolution X E)).IsKInjective] :
    let I := schemeMVResolution X E
    let J := schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)
    let S := schemeMayerVietorisComplex X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) I
    let T := schemeMayerVietorisComplex Y U V J
    let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)
    ∃ m : S.map F ⟶ T,
      (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom I).hom ≫
          DerivedCategory.Q.map m.τ₁ ≫
          (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).hom =
        (schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).hom ∧
      (schemeDerivedDirectImage h).map
          (((schemeMVDerivedRestriction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))) ⋙
              schemeDerivedDirectImage ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)).ι).map
              (schemeMVResolutionIso X E).inv ≫
            (schemeOpenModuleImageComplexComparison X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)) I
              (schemeMVAdjunction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)))).inv) ≫
          (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom
            (schemeOpenModuleImageComplex X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)) I)).hom ≫
          DerivedCategory.Q.map m.τ₃ =
        (schemeMVOpenComparison h (U ⊓ V) E).hom ≫
          (((schemeMVDerivedRestriction Y (U ⊓ V)) ⋙
              schemeDerivedDirectImage (U ⊓ V).ι).map
              (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).inv ≫
            (schemeOpenModuleImageComplexComparison Y (U ⊓ V) J
              (schemeMVAdjunction Y (U ⊓ V))).inv) := by
  dsimp
  obtain ⟨f, hf⟩ := schemeMV_normalized_chain_map_exists X Y h E
  refine ⟨schemeMVImageChainMap (h := h) U V _ _ f, hf, ?_⟩
  exact schemeMV_image_resolution_comparison_intersection X Y h U V E f hf

end AlgebraicGeometry
