/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
public import Sheaf.AlgebraicGeometry.DerivedDirectImageSplitTriangle
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian
/-- Intersection component of the direct-image Mayer--Vietoris comparison.

This is the third-component transport identity in the proof of
`schemeMV_image_resolution_comparison`; it is strictly the intersection
component equality for a supplied morphism of complexes.  It follows from
naturality of the derived open-restriction and direct-image comparison maps,
and the defining equations of the fixed resolution isomorphisms.
(blueprint: lem-pc-mayer-vietoris-image-resolution-comparison-intersection)
-/
theorem schemeMV_image_resolution_comparison_intersection
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
    ∀ m : S.map F ⟶ T,
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
  sorry
end AlgebraicGeometry
