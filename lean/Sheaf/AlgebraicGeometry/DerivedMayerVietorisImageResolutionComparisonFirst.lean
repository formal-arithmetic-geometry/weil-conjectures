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
/-- First component of the direct-image Mayer–Vietoris comparison.
(blueprint: lem-pc-mayer-vietoris-image-resolution-comparison-first)
The comparison is obtained by transporting fixed K-injective resolutions and
representing the localized direct-image map by a concrete chain map. -/
theorem schemeMV_image_resolution_comparison_first
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
        (schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).hom := by
  sorry
end AlgebraicGeometry
