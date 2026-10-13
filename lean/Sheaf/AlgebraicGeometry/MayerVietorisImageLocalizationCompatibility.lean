/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.MayerVietorisImageChainData

/-! # Explicit restriction-induced comparison maps

Source: Stacks Project, Tags 08FE and 08BV.
(blueprint: def-pc-mayer-vietoris-image-chain-data).
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

/-- Compatibility of the sectionwise open-image comparison with localization.
This concerns only the sectionwise isomorphism on a source K-injective complex;
it contains no chosen map to a target resolution and no Mayer--Vietoris morphism.
Source: Stacks Tags 08FE, 079V and 0D5T.
(blueprint: lem-pc-mayer-vietoris-image-localization-compatibility).

Proof: The direct-image computation map is the inverse right-derived unit.
The comparison for the open image is the inverse right-derived unit on the
restricted complex, followed by the exact-restriction localization comparison.
The underived sectionwise isomorphism is the composite of pushforwardComp along
the open square and the restriction/direct-image isomorphism of Tag 08FE.
Apply the unit equations for rightDerivedFunctorCompMapDerivedCategoryIso,
rightDerivedFunctorNatIso and rightDerivedFunctorCompIso to these factors.
The resulting composite is the defining right-derived unit equation for
schemeMVDirectImageComposition and schemeMVOpenRestrictionComparison.
These equations determine the comparisons by the right-derived universal
property. Their composite therefore gives the stated square on I. Transport
along e by naturality of those comparisons gives the displayed equation.
No K-injectivity of h_*I is used: the comparison on that complex is the general
localization map, not an inverse computation isomorphism. -/
theorem schemeMV_image_localization_compatibility
    (X Y : Scheme.{u}) (h : X ⟶ Y) (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] [(schemeOpenModuleImageComplex X (h ⁻¹ᵁ W) I).IsKInjective]
    (E : schemeDerivedCategory X) (e : DerivedCategory.Q.obj I ≅ E) :
    let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)
    let H := (schemeMVDerivedRestriction Y W) ⋙ schemeDerivedDirectImage W.ι
    (schemeDerivedDirectImage h).map
        ((((schemeMVDerivedRestriction X (h ⁻¹ᵁ W)) ⋙
            schemeDerivedDirectImage (h ⁻¹ᵁ W).ι).map e.inv) ≫
          (schemeOpenModuleImageComplexComparison X (h ⁻¹ᵁ W) I
            (schemeMVAdjunction X (h ⁻¹ᵁ W))).inv) ≫
      (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom
        (schemeOpenModuleImageComplex X (h ⁻¹ᵁ W) I)).hom ≫
      DerivedCategory.Q.map (schemeMVImageComponent h W I (F.obj I) (𝟙 _)) ≫
      schemeMVOpenImageLocalization Y W (F.obj I) =
    (schemeMVOpenComparison h W E).hom ≫
      H.map ((schemeDerivedDirectImage h).map e.inv ≫
        (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom I).hom) := by
  sorry

end AlgebraicGeometry
