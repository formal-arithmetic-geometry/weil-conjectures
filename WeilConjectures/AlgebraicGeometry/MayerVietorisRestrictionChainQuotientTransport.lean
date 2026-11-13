/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisRestrictionLocalizationChain

/-! # Complex localization of the open restriction square

Source: Stacks Project, Tags 08FE and 08BV.
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian

set_option maxHeartbeats 800000 in
-- The quotient transports fit the original budget when elaboration respects transparency.
/-- Transport of the explicit four-map restriction chain to the homotopy quotient.
Source: Stacks Project, Tags 08FE and 079V.
Proof: Expand the chain and the transported direct-image unit. Substitute
mapDerivedCategoryFactorsh_hom_app for exact restriction on the quotient.
Use naturality of the quotient comparison on the termwise restriction isomorphism,
and naturality of the restricted direct-image unit on the restriction quotient
factor. The quotient factors cancel in adjacent hom/inverse pairs. The inverse
X-restriction factor is transported by functoriality. This identifies the four-map
complex chain with the homotopy chain; no normalization of the derived restriction
comparison is used. The identity holds also for empty and full opens. -/
theorem schemeMV_restriction_chain_quotient_transport
    (X Y : Scheme.{u}) (h : X ⟶ Y) (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let F := RingedSpace.moduleDirectImage h.toLRSHom.toShHom
    let G := RingedSpace.moduleDirectImage (h ∣_ W).toLRSHom.toShHom
    let LX := schemeOpenRestriction X (h ⁻¹ᵁ W)
    let LY := schemeOpenRestriction Y W
    let K := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I
    schemeMVRestrictionLocalizationChain X Y h W I =
      LY.mapDerivedCategory.map
        ((DerivedCategory.quotientCompQhIso _).inv.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
          DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app I)) ≫
      (LY.mapDerivedCategoryFactorsh.hom.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((schemeMVHomotopyOpenRestriction h W).hom.app K) ≫
        G.rightDerivedFunctorUnit.app ((LX.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
      G.rightDerivedFunctor.map (LX.mapDerivedCategoryFactorsh.inv.app K) ≫
      G.rightDerivedFunctor.map
        (LX.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso _).hom.app I)) := by
  let LX := schemeOpenRestriction X (h ⁻¹ᵁ W)
  let LY := schemeOpenRestriction Y W
  have hxi : LX.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient _ _).obj I) ≫
      LX.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso _).hom.app I) =
      (DerivedCategory.quotientCompQhIso _).hom.app
          ((LX.mapHomologicalComplex (.up ℤ)).obj I) ≫
        LX.mapDerivedCategoryFactors.inv.app I := by
    apply (cancel_epi (LX.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj I))).1
    rw [Iso.hom_inv_id_app_assoc, LX.mapDerivedCategoryFactorsh_hom_app]
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
      Category.assoc]
    erw [DerivedCategory.Qh.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id_app, Category.comp_id]
  have hy := LY.mapDerivedCategoryFactorsh_hom_app
    (((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I)
  have hr : (schemeMVHomotopyOpenRestriction h W).hom.app
      ((HomotopyCategory.quotient _ _).obj I) =
      (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex (schemeMVUnderivedOpenRestriction h W).hom
          (.up ℤ)).app I) := by
    simp only [schemeMVHomotopyOpenRestriction, Iso.trans_hom, NatTrans.comp_app,
      Iso.symm_hom]
    change (HomotopyCategory.quotient _ _).map
      ((NatTrans.mapHomologicalComplex (schemeMVUnderivedOpenRestriction h W).hom
        (.up ℤ)).app I) ≫ (HomotopyCategory.quotient _ _).map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  dsimp only
  unfold schemeMVRestrictionLocalizationChain
  simp only [schemeMVDirectImageLocalization, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  erw [hy, hr]
  simp only [Functor.comp_obj, Category.assoc, Functor.mapHomotopyCategoryFactors,
    Quotient.lift.isLift_inv, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [← Functor.map_comp]
  erw [hxi]
  simp only [Functor.map_comp]
  erw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  rfl

end AlgebraicGeometry
