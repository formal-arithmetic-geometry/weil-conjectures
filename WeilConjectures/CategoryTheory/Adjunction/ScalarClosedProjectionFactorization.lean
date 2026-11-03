/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ScalarClosedProjectionData

/-! # Evaluation normalization of scalar Hom and projection -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
namespace CategoryTheory.Adjunction
variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
  {F : C ⥤ D} {U : D ⥤ C} [F.Monoidal]

private theorem restriction_ev (adj : F ⊣ U) (K : C) (N : D) :
    (adj.homEquiv _ _).symm (uncurry (scalarHomRestrictionIso adj K N).hom) =
      Functor.OplaxMonoidal.δ F K (U.obj ((ihom (F.obj K)).obj N)) ≫
        F.obj K ◁ adj.counit.app ((ihom (F.obj K)).obj N) ≫
          (ihom.ev (F.obj K)).app N := by
  let a1 := (ihom.adjunction K).comp adj
  let a2 := (adj.comp (ihom.adjunction (F.obj K))).ofNatIsoLeft
    (Functor.Monoidal.commTensorLeft F K)
  have h := homEquiv_symm_rightAdjointUniq_hom_app a2 a1 N
  rw [← rightAdjointUniq_inv_app] at h
  dsimp only [a1] at h
  rw [comp_homEquiv] at h
  rw [Equiv.symm_trans_apply] at h
  change (adj.homEquiv _ _).symm (uncurry
    ((a1.rightAdjointUniq a2).inv.app N)) = _ at h
  simpa only [scalarHomRestrictionIso, ihomCompIso, Iso.symm_hom, a1, a2, Iso.app_inv,
    ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.Monoidal.commTensorLeft_inv_app, comp_counit_app,
    Functor.whiskerLeft_app, Functor.comp_obj, tensorLeft, curriedTensor_obj_map, ihom.ev,
    Category.assoc] using h

omit [MonoidalClosed C] [MonoidalClosed D] in
private theorem projection_ev (adj : F ⊣ U) (M : C) :
    F.map (scalarUnitProjection adj M) ≫ adj.counit.app (F.obj M) =
      Functor.OplaxMonoidal.δ F M (U.obj (𝟙_ D)) ≫
        F.obj M ◁ adj.counit.app (𝟙_ D) ≫ (ρ_ (F.obj M)).hom := by
  exact (adj.homEquiv _ _).symm_apply_apply _

/-- The comparison square is normalized by evaluation and scalar counit.
Source: Stacks 07A4, 07A6, 08J9.
Proof: uncurry the two sides and apply the scalar Hom bijection. The counit
formula for restrictionHomIso turns its side into scalar evaluation. Naturality
moves the projection past evaluation. The monoidal associativity and unit laws
identify both composites with the tensorator followed by the scalar counit
in the last factor. Injectivity of both adjunction transposes gives the square.
(blueprint: lem-per-scalar-closed-projection-factorization). -/
theorem scalarClosedProjection_factorization (adj : F ⊣ U) (K L : C) :
    scalarUnitProjection adj ((ihom K).obj L) ≫
        U.map ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app L) ≫
        (scalarHomRestrictionIso adj K (F.obj L)).hom =
      ihomTensorToIhom K L (U.obj (𝟙_ D)) ≫
        (ihom K).map (scalarUnitProjection adj L) := by
  apply uncurry_injective
  apply (adj.homEquiv _ _).symm.injective
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_natural_right]
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_left_symm]
  dsimp only [Functor.comp_obj]
  rw [restriction_ev]
  rw [uncurry_eq, whiskerLeft_ihomTensorToIhom_ev]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
  rw [← whiskerLeft_comp_assoc]
  erw [adj.counit_naturality]
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
  rw [← whiskerLeft_comp_assoc, projection_ev]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [Functor.LaxMonoidal.ihomComparison_ev]
  rw [← whiskerLeft_comp_assoc, projection_ev]
  simp only [whiskerLeft_comp, Category.assoc]
  erw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
  dsimp only [Functor.comp_obj, tensorLeft, curriedTensor_obj_obj]
  erw [← whisker_exchange_assoc, rightUnitor_naturality]
  rw [← cancel_epi (F.map (α_ K ((ihom K).obj L) (U.obj (𝟙_ D))).hom)]
  simp only [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]
  rw [← Functor.OplaxMonoidal.associativity_assoc]
  rw [← associator_naturality_right_assoc]
  dsimp only [Functor.id_obj]
  rw [← rightUnitor_tensor_hom_assoc]
  rw [← whisker_exchange_assoc, rightUnitor_naturality_assoc]
  simp only [Functor.Monoidal.δ_μ_assoc]

end CategoryTheory.Adjunction
