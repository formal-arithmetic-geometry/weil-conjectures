/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.DerivedCompAux
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalComp

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory DerivedCategory Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

set_option maxHeartbeats 2000000 in
-- the images of complexes in the homotopy category are unfolded
lemma leftDerivedUpperStarTensor_comp_aux
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) ℤ) :
    ((leftDerivedUpperStarTensor Λ (f ≫ g)).app (Qh.obj ((HomotopyCategory.quotient _ _).obj A))).app
        (Qh.obj ((HomotopyCategory.quotient _ _).obj B)) ≫
      ((f ≫ g)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj A) ⊗ₘ
        (f ≫ g)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj B)) ≫
      μ Qh (((f ≫ g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj A))
        (((f ≫ g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj B)) ≫
      Qh.map ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ (f ≫ g) A B)) =
    ((leftDerivedUpperStarComp Λ f g).hom.app (Qh.obj ((HomotopyCategory.quotient _ _).obj A) ⊗
        Qh.obj ((HomotopyCategory.quotient _ _).obj B)) ≫
      L((f)^*⟦Λ⟧).map (((leftDerivedUpperStarTensor Λ g).app
        (Qh.obj ((HomotopyCategory.quotient _ _).obj A))).app
          (Qh.obj ((HomotopyCategory.quotient _ _).obj B))) ≫
      ((leftDerivedUpperStarTensor Λ f).app _).app _ ≫
      ((leftDerivedUpperStarComp Λ f g).inv.app (Qh.obj ((HomotopyCategory.quotient _ _).obj A)) ⊗ₘ
        (leftDerivedUpperStarComp Λ f g).inv.app
          (Qh.obj ((HomotopyCategory.quotient _ _).obj B)))) ≫
      ((f ≫ g)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj A) ⊗ₘ
        (f ≫ g)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj B)) ≫
      μ Qh (((f ≫ g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj A))
        (((f ≫ g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj B)) ≫
      Qh.map ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ (f ≫ g) A B)) := by
  have : IsIso ((HomotopyCategory.quotient _ (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (upperStarComp Λ f g).hom (.up ℤ)).app (A ⊗ B))) :=
    inferInstanceAs (IsIso ((HomotopyCategory.quotient _ (.up ℤ)).map
      ((NatIso.mapHomologicalComplex (upperStarComp Λ f g) (.up ℤ)).app (A ⊗ B)).hom))
  have : IsIso ((NatTrans.mapHomotopyCategory (upperStarComp Λ f g).hom (.up ℤ)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj A ⊗ (HomotopyCategory.quotient _ (.up ℤ)).obj B)) :=
    ⟨(NatTrans.mapHomotopyCategory (upperStarComp Λ f g).inv (.up ℤ)).app _, by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
        NatTrans.mapHomotopyCategory_id]
      rfl, by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
        NatTrans.mapHomotopyCategory_id]
      rfl⟩
  exact derivedComp_tensor_aux (g)^*⟦Λ⟧.leftDerivedFunctorCounit (f)^*⟦Λ⟧.leftDerivedFunctorCounit
    (f ≫ g)^*⟦Λ⟧.leftDerivedFunctorCounit (leftDerivedUpperStarComp Λ f g)
    (fun K M ↦ ((leftDerivedUpperStarTensor Λ g).app K).app M)
    (fun K M ↦ ((leftDerivedUpperStarTensor Λ f).app K).app M)
    (fun K M ↦ ((leftDerivedUpperStarTensor Λ (f ≫ g)).app K).app M)
    ((HomotopyCategory.quotient _ _).obj A) ((HomotopyCategory.quotient _ _).obj B)
    (fun K ↦ (NatTrans.mapHomotopyCategory (upperStarComp Λ f g).hom (.up ℤ)).app K)
    ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ g A B))
    ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ f
      (((g)^*⟦Λ⟧.mapHomologicalComplex _).obj A) (((g)^*⟦Λ⟧.mapHomologicalComplex _).obj B)))
    ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ (f ≫ g) A B))
    (leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit Λ f g)
    (leftDerivedUpperStarTensor_app_app_comp Λ (f ≫ g) _ _)
    (leftDerivedUpperStarTensor_app_app_comp Λ g _ _)
    (leftDerivedUpperStarTensor_app_app_comp Λ f _ _)
    (leftDerivedUpperStarTensor_naturality Λ f _ _)
    (quotient_map_upperStarTensorComplexHom_comp Λ f g A B)

end AlgebraicGeometry.ProEtale.CondensedRing
