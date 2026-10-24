/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

set_option maxHeartbeats 1000000 in
-- `erw` unfolds the tensor product of complexes of module objects to its components.
/-- On complexes, the comparison `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` is compatible with the
composition isomorphism of the pullbacks of module objects. -/
@[reassoc]
lemma upperStarTensorComplexHom_comp
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) ℤ) :
    ((NatTrans.mapHomologicalComplex (upperStarComp Λ f g).hom (ComplexShape.up ℤ)).app A ⊗ₘ
        (NatTrans.mapHomologicalComplex (upperStarComp Λ f g).hom (ComplexShape.up ℤ)).app B) ≫
        upperStarTensorComplexHom Λ f (((g)^*⟦Λ⟧.mapHomologicalComplex _).obj A)
          (((g)^*⟦Λ⟧.mapHomologicalComplex _).obj B) ≫
        ((f)^*⟦Λ⟧.mapHomologicalComplex _).map (upperStarTensorComplexHom Λ g A B) =
      upperStarTensorComplexHom Λ (f ≫ g) A B ≫
        (NatTrans.mapHomologicalComplex (upperStarComp Λ f g).hom _).app (A ⊗ B) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    upperStarTensorComplexHom, upperStarTensorComplexHomX]
  erw [HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorDesc_assoc,
    HomologicalComplex.ι_mapBifunctorDesc_assoc]
  rw [Category.assoc, ← Functor.map_comp]
  erw [HomologicalComplex.ι_mapBifunctorDesc]
  simp only [NatTrans.mapHomologicalComplex_app_f, Category.assoc]
  rw [(upperStarComp Λ f g).hom.naturality, Functor.map_comp]
  have hμ := upperStarComp_hom_app_tensor_μ_assoc Λ f g (A.X p) (B.X q)
    ((f)^*⟦Λ⟧.map ((g)^*⟦Λ⟧.map (HomologicalComplex.ιTensorObj A B p q n h)))
  rw [MonoidalCategory.tensorHom_def_assoc] at hμ
  exact hμ

open DerivedCategory Functor.LaxMonoidal

variable {f} in
lemma leftDerivedUpperStarTensorRightCounit_app_app {W : Scheme.{u}} (h : W ⟶ Y)
    (P Q : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) (.up ℤ)) :
    ((leftDerivedUpperStarTensorRightCounit Λ h).app P).app Q =
      ((h)^*⟦Λ⟧.leftDerivedFunctorCounit.app P ⊗ₘ (h)^*⟦Λ⟧.leftDerivedFunctorCounit.app Q) ≫
        μ Qh (((h)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj P)
          (((h)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj Q) ≫
          Qh.map ((HomotopyCategory.quotient _ _).map
          (upperStarTensorComplexHom Λ h P.as Q.as)) := by
  rw [MonoidalCategory.tensorHom_def]
  refine (Category.id_comp _).trans ((Category.id_comp _).trans ?_)
  rfl

/-- On the image of a complex, the composition isomorphism of the derived pullbacks of module
objects is that of the underived pullbacks, read through the counits of the derived pullbacks. -/
@[reassoc]
lemma leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit
    (K : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) (.up ℤ)) :
    (leftDerivedUpperStarComp Λ f g).hom.app (Qh.obj K) ≫
        L((f)^*⟦Λ⟧).map ((g)^*⟦Λ⟧.leftDerivedFunctorCounit.app K) ≫
        (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app (((g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj K) =
      (f ≫ g)^*⟦Λ⟧.leftDerivedFunctorCounit.app K ≫
        Qh.map ((NatTrans.mapHomotopyCategory (upperStarComp Λ f g).hom (.up ℤ)).app K) :=
  Functor.leftDerivedFunctorFactorIso_hom_app_comp_counit (upperStarComp Λ f g) K

/-- The inverse form of `leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit`. -/
@[reassoc]
lemma leftDerivedUpperStarComp_inv_app_Qh_obj_comp_counit
    (K : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) (.up ℤ)) :
    (leftDerivedUpperStarComp Λ f g).inv.app (Qh.obj K) ≫
        (f ≫ g)^*⟦Λ⟧.leftDerivedFunctorCounit.app K ≫
        Qh.map ((NatTrans.mapHomotopyCategory (upperStarComp Λ f g).hom (.up ℤ)).app K) =
      L((f)^*⟦Λ⟧).map ((g)^*⟦Λ⟧.leftDerivedFunctorCounit.app K) ≫
        (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app (((g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj K) := by
  rw [← leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit, Iso.inv_hom_id_app_assoc]

variable {f} in
lemma leftDerivedUpperStarTensorLeftCounit_app_app {W : Scheme.{u}} (h : W ⟶ Y)
    (P Q : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) (.up ℤ)) :
    ((leftDerivedUpperStarTensorLeftCounit Λ h).app P).app Q =
      L((h)^*⟦Λ⟧).map (μ Qh P Q) ≫ (h)^*⟦Λ⟧.leftDerivedFunctorCounit.app (P ⊗ Q) :=
  rfl

set_option maxHeartbeats 2000000 in
-- the statement of `Functor.leftDerived₂_fac_app_app` is unfolded to the tensor comparison
variable {f} in
/-- The comparison `m : Lh^* (K ⊗ᴸ L) ⟶ Lh^* K ⊗ᴸ Lh^* L` on images of complexes, composed with the
counit of the bifunctor `Lh^* - ⊗ᴸ Lh^* -`. -/
@[reassoc]
lemma leftDerivedUpperStarTensor_app_app_comp {W : Scheme.{u}} (h : W ⟶ Y)
    (P Q : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) (.up ℤ)) :
    ((leftDerivedUpperStarTensor Λ h).app (Qh.obj P)).app (Qh.obj Q) ≫
        ((h)^*⟦Λ⟧.leftDerivedFunctorCounit.app P ⊗ₘ (h)^*⟦Λ⟧.leftDerivedFunctorCounit.app Q) ≫
        μ Qh (((h)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj P)
          (((h)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj Q) ≫
        Qh.map ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ h P.as Q.as)) =
      L((h)^*⟦Λ⟧).map (μ Qh P Q) ≫ (h)^*⟦Λ⟧.leftDerivedFunctorCounit.app (P ⊗ Q) := by
  have h1 := Functor.leftDerived₂_fac_app_app (leftDerivedUpperStarTensorRight Λ h)
    (leftDerivedUpperStarTensorRightCounit Λ h) (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) (leftDerivedUpperStarTensorLeft Λ h)
    (leftDerivedUpperStarTensorLeftCounit Λ h) P Q
  rw [leftDerivedUpperStarTensorRightCounit_app_app, leftDerivedUpperStarTensorLeftCounit_app_app]
    at h1
  exact h1

end AlgebraicGeometry.ProEtale.CondensedRing
