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

variable {f} in
/-- The comparison `Lh^* (K ⊗ᴸ M) ⟶ Lh^* K ⊗ᴸ Lh^* M` is natural in both variables. -/
@[reassoc]
lemma leftDerivedUpperStarTensor_naturality {W : Scheme.{u}} (h : W ⟶ Y)
    {K K' M M' : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))}
    (a : K ⟶ K') (b : M ⟶ M') :
    ((leftDerivedUpperStarTensor Λ h).app K).app M ≫ (L((h)^*⟦Λ⟧).map a ⊗ₘ L((h)^*⟦Λ⟧).map b) =
      L((h)^*⟦Λ⟧).map (a ⊗ₘ b) ≫ ((leftDerivedUpperStarTensor Λ h).app K').app M' := by
  have h₁ := NatTrans.congr_app ((leftDerivedUpperStarTensor Λ h).naturality a) M
  have h₂ := ((leftDerivedUpperStarTensor Λ h).app K').naturality b
  dsimp [leftDerivedUpperStarTensorLeft, leftDerivedUpperStarTensorRight] at h₁ h₂
  rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def, Functor.map_comp,
    Category.assoc, ← reassoc_of% h₁, ← h₂]

private lemma quotient_map_whiskerRight_mod
    {K₁ L₁ : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ} (f₁ : K₁ ⟶ L₁)
    (K₂ : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ) :
    (HomotopyCategory.quotient _ (.up ℤ)).map (f₁ ▷ K₂) =
      (HomotopyCategory.quotient _ (.up ℤ)).map f₁ ▷ (HomotopyCategory.quotient _ (.up ℤ)).obj K₂ :=
  HomotopyCategory.MonoidalCategory.quotient_map_whiskerRight _ (.up ℤ) f₁ K₂

private lemma quotient_map_whiskerLeft_mod
    (K₁ : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    {K₂ L₂ : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ} (f₂ : K₂ ⟶ L₂) :
    (HomotopyCategory.quotient _ (.up ℤ)).map (K₁ ◁ f₂) =
      (HomotopyCategory.quotient _ (.up ℤ)).obj K₁ ◁ (HomotopyCategory.quotient _ (.up ℤ)).map f₂ :=
  HomotopyCategory.MonoidalCategory.quotient_map_whiskerLeft _ (.up ℤ) K₁ f₂

/-- `upperStarTensorComplexHom_comp` in the homotopy category. -/
@[reassoc]
lemma quotient_map_upperStarTensorComplexHom_comp
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) ℤ) :
    ((HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex (upperStarComp Λ f g).hom (.up ℤ)).app A) ⊗ₘ
        (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex (upperStarComp Λ f g).hom (.up ℤ)).app B)) ≫
        (HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ f
          (((g)^*⟦Λ⟧.mapHomologicalComplex _).obj A) (((g)^*⟦Λ⟧.mapHomologicalComplex _).obj B)) ≫
        (HomotopyCategory.quotient _ _).map (((f)^*⟦Λ⟧.mapHomologicalComplex _).map
          (upperStarTensorComplexHom Λ g A B)) =
      (HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ (f ≫ g) A B) ≫
        (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex (upperStarComp Λ f g).hom (.up ℤ)).app (A ⊗ B)) := by
  rw [MonoidalCategory.tensorHom_def,
    ← quotient_map_whiskerRight_mod, ← quotient_map_whiskerLeft_mod]
  simp only [← Functor.map_comp, Category.assoc]
  congr 1
  rw [← upperStarTensorComplexHom_comp, MonoidalCategory.tensorHom_def, Category.assoc]

set_option maxHeartbeats 1000000 in
-- `erw` unfolds the tensor product of complexes of module objects to its components.
/-- On complexes, the comparison `(𝟙 X)^* A ⊗ (𝟙 X)^* B ⟶ (𝟙 X)^* (A ⊗ B)` is compatible with the
identity isomorphism of the pullback of module objects. -/
lemma upperStarTensorComplexHom_id (W : Scheme.{u})
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) ℤ) :
    ((NatTrans.mapHomologicalComplex (upperStarId Λ W).hom (ComplexShape.up ℤ)).app A ⊗ₘ
        (NatTrans.mapHomologicalComplex (upperStarId Λ W).hom (ComplexShape.up ℤ)).app B) =
      upperStarTensorComplexHom Λ (𝟙 W) A B ≫
        (NatTrans.mapHomologicalComplex (upperStarId Λ W).hom _).app (A ⊗ B) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, upperStarTensorComplexHom, upperStarTensorComplexHomX]
  erw [HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.ι_mapBifunctorDesc_assoc]
  simp only [NatTrans.mapHomologicalComplex_app_f, Category.assoc]
  rw [(upperStarId Λ W).hom.naturality]
  have hμ := upperStarId_hom_app_tensor_μ_assoc Λ W (A.X p) (B.X q)
    ((𝟭 _).map (HomologicalComplex.ιTensorObj A B p q n h))
  rw [MonoidalCategory.tensorHom_def_assoc] at hμ
  exact hμ

set_option maxHeartbeats 1000000 in
-- `erw` unfolds the tensor product of complexes of module objects to its components.
lemma tensorHom_mapHomologicalComplexIdIso_hom_app (W : Scheme.{u})
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) ℤ) :
    ((Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom.app A ⊗ₘ
        (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom.app B) =
      (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom.app (A ⊗ B) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [Functor.mapHomologicalComplexIdIso_hom_app_f]
  erw [CategoryTheory.Functor.map_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.id_comp]

lemma upperStarTensorComplexHom_id' (W : Scheme.{u})
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) ℤ) :
    (((NatTrans.mapHomologicalComplex (upperStarId Λ W).hom (ComplexShape.up ℤ)).app A ≫
          (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom.app A) ⊗ₘ
        ((NatTrans.mapHomologicalComplex (upperStarId Λ W).hom (ComplexShape.up ℤ)).app B ≫
          (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom.app B)) =
      upperStarTensorComplexHom Λ (𝟙 W) A B ≫
        (NatTrans.mapHomologicalComplex (upperStarId Λ W).hom _).app (A ⊗ B) ≫
        (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom.app (A ⊗ B) := by
  rw [← tensorHom_comp_tensorHom, upperStarTensorComplexHom_id, Category.assoc,
    tensorHom_mapHomologicalComplexIdIso_hom_app]

end AlgebraicGeometry.ProEtale.CondensedRing
