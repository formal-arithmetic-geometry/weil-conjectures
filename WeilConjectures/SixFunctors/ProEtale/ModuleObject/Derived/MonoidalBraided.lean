/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalCompDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-!
# The derived pullback of module objects is braided

The comparison `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` of complexes of module objects commutes with the
Koszul braidings of the tensor products of complexes
(`ProEtale.CondensedRing.upperStarTensorComplexHom_braiding`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `δ_upperStar_braiding` in terms of the tensorators. -/
@[reassoc]
lemma μ_upperStar_braiding
    (A B : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    Functor.LaxMonoidal.μ (f)^*⟦Λ⟧ A B ≫ (f)^*⟦Λ⟧.map (β_ A B).hom =
      (β_ ((f)^*⟦Λ⟧.obj A) ((f)^*⟦Λ⟧.obj B)).hom ≫ Functor.LaxMonoidal.μ (f)^*⟦Λ⟧ B A := by
  rw [← cancel_epi (Functor.OplaxMonoidal.δ (f)^*⟦Λ⟧ A B), Functor.Monoidal.δ_μ_assoc,
    δ_upperStar_braiding_assoc, Functor.Monoidal.δ_μ, Category.comp_id]

set_option maxHeartbeats 1000000 in
-- `erw` unfolds the tensor product of complexes of module objects to its components.
/-- On complexes, the comparison `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` commutes with the Koszul
braidings. -/
lemma upperStarTensorComplexHom_braiding
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    upperStarTensorComplexHom Λ f A B ≫
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map (β_ A B).hom =
      (β_ (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj A)
          (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj B)).hom ≫
        upperStarTensorComplexHom Λ f B A := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    upperStarTensorComplexHom, upperStarTensorComplexHomX]
  erw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
  have hb : HomologicalComplex.ιTensorObj (((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj A)
        (((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj B) p q n h ≫
      (β_ (((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj A)
        (((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj B)).hom.f n =
      ((p * q).negOnePow : ℤ) • ((β_ ((((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj A).X p)
        ((((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj B).X q)).hom ≫
        HomologicalComplex.ιTensorObj (((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj B)
          (((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj A) q p n
          (by rw [← h, add_comm]; rfl)) :=
    CochainComplex.Monoidal.ι_braiding_hom p q n h
  rw [reassoc_of% hb]
  rw [Category.assoc, ← Functor.map_comp]
  have hb2 : HomologicalComplex.ιTensorObj A B p q n h ≫ (β_ A B).hom.f n =
      ((p * q).negOnePow : ℤ) • ((β_ (A.X p) (B.X q)).hom ≫
        HomologicalComplex.ιTensorObj B A q p n (by rw [← h, add_comm]; rfl)) :=
    CochainComplex.Monoidal.ι_braiding_hom p q n h
  rw [hb2]
  rw [Functor.map_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Functor.map_comp,
    μ_upperStar_braiding_assoc, Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorDesc]
  rfl

/-- `upperStarTensorComplexHom_braiding` in the homotopy category. -/
lemma quotient_map_upperStarTensorComplexHom_braiding
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    (HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ f A B) ≫
        ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).map
          (β_ ((HomotopyCategory.quotient _ _).obj A) ((HomotopyCategory.quotient _ _).obj B)).hom =
      (β_ (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj A))
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ _).obj B))).hom ≫
        (HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ f B A) := by
  have h := (HomotopyCategory.quotient _ (.up ℤ)).congr_map
    (upperStarTensorComplexHom_braiding Λ f A B)
  simp only [Functor.map_comp] at h
  exact h

open DerivedCategory Functor Functor.LaxMonoidal

attribute [local instance] DerivedCategory.braidedCategory'

set_option maxHeartbeats 2000000 in
-- the images of complexes in the homotopy category are unfolded
/-- The tensor comparison of `Lf^*` commutes with the derived braidings at images of K-flat
complexes. -/
lemma leftDerivedUpperStarTensor_braiding_Qh
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    (hA : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat A)
    (hB : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat B) :
    L((f)^*⟦Λ⟧).map (β_ (Qh.obj ((HomotopyCategory.quotient _ _).obj A))
        (Qh.obj ((HomotopyCategory.quotient _ _).obj B))).hom ≫
        ((leftDerivedUpperStarTensor Λ f).app _).app _ =
      ((leftDerivedUpperStarTensor Λ f).app _).app _ ≫
        (β_ (L((f)^*⟦Λ⟧).obj (Qh.obj ((HomotopyCategory.quotient _ _).obj A)))
          (L((f)^*⟦Λ⟧).obj (Qh.obj ((HomotopyCategory.quotient _ _).obj B)))).hom := by
  have hA' := (HomotopyCategory.kFlat_quotient_obj_iff A).2 hA
  have hB' := (HomotopyCategory.kFlat_quotient_obj_iff B).2 hB
  have : IsIso ((f)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj A)) :=
    (f)^*⟦Λ⟧.isIso_leftDerivedFunctorCounit_app_of_kFlat' _ hA'
  have : IsIso ((f)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj B)) :=
    (f)^*⟦Λ⟧.isIso_leftDerivedFunctorCounit_app_of_kFlat' _ hB'
  have : IsIso (μ Qh (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient _ _).obj B))
      (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj A))) :=
    isIso_μNatTrans_Qh_app_app_of_kFlat _ _ (kFlat_upperStar_mapHomotopyCategory_obj Λ f hA)
  have : IsIso (Qh.map ((HomotopyCategory.quotient _ _).map
      (upperStarTensorComplexHom Λ f ((HomotopyCategory.quotient _ (.up ℤ)).obj B).as
        ((HomotopyCategory.quotient _ (.up ℤ)).obj A).as))) := by
    have h := upperStarTensorComplexHom_δ Λ f B A
    have : IsIso (upperStarTensorComplexHom Λ f B A ≫
        ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
          (f)^*⟦Λ⟧).app B).app A) := by
      rw [h]
      infer_instance
    have : IsIso (upperStarTensorComplexHom Λ f B A) := IsIso.of_isIso_comp_right _
      (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) (f)^*⟦Λ⟧).app B).app A)
    exact Functor.map_isIso _ ((HomotopyCategory.quotient _ (.up ℤ)).map
      (upperStarTensorComplexHom Λ f B A))
  exact derived_map_braiding_aux (f)^*⟦Λ⟧.leftDerivedFunctorCounit
    (fun K M ↦ ((leftDerivedUpperStarTensor Λ f).app K).app M)
    ((HomotopyCategory.quotient _ _).obj A) ((HomotopyCategory.quotient _ _).obj B)
    (fun P Q ↦ (HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ f P.as Q.as))
    (leftDerivedUpperStarTensor_app_app_comp Λ f)
    (DerivedMonoidal.braiding_hom_μ Qh (HomotopyCategory.quasiIso _ _) _ _)
    (DerivedMonoidal.braiding_hom_μ Qh (HomotopyCategory.quasiIso _ _) _ _)
    (quotient_map_upperStarTensorComplexHom_braiding Λ f A B)

set_option maxHeartbeats 1000000 in
-- the K-flat replacements are unfolded
/-- **The derived pullback of module objects is braided**: the tensor comparison
`m : Lf^* (K ⊗ᴸ M) ⟶ Lf^* K ⊗ᴸ Lf^* M` commutes with the derived braidings,
`Lf^* β_{K, M} ≫ m_{M, K} = m_{K, M} ≫ β_{Lf^* K, Lf^* M}`. -/
theorem leftDerivedUpperStarTensor_braiding
    (K M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    L((f)^*⟦Λ⟧).map (β_ K M).hom ≫ ((leftDerivedUpperStarTensor Λ f).app M).app K =
      ((leftDerivedUpperStarTensor Λ f).app K).app M ≫
        (β_ (L((f)^*⟦Λ⟧).obj K) (L((f)^*⟦Λ⟧).obj M)).hom := by
  have (Z : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).obj Z) := inferInstance
  obtain ⟨P, hP, ⟨eP⟩⟩ := DerivedCategory.exists_kFlat_iso K
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := DerivedCategory.exists_kFlat_iso M
  obtain ⟨A, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  obtain ⟨B, rfl⟩ := HomotopyCategory.quotient_obj_surjective Q
  have key := leftDerivedUpperStarTensor_braiding_Qh Λ f A B
    ((HomotopyCategory.kFlat_quotient_obj_iff A).1 hP)
    ((HomotopyCategory.kFlat_quotient_obj_iff B).1 hQ)
  exact map_braiding_comp_of_iso (fun K M ↦ ((leftDerivedUpperStarTensor Λ f).app K).app M)
    (leftDerivedUpperStarTensor_naturality Λ f) eP eQ key

end AlgebraicGeometry.ProEtale.CondensedRing
