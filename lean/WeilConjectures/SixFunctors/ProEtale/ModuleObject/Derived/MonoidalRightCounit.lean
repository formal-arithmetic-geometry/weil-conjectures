/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalCounit

/-!
# The bifunctor `Lf^* - ⊗ᴸ Lf^* -` as a left derived bifunctor

Part of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`, split off so that
each file compiles within the time limit: the counit
`leftDerivedUpperStarTensorRightCounit` and `isLeftDerivedFunctor₂_upperStarTensor`.
-/


set_option Elab.async false

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### Derived categories -/

/-- The bifunctor `(K, L) ↦ Lf^* K ⊗ᴸ Lf^* L` on `D(Mod_{Λ_Y})`. -/
noncomputable def leftDerivedUpperStarTensorRight :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) :=
  (((whiskeringLeft₂ _).obj L((f)^*⟦Λ⟧)).obj L((f)^*⟦Λ⟧)).obj (curriedTensor _)

/-- The bifunctor `(K, L) ↦ Lf^* (K ⊗ᴸ L)` on `D(Mod_{Λ_Y})`. -/
noncomputable def leftDerivedUpperStarTensorLeft :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) :=
  curriedTensor _ ⋙ (whiskeringRight _ _ _).obj L((f)^*⟦Λ⟧)

/-- The counit of the bifunctor `Lf^* - ⊗ᴸ Lf^* -`: the counits
`Qh ⋙ Lf^* ⟶ f^* ⋙ Qh` of the derived pullback in both variables, followed by
`upperStarTensorCounit`. -/
noncomputable def leftDerivedUpperStarTensorRightCounit :
    (((whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).obj
        (leftDerivedUpperStarTensorRight Λ f) ⟶
      upperStarTensorTarget Λ f :=
  (((whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).map (𝟙 _) ≫
    whiskeringLeft₂Equiv.symm
      (whiskeringLeft₂Equiv (𝟙 _) ≫ whiskerRight
        (NatTrans.prod (f)^*⟦Λ⟧.leftDerivedFunctorCounit (f)^*⟦Λ⟧.leftDerivedFunctorCounit)
          (uncurry.obj (curriedTensor _)) ≫ whiskeringLeft₂Equiv (upperStarTensorCounit Λ f))

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The comparison `f^* A ⊗ f^* B ⟶ f^*(A ⊗ B)` of complexes is a section of the comparison
induced by the comonoidal structure of `f^*`. -/
lemma upperStarTensorComplexHom_δ
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    upperStarTensorComplexHom Λ f A B ≫
      ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) (f)^*⟦Λ⟧).app A).app B =
      𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ (fun n ↦ ?_)
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i₁ i₂ h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, 
    Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
    HomologicalComplex.mapBifunctorComparison_f]
  dsimp only [upperStarTensorComplexHom, upperStarTensorComplexHomX]
  erw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
  rw [Category.assoc]
  erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX]
  erw [Category.comp_id]
  exact Functor.Monoidal.μ_δ_assoc _ _ _ _

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
open DerivedCategory in
/-- The counit of the bifunctor `Lf^* - ⊗ᴸ Lf^* -` on objects of the homotopy category. -/
lemma leftDerivedUpperStarTensorRightCounit_app_app (A B : HomotopyCategory
    (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) (ComplexShape.up ℤ)) :
    ((leftDerivedUpperStarTensorRightCounit Λ f).app A).app B =
      ((f)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ▷ L((f)^*⟦Λ⟧).obj (Qh.obj B)) ≫
        (Qh.obj (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) ◁
          (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app B) ≫
        Functor.LaxMonoidal.μ Qh (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) ≫
        Qh.map ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ f A.as B.as)) := by
  dsimp only [leftDerivedUpperStarTensorRightCounit, NatTrans.comp_app]
  erw [Category.id_comp]
  refine (?_ : _ = 𝟙 _ ≫ (((f)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ▷ L((f)^*⟦Λ⟧).obj (Qh.obj B)) ≫
        (Qh.obj (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) ◁
          (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app B)) ≫
        (Functor.LaxMonoidal.μ Qh (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) ≫
        Qh.map ((HomotopyCategory.quotient _ _).map
          (upperStarTensorComplexHom Λ f A.as B.as)))).trans ?_
  · rfl
  · exact (Category.id_comp _).trans (Category.assoc _ _ _)


set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- On K-flat complexes, the counit of the bifunctor `Lf^* - ⊗ᴸ Lf^* -` is an isomorphism. -/
lemma isIso_leftDerivedUpperStarTensorRightCounit_app_app
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    (hA : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat ((HomotopyCategory.quotient _ _).obj A))
    (hB : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat ((HomotopyCategory.quotient _ _).obj B)) :
    IsIso (((leftDerivedUpperStarTensorRightCounit Λ f).app
      ((HomotopyCategory.quotient _ _).obj A)).app ((HomotopyCategory.quotient _ _).obj B)) := by
  have hB' := (HomotopyCategory.kFlat_quotient_obj_iff B).1 hB
  rw [leftDerivedUpperStarTensorRightCounit_app_app]
  have := (f)^*⟦Λ⟧.isIso_leftDerivedFunctorCounit_app_of_kFlat' _ hA
  have := (f)^*⟦Λ⟧.isIso_leftDerivedFunctorCounit_app_of_kFlat' _ hB
  have h₃ : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj A))
      (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj B))) :=
    isIso_μNatTrans_Qh_app_app_of_kFlat _ _ (kFlat_upperStar_mapHomotopyCategory_obj Λ f hB')
  have h₄ : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
      (upperStarTensorComplexHom Λ f A B))) := by
    rw [upperStarTensorComplexHom_eq_inv]
    infer_instance
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' h₃ h₄))

set_option synthInstance.maxHeartbeats 400000 in
-- the K-flat derivability structure on complexes of module objects is found by instance search
/-- The bifunctor `Lf^* - ⊗ᴸ Lf^* -` is a left derived bifunctor of `(A, B) ↦ Qh (f^* (A ⊗ B))`,
for the counit `leftDerivedUpperStarTensorRightCounit`. See the module docstring. -/
instance isLeftDerivedFunctor₂_upperStarTensor :
    (leftDerivedUpperStarTensorRight Λ f).IsLeftDerivedFunctor₂
      (leftDerivedUpperStarTensorRightCounit Λ f)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
  have := isLeftDerivabilityStructure_localizerMorphismKFlat Λ Y
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat _ (fun X₁ X₂ ↦ ?_)
  obtain ⟨A, hA⟩ := X₁
  obtain ⟨B, hB⟩ := X₂
  obtain ⟨A, rfl⟩ := A.quotient_obj_surjective
  obtain ⟨B, rfl⟩ := B.quotient_obj_surjective
  exact isIso_leftDerivedUpperStarTensorRightCounit_app_app Λ f A B hA hB

end AlgebraicGeometry.ProEtale.CondensedRing
