/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalTensor

/-!
# The tensor comparison of the derived pullback of module objects is an isomorphism

Part of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`, split off so that
each file compiles within the time limit: the factorization
`leftDerivedUpperStarTensor_app_app_fac`, `isIso_leftDerivedUpperStarTensor`, the unit comparison
`leftDerivedUpperStarUnitIso` and the lax square `leftDerivedUpperStarTensor_laxSquare`.
-/


set_option Elab.async false

@[expose] public section

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
open DerivedCategory in
/-- The defining property of the tensor comparison of `Lf^*`, in the form used by
`DerivedCategory.commShift_of_tensorLeft_fac`. -/
lemma leftDerivedUpperStarTensor_app_app_fac (A B : HomotopyCategory
    (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) (ComplexShape.up ℤ)) :
    ((leftDerivedUpperStarTensor Λ f).app (Qh.obj A)).app (Qh.obj B) ≫
        (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ▷ L((f)^*⟦Λ⟧).obj (Qh.obj B) ≫
        Qh.obj (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) ◁
          (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app B ≫
        Functor.LaxMonoidal.μ Qh (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) =
      L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ Qh A B) ≫
        (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app (A ⊗ B) ≫
        Qh.map (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
          (f)^*⟦Λ⟧).app A).app B) := by
  have h : ((leftDerivedUpperStarTensor Λ f).app (Qh.obj A)).app (Qh.obj B) ≫
      ((leftDerivedUpperStarTensorRightCounit Λ f).app A).app B =
      ((leftDerivedUpperStarTensorLeftCounit Λ f).app A).app B :=
    congr_app (congr_app (leftDerivedUpperStarTensor_fac Λ f) A) B
  rw [leftDerivedUpperStarTensorRightCounit_app_app] at h
  have hδ : Qh.map ((HomotopyCategory.quotient _ _).map
      (upperStarTensorComplexHom Λ f A.as B.as)) ≫
      Qh.map (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
          (f)^*⟦Λ⟧).app A).app B) = 𝟙 _ := by
    rw [← Functor.map_comp]
    erw [Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app]
    rw [← Functor.map_comp, upperStarTensorComplexHom_δ]
    exact (congrArg Qh.map ((HomotopyCategory.quotient _ _).map_id _)).trans (Qh.map_id _)
  calc _ = (((leftDerivedUpperStarTensor Λ f).app (Qh.obj A)).app (Qh.obj B) ≫
        (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ▷ L((f)^*⟦Λ⟧).obj (Qh.obj B) ≫
        Qh.obj (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) ◁
          (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app B ≫
        Functor.LaxMonoidal.μ Qh (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) ≫
        Qh.map ((HomotopyCategory.quotient _ _).map
          (upperStarTensorComplexHom Λ f A.as B.as))) ≫
        Qh.map (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
          (f)^*⟦Λ⟧).app A).app B) := by
        simp only [Category.assoc]
        erw [hδ, Category.comp_id]
    _ = _ := by
        erw [h]
        exact Category.assoc _ _ _


set_option synthInstance.maxHeartbeats 400000 in
-- the K-flat derivability structure on complexes of module objects is found by instance search
/-- Every object of `D(Mod_{Λ_Y})` is isomorphic to the image of a K-flat complex. -/
lemma exists_kFlat_iso_Qh_obj (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    ∃ P, (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat P ∧
      Nonempty (DerivedCategory.Qh.obj P ≅ K) := by
  have := isLeftDerivabilityStructure_localizerMorphismKFlat Λ Y
  have := Localization.essSurj (DerivedCategory.Qh (C := Mod (Sheaf (Scheme.ProEt.topology Y)
    Ab.{u + 1}) (condensedRingObj Λ Y))) (HomotopyCategory.quasiIso _ (.up ℤ))
  obtain ⟨R⟩ := LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
    (Φ := (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat)
    (DerivedCategory.Qh.objPreimage K)
  have : IsIso (DerivedCategory.Qh.map R.w) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _ R.hw
  exact ⟨R.X₁.obj, R.X₁.property,
    ⟨asIso (DerivedCategory.Qh.map R.w) ≪≫ DerivedCategory.Qh.objObjPreimageIso K⟩⟩

set_option synthInstance.maxHeartbeats 400000 in
-- the K-flat derivability structure on complexes of module objects is found by instance search
set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- On K-flat complexes, the comparison `m` is an isomorphism: both counits are isomorphisms. -/
lemma isIso_leftDerivedUpperStarTensor_app_app_Qh_obj
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    (hA : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat ((HomotopyCategory.quotient _ _).obj A))
    (hB : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat ((HomotopyCategory.quotient _ _).obj B)) :
    IsIso (((leftDerivedUpperStarTensor Λ f).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj A))).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj B))) := by
  have := isIso_leftDerivedUpperStarTensorRightCounit_app_app Λ f A B hA hB
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh ((HomotopyCategory.quotient _ _).obj A)
      ((HomotopyCategory.quotient _ _).obj B)) :=
    isIso_μNatTrans_Qh_app_app_of_kFlat ((HomotopyCategory.quotient _ _).obj A)
      ((HomotopyCategory.quotient _ _).obj B) hB
  have := (f)^*⟦Λ⟧.isIso_leftDerivedFunctorCounit_app_of_kFlat' _
    ((HomotopyCategory.quasiIso _ (.up ℤ)).kFlat.prop_tensor hA hB)
  have hL : IsIso (((leftDerivedUpperStarTensorLeftCounit Λ f).app
      ((HomotopyCategory.quotient _ _).obj A)).app ((HomotopyCategory.quotient _ _).obj B)) :=
    IsIso.comp_isIso' (Functor.map_isIso L((f)^*⟦Λ⟧) (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient _ _).obj A) ((HomotopyCategory.quotient _ _).obj B)))
      inferInstance
  have h := congr_app (congr_app (leftDerivedUpperStarTensor_fac Λ f)
    ((HomotopyCategory.quotient _ _).obj A)) ((HomotopyCategory.quotient _ _).obj B)
  rw [NatTrans.comp_app, NatTrans.comp_app] at h
  have : IsIso ((((leftDerivedUpperStarTensor Λ f).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj A))).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj B))) ≫
      ((leftDerivedUpperStarTensorRightCounit Λ f).app
        ((HomotopyCategory.quotient _ _).obj A)).app ((HomotopyCategory.quotient _ _).obj B)) := by
    rw [← h] at hL
    exact hL
  exact IsIso.of_isIso_comp_right _ (((leftDerivedUpperStarTensorRightCounit Λ f).app
    ((HomotopyCategory.quotient _ _).obj A)).app ((HomotopyCategory.quotient _ _).obj B))

set_option synthInstance.maxHeartbeats 400000 in
-- the K-flat derivability structure on complexes of module objects is found by instance search
/-- The comparison `m : Lf^* (- ⊗ᴸ -) ⟶ Lf^* - ⊗ᴸ Lf^* -` is an isomorphism: every object is
isomorphic to the image of a K-flat complex, on which `m` is an isomorphism
(`isIso_leftDerivedUpperStarTensor_app_app_Qh_obj`). -/
instance isIso_leftDerivedUpperStarTensor : IsIso (leftDerivedUpperStarTensor Λ f) := by
  have hQ (P Q : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) (.up ℤ))
      (hP : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat P)
      (hQ : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat Q) :
      IsIso (((leftDerivedUpperStarTensor Λ f).app (DerivedCategory.Qh.obj P)).app
        (DerivedCategory.Qh.obj Q)) := by
    obtain ⟨P, rfl⟩ := P.quotient_obj_surjective
    obtain ⟨Q, rfl⟩ := Q.quotient_obj_surjective
    exact isIso_leftDerivedUpperStarTensor_app_app_Qh_obj Λ f P Q hP hQ
  have (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
      IsIso ((leftDerivedUpperStarTensor Λ f).app K) := by
    obtain ⟨P, hP, ⟨e⟩⟩ := exists_kFlat_iso_Qh_obj Λ K
    have (M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
        IsIso (((leftDerivedUpperStarTensor Λ f).app (DerivedCategory.Qh.obj P)).app M) := by
      obtain ⟨Q, hQ', ⟨e'⟩⟩ := exists_kFlat_iso_Qh_obj Λ M
      have := hQ P Q hP hQ'
      exact NatTrans.isIso_app_of_iso _ e'.symm
    have : IsIso ((leftDerivedUpperStarTensor Λ f).app (DerivedCategory.Qh.obj P)) :=
      NatIso.isIso_of_isIso_app _
    exact NatTrans.isIso_app_of_iso _ e.symm
  exact NatIso.isIso_of_isIso_app _

/-- The comparison isomorphism `m_{K,L} : Lf^* (K ⊗ᴸ L) ≅ Lf^* K ⊗ᴸ Lf^* L` of the derived
pullback with the derived tensor product. -/
noncomputable def leftDerivedUpperStarTensorIso :
    leftDerivedUpperStarTensorLeft Λ f ≅ leftDerivedUpperStarTensorRight Λ f :=
  asIso (leftDerivedUpperStarTensor Λ f)

/-! ### The monoidal structure -/

/-- The derived pullback of the tensor unit `Λ_Y` is the tensor unit `Λ_X`: the counit
`Lf^* (Qh 𝟙) ≅ Qh (f^* 𝟙)` of the derived pullback of the exact functor `f^*`, followed by the
unit comparison `f^* 𝟙 ≅ 𝟙` of the strong monoidal pullback of module objects, in degree `0`. -/
noncomputable def leftDerivedUpperStarUnitIso :
    L((f)^*⟦Λ⟧).obj (𝟙_ _) ≅ 𝟙_ _ :=
  asIso ((f)^*⟦Λ⟧.leftDerivedFunctorCounit.app (𝟙_ _)) ≪≫
    DerivedCategory.Qh.mapIso
      (((f)^*⟦Λ⟧.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app (𝟙_ _) ≪≫
        (HomotopyCategory.quotient _ _).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex (f)^*⟦Λ⟧
              (ComplexShape.up ℤ) 0).app (𝟙_ _) ≪≫
            (HomologicalComplex.single _ _ 0).mapIso (Functor.Monoidal.εIso (f)^*⟦Λ⟧).symm))

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The compatibility of the comparison `m` with the comonoidal structure of `f^*` on the
homotopy category, in the form of the hypothesis of
`CategoryTheory.Functor.OplaxMonoidal.ofLaxSquare'`. -/
lemma leftDerivedUpperStarTensor_laxSquare (A B : HomotopyCategory
    (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) (ComplexShape.up ℤ)) :
    ((leftDerivedUpperStarTensor Λ f).app (DerivedCategory.Qh.obj A)).app
        (DerivedCategory.Qh.obj B) ≫
      ((f)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ⊗ₘ (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app B) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Qh
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) =
      L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A B) ≫
        (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app (A ⊗ B) ≫
        DerivedCategory.Qh.map
          (Functor.OplaxMonoidal.δ ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)) A B) := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc]
  exact leftDerivedUpperStarTensor_app_app_fac Λ f A B

end AlgebraicGeometry.ProEtale.CondensedRing
