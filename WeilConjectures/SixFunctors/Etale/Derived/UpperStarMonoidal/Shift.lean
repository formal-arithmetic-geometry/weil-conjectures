/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidalShift
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!
# The tensor comparison of the derived pullback commutes with shifts

For `g : Z ⟶ Y`, the comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison`) commutes with the shifts in
each variable.
-/

@[expose] public section

universe w v u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace DerivedCategory

section

variable (C : Type*) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

local instance : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

variable [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

variable {C}

lemma commShift_tensorLeftCounit
    (X : HomotopyCategory C (.up ℤ)) (hX : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat X) :
    NatTrans.CommShift (tensorLeftCounit X) ℤ := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have hP := (HomotopyCategory.kFlat_quotient_obj_iff _).1 hX
  have e := commShiftTensorLeft_eq C ⟨P, hP⟩
  let := commShiftTensorLeftQhObj ((HomotopyCategory.quotient C _).obj P) hX
  have := isIso_tensorLeftCounit ((HomotopyCategory.quotient C _).obj P) hX
  let : Localization.Lifting Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((curriedTensor _).obj ((HomotopyCategory.quotient C _).obj P) ⋙ Qh)
      ((curriedTensor _).obj (Qh.obj ((HomotopyCategory.quotient C _).obj P))) :=
    ⟨asIso (tensorLeftCounit _)⟩
  have h := NatTrans.commShift_iso_hom_of_localization Qh (HomotopyCategory.quasiIso C (.up ℤ)) ℤ
    ((curriedTensor _).obj ((HomotopyCategory.quotient C _).obj P) ⋙ Qh)
    ((curriedTensor (DerivedCategory C)).obj
      (Qh.obj ((HomotopyCategory.quotient C _).obj P)))
  convert h using 1
  · rfl
  · congr 1

lemma commShift_tensorRightCounit
    (X : HomotopyCategory C (.up ℤ)) (hX : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat X) :
    NatTrans.CommShift (tensorRightCounit X) ℤ := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have hP := (HomotopyCategory.kFlat_quotient_obj_iff _).1 hX
  have e := commShiftTensorRight_eq C ⟨P, hP⟩
  let := commShiftTensorRightQhObj ((HomotopyCategory.quotient C _).obj P) hX
  have := isIso_tensorRightCounit ((HomotopyCategory.quotient C _).obj P) hX
  let : Localization.Lifting Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((curriedTensor _).flip.obj ((HomotopyCategory.quotient C _).obj P) ⋙ Qh)
      ((curriedTensor _).flip.obj (Qh.obj ((HomotopyCategory.quotient C _).obj P))) :=
    ⟨asIso (tensorRightCounit _)⟩
  have h := NatTrans.commShift_iso_hom_of_localization Qh (HomotopyCategory.quasiIso C (.up ℤ)) ℤ
    ((curriedTensor _).flip.obj ((HomotopyCategory.quotient C _).obj P) ⋙ Qh)
    ((curriedTensor (DerivedCategory C)).flip.obj
      (Qh.obj ((HomotopyCategory.quotient C _).obj P)))
  convert h using 1
  · rfl
  · congr 1

end

end DerivedCategory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

open DerivedCategory

/-- The counit `Qh ⋙ Lg^* ⟶ g^* ⋙ Qh` of the derived pullback commutes with the shifts. -/
instance commShift_leftDerivedFunctorCounit_upperStar :
    NatTrans.CommShift (g)^*[A].leftDerivedFunctorCounit ℤ := by
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).hom ℤ :=
    inferInstanceAs
      (NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.inv ℤ)
  rw [← (g)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  exact inferInstanceAs (NatTrans.CommShift (Functor.whiskerLeft Qh
    (leftDerivedUpperStarIsoMapDerivedCategory A g).hom ≫ _) ℤ)

section

variable [(g)^*[A].PreservesFlat]


/-- The tensor comparison `Lg^*(K ⊗ᴸ -) ⟶ Lg^*K ⊗ᴸ Lg^*(-)` for a fixed `K`. -/
noncomputable abbrev leftDerivedUpperStarTensorComparisonApp
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (-⊗ᴸ-(Y)[A]).obj K ⋙ L((g)^*[A]) ⟶ L((g)^*[A]) ⋙ (-⊗ᴸ-(Z)[A]).obj (L((g)^*[A]).obj K) :=
  (leftDerivedUpperStarTensorComparison A g).app K

lemma commShift_leftDerivedUpperStarTensorComparisonApp_of_iso
    {K K' : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (e : K ≅ K')
    [NatTrans.CommShift (leftDerivedUpperStarTensorComparisonApp A g K') ℤ] :
    NatTrans.CommShift (leftDerivedUpperStarTensorComparisonApp A g K) ℤ := by
  have eq : leftDerivedUpperStarTensorComparisonApp A g K =
      Functor.whiskerRight ((-⊗ᴸ-(Y)[A]).map e.hom) L((g)^*[A]) ≫
        leftDerivedUpperStarTensorComparisonApp A g K' ≫
        Functor.whiskerLeft L((g)^*[A]) ((-⊗ᴸ-(Z)[A]).map (L((g)^*[A]).map e.inv)) := by
    have := (leftDerivedUpperStarTensorComparison A g).naturality e.hom
    ext M
    have := congr_app this M
    dsimp at this ⊢
    rw [reassoc_of% this, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp,
      e.hom_inv_id]
    simp
  have : NatTrans.CommShift ((-⊗ᴸ-(Y)[A]).map e.hom) ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor _).map e.hom) ℤ)
  have : NatTrans.CommShift ((-⊗ᴸ-(Z)[A]).map (L((g)^*[A]).map e.inv)) ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor _).map (L((g)^*[A]).map e.inv)) ℤ)
  rw [eq]
  infer_instance

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

lemma leftDerivedUpperStarTensorComparison_eq :
    leftDerivedUpperStarTensorComparison A g =
      Functor.leftDerived₂NatTrans _ (derivedTensorLeftDerivedUpperStarCounit A g)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
        (leftDerivedUpperStarDerivedTensorCounit A g)
        (Functor.postcompose₂MapWhiskeringLeft₂
          (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh) :=
  rfl

/-- The defining property of the tensor comparison of `Lg^*`, on objects of the homotopy
category. -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_app_app_fac
    (X M : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :
    ((leftDerivedUpperStarTensorComparison A g).app (Qh.obj X)).app (Qh.obj M) ≫
        ((derivedTensorLeftDerivedUpperStarCounit A g).app X).app M =
      ((leftDerivedUpperStarDerivedTensorCounit A g).app X).app M ≫
        ((Functor.postcompose₂MapWhiskeringLeft₂
          (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh).app X).app M := by
  rw [leftDerivedUpperStarTensorComparison_eq]
  exact Functor.leftDerived₂NatTrans_app_app _ (derivedTensorLeftDerivedUpperStarCounit A g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedUpperStarDerivedTensorCounit A g)
    (Functor.postcompose₂MapWhiskeringLeft₂
      (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh) X M

open Functor in
set_option maxHeartbeats 1000000 in
lemma commShift_leftDerivedUpperStarTensorComparisonApp_Qh_obj
    (X : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ))
    (hX : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat X) (hgX : kFlatUpperStar A g X) :
    NatTrans.CommShift (leftDerivedUpperStarTensorComparisonApp A g (Qh.obj X)) ℤ := by
  let G := (g)^*[A].mapHomotopyCategory (.up ℤ)
  let cL := (g)^*[A].leftDerivedFunctorCounit
  let c₂ : Qh ⋙ ((-⊗ᴸ-(Y)[A]).obj (Qh.obj X) ⋙ L((g)^*[A])) ⟶
      ((curriedTensor _).obj X ⋙ G) ⋙ Qh :=
    (Functor.associator _ _ _).inv ≫ whiskerRight (tensorLeftCounit X) L((g)^*[A]) ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft ((curriedTensor _).obj X) cL ≫
      (Functor.associator _ _ _).inv
  let δ₀ : ((curriedTensor _).obj X ⋙ G) ⋙ Qh ⟶ (G ⋙ (curriedTensor _).obj (G.obj X)) ⋙ Qh :=
    whiskerRight ((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]).app X) Qh
  let c₁ : Qh ⋙ (L((g)^*[A]) ⋙ (-⊗ᴸ-(Z)[A]).obj (L((g)^*[A]).obj (Qh.obj X))) ⟶
      (G ⋙ (curriedTensor _).obj (G.obj X)) ⋙ Qh :=
    (Functor.associator _ _ _).inv ≫
      whiskerLeft (Qh ⋙ L((g)^*[A])) ((curriedTensor _).map (cL.app X)) ≫
      whiskerRight cL ((curriedTensor _).obj (Qh.obj (G.obj X))) ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft G (tensorLeftCounit (G.obj X)) ≫
      (Functor.associator _ _ _).inv
  have := isIso_tensorLeftCounit (G.obj X) hgX
  have : IsIso c₁ := by dsimp only [c₁]; infer_instance
  have fac : whiskerLeft Qh (leftDerivedUpperStarTensorComparisonApp A g (Qh.obj X)) ≫ c₁ =
      c₂ ≫ δ₀ := by
    ext M
    have key := leftDerivedUpperStarTensorComparison_app_app_fac A g X M
    have e₁ : c₁.app M = ((derivedTensorLeftDerivedUpperStarCounit A g).app X).app M := by
      simp [c₁, derivedTensorLeftDerivedUpperStarCounit]
      rfl
    have e₂ : (c₂ ≫ δ₀).app M = ((leftDerivedUpperStarDerivedTensorCounit A g).app X).app M ≫
          ((Functor.postcompose₂MapWhiskeringLeft₂
            (OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh).app X).app M := by
      simp [c₂, δ₀, leftDerivedUpperStarDerivedTensorCounit]
      rfl
    rw [NatTrans.comp_app, e₂, Functor.whiskerLeft_app, e₁]
    exact key
  have := commShift_tensorLeftCounit X hX
  have := commShift_tensorLeftCounit (G.obj X) hgX
  have : NatTrans.CommShift ((curriedTensor (DerivedCategory (Sheaf Z.smallEtaleTopology A))).map
      (cL.app X)) ℤ := inferInstance
  have : NatTrans.CommShift (whiskerLeft (Qh ⋙ L((g)^*[A]))
      ((curriedTensor (DerivedCategory (Sheaf Z.smallEtaleTopology A))).map (cL.app X))) ℤ :=
    inferInstance
  have : NatTrans.CommShift (whiskerRight cL ((curriedTensor _).obj (Qh.obj (G.obj X)))) ℤ :=
    inferInstance
  have : NatTrans.CommShift (whiskerLeft G (tensorLeftCounit (G.obj X))) ℤ :=
    inferInstance
  have : NatTrans.CommShift c₁ ℤ := by dsimp only [c₁]; infer_instance
  have : NatTrans.CommShift c₂ ℤ := by dsimp only [c₂]; infer_instance
  have := OplaxMonoidal.commShift_mapHomotopyCategoryδNatTrans_app (g)^*[A] X
  have : NatTrans.CommShift δ₀ ℤ := by dsimp only [δ₀]; infer_instance
  have : NatTrans.CommShift (inv c₁) ℤ := NatTrans.CommShift.of_isIso c₁ ℤ
  have : NatTrans.CommShift
      (whiskerLeft Qh (leftDerivedUpperStarTensorComparisonApp A g (Qh.obj X))) ℤ := by
    rw [(IsIso.eq_comp_inv c₁).2 fac]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ Qh
    (fun M ↦ ⟨Qh.objPreimage M, (Qh.objObjPreimageIso M).inv, inferInstance⟩)

/-- For a fixed `K`, the tensor comparison `Lg^*(K ⊗ᴸ -) ⟶ Lg^*K ⊗ᴸ Lg^*(-)` commutes with
the shifts. -/
instance commShift_leftDerivedUpperStarTensorComparisonApp
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    NatTrans.CommShift (leftDerivedUpperStarTensorComparisonApp A g K) ℤ := by
  let Λ := (inferInstance : HasFunctorialFlatResolution (Sheaf Y.smallEtaleTopology A)).some.reduced
  let K₀ := DerivedCategory.Q.objPreimage K
  let R := Λ.resolutionFunctor.obj K₀
  have hR := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K₀
  have hgR := kFlatUpperStar_quotient_obj_resolutionFunctor_obj A g Λ K₀
  have := commShift_leftDerivedUpperStarTensorComparisonApp_Qh_obj A g
    ((HomotopyCategory.quotient _ _).obj R) ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hR) hgR
  let e : K ≅ Qh.obj ((HomotopyCategory.quotient _ _).obj R) :=
    (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      (asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app K₀))).symm ≪≫
      (DerivedCategory.quotientCompQhIso _).symm.app R
  exact commShift_leftDerivedUpperStarTensorComparisonApp_of_iso A g e

/-- The tensor comparison `Lg^*(- ⊗ᴸ M) ⟶ Lg^*(-) ⊗ᴸ Lg^*M` for a fixed `M`. -/
noncomputable abbrev leftDerivedUpperStarTensorComparisonFlipApp
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (-⊗ᴸ-(Y)[A]).flip.obj M ⋙ L((g)^*[A]) ⟶
      L((g)^*[A]) ⋙ (-⊗ᴸ-(Z)[A]).flip.obj (L((g)^*[A]).obj M) :=
  (leftDerivedUpperStarTensorComparison A g).flipApp M

lemma commShift_leftDerivedUpperStarTensorComparisonFlipApp_of_iso
    {M M' : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (e : M ≅ M')
    [NatTrans.CommShift (leftDerivedUpperStarTensorComparisonFlipApp A g M') ℤ] :
    NatTrans.CommShift (leftDerivedUpperStarTensorComparisonFlipApp A g M) ℤ := by
  have eq : leftDerivedUpperStarTensorComparisonFlipApp A g M =
      Functor.whiskerRight ((-⊗ᴸ-(Y)[A]).flip.map e.hom) L((g)^*[A]) ≫
        leftDerivedUpperStarTensorComparisonFlipApp A g M' ≫
        Functor.whiskerLeft L((g)^*[A]) ((-⊗ᴸ-(Z)[A]).flip.map (L((g)^*[A]).map e.inv)) := by
    ext K
    have := ((leftDerivedUpperStarTensorComparison A g).app K).naturality e.hom
    dsimp at this ⊢
    rw [reassoc_of% this, ← Functor.map_comp, ← Functor.map_comp, e.hom_inv_id]
    simp
  have : NatTrans.CommShift ((-⊗ᴸ-(Y)[A]).flip.map e.hom) ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor _).flip.map e.hom) ℤ)
  have : NatTrans.CommShift ((-⊗ᴸ-(Z)[A]).flip.map (L((g)^*[A]).map e.inv)) ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor _).flip.map (L((g)^*[A]).map e.inv)) ℤ)
  rw [eq]
  infer_instance

open Functor in
set_option maxHeartbeats 1000000 in
lemma commShift_leftDerivedUpperStarTensorComparisonFlipApp_Qh_obj
    (X : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ))
    (hX : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat X) (hgX : kFlatUpperStar A g X) :
    NatTrans.CommShift (leftDerivedUpperStarTensorComparisonFlipApp A g (Qh.obj X)) ℤ := by
  let G := (g)^*[A].mapHomotopyCategory (.up ℤ)
  let cL := (g)^*[A].leftDerivedFunctorCounit
  let c₂ : Qh ⋙ ((-⊗ᴸ-(Y)[A]).flip.obj (Qh.obj X) ⋙ L((g)^*[A])) ⟶
      ((curriedTensor _).flip.obj X ⋙ G) ⋙ Qh :=
    (Functor.associator _ _ _).inv ≫ whiskerRight (tensorRightCounit X) L((g)^*[A]) ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft ((curriedTensor _).flip.obj X) cL ≫
      (Functor.associator _ _ _).inv
  let δ₀ : ((curriedTensor _).flip.obj X ⋙ G) ⋙ Qh ⟶
      (G ⋙ (curriedTensor _).flip.obj (G.obj X)) ⋙ Qh :=
    whiskerRight ((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]).flipApp X) Qh
  let c₁ : Qh ⋙ (L((g)^*[A]) ⋙ (-⊗ᴸ-(Z)[A]).flip.obj (L((g)^*[A]).obj (Qh.obj X))) ⟶
      (G ⋙ (curriedTensor _).flip.obj (G.obj X)) ⋙ Qh :=
    (Functor.associator _ _ _).inv ≫
      whiskerRight cL ((curriedTensor _).flip.obj (L((g)^*[A]).obj (Qh.obj X))) ≫
      whiskerLeft (G ⋙ Qh) ((curriedTensor _).flip.map (cL.app X)) ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft G (tensorRightCounit (G.obj X)) ≫
      (Functor.associator _ _ _).inv
  have := isIso_tensorRightCounit (G.obj X) hgX
  have : IsIso c₁ := by dsimp only [c₁]; infer_instance
  have fac : whiskerLeft Qh (leftDerivedUpperStarTensorComparisonFlipApp A g (Qh.obj X)) ≫ c₁ =
      c₂ ≫ δ₀ := by
    ext M
    have key := leftDerivedUpperStarTensorComparison_app_app_fac A g M X
    have e₁ : c₁.app M = ((derivedTensorLeftDerivedUpperStarCounit A g).app M).app X := by
      simp [c₁, derivedTensorLeftDerivedUpperStarCounit]
      rfl
    have e₂ : (c₂ ≫ δ₀).app M = ((leftDerivedUpperStarDerivedTensorCounit A g).app M).app X ≫
          ((Functor.postcompose₂MapWhiskeringLeft₂
            (OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh).app M).app X := by
      simp [c₂, δ₀, leftDerivedUpperStarDerivedTensorCounit]
      rfl
    rw [NatTrans.comp_app, e₂, Functor.whiskerLeft_app, e₁]
    exact key
  have := commShift_tensorRightCounit X hX
  have := commShift_tensorRightCounit (G.obj X) hgX
  have : NatTrans.CommShift ((curriedTensor
      (DerivedCategory (Sheaf Z.smallEtaleTopology A))).flip.map (cL.app X)) ℤ := inferInstance
  have : NatTrans.CommShift (whiskerLeft (G ⋙ Qh)
      ((curriedTensor (DerivedCategory (Sheaf Z.smallEtaleTopology A))).flip.map (cL.app X))) ℤ :=
    inferInstance
  have : NatTrans.CommShift (whiskerRight cL
      ((curriedTensor _).flip.obj (L((g)^*[A]).obj (Qh.obj X)))) ℤ :=
    inferInstance
  have : NatTrans.CommShift (whiskerLeft G (tensorRightCounit (G.obj X))) ℤ :=
    inferInstance
  have : NatTrans.CommShift c₁ ℤ := by dsimp only [c₁]; infer_instance
  have : NatTrans.CommShift c₂ ℤ := by dsimp only [c₂]; infer_instance
  have := OplaxMonoidal.commShift_mapHomotopyCategoryδNatTrans_flipApp (g)^*[A] X
  have : NatTrans.CommShift δ₀ ℤ := by dsimp only [δ₀]; infer_instance
  have : NatTrans.CommShift (inv c₁) ℤ := NatTrans.CommShift.of_isIso c₁ ℤ
  have : NatTrans.CommShift
      (whiskerLeft Qh (leftDerivedUpperStarTensorComparisonFlipApp A g (Qh.obj X))) ℤ := by
    rw [(IsIso.eq_comp_inv c₁).2 fac]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ Qh
    (fun M ↦ ⟨Qh.objPreimage M, (Qh.objObjPreimageIso M).inv, inferInstance⟩)

/-- For a fixed `M`, the tensor comparison `Lg^*(- ⊗ᴸ M) ⟶ Lg^*(-) ⊗ᴸ Lg^*M` commutes with
the shifts. -/
instance commShift_leftDerivedUpperStarTensorComparisonFlipApp
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    NatTrans.CommShift (leftDerivedUpperStarTensorComparisonFlipApp A g M) ℤ := by
  let Λ := (inferInstance : HasFunctorialFlatResolution (Sheaf Y.smallEtaleTopology A)).some.reduced
  let M₀ := DerivedCategory.Q.objPreimage M
  let R := Λ.resolutionFunctor.obj M₀
  have hR := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le M₀
  have hgR := kFlatUpperStar_quotient_obj_resolutionFunctor_obj A g Λ M₀
  have := commShift_leftDerivedUpperStarTensorComparisonFlipApp_Qh_obj A g
    ((HomotopyCategory.quotient _ _).obj R) ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hR) hgR
  let e : M ≅ Qh.obj ((HomotopyCategory.quotient _ _).obj R) :=
    (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
      (asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app M₀))).symm ≪≫
      (DerivedCategory.quotientCompQhIso _).symm.app R
  exact commShift_leftDerivedUpperStarTensorComparisonFlipApp_of_iso A g e


end

end Etale

end AlgebraicGeometry
