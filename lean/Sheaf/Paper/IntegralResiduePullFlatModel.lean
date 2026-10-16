/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: SHEAF group B2
-/
module

public import Sheaf.Paper.IntegralResiduePullSquareData
import Sheaf.Paper.IntegralResiduePullbackPreservesFlat
import Sheaf.Paper.IntegralResiduePullOrdinaryUnit
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Computing residue pullback on flat complexes -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory.Obj CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
section ProofCalculations
section CachedInstances
variable (T : AlgebraicGeometry.Scheme.{u})
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
local notation "M" => Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab)
  (AlgebraicGeometry.ProEtale.condensedRingObj Λ T)
@[instance_reducible]
private noncomputable def cachedProofInstance1 : MonoidalCategory M := inferInstance
private theorem cachedProofInstance2 : MonoidalPreadditive M := inferInstance
omit [IsCommMonObj Λ] in
private theorem cachedProofInstance3 : HasCountableCoproducts M := inferInstance
omit [IsCommMonObj Λ] in
private theorem cachedProofInstance4 : HasColimitsOfShape ℤ M := inferInstance
private theorem cachedProofInstance5 : Abelian.HasFunctorialFlatResolution M := inferInstance
omit [IsCommMonObj Λ] in
private theorem cachedProofInstance6 : Abelian.HasKInjectiveResolutions M := inferInstance
omit [IsCommMonObj Λ] in
private theorem cachedProofInstance7 : HasExactColimitsOfShape ℤ M := inferInstance
private theorem cachedProofInstance8 : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ M),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
private theorem cachedProofInstance9 : ∀ (X₁ X₂ X₃ : GradedObject ℤ M),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
private theorem cachedProofInstance10 : ∀ (X₁ X₂ X₃ : GradedObject ℤ M),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
private theorem cachedProofInstance11 : ∀ (X : M),
    PreservesColimitsOfShape ℤ ((curriedTensor M).obj X) := inferInstance
private theorem cachedProofInstance12 : ∀ (X : M),
    PreservesColimitsOfShape ℤ ((curriedTensor M).flip.obj X) := inferInstance
end CachedInstances
attribute [local instance]
  cachedProofInstance1 cachedProofInstance2 cachedProofInstance3 cachedProofInstance4
  cachedProofInstance5 cachedProofInstance6 cachedProofInstance7 cachedProofInstance8
  cachedProofInstance9 cachedProofInstance10 cachedProofInstance11 cachedProofInstance12


private theorem exactSquareFac
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    [Limits.PreservesFiniteLimits I] [Limits.PreservesFiniteColimits I]
    (e : F ⋙ G ≅ H ⋙ I) (N : HomotopyCategory A (.up ℤ)) :
    ((mapDerivedCategoryCompIso F G).symm ≪≫ mapDerivedCategoryNatIso e ≪≫
      mapDerivedCategoryCompIso H I).hom.app (DerivedCategory.Qh.obj N) ≫
        I.mapDerivedCategory.map (H.mapDerivedCategoryFactorsh.hom.app N) ≫
        I.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj N) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app N) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app N) := by
  have hF := mapDerivedCategoryCompIso_fach F G N
  have hH := mapDerivedCategoryCompIso_fach H I N
  rw [mapHomotopyCategoryCompIso_refl_hom_app] at hF hH
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at hF hH
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [hH, mapDerivedCategoryNatIso_fach, ← hF]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private theorem exactSquareFacInv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : H ⋙ I ≅ F ⋙ G) (N : HomotopyCategory A (.up ℤ)) :
    ((mapDerivedCategoryCompIso F G).symm ≪≫ (mapDerivedCategoryNatIso e).symm ≪≫
      mapDerivedCategoryCompIso H I).hom.app (DerivedCategory.Qh.obj N) ≫
        I.mapDerivedCategory.map (H.mapDerivedCategoryFactorsh.hom.app N) ≫
        I.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj N) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app N) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app N) := by
  have h := exactSquareFac F G H I e.symm N
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    mapDerivedCategoryNatIso_symm] using h

private theorem liftedSquareFac
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (G G' : B ⥤ D) (H H' : A ⥤ C) (I : C ⥤ D)
    (eG : G' ≅ G) (eH : H' ≅ H) (q : F ⋙ G ≅ H ⋙ I)
    {N : A} {B₀ : B} {C₀ : C} {D₀ D₁ : D}
    (x : F.obj N ⟶ B₀) (u : G.obj B₀ ⟶ D₀)
    (v : H.obj N ⟶ C₀) (r : I.obj C₀ ⟶ D₁) (o : D₀ ⟶ D₁)
    (u' : G'.obj B₀ ⟶ D₀) (v' : H'.obj N ⟶ C₀)
    (hu : eG.hom.app B₀ ≫ u = u') (hv : eH.hom.app N ≫ v = v')
    (hq : q.hom.app N ≫ I.map v ≫ r = G.map x ≫ u ≫ o) :
    (isoWhiskerLeft F eG ≪≫ q ≪≫ isoWhiskerRight eH.symm I).hom.app N ≫
      I.map v' ≫ r =
      G'.map x ≫ u' ≫ o := by
  rw [← hu, ← hv]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Functor.map_comp, Category.assoc]
  rw [← I.map_comp_assoc, Iso.inv_hom_id_app, I.map_id, Category.id_comp, hq]
  rw [← eG.hom.naturality_assoc]

private theorem exactLeftSquareFac
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [MonoidalCategory A] [MonoidalPreadditive A] [HasCountableCoproducts A]
    [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution A]
    [MonoidalCategory B] [MonoidalPreadditive B] [HasCountableCoproducts B]
    [HasColimitsOfShape ℤ B] [HasExactColimitsOfShape ℤ B]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X : B), PreservesColimitsOfShape ℤ ((curriedTensor B).obj X)]
    [∀ (X : B), PreservesColimitsOfShape ℤ ((curriedTensor B).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution B]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : H ⋙ I ≅ F ⋙ G) (N : HomotopyCategory A (.up ℤ)) :
    (isoWhiskerLeft F.mapDerivedCategory G.leftDerivedFunctorIsoMapDerivedCategory ≪≫
      ((mapDerivedCategoryCompIso F G).symm ≪≫ (mapDerivedCategoryNatIso e).symm ≪≫
        mapDerivedCategoryCompIso H I) ≪≫
      isoWhiskerRight H.leftDerivedFunctorIsoMapDerivedCategory.symm
        I.mapDerivedCategory).hom.app (DerivedCategory.Qh.obj N) ≫
      I.mapDerivedCategory.map (H.leftDerivedFunctorCounit.app N) ≫
      I.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj N) =
    G.leftDerivedFunctor.map (F.mapDerivedCategoryFactorsh.hom.app N) ≫
      G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory (.up ℤ)).obj N) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app N) := by
  have hG := NatTrans.congr_app G.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((F.mapHomotopyCategory (.up ℤ)).obj N)
  have hH := NatTrans.congr_app H.leftDerivedFunctorIsoMapDerivedCategory_hom_fac N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hG hH
  exact liftedSquareFac F.mapDerivedCategory G.mapDerivedCategory
    G.leftDerivedFunctor H.mapDerivedCategory H.leftDerivedFunctor I.mapDerivedCategory
    G.leftDerivedFunctorIsoMapDerivedCategory H.leftDerivedFunctorIsoMapDerivedCategory
    ((mapDerivedCategoryCompIso F G).symm ≪≫ (mapDerivedCategoryNatIso e).symm ≪≫
      mapDerivedCategoryCompIso H I)
    (F.mapDerivedCategoryFactorsh.hom.app N)
    (G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj N))
    (H.mapDerivedCategoryFactorsh.hom.app N)
    (I.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj N))
    (DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app N))
    (G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory (.up ℤ)).obj N))
    (H.leftDerivedFunctorCounit.app N) hG hH (exactSquareFacInv F G H I e N)

private theorem transportedUnitFac
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {R S : B ⥤ A} (ad : L ⊣ R) (e : R ≅ S)
    {X Z : A} {Y : B} (a : L.obj X ⟶ Y) (s : S.obj Y ≅ Z)
    (u : X ⟶ Z) (v : Z ⟶ R.obj Y)
    (hu : ad.unit.app X ≫ R.map a = u ≫ v)
    (hv : v ≫ e.hom.app Y = s.inv) :
    (ad.ofNatIsoRight e).unit.app X ≫ S.map a ≫ s.hom = u := by
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  rw [Category.assoc, ← e.hom.naturality_assoc, ← Category.assoc, hu]
  simp only [Category.assoc]
  rw [reassoc_of% hv, Iso.inv_hom_id, Category.comp_id]

private theorem mixedDerivedUnitFac
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {R : D ⥤ C} [F.Additive] [R.Additive]
    [F.PreservesKFlatQuasiIso] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (adj : F ⊣ R) (H : HomotopyCategory C (.up ℤ)) :
    (adj.derivedAdjunction.ofNatIsoRight R.rightDerivedFunctorIsoMapDerivedCategory).unit.app
        (DerivedCategory.Qh.obj H) ≫
      R.mapDerivedCategory.map (F.leftDerivedFunctorCounit.app H) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj H) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app H) := by
  have h₁ := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (L₁ := DerivedCategory.Qh) (L₂ := DerivedCategory.Qh)
    (G' := F.leftDerivedFunctor) (F' := R.rightDerivedFunctor)
    (HomotopyCategory.quasiIso _ (.up ℤ)) F.leftDerivedFunctorCounit
    R.rightDerivedFunctorUnit H
  have h₃ := NatTrans.congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((F.mapHomotopyCategory (.up ℤ)).obj H)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₃
  exact transportedUnitFac adj.derivedAdjunction
    R.rightDerivedFunctorIsoMapDerivedCategory (F.leftDerivedFunctorCounit.app H)
    (R.mapDerivedCategoryFactorsh.app ((F.mapHomotopyCategory (.up ℤ)).obj H))
    (DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app H))
    (R.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj H)) h₁ h₃

private theorem mateModel
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {LX : C ⥤ D} {RX : D ⥤ C} {LY : C' ⥤ D'} {RY : D' ⥤ C'}
    (adX : LX ⊣ RX) (adY : LY ⊣ RY)
    (U : C' ⥤ C) (V : D' ⥤ D) (q : RY ⋙ U ⟶ V ⋙ RX)
    {K : C'} {A Z₀ Z₁ Z₂ : C} {B : D'} {T₀ T₁ : D} {W : C'}
    (u : U.obj K ⟶ A) (a : LX.obj A ⟶ T₀) (o : T₀ ⟶ T₁)
    (s : LY.obj K ⟶ B) (v : V.obj B ⟶ T₁)
    (r₀ : RX.obj T₀ ⟶ Z₀) (r₁ : RX.obj T₁ ⟶ Z₁) [IsIso r₁]
    (w : RY.obj B ⟶ W) (t : U.obj W ⟶ Z₂) (qo : Z₂ ⟶ Z₁)
    (η₀ : A ⟶ Z₀) (η₁ : K ⟶ W) (on : Z₀ ⟶ Z₁)
    (hηX : adX.unit.app A ≫ RX.map a ≫ r₀ = η₀)
    (hηY : adY.unit.app K ≫ RY.map s ≫ w = η₁)
    (ho : RX.map o ≫ r₁ = r₀ ≫ on)
    (hq : q.app B ≫ RX.map v ≫ r₁ = U.map w ≫ t ≫ qo)
    (hOrd : u ≫ η₀ ≫ on = U.map η₁ ≫ t ≫ qo) :
    LX.map u ≫ a ≫ o =
      (((mateEquiv adY adX).symm (TwoSquare.mk _ _ _ _ q)).natTrans.app K) ≫
        V.map s ≫ v := by
  apply (adX.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  apply (cancel_mono r₁).1
  have hm := unit_mateEquiv_symm adY adX (TwoSquare.mk _ _ _ _ q) K
  change U.map (adY.unit.app K) ≫ q.app (LY.obj K) =
    adX.unit.app (U.obj K) ≫ RX.map
      (((mateEquiv adY adX).symm (TwoSquare.mk _ _ _ _ q)).natTrans.app K) at hm
  rw [← reassoc_of% adX.unit.naturality u]
  simp only [comp_obj] 
  rw [← reassoc_of% hm]
  have hn := q.naturality s
  dsimp only [Functor.comp_map, comp_obj] at hn
  simp only [Category.assoc]
  rw [ho]
  rw [reassoc_of% hηX]
  rw [← reassoc_of% hn, hq]
  rw [← U.map_comp_assoc, ← U.map_comp_assoc, Category.assoc, hηY]
  exact hOrd


private theorem naturalOrdinaryFac
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {Q : A ⥤ B} {F : A ⥤ C} {G : B ⥤ D} {R : C ⥤ D}
    (c : Q ⋙ G ⟶ F ⋙ R) {X Y : A} {Z W : C}
    (η : X ⟶ Y) (ηX : F.obj X ⟶ Z) (on : Z ⟶ W) (qo : F.obj Y ⟶ W)
    (h : F.map η ≫ qo = ηX ≫ on) :
    c.app X ≫ R.map ηX ≫ R.map on =
      G.map (Q.map η) ≫ c.app Y ≫ R.map qo := by
  have hn := c.naturality η
  dsimp only [Functor.comp_map] at hn
  rw [← R.map_comp, ← h, R.map_comp, ← Category.assoc, ← hn, Category.assoc]

namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]


private theorem reduction_unit_fac (T : Scheme.{u})
    (H : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) T)) (.up ℤ)) :
    (residueExchangeReductionAdjunction ℓ E T).unit.app (DerivedCategory.Qh.obj H) ≫
      (residueExchangeRestriction ℓ E T).map
        ((residueExchangeReductionCounit ℓ E T).app H) ≫
      (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategoryFactorsh.hom.app
          (((Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) T)).mapHomotopyCategory
            (.up ℤ)).obj H) =
      DerivedCategory.Qh.map
        (((Mod.extendRestrictAdjunction
          (coefficientMap (integralReductionMap ℓ E) T)).mapHomotopyCategory
            (.up ℤ)).unit.app H) := by
  unfold residueExchangeReductionAdjunction residueExchangeReductionCounit
    residueExchangeRestriction residueExchangeReduction integralReduction
  dsimp only [id_eq]
  exact mixedDerivedUnitFac
    (Mod.extendRestrictAdjunction (coefficientMap (integralReductionMap ℓ E) T)) H



private theorem restrict_pull_fac {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) Y))
      (.up ℤ)) :
    (residueExchangeRestrictPullIso ℓ E f).hom.app (DerivedCategory.Qh.obj N) ≫
      (residueExchangeRestriction ℓ E X).map
        ((residueExchangeUpperStarCounit
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app N) ≫
      (Mod.comap (coefficientMap (integralReductionMap ℓ E) X)).mapDerivedCategoryFactorsh.hom.app
        ((((f)^*⟦Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)⟧).mapHomotopyCategory
          (.up ℤ)).obj N) =
      (residueExchangeUpperStar (integralCoeff ℓ E) f).map
        ((Mod.comap
          (coefficientMap (integralReductionMap ℓ E) Y)).mapDerivedCategoryFactorsh.hom.app N) ≫
        (residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app
          (((Mod.comap (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
            (.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory
            (comapUpperStarIso (integralReductionMap ℓ E) f).inv (.up ℤ)).app N) := by
  sorry



end AlgebraicGeometry.ProEtale.CondensedRing
end ProofCalculations

namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

set_option maxHeartbeats 400000 in
-- The final mate application compares four concrete homotopy-category composites.
/-- On a flat-resolution complex the derived pull mate is the ordinary scalar comparison.

Source: Bhatt--Scholze, Remark 6.8.15, derived scalar extension on flat resolutions.
(blueprint: new-integral-residue-pull-flat-model)

Proof. Inverse image of sheaves is exact and preserves colimits. Pullback of the
coefficient ring is identified with the coefficient ring on the source. Thus pullback
preserves flat objects (this can be checked on stalks, where it is scalar extension).
The hypothesis presents P as a colimit of bounded above flat complexes. Pullback
preserves that presentation and its terms are flat; therefore its image is K-flat by
`kFlat_mapHomologicalComplex_obj_of_colimitsOfShape`. Consequently the extension counit
on the pulled complex is invertible. Compare the two maps in the second clause by
transposing under extension/restriction of scalars. The derived adjunction unit and
counit factorization equations and the localization factors for exact pullback reduce
this equality to the ordinary scalar square. The ordinary pull isomorphism is the
conjugate of restriction/pushforward. The ordinary unit identity is isolated in
`residueExchangePull_ordinary_unit`; it is the degreewise geometric/scalar mate
compatibility. Applying this identity gives the homotopy comparison;
localization gives the displayed equation. No residue flatness is used: only the input
resolution and its pullback need compute derived scalar extension. -/
theorem residueExchangePull_flatModel
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hcolim : ObjectProperty.flat.cochainComplexMinus.colimitsOfShape ℤ P) :
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj P
    IsIso ((residueExchangeReductionCounit ℓ E X).app
        ((((f)^*⟦integralCoeff ℓ E⟧).mapHomotopyCategory (.up ℤ)).obj H)) ∧
    (residueExchangeReduction ℓ E X).map
        ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app H) ≫
      (residueExchangeReductionCounit ℓ E X).app
          ((((f)^*⟦integralCoeff ℓ E⟧).mapHomotopyCategory (.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory
          (pullIso (integralReductionMap ℓ E) f).hom (.up ℤ)).app H) =
    (residueExchangePullHom ℓ E f).app (DerivedCategory.Qh.obj H) ≫
      (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
          ((residueExchangeReductionCounit ℓ E Y).app H) ≫
      ((residueExchangeUpperStarCounit
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app
          (((Mod.extendScalars
            (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
              (.up ℤ)).obj H)) := by
  sorry



end AlgebraicGeometry.ProEtale.CondensedRing
