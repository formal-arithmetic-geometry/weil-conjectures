/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralResidueTensorModel
public import Sheaf.Paper.IntegralResidueOrdinaryTensorSquare
import Sheaf.Paper.IntegralResidueOrdinaryTensorNormalization
import Sheaf.Paper.IntegralResiduePullSquareData
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.Paper.IntegralResiduePullOrdinaryUnit

/-! Scalar-counit normalization for the residue pull square.

The tensor presentation on X has already been normalized to its defining counit.
Only the scalar mate and the ordinary balanced tensor comparison occur below.
-/

@[expose] public section

universe v u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

-- Private counit and mate calculations retained from the former flat-model proof.
section ProofCalculations
open CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
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
  unfold residueExchangeRestrictPullIso residueExchangeUpperStarCounit
    residueExchangeRestriction residueExchangeUpperStar
    leftDerivedUpperStarIsoMapDerivedCategory
  dsimp only [id_eq]
  have h := exactLeftSquareFac
    (Mod.comap (coefficientMap (integralReductionMap ℓ E) Y))
    ((f)^*⟦integralCoeff ℓ E⟧)
    ((f)^*⟦Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)⟧)
    (Mod.comap (coefficientMap (integralReductionMap ℓ E) X))
    (comapUpperStarIso (integralReductionMap ℓ E) f) N
  simpa only [derivedComapUpperStarIso, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc] using h



end AlgebraicGeometry.ProEtale.CondensedRing
end ProofCalculations

private theorem tensorPresentation_app
    {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ]
    (P : HomotopyCategory (Mod C R) (.up ℤ)) :
    (Mod.tensorPresentationDerivedCounit φ).app P =
      (Mod.comap φ).mapDerivedCategory.map ((Mod.extendScalars φ).leftDerivedFunctorCounit.app P) ≫
      (Mod.comap φ).mapDerivedCategoryFactorsh.hom.app
        (((Mod.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((Mod.tensorPresentationHomotopyIso φ).hom.app P) := by
  dsimp only [Mod.tensorPresentationDerivedCounit, Mod.extendComapCounit,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app]
  simp only [DerivedCategory.Qh.map_id, Category.assoc]
  erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
set_option maxHeartbeats 400000 in
-- The four concrete derived module functors occur in a single mate calculation.
private theorem scalar_mate_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    (residueExchangeReduction ℓ E X).map
        ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P) ≫
      (residueExchangeReductionCounit ℓ E X).app
          ((((f)^*⟦integralCoeff ℓ E⟧).mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory
          (pullIso (integralReductionMap ℓ E) f).hom (.up ℤ)).app P) =
    (residueExchangePullHom ℓ E f).app (DerivedCategory.Qh.obj P) ≫
      (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
          ((residueExchangeReductionCounit ℓ E Y).app P) ≫
      ((residueExchangeUpperStarCounit
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app
          (((Mod.extendScalars
            (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
              (.up ℤ)).obj P)) := by
  let F := (f)^*⟦integralCoeff ℓ E⟧
  let G := (f)^*⟦Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)⟧
  let TY := Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) Y)
  let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (integralReductionMap ℓ E) X)
  let SY := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (coefficientMap (integralReductionMap ℓ E) Y)
  let FP := (F.mapHomotopyCategory (.up ℤ)).obj P
  let TP := (TY.mapHomotopyCategory (.up ℤ)).obj P
  let ph := (NatTrans.mapHomotopyCategory
    (pullIso (integralReductionMap ℓ E) f).hom (.up ℤ)).app P
  let qh := (NatTrans.mapHomotopyCategory
    (comapUpperStarIso (integralReductionMap ℓ E) f).inv (.up ℤ)).app TP
  let ηX := ((Mod.extendRestrictAdjunction
    (coefficientMap (integralReductionMap ℓ E) X)).mapHomotopyCategory (.up ℤ)).unit.app FP
  let ηY := ((Mod.extendRestrictAdjunction
    (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory (.up ℤ)).unit.app P
  have hOrd := naturalOrdinaryFac
    (residueExchangeUpperStarCounit (integralCoeff ℓ E) f) ηY ηX
    ((SX.mapHomotopyCategory (.up ℤ)).map ph) qh
    (residueExchangePull_ordinary_unit ℓ E f P)
  have ho := SX.mapDerivedCategoryFactorsh.hom.naturality ph
  dsimp only [Functor.comp_map] at ho
  have hm := mateModel
    (residueExchangeReductionAdjunction ℓ E X)
    (residueExchangeReductionAdjunction ℓ E Y)
    (residueExchangeUpperStar (integralCoeff ℓ E) f)
    (residueExchangeUpperStar
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f)
    (residueExchangeRestrictPullIso ℓ E f).hom
    ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P)
    ((residueExchangeReductionCounit ℓ E X).app FP)
    (DerivedCategory.Qh.map ph)
    ((residueExchangeReductionCounit ℓ E Y).app P)
    ((residueExchangeUpperStarCounit
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app TP)
    (SX.mapDerivedCategoryFactorsh.hom.app _)
    (SX.mapDerivedCategoryFactorsh.hom.app _)
    (SY.mapDerivedCategoryFactorsh.hom.app TP)
    ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app _)
    (DerivedCategory.Qh.map qh)
    (DerivedCategory.Qh.map ηX) (DerivedCategory.Qh.map ηY)
    (DerivedCategory.Qh.map ((SX.mapHomotopyCategory (.up ℤ)).map ph))
    (reduction_unit_fac ℓ E X FP) (reduction_unit_fac ℓ E Y P)
    ho (restrict_pull_fac ℓ E f TP) hOrd
  unfold residueExchangePullHom
  exact hm


-- Normalize the inverse scalar mate, retaining ordinary restriction factors.
set_option maxHeartbeats 800000 in
-- Naturality compares the four derived functors with their homotopy models.
private theorem scalar_restriction_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    let F := (f)^*⟦integralCoeff ℓ E⟧
    let TX := Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) X)
    let TY := Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) Y)
    let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap (integralReductionMap ℓ E) X)
    let SY := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (coefficientMap (integralReductionMap ℓ E) Y)
    let FP := (F.mapHomotopyCategory (.up ℤ)).obj P
    let TP := (TY.mapHomotopyCategory (.up ℤ)).obj P
    let ph := (NatTrans.mapHomotopyCategory
      (pullIso (integralReductionMap ℓ E) f).inv (.up ℤ)).app P
    let qh := (NatTrans.mapHomotopyCategory
      (comapUpperStarIso (integralReductionMap ℓ E) f).inv (.up ℤ)).app TP
    (residueExchangeRestrictPullIso ℓ E f).hom.app
        ((residueExchangeReduction ℓ E Y).obj (DerivedCategory.Qh.obj P)) ≫
      (residueExchangeRestriction ℓ E X).map
        (((residueExchangePullComparisons ℓ E).pull f).inv.app (DerivedCategory.Qh.obj P)) ≫
      (residueExchangeRestriction ℓ E X).map
        ((residueExchangeReduction ℓ E X).map
          ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P)) ≫
      (residueExchangeRestriction ℓ E X).map
        ((residueExchangeReductionCounit ℓ E X).app FP) ≫
      SX.mapDerivedCategoryFactorsh.hom.app ((TX.mapHomotopyCategory (.up ℤ)).obj FP) =
    (residueExchangeUpperStar (integralCoeff ℓ E) f).map
        ((residueExchangeRestriction ℓ E Y).map
          ((residueExchangeReductionCounit ℓ E Y).app P) ≫
          SY.mapDerivedCategoryFactorsh.hom.app TP) ≫
      (residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app
        ((SY.mapHomotopyCategory (.up ℤ)).obj TP) ≫
      DerivedCategory.Qh.map (qh ≫ (SX.mapHomotopyCategory (.up ℤ)).map ph) := by
  dsimp only
  let F := (f)^*⟦integralCoeff ℓ E⟧
  let G := (f)^*⟦Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)⟧
  let TX := Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) X)
  let TY := Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) Y)
  let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (integralReductionMap ℓ E) X)
  let SY := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (coefficientMap (integralReductionMap ℓ E) Y)
  let FP := (F.mapHomotopyCategory (.up ℤ)).obj P
  let TP := (TY.mapHomotopyCategory (.up ℤ)).obj P
  let pH : (TX.mapHomotopyCategory (.up ℤ)).obj FP ≅
      (G.mapHomotopyCategory (.up ℤ)).obj TP :=
    { hom := (NatTrans.mapHomotopyCategory
        (pullIso (integralReductionMap ℓ E) f).hom (.up ℤ)).app P
      inv := (NatTrans.mapHomotopyCategory
        (pullIso (integralReductionMap ℓ E) f).inv (.up ℤ)).app P
      hom_inv_id := by
        rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp]
        simp
        rfl
      inv_hom_id := by
        rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp]
        simp
        rfl }
  have hm := scalar_mate_counit ℓ E f P
  have hmi : ((residueExchangePullComparisons ℓ E).pull f).inv.app
        (DerivedCategory.Qh.obj P) ≫
      (residueExchangeReduction ℓ E X).map
        ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P) ≫
      (residueExchangeReductionCounit ℓ E X).app FP =
    (residueExchangeUpperStar
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
        ((residueExchangeReductionCounit ℓ E Y).app P) ≫
      (residueExchangeUpperStarCounit
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app TP ≫
      DerivedCategory.Qh.map pH.inv := by
    have hi := ((residueExchangePullComparisons ℓ E).pull f).inv_hom_id_app
      (DerivedCategory.Qh.obj P)
    have hp : ((residueExchangePullComparisons ℓ E).pull f).hom.app
        (DerivedCategory.Qh.obj P) = (residueExchangePullHom ℓ E f).app
          (DerivedCategory.Qh.obj P) := by
      unfold residueExchangePullComparisons
      rfl
    rw [hp] at hi
    calc
      _ = ((residueExchangePullComparisons ℓ E).pull f).inv.app
            (DerivedCategory.Qh.obj P) ≫
          ((residueExchangeReduction ℓ E X).map
            ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P) ≫
            (residueExchangeReductionCounit ℓ E X).app FP ≫
            DerivedCategory.Qh.map pH.hom) ≫ DerivedCategory.Qh.map pH.inv := by
        simp only [Category.assoc, ← DerivedCategory.Qh.map_comp, Iso.hom_inv_id,
          DerivedCategory.Qh.map_id]
        erw [Category.comp_id]
      _ = _ := by
        rw [hm]
        simp only [← Category.assoc, hi, Category.id_comp]
        rfl
  have ho := SX.mapDerivedCategoryFactorsh.hom.naturality pH.inv
  have hq := restrict_pull_fac ℓ E f TP
  have hn := (residueExchangeRestrictPullIso ℓ E f).hom.naturality
    ((residueExchangeReductionCounit ℓ E Y).app P)
  dsimp only [Functor.comp_map] at hn ho
  simp only [← Functor.map_comp_assoc]
  rw [hmi]
  simp only [Functor.map_comp, Category.assoc]
  rw [ho]
  erw [← reassoc_of% hn]
  erw [reassoc_of% hq]


private theorem tensor_counit_app (T : Scheme.{u})
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) T)) (.up ℤ)) :
    let ε : DerivedCategory.Qh ⋙
        (residueExchangeReduction ℓ E T ⋙ residueExchangeRestriction ℓ E T) ⟶
      (tensorLeft (residueExchangeOrdinaryCoefficient ℓ E T)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh := by
      unfold residueExchangeReduction integralReduction residueExchangeRestriction
        residueExchangeOrdinaryCoefficient
      exact Mod.tensorPresentationDerivedCounit
        (coefficientMap (integralReductionMap ℓ E) T)
    ε.app P =
    (residueExchangeRestriction ℓ E T).map
      ((residueExchangeReductionCounit ℓ E T).app P) ≫
      (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategoryFactorsh.hom.app
        (((Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) T)).mapHomotopyCategory
          (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
        ((Mod.tensorPresentationHomotopyIso
          (coefficientMap (integralReductionMap ℓ E) T)).hom.app P) := by
  dsimp only
  unfold residueExchangeRestriction residueExchangeReductionCounit
    residueExchangeReduction integralReduction
  dsimp only [id]
  exact tensorPresentation_app (coefficientMap (integralReductionMap ℓ E) T) P

set_option linter.unusedVariables false in
-- Preserve the original public statement, including its auxiliary SX let.
set_option maxHeartbeats 800000 in
-- The counit calculation compares several composed concrete module functors.
/-- The scalar pull square, followed by the tensor-presentation counit on X,
computes the ordinary pullback model map. No derived tensor comparison occurs.

Source: Bhatt--Scholze, Remark 6.8.15 and the tensor-pullback identity in the
proof of Lemma 6.5.9(5), p. 51. The counit normalization below is the explicit
formal comparison argument, rather than a separately stated lemma of the paper.
(blueprint: new-integral-residue-scalar-counit-model)

Proof. Write F for integral pullback, G for residue pullback, S for restriction,
and T for extension of scalars; append subscripts X and Y for the sites. Write
Fh, Gh, Sh, Th for their homotopy functors and LF, LG, LT for the derived ones.
Let gamma denote their left-derived counits. Restriction and both pullbacks
are exact. Let q : SY then F -> G then SX be the ordinary restriction/pullback
isomorphism, and let p : F then TX -> TY then G be its inverse scalar-adjunction
mate. Its homotopy version is ph and its derived version is pd. The latter is
exactly residueExchangePullComparisons.pull.hom by the definition of PullHom.

First apply the mate unit identity and the defining unit identity of the
derived extension/restriction adjunction. Naturality of gamma and the triangle
identities give, at P,
pd(Qh P) followed by LG(gamma_TY(P)) followed by gamma_G(ThY P)
= LTX(gamma_F(P)) followed by gamma_TX(Fh P) followed by Qh(ph(P)).
To see this without choosing resolutions, transpose both sides along the
extension/restriction adjunction on X. Both transposes are q at the image of
P, followed by the ordinary extension unit; the exact-functor comparisons
commute with these units by the derived adjunction's defining unit formula.
The adjunction hom-equivalence is injective, giving the displayed equality.
Use the inverse of pd to rewrite it in the direction needed here, apply SX,
and compose with the exact restriction/pullback comparison.

Next expand epsilon_X = tensorPresentationDerivedCounit: it is the extension
counit gamma_TX, followed by exact restriction's comparison, followed by the
ordinary extendComapTensorIso. The previous identity cancels the scalar mate
in the claimed composite. What remains is the ordinary comparison between
pullback of the balanced tensor presentation on Y and that presentation on X.
The coefficient isomorphism e is q on the residue regular module, followed by
restriction of the inverse monoidal unit of G; eH is its homotopy image.
Consequently this remaining comparison is the ordinary tensor comparison for
F, after F applied to the Y presentation and after eH inverse on the first
factor. Explicitly, after forgetting module actions and precomposing with the
balanced tensor coequalizer epimorphism, both morphisms pull back the residue
coefficient and the module argument and apply the same scalar action. The
relations agree by naturality of coefficientMap. The inverse unit in e cancels
the pulled-back regular residue module. The coequalizer universal property
and faithfulness of forgetting actions therefore give equality of module
morphisms. Naturality makes this equality compatible with the differentials,
so it passes to homotopy complexes and then to Qh.

Finally combine this ordinary equality with the preceding counit identity.
The resulting composite is LF applied to the Y tensor-presentation counit,
then gamma_F, then Qh applied to Fh of homotopyTensorSingleIso inverse and the
ordinary oplax tensor comparison. This is tensorModelMap by definition, hence
residueExchangeTensorModelMap. No tensor-model target, tensor comparison, or
extension counit has been inverted. In particular the argument applies to
arbitrary P and requires no flatness hypothesis. -/
theorem integralResidue_scalarCounit_model {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    let F := (f)^*⟦integralCoeff ℓ E⟧
    let B := residueExchangeOrdinaryCoefficient ℓ E Y
    let B' := residueExchangeOrdinaryCoefficient ℓ E X
    let A := Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)
    let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap (integralReductionMap ℓ E) X)
    letI := residueOrdinaryUpperStarMonoidal A f
    let e : F.obj B ≅ B' :=
      residueOrdinaryRestrictedRegularPullIso (integralCoeff ℓ E) A
        (integralReductionMap ℓ E) f
    let eH : (F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B) ≅
      Functor.tensorModelCoefficient B' := (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor _ 0).obj B) ≪≫
      (HomotopyCategory.quotient _ (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app B ≪≫
          (HomologicalComplex.single _ (.up ℤ) 0).mapIso e)
    let φX := coefficientMap (integralReductionMap ℓ E) X
    let H := residueExchangeReduction ℓ E X ⋙ residueExchangeRestriction ℓ E X
    let εX : DerivedCategory.Qh ⋙ H ⟶
        (tensorLeft B').mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh := by
      unfold H B' residueExchangeOrdinaryCoefficient
        residueExchangeReduction integralReduction residueExchangeRestriction
      exact Mod.tensorPresentationDerivedCounit φX
    let M := DerivedCategory.Qh.obj P
    let a : (residueExchangeUpperStar (integralCoeff ℓ E) f).obj M ⟶
        DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj P) :=
      (residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P
    (residueExchangeRestrictPullIso ℓ E f).hom.app
          ((residueExchangeReduction ℓ E Y).obj M) ≫
      (residueExchangeRestriction ℓ E X).map
        (((residueExchangePullComparisons ℓ E).pull f).inv.app M) ≫
      H.map a ≫
      εX.app
        ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
        ((homotopyTensorSingleIso B').inv.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
          eH.inv ▷ (F.mapHomotopyCategory (.up ℤ)).obj P) =
      residueExchangeTensorModelMap ℓ E f P := by
  dsimp only
  have h := scalar_restriction_counit ℓ E f P
  have ho := residueOrdinaryTensorPull_homotopy (integralCoeff ℓ E)
    (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E))
    (integralReductionMap ℓ E) f P
  unfold residueExchangeTensorModelMap Functor.tensorModelMap
  dsimp only [id]
  erw [tensor_counit_app ℓ E X, tensor_counit_app ℓ E Y]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  dsimp only at h ho
  erw [reassoc_of% h]
  simp only [← DerivedCategory.Qh.map_comp, Category.assoc]
  have ho' := congrArg DerivedCategory.Qh.map ho
  erw [ho']
  have hn := (residueExchangeUpperStarCounit (integralCoeff ℓ E) f).naturality
    ((Mod.tensorPresentationHomotopyIso
      (coefficientMap (integralReductionMap ℓ E) Y)).hom.app P)
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hn]
  unfold residueExchangeUpperStar residueExchangeUpperStarCounit
  dsimp only [id]
end AlgebraicGeometry.ProEtale.CondensedRing
