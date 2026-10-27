/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.CategoryTheory.CechCoefficientComparisonData
import Sheaf.CategoryTheory.CechCoefficientStrictMaps
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import
  WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-! # Proof of the coherent Čech coefficient comparison. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true

universe u wX wXp wY wYp wS wSp
universe a b va vb

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace CategoryTheory

private noncomputable instance cech_module_abelian
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : Abelian (ringedSiteModules.{u} R) := inferInstance

section ComparisonCalculation

universe a' b' va' vb' wa wb wa' wb'
variable {A : Type a} {B : Type b} {A' : Type a'} {B' : Type b'}
  [Category.{va} A] [Category.{vb} B] [Category.{va'} A'] [Category.{vb'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
  [HasDerivedCategory.{wa'} A'] [HasDerivedCategory.{wb'} B']

set_option backward.isDefEq.respectTransparency false in
private theorem cech_comparison_equation
    (F : A ⥤ B) (G : A' ⥤ B') (U : A ⥤ A') (V : B ⥤ B')
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (c : F ⋙ V ≅ U ⋙ G) (RF : CechCoefficientDerivedPair F)
    (RG : CechCoefficientDerivedPair G)
    (γ : RF.functor ⋙ V.mapDerivedCategory ⟶ U.mapDerivedCategory ⋙ RG.functor)
    (hγ : CechCoefficientUnitEquation F G U V c RF RG γ)
    {P I : CochainComplex A ℤ} {I' : CochainComplex A' ℤ}
    (a : P ⟶ I) [QuasiIso a]
    (a' : (U.mapHomologicalComplex (.up ℤ)).obj P ⟶ I') [QuasiIso a']
    (t : (U.mapHomologicalComplex (.up ℤ)).obj I ⟶ I')
    (ht : DerivedCategory.Q.map ((U.mapHomologicalComplex (.up ℤ)).map a) ≫
      DerivedCategory.Q.map t = DerivedCategory.Q.map a')
    (e : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
      RF.functor.obj (DerivedCategory.Q.obj P))
    (e' : DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj I') ≅
      RG.functor.obj (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj P)))
    (he : IsCechResolutionComparison F RF a e)
    (he' : IsCechResolutionComparison G RG a' e') :
    V.mapDerivedCategory.map e.inv ≫
        V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app I) ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map t) =
      γ.app (DerivedCategory.Q.obj P) ≫
        RG.functor.map (U.mapDerivedCategoryFactors.hom.app P) ≫ e'.inv := by
  apply (cancel_epi (V.mapDerivedCategory.map e.hom)).mp
  apply (cancel_mono (e'.hom ≫ RG.functor.map (DerivedCategory.Q.map a'))).mp
  simp only [← V.mapDerivedCategory.map_comp_assoc, Iso.hom_inv_id, Functor.map_id,
    Category.id_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [show e'.hom ≫ RG.functor.map (DerivedCategory.Q.map a') = RG.unit.app I' from he']
  have hn := RG.unit.naturality t
  dsimp only [Functor.comp_map] at hn
  have hfac := U.mapDerivedCategoryFactors.hom.naturality a
  have hnat := γ.naturality (DerivedCategory.Q.map a)
  dsimp only [Functor.comp_map] at hfac hnat
  have heq : e.hom ≫ RF.functor.map (DerivedCategory.Q.map a) = RF.unit.app I := he
  have hh : U.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map a' =
      U.mapDerivedCategory.map (DerivedCategory.Q.map a) ≫
        U.mapDerivedCategoryFactors.hom.app I ≫ DerivedCategory.Q.map t := by
    rw [← ht, ← Category.assoc, ← hfac, Category.assoc]
  symm
  simp only [← RG.functor.map_comp]
  rw [hh]
  simp only [RG.functor.map_comp]
  rw [← reassoc_of% hnat, ← V.mapDerivedCategory.map_comp_assoc, heq, reassoc_of% (hγ I)]
  simp only [← RG.functor.map_comp, Iso.inv_hom_id_app_assoc]
  rw [← hn]



set_option backward.isDefEq.respectTransparency false in
private theorem cech_augmentation_equation
    (F : A ⥤ B) (G : A' ⥤ B') (U : A ⥤ A') (V : B ⥤ B')
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (c : F ⋙ V ≅ U ⋙ G) (RF : CechCoefficientDerivedPair F)
    (RG : CechCoefficientDerivedPair G)
    (γ : RF.functor ⋙ V.mapDerivedCategory ⟶ U.mapDerivedCategory ⋙ RG.functor)
    (hγ : CechCoefficientUnitEquation F G U V c RF RG γ)
    {P I : CochainComplex A ℤ} {I' : CochainComplex A' ℤ}
    (a : P ⟶ I) [QuasiIso a]
    (a' : (U.mapHomologicalComplex (.up ℤ)).obj P ⟶ I') [QuasiIso a']
    (t : (U.mapHomologicalComplex (.up ℤ)).obj I ⟶ I')
    (ht : DerivedCategory.Q.map ((U.mapHomologicalComplex (.up ℤ)).map a) ≫
      DerivedCategory.Q.map t = DerivedCategory.Q.map a')
    (e : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
      RF.functor.obj (DerivedCategory.Q.obj P))
    (e' : DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj I') ≅
      RG.functor.obj (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj P)))
    (he : IsCechResolutionComparison F RF a e)
    (he' : IsCechResolutionComparison G RG a' e')
    {T : CochainComplex B ℤ} {T' : CochainComplex B' ℤ}
    (b : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ T)
    (b' : (G.mapHomologicalComplex (.up ℤ)).obj I' ⟶ T')
    (β : (V.mapHomologicalComplex (.up ℤ)).obj T ⟶ T')
    (hb : (V.mapHomologicalComplex (.up ℤ)).map b ≫ β =
      (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app I ≫
        (G.mapHomologicalComplex (.up ℤ)).map t ≫ b') :
    V.mapDerivedCategory.map (e.inv ≫ DerivedCategory.Q.map b) ≫
        V.mapDerivedCategoryFactors.hom.app T ≫ DerivedCategory.Q.map β =
      γ.app (DerivedCategory.Q.obj P) ≫
        RG.functor.map (U.mapDerivedCategoryFactors.hom.app P) ≫
          e'.inv ≫ DerivedCategory.Q.map b' := by
  have h := cech_comparison_equation F G U V c RF RG γ hγ a a' t ht e e' he he'
  have hn := V.mapDerivedCategoryFactors.hom.naturality b
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← DerivedCategory.Q.map_comp, hb]
  simp only [Functor.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ DerivedCategory.Q.map b') h

end ComparisonCalculation

private theorem cech_kinjective_derives
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wY} B]
    (F : A ⥤ B) [F.Additive] :
    (CochainComplex.KInjectives.localizerMorphism A).Derives
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have hX : X.obj.IsKInjective := X.property
  have hY : Y.obj.IsKInjective := Y.property
  have hq : QuasiIso f.hom := hf
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp hq
  have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f.hom) := by
    rw [← he]
    exact (F.mapHomotopyEquiv e).quasiIso_hom
  change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f.hom))
  infer_instance

private theorem cech_pair_unit_isIso
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wX} A] [HasDerivedCategory.{wY} B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive]
    (RF : CechCoefficientDerivedPair F) (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso (RF.unit.app I) := by
  have := RF.universal
  exact (cech_kinjective_derives F).isIso_of_isRightDerivedFunctor RF.unit
    (CochainComplex.KInjectives.mk I)

private theorem cech_pair_nonempty
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wX} A] [HasDerivedCategory.{wY} B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive] :
    Nonempty (CechCoefficientDerivedPair F) := by
  have := (cech_kinjective_derives F).hasPointwiseRightDerivedFunctor
  exact ⟨{
    functor := (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived
      DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    unit := (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).totalRightDerivedUnit
      DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    universal := inferInstance }⟩

section DerivedExistence

universe a' b' va' vb' wa wb wa' wb'
variable {A : Type a} {B : Type b} {A' : Type a'} {B' : Type b'}
  [Category.{va} A] [Category.{vb} B] [Category.{va'} A'] [Category.{vb'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
  [HasDerivedCategory.{wa'} A'] [HasDerivedCategory.{wb'} B']

set_option backward.isDefEq.respectTransparency false in
private theorem cech_pair_comparison
    [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) (G : A' ⥤ B') (U : A ⥤ A') (V : B ⥤ B')
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (c : F ⋙ V ≅ U ⋙ G) (RF : CechCoefficientDerivedPair F)
    (RG : CechCoefficientDerivedPair G) :
    ∃ γ : RF.functor ⋙ V.mapDerivedCategory ⟶ U.mapDerivedCategory ⋙ RG.functor,
      CechCoefficientUnitEquation F G U V c RF RG γ := by
  let α := Functor.whiskerRight RF.unit V.mapDerivedCategory ≫
    (associator _ _ _).hom
  let τ : (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙
      V.mapDerivedCategory ⟶ DerivedCategory.Q ⋙ U.mapDerivedCategory ⋙ RG.functor :=
    (associator _ _ _).hom ≫
      Functor.whiskerLeft _ V.mapDerivedCategoryFactors.hom ≫
      (associator _ _ _).inv ≫
      Functor.whiskerRight
        (mapHomologicalComplexCompIso (Iso.refl (F ⋙ V)) (.up ℤ)).hom
        DerivedCategory.Q ≫
      Functor.whiskerRight (NatTrans.mapHomologicalComplex c.hom (.up ℤ))
        DerivedCategory.Q ≫
      Functor.whiskerRight
        (mapHomologicalComplexCompIso (Iso.refl (U ⋙ G)) (.up ℤ)).inv
        DerivedCategory.Q ≫
      (associator _ _ _).hom ≫
      Functor.whiskerLeft _ RG.unit ≫
      (associator _ _ _).inv ≫
      Functor.whiskerRight U.mapDerivedCategoryFactors.inv RG.functor ≫
      (associator _ _ _).hom
  have hα : (RF.functor ⋙ V.mapDerivedCategory).IsRightDerivedFunctor α
      (HomologicalComplex.quasiIso A (.up ℤ)) :=
    (CochainComplex.KInjectives.localizerMorphism A)
      |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure RF.unit
        (fun I ↦ by
          have := I.property
          exact cech_pair_unit_isIso F RF I.obj) V.mapDerivedCategory
  let := hα
  let γ := (RF.functor ⋙ V.mapDerivedCategory).rightDerivedDesc α
    (HomologicalComplex.quasiIso A (.up ℤ)) _ τ
  refine ⟨γ, ?_⟩
  intro P
  have hFV : (mapHomologicalComplexCompIso (Iso.refl (F ⋙ V)) (.up ℤ)).hom.app P =
      𝟙 _ := by ext; rfl
  have hUG : (mapHomologicalComplexCompIso (Iso.refl (U ⋙ G)) (.up ℤ)).inv.app P =
      𝟙 _ := by ext; rfl
  have hh := NatTrans.congr_app
    ((RF.functor ⋙ V.mapDerivedCategory).rightDerived_fac α
      (HomologicalComplex.quasiIso A (.up ℤ)) _ τ) P
  simpa [α, τ, hFV, hUG] using hh

private theorem cech_pair_resolution_comparison
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive]
    (RF : CechCoefficientDerivedPair F)
    {P I : CochainComplex A ℤ} (a : P ⟶ I) [QuasiIso a] [I.IsKInjective] :
    ∃ e : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
      RF.functor.obj (DerivedCategory.Q.obj P), IsCechResolutionComparison F RF a e := by
  let := cech_pair_unit_isIso F RF I
  refine ⟨asIso (RF.unit.app I) ≪≫
    (RF.functor.mapIso (asIso (DerivedCategory.Q.map a))).symm, ?_⟩
  dsimp [IsCechResolutionComparison]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem cech_column_comparison
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions A']
    (F : A ⥤ B) (G : A' ⥤ B') (U : A ⥤ A') (V : B ⥤ B')
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (c : F ⋙ V ≅ U ⋙ G)
    {P I : CochainComplex A ℤ} {I' : CochainComplex A' ℤ}
    (a : P ⟶ I) [QuasiIso a] [I.IsKInjective]
    (a' : (U.mapHomologicalComplex (.up ℤ)).obj P ⟶ I') [QuasiIso a']
    [I'.IsKInjective] (t : (U.mapHomologicalComplex (.up ℤ)).obj I ⟶ I')
    (ht : DerivedCategory.Q.map ((U.mapHomologicalComplex (.up ℤ)).map a) ≫
      DerivedCategory.Q.map t = DerivedCategory.Q.map a') :
    IsCechCoefficientColumnComparison F G U V c a a' t := by
  obtain ⟨RF⟩ := cech_pair_nonempty F
  obtain ⟨RG⟩ := cech_pair_nonempty G
  obtain ⟨γ, hγ⟩ := cech_pair_comparison F G U V c RF RG
  obtain ⟨e, he⟩ := cech_pair_resolution_comparison F RF a
  obtain ⟨e', he'⟩ := cech_pair_resolution_comparison G RG a'
  exact ⟨RF, RG, γ, e, e', hγ, he, he',
    cech_comparison_equation F G U V c RF RG γ hγ a a' t ht e e' he he'⟩

end DerivedExistence

private theorem cech_Q_map_surjective
    {A : Type a} [Category.{va} A] [Abelian A] [HasDerivedCategory.{wX} A]
    (K L : CochainComplex A ℤ) [L.IsKInjective] :
    Function.Surjective (DerivedCategory.Q.map : (K ⟶ L) → _) := by
  intro f
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (.up ℤ)).obj K) L).surjective
    ((DerivedCategory.quotientCompQhIso A).hom.app K ≫ f ≫
      (DerivedCategory.quotientCompQhIso A).inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective g
  refine ⟨g, ?_⟩
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso A).hom.app K),
    ← cancel_mono ((DerivedCategory.quotientCompQhIso A).inv.app L)]
  simpa using hg

private theorem cech_homotopy_of_Q_eq
    {A : Type a} [Category.{va} A] [Abelian A] [HasDerivedCategory.{wX} A]
    {K L : CochainComplex A ℤ} [L.IsKInjective] (f g : K ⟶ L)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) : Nonempty (Homotopy f g) := by
  refine ⟨HomotopyCategory.homotopyOfEq f g ?_⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (.up ℤ)).obj K) L).injective
  rw [← cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app L),
    DerivedCategory.quotientCompQhIso_hom_naturality,
    DerivedCategory.quotientCompQhIso_hom_naturality, h]

private theorem cech_nonnegative_resolution_lifts
    {A : Type a} [Category.{va} A] [Abelian A] [HasDerivedCategory.{wX} A]
    {P K L : CochainComplex A ℕ}
    (a : P ⟶ K) [QuasiIso a] [∀ n : ℕ, Injective (L.X n)] (c : P ⟶ L) :
    (∃ t : K ⟶ L,
      DerivedCategory.Q.map (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat) ≫
        DerivedCategory.Q.map (HomologicalComplex.extendMap t ComplexShape.embeddingUpNat) =
      DerivedCategory.Q.map (HomologicalComplex.extendMap c ComplexShape.embeddingUpNat)) ∧
    (∀ t₀ t₁ : K ⟶ L,
      DerivedCategory.Q.map (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat) ≫
          DerivedCategory.Q.map (HomologicalComplex.extendMap t₀ ComplexShape.embeddingUpNat) =
        DerivedCategory.Q.map (HomologicalComplex.extendMap c ComplexShape.embeddingUpNat) →
      DerivedCategory.Q.map (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat) ≫
          DerivedCategory.Q.map (HomologicalComplex.extendMap t₁ ComplexShape.embeddingUpNat) =
        DerivedCategory.Q.map (HomologicalComplex.extendMap c ComplexShape.embeddingUpNat) →
      Nonempty (Homotopy t₀ t₁)) := by
  let ae := HomologicalComplex.extendMap a ComplexShape.embeddingUpNat
  let ce := HomologicalComplex.extendMap c ComplexShape.embeddingUpNat
  constructor
  · obtain ⟨t, ht⟩ := cech_Q_map_surjective _
      (L.extend ComplexShape.embeddingUpNat)
      (inv (DerivedCategory.Q.map ae) ≫ DerivedCategory.Q.map ce)
    obtain ⟨t, rfl⟩ := (ComplexShape.embeddingUpNat.extendFunctor A).map_surjective t
    refine ⟨t, ?_⟩
    change DerivedCategory.Q.map
      (HomologicalComplex.extendMap t ComplexShape.embeddingUpNat) = _ at ht
    rw [ht]
    exact IsIso.hom_inv_id_assoc _ _
  · intro t₀ t₁ h₀ h₁
    have h : DerivedCategory.Q.map
        (HomologicalComplex.extendMap t₀ ComplexShape.embeddingUpNat) =
        DerivedCategory.Q.map
          (HomologicalComplex.extendMap t₁ ComplexShape.embeddingUpNat) :=
      (cancel_epi (DerivedCategory.Q.map ae)).mp (h₀.trans h₁.symm)
    exact ⟨(cech_homotopy_of_Q_eq _ _ h).some.ofExtend⟩

set_option backward.isDefEq.respectTransparency false in
private theorem cech_extend_lift_equation
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wY} B]
    (U : A ⥤ B) [U.Additive]
    {P I : CochainComplex A ℕ} {I' : CochainComplex B ℕ}
    (a : P ⟶ I) (c : (U.mapHomologicalComplex (.up ℕ)).obj P ⟶ I')
    (t : (U.mapHomologicalComplex (.up ℕ)).obj I ⟶ I')
    (ht : DerivedCategory.Q.map (HomologicalComplex.extendMap
        ((U.mapHomologicalComplex (.up ℕ)).map a) ComplexShape.embeddingUpNat) ≫
      DerivedCategory.Q.map (HomologicalComplex.extendMap t ComplexShape.embeddingUpNat) =
        DerivedCategory.Q.map (HomologicalComplex.extendMap c ComplexShape.embeddingUpNat)) :
    DerivedCategory.Q.map ((U.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat)) ≫
      DerivedCategory.Q.map (cechCoefficientExtendMap U t) =
        DerivedCategory.Q.map (cechCoefficientExtendMap U c) := by
  have hn := (ComplexShape.embeddingUpNat.mapExtendFunctorNatIso U).hom.naturality a
  change (U.mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat) ≫
        (I.mapExtendIso ComplexShape.embeddingUpNat U).hom =
      (P.mapExtendIso ComplexShape.embeddingUpNat U).hom ≫
        HomologicalComplex.extendMap ((U.mapHomologicalComplex (.up ℕ)).map a)
          ComplexShape.embeddingUpNat at hn
  dsimp only [cechCoefficientExtendMap]
  rw [Functor.map_comp, ← DerivedCategory.Q.map_comp_assoc, hn,
    DerivedCategory.Q.map_comp_assoc, ht, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem cech_exact_map_equation
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wX} A] [HasDerivedCategory.{wY} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y Z : CochainComplex A ℤ} (a : X ⟶ Y) (t : Y ⟶ Z) (c : X ⟶ Z)
    (h : DerivedCategory.Q.map a ≫ DerivedCategory.Q.map t = DerivedCategory.Q.map c) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map t) =
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map c) := by
  have hh := congrArg F.mapDerivedCategory.map h
  simp only [Functor.map_comp] at hh
  have hn (X Y : CochainComplex A ℤ) (f : X ⟶ Y) :
      F.mapDerivedCategory.map (DerivedCategory.Q.map f) ≫
        F.mapDerivedCategoryFactors.hom.app Y =
      F.mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) :=
    F.mapDerivedCategoryFactors.hom.naturality f
  apply (cancel_epi (F.mapDerivedCategoryFactors.hom.app X)).mp
  rw [← reassoc_of% (hn X Y a),
    ← hn Y Z t, ← Category.assoc, ← hn X Z c]
  exact congrArg (fun k ↦ k ≫ F.mapDerivedCategoryFactors.hom.app Z) hh

set_option backward.isDefEq.respectTransparency false in
private theorem cech_localized_lift_equation
    {C Y : Type u} [SmallCategory C] [SmallCategory Y]
    {J : GrothendieckTopology C} {L : GrothendieckTopology Y}
    {R R' : Sheaf J RingCat.{u}} {S S' : Sheaf L RingCat.{u}}
    {f : RingedToposMorphism R S} {f' : RingedToposMorphism R' S'}
    {φ : R' ⟶ R} {ψ : S' ⟶ S} {hd : f.direct = f'.direct}
    {D : CoherentCechImageModel R} {D' : CoherentCechImageModel R'}
    [HasDerivedCategory.{wXp} (ringedSiteModules.{u} R')]
    (E : CechCoefficientCommutations f f' φ ψ hd D D')
    (A : Sheaf J (Type u))
    [HasDerivedCategory.{wSp} (ringedSiteModules.{u} (elementRing R' A))]
    {P I : CochainComplex (ringedSiteModules.{u} R) ℤ}
    {I' : CochainComplex (ringedSiteModules.{u} R') ℤ}
    (a : P ⟶ I) (c : (cechCoefficientComplex φ (.up ℤ)).obj P ⟶ I')
    (t : (cechCoefficientComplex φ (.up ℤ)).obj I ⟶ I')
    (ht : DerivedCategory.Q.map ((cechCoefficientComplex φ (.up ℤ)).map a) ≫
      DerivedCategory.Q.map t = DerivedCategory.Q.map c) :
    DerivedCategory.Q.map ((cechCoefficientComplex (cechCoefficientRingMap φ A) (.up ℤ)).map
        ((cechColumnRestrictComplex D A).map a)) ≫
      DerivedCategory.Q.map (cechCoefficientLocalizedMap E A t) =
      DerivedCategory.Q.map ((cechCoefficientPullComplexIso E A P).hom ≫
        (cechColumnRestrictComplex D' A).map c) := by
  obtain ⟨sliceAdj⟩ := elementModuleExtension_adjunction R' A
  let := sliceAdj.isRightAdjoint
  let := (D'.adj A).isLeftAdjoint
  let : HasBinaryBiproducts (ringedSiteModules.{u} R') := Abelian.hasBinaryBiproducts
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (elementModulePullback R' A)
  let := Functor.additive_of_preservesBinaryBiproducts (elementModulePullback R' A)
  have hh := cech_exact_map_equation (elementModulePullback R' A)
    ((cechCoefficientComplex φ (.up ℤ)).map a) t c ht
  change DerivedCategory.Q.map ((cechColumnRestrictComplex D' A).map
      ((cechCoefficientComplex φ (.up ℤ)).map a)) ≫
    DerivedCategory.Q.map ((cechColumnRestrictComplex D' A).map t) =
      DerivedCategory.Q.map ((cechColumnRestrictComplex D' A).map c) at hh
  have hn : (cechCoefficientComplex (cechCoefficientRingMap φ A) (.up ℤ)).map
      ((cechColumnRestrictComplex D A).map a) ≫ (cechCoefficientPullComplexIso E A I).hom =
      (cechCoefficientPullComplexIso E A P).hom ≫
        (cechColumnRestrictComplex D' A).map ((cechCoefficientComplex φ (.up ℤ)).map a) := by
    ext1 q
    exact (E.pull A).hom.naturality (a.f q)
  dsimp only [cechCoefficientLocalizedMap]
  rw [Functor.map_comp, ← DerivedCategory.Q.map_comp_assoc, hn,
    DerivedCategory.Q.map_comp_assoc, hh, ← Functor.map_comp]

private theorem cech_resolution_lifts
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}} (φ : R' ⟶ R)
    [HasDerivedCategory.{wXp} (ringedSiteModules.{u} R')]
    [PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} φ)]
    [PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} φ)]
    (M : ringedSiteModules.{u} R) (I : InjectiveResolution M)
    (I' : InjectiveResolution ((SheafOfModules.restrictScalars φ).obj M)) :
    (∃ t : (cechCoefficientComplex φ (.up ℕ)).obj I.cocomplex ⟶ I'.cocomplex,
      IsCechCoefficientResolutionLift φ M I I' t) ∧
    (∀ t₀ t₁ : (cechCoefficientComplex φ (.up ℕ)).obj I.cocomplex ⟶ I'.cocomplex,
      IsCechCoefficientResolutionLift φ M I I' t₀ →
      IsCechCoefficientResolutionLift φ M I I' t₁ → Nonempty (Homotopy t₀ t₁)) := by
  exact cech_nonnegative_resolution_lifts
    ((cechCoefficientComplex φ (.up ℕ)).map I.ι)
    ((HomologicalComplex.singleMapHomologicalComplex
      (SheafOfModules.restrictScalars.{u} φ) (.up ℕ) 0).hom.app M ≫ I'.ι)


set_option maxHeartbeats 800000 in
-- Elaborating the full comparison and refinement signature needs more than the default count.
/-- Actual restriction of coefficients on a coherent Čech resolution represents the
canonical derived coefficient comparison, including its augmentation, columns, choice
independence and refinement. The scalar functors need not preserve injectives, and the
canonical derived comparisons need not be invertible.

Source: Stacks derived.tex, Tags 015F and 070I; agent coefficient-comparison extension
(blueprint: lem-sfb-cech-coefficient-derived-comparison).

Proof plan (the seven DAG steps):
1. Apply lem-sfb-cech-injective-column-model to the two ordinary resolutions. It gives
   K-injectivity of them and of every localized resolution, actual restrictions and units.
   Small-site K-injective resolutions also exist by prop-pur-kinjective-resolutions-exist.
2. Exact scalar restriction preserves the resolution quasi-isomorphism. Invert it after
   Q and use lem-weil-pbc-kinjective-hom-derived with target J to lift Q(c) Q(Ta) inverse.
   The Hom bijection gives uniqueness up to chain homotopy, without injectivity of TI.
3. Form each component by base, push and pull scalar identifications followed by t.
   The identities on sections commute with all faces and degeneracies, and the chain-map
   identity commutes with the vertical differential. Their finite diagonal sums give the
   signed total map, uniquely specified by its composites with every coprojection.
4. Apply lem-sfb-exact-square-right-derived-unit to the base and each column. Its unit
   equation and naturality at t give the resolution comparison equation after cancelling
   the derived image of c; the normalized resolution comparisons are unit times inverse Qa.
5. The augmentation has only its (0,q) component. Compatibility with localization units
   and naturality at t give the chain augmentation square. Apply Q and substitute step 4
   to obtain the displayed total equation. Localizing a,c,t gives the column equations.
6. A homotopy s between lifts gives total homotopy with (n,q) component (-1)^n s_n^q.
   Horizontal terms cancel and vertical terms give the difference of the maps. At q=0
   the target degree -1 is zero. Thus columns and totals agree after Q for all lifts.
7. For r:W→V, section-restriction naturality gives the column refinement square. Sum it
   over each finite diagonal for the total square. Localization units restrict to units;
   identity and composition are the actual refinement identities of the coherent model.
-/
theorem cech_coefficient_derived_comparison
    {C Y : Type u} [SmallCategory C] [SmallCategory Y]
    {J : GrothendieckTopology C} {L : GrothendieckTopology Y}
    (R R' : Sheaf J RingCat.{u}) (S S' : Sheaf L RingCat.{u})
    (_hR : ∀ (U : Cᵒᵖ) (x y : R.obj.obj U), x * y = y * x)
    (_hR' : ∀ (U : Cᵒᵖ) (x y : R'.obj.obj U), x * y = y * x)
    (_hS : ∀ (U : Yᵒᵖ) (x y : S.obj.obj U), x * y = y * x)
    (_hS' : ∀ (U : Yᵒᵖ) (x y : S'.obj.obj U), x * y = y * x)
    [HasDerivedCategory.{wX} (ringedSiteModules.{u} R)]
    [HasDerivedCategory.{wXp} (ringedSiteModules.{u} R')]
    [HasDerivedCategory.{wY} (ringedSiteModules.{u} S)]
    [HasDerivedCategory.{wYp} (ringedSiteModules.{u} S')]
    [∀ A : Sheaf J (Type u),
      HasDerivedCategory.{wS} (ringedSiteModules.{u} (elementRing R A))]
    [∀ A : Sheaf J (Type u),
      HasDerivedCategory.{wSp} (ringedSiteModules.{u} (elementRing R' A))]
    (f : RingedToposMorphism R S) (f' : RingedToposMorphism R' S')
    [IsIso f.ringMap] [IsIso f'.ringMap]
    (fInverse : ringedSiteModules.{u} S ⥤ ringedSiteModules.{u} R)
    (fInverse' : ringedSiteModules.{u} S' ⥤ ringedSiteModules.{u} R')
    [fInverse.Additive] [PreservesFiniteLimits fInverse]
    [PreservesFiniteColimits fInverse]
    [fInverse'.Additive] [PreservesFiniteLimits fInverse']
    [PreservesFiniteColimits fInverse']
    (_adj : fInverse ⊣ f.modules) (_adj' : fInverse' ⊣ f'.modules)
    (hi : f.inverse = f'.inverse) (hd : f.direct = f'.direct)
    (φ : R' ⟶ R) (ψ : S' ⟶ S)
    (_coefficient_square :
      f.inverse.map ((sheafCompose L (forget RingCat)).map ψ) ≫ f.ringMap =
        eqToHom (congrArg (fun G ↦ G.obj ((sheafCompose L (forget RingCat)).obj S')) hi) ≫
          f'.ringMap ≫ (sheafCompose J (forget RingCat)).map φ)
    [PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} φ)]
    [PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} φ)]
    [PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} ψ)]
    [PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} ψ)]
    [∀ A : Sheaf J (Type u), PreservesFiniteLimits
      (SheafOfModules.restrictScalars.{u} (cechCoefficientRingMap φ A))]
    [∀ A : Sheaf J (Type u), PreservesFiniteColimits
      (SheafOfModules.restrictScalars.{u} (cechCoefficientRingMap φ A))]
    (D : CoherentCechImageModel R) (D' : CoherentCechImageModel R')
    (E : CechCoefficientCommutations f f' φ ψ hd D D')
    (RF : CechCoefficientDerivedPair f.modules)
    (RG : CechCoefficientDerivedPair f'.modules)
    (γ : RF.functor ⋙ (SheafOfModules.restrictScalars ψ).mapDerivedCategory ⟶
      (SheafOfModules.restrictScalars φ).mapDerivedCategory ⋙ RG.functor)
    (_hγ : CechCoefficientUnitEquation f.modules f'.modules
      (SheafOfModules.restrictScalars φ) (SheafOfModules.restrictScalars ψ) E.base RF RG γ)
    (M : ringedSiteModules.{u} R) (I : InjectiveResolution M)
    (I' : InjectiveResolution ((SheafOfModules.restrictScalars φ).obj M)) :
    (∃ t : (cechCoefficientComplex φ (.up ℕ)).obj I.cocomplex ⟶ I'.cocomplex,
      IsCechCoefficientResolutionLift φ M I I' t) ∧
    (∀ t₀ t₁ : (cechCoefficientComplex φ (.up ℕ)).obj I.cocomplex ⟶ I'.cocomplex,
      IsCechCoefficientResolutionLift φ M I I' t₀ →
      IsCechCoefficientResolutionLift φ M I I' t₁ → Nonempty (Homotopy t₀ t₁)) ∧
    ∃ (maps : ∀ (V : Sheaf J (Type u))
        (t : (cechCoefficientComplex φ (.up ℕ)).obj I.cocomplex ⟶ I'.cocomplex),
        CechCoefficientMapData E V I.cocomplex I'.cocomplex t)
      (b : ∀ V : Sheaf J (Type u),
        (f.modules.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
          (D.bicomplex f.modules V I.cocomplex).total (.up ℕ))
      (b' : ∀ V : Sheaf J (Type u),
        (f'.modules.mapHomologicalComplex (.up ℕ)).obj I'.cocomplex ⟶
          (D'.bicomplex f'.modules V I'.cocomplex).total (.up ℕ))
      (eI : DerivedCategory.Q.obj ((f.modules.mapHomologicalComplex (.up ℤ)).obj
          (I.cocomplex.extend ComplexShape.embeddingUpNat)) ≅
        RF.functor.obj (DerivedCategory.Q.obj
          (((CochainComplex.single₀ _).obj M).extend ComplexShape.embeddingUpNat)))
      (eJ : DerivedCategory.Q.obj ((f'.modules.mapHomologicalComplex (.up ℤ)).obj
          (I'.cocomplex.extend ComplexShape.embeddingUpNat)) ≅
        RG.functor.obj (DerivedCategory.Q.obj ((cechCoefficientComplex φ (.up ℤ)).obj
          (((CochainComplex.single₀ _).obj M).extend ComplexShape.embeddingUpNat)))),
      IsCechResolutionComparison f.modules RF
        (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat) eI ∧
      IsCechResolutionComparison f'.modules RG
        (cechCoefficientResolutionAugmentation φ M I') eJ ∧
      (∀ V : Sheaf J (Type u), D.IsAugmentation f.modules V I.cocomplex (b V) ∧
        D'.IsAugmentation f'.modules V I'.cocomplex (b' V)) ∧
      (∀ (V : Sheaf J (Type u)) (_hV : Epi (terminal.from V))
        (t : (cechCoefficientComplex φ (.up ℕ)).obj I.cocomplex ⟶ I'.cocomplex),
        IsCechCoefficientResolutionLift φ M I I' t →
        (SheafOfModules.restrictScalars ψ).mapDerivedCategory.map
            (eI.inv ≫ DerivedCategory.Q.map (cechCoefficientExtendMap f.modules (b V))) ≫
          (SheafOfModules.restrictScalars ψ).mapDerivedCategoryFactors.hom.app
            (D.total f.modules V I.cocomplex) ≫
          DerivedCategory.Q.map (cechCoefficientExtendMap
            (SheafOfModules.restrictScalars ψ) (maps V t).total) =
        γ.app (DerivedCategory.Q.obj
            (((CochainComplex.single₀ _).obj M).extend ComplexShape.embeddingUpNat)) ≫
          RG.functor.map ((SheafOfModules.restrictScalars φ).mapDerivedCategoryFactors.hom.app
            (((CochainComplex.single₀ _).obj M).extend ComplexShape.embeddingUpNat)) ≫
          eJ.inv ≫ DerivedCategory.Q.map (cechCoefficientExtendMap f'.modules (b' V))) ∧
      (∀ (V : Sheaf J (Type u)) (_hV : Epi (terminal.from V))
        (t : (cechCoefficientComplex φ (.up ℕ)).obj I.cocomplex ⟶ I'.cocomplex)
        (_ht : IsCechCoefficientResolutionLift φ M I I' t) (n : SimplexCategory),
        IsCechCoefficientColumnComparison
          (D.push ((sheafCoverNerve V).obj (op n)) ⋙ f.modules)
          (D'.push ((sheafCoverNerve V).obj (op n)) ⋙ f'.modules)
          (SheafOfModules.restrictScalars
            (cechCoefficientRingMap φ ((sheafCoverNerve V).obj (op n))))
          (SheafOfModules.restrictScalars ψ) (E.column ((sheafCoverNerve V).obj (op n)))
          ((cechColumnRestrictComplex D ((sheafCoverNerve V).obj (op n))).map
            (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat))
          ((cechCoefficientPullComplexIso E ((sheafCoverNerve V).obj (op n))
              (((CochainComplex.single₀ _).obj M).extend ComplexShape.embeddingUpNat)).hom ≫
            (cechColumnRestrictComplex D' ((sheafCoverNerve V).obj (op n))).map
              (cechCoefficientResolutionAugmentation φ M I'))
          (cechCoefficientLocalizedMap E ((sheafCoverNerve V).obj (op n))
            (cechCoefficientLiftExtend φ t))) ∧
      (∀ (V : Sheaf J (Type u)) (t₀ t₁ :
          (cechCoefficientComplex φ (.up ℕ)).obj I.cocomplex ⟶ I'.cocomplex),
        IsCechCoefficientResolutionLift φ M I I' t₀ →
        IsCechCoefficientResolutionLift φ M I I' t₁ →
        DerivedCategory.Q.map (HomologicalComplex.extendMap (maps V t₀).total
            ComplexShape.embeddingUpNat) =
          DerivedCategory.Q.map (HomologicalComplex.extendMap (maps V t₁).total
            ComplexShape.embeddingUpNat) ∧
        ∀ n : ℕ, DerivedCategory.Q.map (HomologicalComplex.extendMap
            ((maps V t₀).bicomplex.f n) ComplexShape.embeddingUpNat) =
          DerivedCategory.Q.map (HomologicalComplex.extendMap
            ((maps V t₁).bicomplex.f n) ComplexShape.embeddingUpNat)) ∧
      (∀ (V W : Sheaf J (Type u)) (r : W ⟶ V)
        (t : (cechCoefficientComplex φ (.up ℕ)).obj I.cocomplex ⟶ I'.cocomplex),
        (cechCoefficientComplex ψ (.up ℕ)).map
            (D.totalRefinement f.modules r I.cocomplex) ≫ (maps W t).total =
          (maps V t).total ≫ D'.totalRefinement f'.modules r I'.cocomplex ∧
        ∀ n q : ℕ,
          (SheafOfModules.restrictScalars ψ).map (f.modules.map
              ((D.image.map (((Arrow.mapCechNerve
                (Arrow.homMk r (𝟙 _) (terminal.hom_ext _ _) :
                  Arrow.mk (terminal.from W) ⟶ Arrow.mk (terminal.from V))).app
                  (op (SimplexCategory.mk n))).op)).app (I.cocomplex.X q))) ≫
            ((maps W t).bicomplex.f n).f q =
          ((maps V t).bicomplex.f n).f q ≫ f'.modules.map
            ((D'.image.map (((Arrow.mapCechNerve
              (Arrow.homMk r (𝟙 _) (terminal.hom_ext _ _) :
                  Arrow.mk (terminal.from W) ⟶ Arrow.mk (terminal.from V))).app
                (op (SimplexCategory.mk n))).op)).app (I'.cocomplex.X q))) := by
  obtain ⟨ht, huniq⟩ := cech_resolution_lifts φ M I I'
  refine ⟨ht, huniq, ?_⟩
  classical
  let := SheafOfModules.isGrothendieckAbelian R
  let := SheafOfModules.isGrothendieckAbelian R'
  obtain ⟨eI, heI⟩ := cech_pair_resolution_comparison f.modules RF
    (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat)
  have hqa : QuasiIso (cechCoefficientResolutionAugmentation φ M I') := by
    dsimp [cechCoefficientResolutionAugmentation]
    infer_instance
  obtain ⟨eJ, heJ⟩ := cech_pair_resolution_comparison f'.modules RG
    (cechCoefficientResolutionAugmentation φ M I')
  obtain ⟨maps, b, b', haug, hsq, hhom, href⟩ :=
    cech_coefficient_strict_maps E I.cocomplex I'.cocomplex
  refine ⟨maps, b, b', eI, eJ, heI, heJ, haug, ?_, ?_, ?_, href⟩
  · intro V _ t ht
    have hte := cech_extend_lift_equation (SheafOfModules.restrictScalars φ)
      I.ι ((HomologicalComplex.singleMapHomologicalComplex
        (SheafOfModules.restrictScalars.{u} φ) (.up ℕ) 0).hom.app M ≫ I'.ι) t ht
    exact cech_augmentation_equation f.modules f'.modules
      (SheafOfModules.restrictScalars φ) (SheafOfModules.restrictScalars ψ)
      E.base RF RG γ _hγ
      (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat)
      (cechCoefficientResolutionAugmentation φ M I')
      (cechCoefficientLiftExtend φ t) hte eI eJ heI heJ
      (cechCoefficientExtendMap f.modules (b V))
      (cechCoefficientExtendMap f'.modules (b' V))
      (cechCoefficientExtendMap (SheafOfModules.restrictScalars ψ) (maps V t).total)
      (hsq V t)
  · intro V hV t ht n
    let A := (sheafCoverNerve V).obj (op n)
    have hc := ((cech_injective_column_model R S _hR _hS f fInverse _adj V M).2.2
      I D).2.1 n
    have hc' := ((cech_injective_column_model R' S' _hR' _hS' f' fInverse' _adj' V
      ((SheafOfModules.restrictScalars φ).obj M)).2.2 I' D').2.1 n
    let := hc.1
    let := hc.2
    let := hc'.1
    let := SheafOfModules.isGrothendieckAbelian (elementRing R A)
    let := SheafOfModules.isGrothendieckAbelian (elementRing R' A)
    obtain ⟨sliceAdj⟩ := elementModuleExtension_adjunction R' A
    let := sliceAdj.isRightAdjoint
    let := (D'.adj A).isLeftAdjoint
    let : HasBinaryBiproducts (ringedSiteModules.{u} R') := Abelian.hasBinaryBiproducts
    let := preservesBinaryBiproducts_of_preservesBinaryCoproducts
      (elementModulePullback R' A)
    let := Functor.additive_of_preservesBinaryBiproducts (elementModulePullback R' A)
    have hqa' : QuasiIso ((cechCoefficientPullComplexIso E A
        (((CochainComplex.single₀ _).obj M).extend ComplexShape.embeddingUpNat)).hom ≫
        (cechColumnRestrictComplex D' A).map
          (cechCoefficientResolutionAugmentation φ M I')) := by
      have hmap : QuasiIso ((cechColumnRestrictComplex D' A).map
          (cechCoefficientResolutionAugmentation φ M I')) :=
        HomologicalComplex.quasiIso_map_of_preservesHomology
          (cechCoefficientResolutionAugmentation φ M I') (elementModulePullback R' A)
      exact quasiIso_comp
        (cechCoefficientPullComplexIso E A
          (((CochainComplex.single₀ _).obj M).extend ComplexShape.embeddingUpNat)).hom
        ((cechColumnRestrictComplex D' A).map (cechCoefficientResolutionAugmentation φ M I'))
    have hte := cech_extend_lift_equation (SheafOfModules.restrictScalars φ)
      I.ι ((HomologicalComplex.singleMapHomologicalComplex
        (SheafOfModules.restrictScalars.{u} φ) (.up ℕ) 0).hom.app M ≫ I'.ι) t ht
    exact cech_column_comparison (D.push A ⋙ f.modules) (D'.push A ⋙ f'.modules)
      (SheafOfModules.restrictScalars (cechCoefficientRingMap φ A))
      (SheafOfModules.restrictScalars ψ) (E.column A)
      ((cechColumnRestrictComplex D A).map
        (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat))
      ((cechCoefficientPullComplexIso E A
        (((CochainComplex.single₀ _).obj M).extend ComplexShape.embeddingUpNat)).hom ≫
          (cechColumnRestrictComplex D' A).map
            (cechCoefficientResolutionAugmentation φ M I'))
      (cechCoefficientLocalizedMap E A (cechCoefficientLiftExtend φ t))
      (cech_localized_lift_equation E A _ _ _ hte)
  · intro V t₀ t₁ h₀ h₁
    exact hhom V t₀ t₁ (huniq t₀ t₁ h₀ h₁)

end CategoryTheory
