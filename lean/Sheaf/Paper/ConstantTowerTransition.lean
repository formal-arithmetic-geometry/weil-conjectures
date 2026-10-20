/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q130, J6
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.CategoryTheory.Abelian.RightDerived
import all Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalarsLowerStar
import WeilConjectures.CategoryTheory.RightDerivedSingleZeroUnit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat

/-!
# Degree-zero direct image and coefficient transition maps

Source: Stacks Project, derived.tex, Tag 05TD (`lemma-left-exact-higher-derived`),
and the normalized coefficient comparison
(blueprint: lem-pod-constant-tower-transition).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

-- Use the mate identities without expanding the inverse-image and derived-mate constructions.
attribute [local irreducible] upperStar fixedScalarRestrictionDirectImageMap

private theorem chain_unit_pasting {C : Type*} [Category C]
    {V A₀ A₁ P P' T U B₀ B₁ C₀ C₁ : C}
    {a : V ⟶ A₀} {η : A₀ ⟶ P} {t : A₀ ⟶ A₁} {ν : A₁ ⟶ P'}
    {p : P ⟶ P'} {q : P' ⟶ T} {c : T ⟶ U}
    {b : V ⟶ B₀} {m : B₀ ⟶ B₁} {v : B₁ ⟶ A₁}
    {n : B₁ ⟶ C₁} {n₀ : B₀ ⟶ C₀} {l : C₀ ⟶ C₁} {e : C₁ ⟶ U}
    {d : V ⟶ C₀}
    (hη : t ≫ ν = η ≫ p) (hchain : a ≫ t = b ≫ m ≫ v)
    (hunit : v ≫ ν ≫ q ≫ c = n ≫ e) (hfac : m ≫ n = n₀ ≫ l)
    (hsingle : d = b ≫ n₀) : a ≫ η ≫ p ≫ q ≫ c = d ≫ l ≫ e := by
  rw [← reassoc_of% hη, ← Category.assoc a t, hchain]
  simp only [Category.assoc]
  rw [hunit, reassoc_of% hfac, hsingle]
  simp only [Category.assoc]

section

open CategoryTheory.Abelian

variable {CA CB DA DB : Type*}
  [Category CA] [Category CB] [Category DA] [Category DB]
  [Abelian CA] [Abelian CB] [Abelian DA] [Abelian DB]
  [HasDerivedCategory CA] [HasDerivedCategory CB]
  [HasDerivedCategory DA] [HasDerivedCategory DB]
  [HasKInjectiveResolutions CA] [HasKInjectiveResolutions CB]
  (r : CB ⥤ CA) (s : DB ⥤ DA) (FA : CA ⥤ DA) (FB : CB ⥤ DB)
  [r.Additive] [s.Additive] [FA.Additive] [FB.Additive]
  [PreservesFiniteLimits r] [PreservesFiniteColimits r]
  [PreservesFiniteLimits s] [PreservesFiniteColimits s]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem single_unit_of_complex (G : CB)
    (m : (s.mapHomologicalComplex (.up ℤ)).obj
        ((FB.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor CB 0).obj G)) ⟶
      (FA.mapHomologicalComplex (.up ℤ)).obj
        ((r.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor CB 0).obj G)))
    (e : (CochainComplex.singleFunctor DA 0).obj (FA.obj (r.obj G)) ⟶
      (CochainComplex.singleFunctor DA 0).obj (s.obj (FB.obj G)))
    (c : FA.rightDerivedFunctor.obj
        (r.mapDerivedCategory.obj ((DerivedCategory.singleFunctor CB 0).obj G)) ⟶
      s.mapDerivedCategory.obj
        (FB.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor CB 0).obj G)))
    (hchain : (FA.mapCochainComplexSingleFunctor 0).inv.app (r.obj G) ≫
        (FA.mapHomologicalComplex (.up ℤ)).map
          ((r.mapCochainComplexSingleFunctor 0).inv.app G) =
      e ≫ (s.mapCochainComplexSingleFunctor 0).inv.app (FB.obj G) ≫
        (s.mapHomologicalComplex (.up ℤ)).map
          ((FB.mapCochainComplexSingleFunctor 0).inv.app G) ≫ m)
    (hunit : DerivedCategory.Q.map m ≫
        FA.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
          ((r.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor CB 0).obj G))) ≫
        FA.rightDerivedFunctor.map (r.mapDerivedCategoryFactors.inv.app
          ((CochainComplex.singleFunctor CB 0).obj G)) ≫ c =
      s.mapDerivedCategoryFactors.inv.app
          ((FB.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor CB 0).obj G)) ≫
        s.mapDerivedCategory.map (FB.rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj ((CochainComplex.singleFunctor CB 0).obj G)))) :
    FA.rightDerivedSingleUnit (r.obj G) ≫ FA.rightDerivedFunctor.map
        ((r.mapDerivedCategorySingleFunctor 0).inv.app G) ≫ c =
      DerivedCategory.Q.map e ≫ (s.mapDerivedCategorySingleFunctor 0).inv.app (FB.obj G) ≫
        s.mapDerivedCategory.map (FB.rightDerivedSingleUnit G) := by
  have ht := (Iso.eq_comp_inv (r.mapDerivedCategoryFactors.app
    ((CochainComplex.singleFunctor CB 0).obj G))).2
    (r.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app G)
  have hsingle := (Iso.eq_comp_inv (s.mapDerivedCategoryFactors.app
    ((CochainComplex.singleFunctor DB 0).obj (FB.obj G)))).2
    (s.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app (FB.obj G))
  have hn := restrictionDerivedUnit_naturality FA
    ((r.mapCochainComplexSingleFunctor 0).inv.app G)
  have hs := s.mapDerivedCategoryFactors.inv.naturality
    ((FB.mapCochainComplexSingleFunctor 0).inv.app G)
  have hchain' := congrArg (fun v => DerivedCategory.Q.map v) hchain
  simp only [Functor.map_comp] at hchain'
  rw [← Category.assoc (DerivedCategory.Q.map e)
    (DerivedCategory.Q.map ((s.mapCochainComplexSingleFunctor 0).inv.app (FB.obj G)))]
    at hchain'
  have hsingle' := congrArg (fun z => DerivedCategory.Q.map e ≫ z) hsingle
  rw [← Category.assoc] at hsingle'
  dsimp only [Functor.comp_map] at hn hs
  rw [ht, Functor.map_comp]
  dsimp only [Functor.rightDerivedSingleUnit]
  simp only [Functor.map_comp, Category.assoc]
  have hp := chain_unit_pasting hn hchain' hunit hs hsingle'
  simpa only [Category.assoc, restrictionDerivedUnit, Iso.app_inv, Functor.comp_obj]
    using hp

end

private theorem exact_single_homology
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (s : C ⥤ D) [s.Additive] [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (G : C) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).inv.app (s.obj G) ≫
      (DerivedCategory.homologyFunctor D 0).map
        ((s.mapDerivedCategorySingleFunctor 0).inv.app G) =
    s.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app G) ≫
      (s.mapDerivedCategoryHomologyFunctorIso 0).hom.app
        ((DerivedCategory.singleFunctor C 0).obj G) := by
  apply (cancel_mono
    ((DerivedCategory.homologyFunctor D 0).map
        ((s.mapDerivedCategorySingleFunctor 0).hom.app G) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).hom.app (s.obj G))).1
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [s.mapDerivedCategoryHomologyFunctorIso_hom_app_singleFunctor 0 G]
  rw [← s.map_comp, Iso.inv_hom_id_app, s.map_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact Iso.inv_hom_id_app (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0) (s.obj G)


section

open CategoryTheory.Abelian

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives C] [HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

private theorem functor_augmentation_unit (M : C) :
    (F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
      F.rightDerivedZeroIsoSelf.app M).inv =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).inv.app (F.obj M) ≫
      (DerivedCategory.homologyFunctor D 0).map (F.rightDerivedSingleUnit M) := by
  apply (cancel_mono (F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
    F.rightDerivedZeroIsoSelf.app M).hom).1
  simp only [Iso.inv_hom_id, Category.assoc]
  rw [F.rightDerivedSingleUnit_zero M]
  simp only [Iso.inv_hom_id_app]
  rfl

private theorem functor_augmentation_naturality {M N : C} (v : M ⟶ N) :
    (F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
      F.rightDerivedZeroIsoSelf.app M).inv ≫
      (DerivedCategory.homologyFunctor D 0).map
        (F.rightDerivedFunctor.map ((DerivedCategory.singleFunctor C 0).map v)) =
    F.map v ≫ (F.homologyRightDerivedFunctorObjSingleFunctorIso N 0 ≪≫
      F.rightDerivedZeroIsoSelf.app N).inv := by
  apply (cancel_mono (F.homologyRightDerivedFunctorObjSingleFunctorIso N 0 ≪≫
    F.rightDerivedZeroIsoSelf.app N).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [Iso.trans_hom]
  erw [F.homologyRightDerivedFunctorObjSingleFunctorIso_hom_naturality_assoc v 0]
  erw [F.rightDerivedZeroIsoSelf.hom.naturality]
  simpa only [Iso.trans_hom, Category.assoc, Iso.app_hom] using
    Iso.inv_hom_id_assoc (F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
      F.rightDerivedZeroIsoSelf.app M) (F.map v)


end

section

open CategoryTheory.Abelian

variable {CA CB DA DB : Type*}
  [Category CA] [Category CB] [Category DA] [Category DB]
  [Abelian CA] [Abelian CB] [Abelian DA] [Abelian DB]
  [HasDerivedCategory CA] [HasDerivedCategory CB]
  [HasDerivedCategory DA] [HasDerivedCategory DB]
  [EnoughInjectives CA] [EnoughInjectives CB]
  [HasKInjectiveResolutions CA] [HasKInjectiveResolutions CB]
  (r : CB ⥤ CA) (s : DB ⥤ DA) (FA : CA ⥤ DA) (FB : CB ⥤ DB)
  [r.Additive] [s.Additive] [FA.Additive] [FB.Additive]
  [PreservesFiniteLimits r] [PreservesFiniteColimits r]
  [PreservesFiniteLimits s] [PreservesFiniteColimits s]
  [PreservesFiniteLimits FA] [PreservesFiniteLimits FB]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem transition_from_complex (M : CA) (G : CB) (u : M ⟶ r.obj G)
    (v : FA.obj (r.obj G) ⟶ s.obj (FB.obj G))
    (m : (s.mapHomologicalComplex (.up ℤ)).obj
        ((FB.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor CB 0).obj G)) ⟶
      (FA.mapHomologicalComplex (.up ℤ)).obj
        ((r.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor CB 0).obj G)))
    (c : FA.rightDerivedFunctor.obj
        (r.mapDerivedCategory.obj ((DerivedCategory.singleFunctor CB 0).obj G)) ⟶
      s.mapDerivedCategory.obj
        (FB.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor CB 0).obj G)))
    (hchain : (FA.mapCochainComplexSingleFunctor 0).inv.app (r.obj G) ≫
        (FA.mapHomologicalComplex (.up ℤ)).map
          ((r.mapCochainComplexSingleFunctor 0).inv.app G) =
      (CochainComplex.singleFunctor DA 0).map v ≫
        (s.mapCochainComplexSingleFunctor 0).inv.app (FB.obj G) ≫
        (s.mapHomologicalComplex (.up ℤ)).map
          ((FB.mapCochainComplexSingleFunctor 0).inv.app G) ≫ m)
    (hunit : DerivedCategory.Q.map m ≫
        FA.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
          ((r.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor CB 0).obj G))) ≫
        FA.rightDerivedFunctor.map (r.mapDerivedCategoryFactors.inv.app
          ((CochainComplex.singleFunctor CB 0).obj G)) ≫ c =
      s.mapDerivedCategoryFactors.inv.app
          ((FB.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor CB 0).obj G)) ≫
        s.mapDerivedCategory.map (FB.rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj ((CochainComplex.singleFunctor CB 0).obj G)))) :
    (FA.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
        FA.rightDerivedZeroIsoSelf.app M).inv ≫
      (DerivedCategory.homologyFunctor DA 0).map
        (FA.rightDerivedFunctor.map ((DerivedCategory.singleFunctor CA 0).map u) ≫
          FA.rightDerivedFunctor.map ((r.mapDerivedCategorySingleFunctor 0).inv.app G) ≫ c) =
    FA.map u ≫ v ≫
      s.map (FB.homologyRightDerivedFunctorObjSingleFunctorIso G 0 ≪≫
        FB.rightDerivedZeroIsoSelf.app G).inv ≫
      (s.mapDerivedCategoryHomologyFunctorIso 0).hom.app
        (FB.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor CB 0).obj G)) := by
  have h := single_unit_of_complex r s FA FB G m
    ((CochainComplex.singleFunctor DA 0).map v) c hchain hunit
  have hc : (FA.homologyRightDerivedFunctorObjSingleFunctorIso (r.obj G) 0 ≪≫
        FA.rightDerivedZeroIsoSelf.app (r.obj G)).inv ≫
      (DerivedCategory.homologyFunctor DA 0).map
        (FA.rightDerivedFunctor.map ((r.mapDerivedCategorySingleFunctor 0).inv.app G) ≫ c) =
      v ≫ s.map (FB.homologyRightDerivedFunctorObjSingleFunctorIso G 0 ≪≫
          FB.rightDerivedZeroIsoSelf.app G).inv ≫
        (s.mapDerivedCategoryHomologyFunctorIso 0).hom.app
          (FB.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor CB 0).obj G)) := by
    rw [functor_augmentation_unit FA (r.obj G), functor_augmentation_unit FB G, s.map_comp]
    simp only [Category.assoc]
    rw [← Functor.map_comp, h, Functor.map_comp]
    simp only [Functor.map_comp]
    have hv := (DerivedCategory.singleFunctorCompHomologyFunctorIso DA 0).inv.naturality v
    dsimp only [Functor.id_map, Functor.comp_map] at hv
    erw [← reassoc_of% hv]
    rw [← Category.assoc
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso DA 0).inv.app (s.obj (FB.obj G)))
      ((DerivedCategory.homologyFunctor DA 0).map
        ((s.mapDerivedCategorySingleFunctor 0).inv.app (FB.obj G))),
      exact_single_homology s (FB.obj G)]
    simp only [Category.assoc]
    congr 1
    congr 1
    exact ((s.mapDerivedCategoryHomologyFunctorIso 0).hom.naturality
      (FB.rightDerivedSingleUnit G)).symm
  simp only [Functor.map_comp]
  rw [reassoc_of% functor_augmentation_naturality FA u]
  exact congrArg (FA.map u ≫ ·) (by
    simpa only [Functor.map_comp, Category.assoc] using hc)

end

private theorem cancel_unit_square {C : Type*} [Category C]
    {V W X Y Z : C} (a : V ⟶ W) (b : W ⟶ X) (c : X ⟶ Y)
    (d : V ⟶ Z) (e : Z ⟶ Y) [IsIso b] [IsIso c] [IsIso d]
    (h : a ≫ b ≫ c = d ≫ e) : e ≫ inv c ≫ inv b = inv d ≫ a := by
  apply (cancel_epi d).1
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [← h]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem inverse_mate_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    (c : H.mapDerivedCategory ⋙ R'.rightDerivedFunctor ≅
      R.rightDerivedFunctor ⋙ G.mapDerivedCategory)
    (hc : c.inv = (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso s).hom)).natTrans)
    (K : CochainComplex B ℤ) :
    DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)).natTrans (.up ℤ)).app K) ≫
      restrictionDerivedUnit R' ((H.mapHomologicalComplex (.up ℤ)).obj K) ≫
      R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.inv.app K) ≫
      c.hom.app (DerivedCategory.Q.obj K) =
    G.mapDerivedCategoryFactors.inv.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      G.mapDerivedCategory.map (restrictionDerivedUnit R K) := by
  have h := simple_derived_mate_factors adj adj' s K
  dsimp only [Functor.mapDerivedCategorySquareIso, TwoSquare.natTrans] at hc
  rw [← hc] at h
  have h' := cancel_unit_square _ _ _ _ _ h
  rw [← R'.rightDerivedFunctor.map_inv (H.mapDerivedCategoryFactors.hom.app K),
    NatIso.inv_hom_app H.mapDerivedCategoryFactors K,
    NatIso.inv_hom_app G.mapDerivedCategoryFactors
      ((R.mapHomologicalComplex (.up ℤ)).obj K),
    NatIso.inv_inv_app c (DerivedCategory.Q.obj K)] at h'
  simpa only [Category.assoc] using h'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem single_chain_comparison
    {CA CB DA DB : Type*}
    [Category CA] [Category CB] [Category DA] [Category DB]
    [Abelian CA] [Abelian CB] [Abelian DA] [Abelian DB]
    (r : CB ⥤ CA) (s : DB ⥤ DA) (FA : CA ⥤ DA) (FB : CB ⥤ DB)
    [r.Additive] [s.Additive] [FA.Additive] [FB.Additive]
    (e : FB ⋙ s ≅ r ⋙ FA) (G : CB) :
    (FA.mapCochainComplexSingleFunctor 0).inv.app (r.obj G) ≫
        (FA.mapHomologicalComplex (.up ℤ)).map
          ((r.mapCochainComplexSingleFunctor 0).inv.app G) =
      (CochainComplex.singleFunctor DA 0).map (e.inv.app G) ≫
        (s.mapCochainComplexSingleFunctor 0).inv.app (FB.obj G) ≫
        (s.mapHomologicalComplex (.up ℤ)).map
          ((FB.mapCochainComplexSingleFunctor 0).inv.app G) ≫
        (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
          ((CochainComplex.singleFunctor CB 0).obj G) := by
  ext i : 1
  by_cases hi : i = 0
  · subst i
    simp only [Functor.mapCochainComplexSingleFunctor, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
      Category.id_comp]
    erw [FA.map_id, r.map_id, FA.map_id, s.map_id, FB.map_id, s.map_id]
    change (𝟙 (FA.obj (r.obj G))) ≫ 𝟙 _ =
      (e.inv.app G ≫ 𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ e.hom.app G
    simp only [Category.id_comp, Category.comp_id, Iso.inv_hom_id_app]
    rfl
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
      (FA.obj (r.obj G)) i hi).eq_of_src _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem transition_from_mate
    {CA CB DA DB : Type*}
    [Category CA] [Category CB] [Category DA] [Category DB]
    [Abelian CA] [Abelian CB] [Abelian DA] [Abelian DB]
    [HasDerivedCategory CA] [HasDerivedCategory CB]
    [HasDerivedCategory DA] [HasDerivedCategory DB]
    [EnoughInjectives CA] [EnoughInjectives CB]
    [Abelian.HasKInjectiveResolutions CA] [Abelian.HasKInjectiveResolutions CB]
    (r : CB ⥤ CA) (s : DB ⥤ DA) (FA : CA ⥤ DA) (FB : CB ⥤ DB)
    (LA : DA ⥤ CA) (LB : DB ⥤ CB)
    [r.Additive] [s.Additive] [FA.Additive] [FB.Additive] [LA.Additive] [LB.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    [PreservesFiniteLimits FA] [PreservesFiniteLimits FB]
    [PreservesFiniteLimits LA] [PreservesFiniteColimits LA]
    [PreservesFiniteLimits LB] [PreservesFiniteColimits LB]
    (adjB : LB ⊣ FB) (adjA : LA ⊣ FA) (square : s ⋙ LA ≅ LB ⋙ r)
    (e : FB ⋙ s ≅ r ⋙ FA)
    (ht : (mateEquiv adjB adjA (TwoSquare.mk _ _ _ _ square.hom)).natTrans = e.hom)
    (m : FB.rightDerivedFunctor ⋙ s.mapDerivedCategory ⟶
      r.mapDerivedCategory ⋙ FA.rightDerivedFunctor) [IsIso m]
    (hc : m = (mateEquiv adjB.mapDerivedCategoryRightDerivedAdjunction
      adjA.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso square).hom)).natTrans)
    (M : CA) (G : CB) (u : M ⟶ r.obj G)
    (w : FA.obj M ⟶ s.obj (FB.obj G))
    (hw : FA.map u ≫ e.inv.app G = w) :
    (FA.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
        FA.rightDerivedZeroIsoSelf.app M).inv ≫
      (DerivedCategory.homologyFunctor DA 0).map
        (FA.rightDerivedFunctor.map ((DerivedCategory.singleFunctor CA 0).map u) ≫
          FA.rightDerivedFunctor.map ((r.mapDerivedCategorySingleFunctor 0).inv.app G) ≫
          (asIso m).inv.app ((DerivedCategory.singleFunctor CB 0).obj G)) =
    w ≫
      s.map (FB.homologyRightDerivedFunctorObjSingleFunctorIso G 0 ≪≫
        FB.rightDerivedZeroIsoSelf.app G).inv ≫
      (s.mapDerivedCategoryHomologyFunctorIso 0).hom.app
        (FB.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor CB 0).obj G)) := by
  have h := transition_from_complex r s FA FB M G u (e.inv.app G)
    ((NatTrans.mapHomologicalComplex
      (mateEquiv adjB adjA (TwoSquare.mk _ _ _ _ square.hom)).natTrans
      (.up ℤ)).app ((CochainComplex.singleFunctor CB 0).obj G))
    ((asIso m).inv.app ((DerivedCategory.singleFunctor CB 0).obj G))
    (by rw [ht]; exact single_chain_comparison r s FA FB e G)
    (inverse_mate_unit adjB adjA square (asIso m).symm hc _)
  rw [← Category.assoc (FA.map u) (e.inv.app G), hw] at h
  exact h


attribute [-instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint in
/-- The canonical augmentation isomorphism from ordinary direct image to degree-zero
unbounded derived direct image. The first comparison uses nonnegative injective
resolutions; the second is the inverse of the augmentation to the zeroth classical
right derived functor. Thus no arbitrary isomorphism is chosen.
Source: Stacks Project, Tag 05TD, part (3)
(blueprint: lem-pod-constant-tower-transition). -/
noncomputable def constantTowerTransitionAugmentation
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (lowerStar (ModuleCat.{u + 1} A) f).obj F ≅
      (DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) 0).obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor
            (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).obj F)) :=
  let L := lowerStar (ModuleCat.{u + 1} A) f
  (L.rightDerivedZeroIsoSelf.app F).symm ≪≫
    (L.homologyRightDerivedFunctorObjSingleFunctorIso F 0).symm

attribute [-instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint in
private theorem augmentation_hom
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (constantTowerTransitionAugmentation A f F).hom =
      ((lowerStar (ModuleCat.{u + 1} A) f).homologyRightDerivedFunctorObjSingleFunctorIso F 0 ≪≫
        (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedZeroIsoSelf.app F).inv := rfl

attribute [local irreducible] constantTowerTransitionAugmentation

attribute [-instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint in
/-- The derived coefficient comparison retains the ordinary direct-image section map
under the canonical degree-zero augmentations. The single/restriction comparison and
exact-restriction/homology comparison are included explicitly.
Source: Stacks Project, Tag 05TD, part (3), and the K-injective normalization of
lem-weil-proetale-direct-image-restriction-of-scalars
(blueprint: lem-pod-constant-tower-transition).

Proof: First use the defining unit equation of the derived mate to obtain the
coefficient-comparison equation on complexes. Its ordinary mate is the identity
section map, which is compatible with the canonical single-complex comparisons
in degree zero; all other components have zero source. Naturality of the derived
unit specializes the equation to a single object. The proved
`rightDerivedSingleUnit_zero` formula identifies the prescribed augmentation
with H⁰ of this unit. Apply H⁰, use exact restriction's single/homology comparison,
and then augmentation naturality in u to obtain the displayed square. -/
theorem constantTowerTransition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
    (u : F ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj G) :
    (constantTowerTransitionAugmentation A f F).hom ≫
        (DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) 0).map
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map
              ((DerivedCategory.singleFunctor
                (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).map u) ≫
            (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map
              (((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategorySingleFunctor
                0).inv.app G) ≫
            (fixedScalarRestrictionDirectImage φ f).hom.app
              ((DerivedCategory.singleFunctor
                (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) 0).obj G)) =
      (lowerStar (ModuleCat.{u + 1} A) f).map u ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).map
          (constantTowerTransitionAugmentation B f G).hom ≫
        ((Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryHomologyFunctorIso
          0).hom.app
          ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor
              (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) 0).obj G)) := by
  rw [augmentation_hom, augmentation_hom]
  let r := Sheaf.restrictScalars (Scheme.ProEt.topology X) φ
  let s := Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ
  let FA := lowerStar (ModuleCat.{u + 1} A) f
  let FB := lowerStar (ModuleCat.{u + 1} B) f
  let := fixedScalarRestrictionDirectImageMap_isIso φ f
  exact transition_from_mate
    r
    s
    FA FB
    (upperStar (ModuleCat.{u + 1} A) f) (upperStar (ModuleCat.{u + 1} B) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarRestrictScalarsIso φ f)
    (lowerStarCompRestrictScalarsIso φ f)
    (restriction_underived_mate φ f) (fixedScalarRestrictionDirectImageMap φ f)
    (restriction_mate_eq φ f) F G u (FA.map u)
    (Category.comp_id _)

end AlgebraicGeometry.ProEtale

