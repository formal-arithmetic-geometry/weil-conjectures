/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F9
-/
module

public import Sheaf.Paper.StrictQuotientScalarBalancing
public import Mathlib.CategoryTheory.Adjunction.Mates
import all Sheaf.Paper.ConstantCompletionEquivalence
import all Sheaf.Paper.CompletedPullbackAdjunction
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-! # Invertibility of the normalized strict scalar direct-image mates

Source: main-20261015, completed-exchange-coherence proof, second paragraph;
Stacks 03D2, 03D3, 0FND and 0DVC.
(blueprint: lem-weil-pbc-strict-quotient-scalar-direct-isomorphisms).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme.StrictScalarBalancing
variable {A : Type (u + 1)} [CommRing A]

attribute [local irreducible] CategoryTheory.ConstantCompletion.completed
attribute [local irreducible] CategoryTheory.ConstantCompletion.pull
attribute [local irreducible] CategoryTheory.ConstantCompletion.pullInsertion
attribute [local irreducible] inverseData dres tdres resFactors tresFactors towerSquare

private theorem mate_adjunct
    {C₁ C₂ C₃ C₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (G : C₁ ⥤ C₃) (H : C₂ ⥤ C₄) (α : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (M : C₁) (N : C₂) (t : L₁.obj M ⟶ N) :
    adj₂.homEquiv _ _ (α.app M ≫ H.map t) =
      G.map (adj₁.homEquiv _ _ t) ≫
        (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)).app N := by
  let δ := mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)
  have h := unit_mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α) M
  change G.map (adj₁.unit.app M) ≫ δ.app (L₁.obj M) =
    adj₂.unit.app (G.obj M) ≫ R₂.map (α.app M) at h
  rw [adj₂.homEquiv_unit, R₂.map_comp, ← Category.assoc, ← h, Category.assoc]
  have hd : δ.app (L₁.obj M) ≫ R₂.map (H.map t) =
      G.map (R₁.map t) ≫ δ.app N := δ.natTrans.naturality t |>.symm
  rw [hd, adj₁.homEquiv_unit, G.map_comp, Category.assoc]


private theorem normalizedDerivedRight
    {B C : Type*} [Category B] [Category C] [Abelian B] [Abelian C]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} C] [Abelian.HasKInjectiveResolutions C]
    (L : B ⥤ C) (G : C ⥤ B) [L.Additive] [G.Additive] (aM : L ⊣ G)
    (LF : DerivedCategory.{w} B ⥤ DerivedCategory.{w} C)
    (α : DerivedCategory.Q.{w} ⋙ LF ≅ L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w})
    (hLF : LF.IsLeftDerivedFunctor α.hom (HomologicalComplex.quasiIso B (.up ℤ))) :
    ∃ (RF : DerivedCategory.{w} C ⥤ DerivedCategory.{w} B)
      (β : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RF) (aD : LF ⊣ RF),
      (∀ I : CochainComplex C ℤ, I.IsKInjective → IsIso (β.app I)) ∧
      ∀ (P : CochainComplex B ℤ) (I : CochainComplex C ℤ)
        (f : (L.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
        aD.homEquiv (DerivedCategory.Q.{w}.obj P) (DerivedCategory.Q.{w}.obj I)
          (α.hom.app P ≫ DerivedCategory.Q.{w}.map f) =
        DerivedCategory.Q.{w}.map ((aM.mapHomologicalComplex (.up ℤ)).homEquiv P I f) ≫
          β.app I := by
  obtain ⟨RF, β, hRF, hβ⟩ := CategoryTheory.exists_derived G
  let W := HomologicalComplex.quasiIso B (.up ℤ)
  let W' := HomologicalComplex.quasiIso C (.up ℤ)
  let Φ := CochainComplex.KInjectives.localizerMorphism C
  have : LF.IsLeftDerivedFunctor α.hom W := hLF
  have : RF.IsRightDerivedFunctor β W' := hRF
  have : (LF ⋙ RF).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α.hom RF) W :=
    Functor.isLeftDerivedFunctor_of_inverts W _
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α RF)
  have : (RF ⋙ LF).IsRightDerivedFunctor
      (Functor.whiskerRight β LF ≫ (Functor.associator _ _ _).hom) W' :=
    Φ.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure β
      (fun J ↦ hβ J.obj J.property) LF
  let ad := (aM.mapHomologicalComplex (.up ℤ)).derived W W' α.hom β
  refine ⟨RF, β, ad, hβ, ?_⟩
  intro P I f
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  change (((aM.mapHomologicalComplex (.up ℤ)).derivedη W α.hom β).app
    (DerivedCategory.Q.{w}.obj P) ≫ RF.map (α.hom.app P)) ≫
      RF.map (DerivedCategory.Q.{w}.map f) = _
  rw [Adjunction.derivedη_fac_app, Category.assoc]
  have hn := β.naturality f
  change DerivedCategory.Q.{w}.map ((G.mapHomologicalComplex (.up ℤ)).map f) ≫ β.app I =
    β.app ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
      RF.map (DerivedCategory.Q.{w}.map f) at hn
  rw [← hn, ← Category.assoc, ← Functor.map_comp, Adjunction.homEquiv_unit]


private theorem normalizedSpecifiedRight
    {B C : Type*} [Category B] [Category C] [Abelian B] [Abelian C]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} C] [Abelian.HasKInjectiveResolutions C]
    (L : B ⥤ C) (G : C ⥤ B) [L.Additive] [G.Additive] (aM : L ⊣ G)
    (LF : DerivedCategory.{w} B ⥤ DerivedCategory.{w} C)
    (α : DerivedCategory.Q.{w} ⋙ LF ≅ L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w})
    (hLF : LF.IsLeftDerivedFunctor α.hom (HomologicalComplex.quasiIso B (.up ℤ)))
    (RF : DerivedCategory.{w} C ⥤ DerivedCategory.{w} B) (aD : LF ⊣ RF) :
    ∃ β : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RF,
      (∀ I : CochainComplex C ℤ, I.IsKInjective → IsIso (β.app I)) ∧
      ∀ (P : CochainComplex B ℤ) (I : CochainComplex C ℤ)
        (f : (L.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
        aD.homEquiv (DerivedCategory.Q.{w}.obj P) (DerivedCategory.Q.{w}.obj I)
          (α.hom.app P ≫ DerivedCategory.Q.{w}.map f) =
        DerivedCategory.Q.{w}.map ((aM.mapHomologicalComplex (.up ℤ)).homEquiv P I f) ≫
          β.app I := by
  obtain ⟨RF', β', aD', hc, ht⟩ := normalizedDerivedRight L G aM LF α hLF
  let e := aD'.rightAdjointUniq aD
  let β := β' ≫ Functor.whiskerLeft DerivedCategory.Q.{w} e.hom
  refine ⟨β, ?_, ?_⟩
  · intro I hI
    have := hc I hI
    change IsIso (β'.app I ≫ e.hom.app (DerivedCategory.Q.{w}.obj I))
    infer_instance
  · intro P I f
    have he (M : DerivedCategory.{w} B) (N : DerivedCategory.{w} C) (t : LF.obj M ⟶ N) :
        aD.homEquiv M N t = aD'.homEquiv M N t ≫ e.hom.app N := by
      rw [aD.homEquiv_unit, aD'.homEquiv_unit]
      rw [Category.assoc, e.hom.naturality t, ← Category.assoc]
      exact congrArg (fun k ↦ k ≫ RF.map t)
        (Adjunction.unit_rightAdjointUniq_hom_app aD' aD M).symm
    rw [he, ht]
    exact Category.assoc _ _ _


private theorem localizedMateIso
    {B₁ B₂ C₁ C₂ : Type*}
    [Category B₁] [Category B₂] [Category C₁] [Category C₂]
    [Abelian B₁] [Abelian B₂] [Abelian C₁] [Abelian C₂]
    [HasDerivedCategory.{w} B₁] [HasDerivedCategory.{w} B₂]
    [HasDerivedCategory.{w} C₁] [HasDerivedCategory.{w} C₂]
    [Abelian.HasKInjectiveResolutions C₁]
    {La : CochainComplex B₁ ℤ ⥤ CochainComplex C₁ ℤ}
    {L0 : CochainComplex B₂ ℤ ⥤ CochainComplex C₂ ℤ}
    {Ga : CochainComplex C₁ ℤ ⥤ CochainComplex B₁ ℤ}
    {G0 : CochainComplex C₂ ℤ ⥤ CochainComplex B₂ ℤ}
    (aa : La ⊣ Ga) (a0 : L0 ⊣ G0)
    (rV : CochainComplex B₁ ℤ ⥤ CochainComplex B₂ ℤ)
    (rU : CochainComplex C₁ ℤ ⥤ CochainComplex C₂ ℤ)
    (γ : rV ⋙ L0 ≅ La ⋙ rU) (δ0 : Ga ⋙ rV ≅ rU ⋙ G0)
    (hOrd : ∀ P I c, a0.homEquiv _ _ (γ.hom.app P ≫ rU.map c) =
      rV.map (aa.homEquiv P I c) ≫ δ0.hom.app I)
    (LA : DerivedCategory.{w} B₁ ⥤ DerivedCategory.{w} C₁)
    (LZ : DerivedCategory.{w} B₂ ⥤ DerivedCategory.{w} C₂)
    (RA : DerivedCategory.{w} C₁ ⥤ DerivedCategory.{w} B₁)
    (RZ : DerivedCategory.{w} C₂ ⥤ DerivedCategory.{w} B₂)
    (aA : LA ⊣ RA) (aZ : LZ ⊣ RZ)
    (qA : DerivedCategory.Q ⋙ LA ≅ La ⋙ DerivedCategory.Q)
    (qZ : DerivedCategory.Q ⋙ LZ ≅ L0 ⋙ DerivedCategory.Q)
    (βA : Ga ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RA)
    (βZ : G0 ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RZ)
    (tA : ∀ P I c, aA.homEquiv _ _ (qA.hom.app P ≫ DerivedCategory.Q.map c) =
      DerivedCategory.Q.map (aa.homEquiv P I c) ≫ βA.app I)
    (tZ : ∀ P I c, aZ.homEquiv _ _ (qZ.hom.app P ≫ DerivedCategory.Q.map c) =
      DerivedCategory.Q.map (a0.homEquiv P I c) ≫ βZ.app I)
    (cA : ∀ I : CochainComplex C₁ ℤ, I.IsKInjective → IsIso (βA.app I))
    (cZ : ∀ I : CochainComplex C₂ ℤ, I.IsKInjective → IsIso (βZ.app I))
    (hU : ∀ I : CochainComplex C₁ ℤ, I.IsKInjective → (rU.obj I).IsKInjective)
    (dV : DerivedCategory.{w} B₁ ⥤ DerivedCategory.{w} B₂)
    (dU : DerivedCategory.{w} C₁ ⥤ DerivedCategory.{w} C₂)
    (qV : DerivedCategory.Q ⋙ dV ≅ rV ⋙ DerivedCategory.Q)
    (qU : DerivedCategory.Q ⋙ dU ≅ rU ⋙ DerivedCategory.Q)
    (b : LA ⋙ dU ≅ dV ⋙ LZ)
    (hb : ∀ P, LZ.map (qV.hom.app P) ≫ qZ.hom.app (rV.obj P) ≫
        DerivedCategory.Q.map (γ.hom.app P) =
      b.inv.app (DerivedCategory.Q.obj P) ≫ dU.map (qA.hom.app P) ≫
        qU.hom.app (La.obj P)) :
    IsIso (mateEquiv aA aZ (TwoSquare.mk _ _ _ _ b.inv)).natTrans := by
  let δ := (mateEquiv aA aZ (TwoSquare.mk _ _ _ _ b.inv)).natTrans
  have hn (I : CochainComplex C₁ ℤ) :
      dV.map (βA.app I) ≫ δ.app (DerivedCategory.Q.obj I) ≫
        RZ.map (qU.hom.app I) =
      qV.hom.app (Ga.obj I) ≫ DerivedCategory.Q.map (δ0.hom.app I) ≫
        βZ.app (rU.obj I) := by
    let P := Ga.obj I
    let c : La.obj P ⟶ I := aa.counit.app I
    have hc : aa.homEquiv (Ga.obj I) I (aa.counit.app I) = 𝟙 (Ga.obj I) := by
      rw [← aa.homEquiv_symm_id I]
      exact Equiv.apply_symm_apply _ _
    have hs := tA P I c
    rw [hc, DerivedCategory.Q.map_id, Category.id_comp] at hs
    have hm := mate_adjunct aA aZ dV dU b.inv
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
      (qA.hom.app P ≫ DerivedCategory.Q.map c)
    rw [hs] at hm
    change _ = dV.map (βA.app I) ≫ δ.app (DerivedCategory.Q.obj I) at hm
    erw [← Category.assoc, ← hm]
    erw [← aZ.homEquiv_naturality_right]
    have hq := qU.hom.naturality c
    change dU.map (DerivedCategory.Q.map c) ≫ qU.hom.app I =
      qU.hom.app (La.obj P) ≫ DerivedCategory.Q.map (rU.map c) at hq
    have hb' := (hb P).symm
    rw [← Category.assoc] at hb'
    erw [dU.map_comp, Category.assoc, Category.assoc, hq,
      ← Category.assoc, ← Category.assoc, hb']
    rw [Category.assoc, Category.assoc, ← DerivedCategory.Q.map_comp]
    erw [aZ.homEquiv_naturality_left, tZ]
    rw [hOrd, hc]
    simp [P]
  have hi (I : CochainComplex C₁ ℤ) (hI : I.IsKInjective) :
      IsIso (δ.app (DerivedCategory.Q.obj I)) := by
    have : IsIso (βA.app I) := cA I hI
    have : IsIso (βZ.app (rU.obj I)) := cZ _ (hU I hI)
    have : IsIso (dV.map (βA.app I) ≫ δ.app (DerivedCategory.Q.obj I) ≫
        RZ.map (qU.hom.app I)) := by rw [hn]; infer_instance
    have : IsIso (δ.app (DerivedCategory.Q.obj I) ≫ RZ.map (qU.hom.app I)) :=
      IsIso.of_isIso_comp_left (dV.map (βA.app I)) _
    exact IsIso.of_isIso_comp_right _ (RZ.map (qU.hom.app I))
  have : ∀ M, IsIso (δ.app M) := by
    intro M
    obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
    have : IsIso (δ.app (DerivedCategory.Q.obj I)) := hi I hI
    exact (NatTrans.isIso_app_iff_of_iso δ e).mpr inferInstance
  exact NatIso.isIso_of_isIso_app δ


private theorem moduleDerivedMateIso
    {B₁ B₂ C₁ C₂ : Type (u + 2)}
    [Category.{u + 1} B₁] [Category.{u + 1} B₂]
    [Category.{u + 1} C₁] [Category.{u + 1} C₂]
    [Abelian B₁] [Abelian B₂] [Abelian C₁] [Abelian C₂]
    [HasDerivedCategory.{u + 2} B₁] [HasDerivedCategory.{u + 2} B₂]
    [HasDerivedCategory.{u + 2} C₁] [HasDerivedCategory.{u + 2} C₂]
    [Abelian.HasKInjectiveResolutions C₁] [Abelian.HasKInjectiveResolutions C₂]
    (La : B₁ ⥤ C₁) (L0 : B₂ ⥤ C₂) (Ga : C₁ ⥤ B₁) (G0 : C₂ ⥤ B₂)
    [La.Additive] [L0.Additive] [Ga.Additive] [G0.Additive]
    (aa : La ⊣ Ga) (a0 : L0 ⊣ G0)
    (rV : B₁ ⥤ B₂) (rU : C₁ ⥤ C₂) [rV.Additive] [rU.Additive]
    [rU.PreservesKInjectiveComplexes]
    (γ : rV ⋙ L0 ≅ La ⋙ rU)
    (hi : IsIso (mateEquiv aa a0 (TwoSquare.mk _ _ _ _ γ.hom)).natTrans)
    (LA : DerivedCategory.{u + 2} B₁ ⥤ DerivedCategory.{u + 2} C₁)
    (LZ : DerivedCategory.{u + 2} B₂ ⥤ DerivedCategory.{u + 2} C₂)
    (RA : DerivedCategory.{u + 2} C₁ ⥤ DerivedCategory.{u + 2} B₁)
    (RZ : DerivedCategory.{u + 2} C₂ ⥤ DerivedCategory.{u + 2} B₂)
    (aA : LA ⊣ RA) (aZ : LZ ⊣ RZ)
    (qA : DerivedCategory.Q ⋙ LA ≅ La.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qZ : DerivedCategory.Q ⋙ LZ ≅ L0.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hA : LA.IsLeftDerivedFunctor qA.hom (HomologicalComplex.quasiIso B₁ (.up ℤ)))
    (hZ : LZ.IsLeftDerivedFunctor qZ.hom (HomologicalComplex.quasiIso B₂ (.up ℤ)))
    (dV : DerivedCategory.{u + 2} B₁ ⥤ DerivedCategory.{u + 2} B₂)
    (dU : DerivedCategory.{u + 2} C₁ ⥤ DerivedCategory.{u + 2} C₂)
    (qV : DerivedCategory.Q ⋙ dV ≅ rV.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qU : DerivedCategory.Q ⋙ dU ≅ rU.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (b : LA ⋙ dU ≅ dV ⋙ LZ)
    (hb : ∀ P, DerivedPullComparisonFormula
      (DerivedCategory.Q : CochainComplex B₁ ℤ ⥤ _) DerivedCategory.Q
      DerivedCategory.Q DerivedCategory.Q rV rU L0 La
      qV.symm qZ.hom γ.hom qA.hom qU.symm b.inv P) :
    IsIso (mateEquiv aA aZ (TwoSquare.mk _ _ _ _ b.inv)).natTrans := by
  obtain ⟨βA, cA, tA⟩ := normalizedSpecifiedRight La Ga aa LA qA hA RA aA
  obtain ⟨βZ, cZ, tZ⟩ := normalizedSpecifiedRight L0 G0 a0 LZ qZ hZ RZ aZ
  have := hi
  let δ0 := asIso (mateEquiv aa a0 (TwoSquare.mk _ _ _ _ γ.hom)).natTrans
  let γc := complexSquare rV L0 La rU γ
  let δc := complexSquare Ga rV rU G0 δ0
  have ht : ∀ P I c,
      (a0.mapHomologicalComplex (.up ℤ)).homEquiv _ _
        (γc.hom.app P ≫ (rU.mapHomologicalComplex (.up ℤ)).map c) =
      (rV.mapHomologicalComplex (.up ℤ)).map
        ((aa.mapHomologicalComplex (.up ℤ)).homEquiv P I c) ≫ δc.hom.app I := by
    intro P I c
    ext n : 1
    simp only [Adjunction.homEquiv_unit, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, Adjunction.mapHomologicalComplex_unit_app_f]
    have hg : (γc.hom.app P).f n = γ.hom.app (P.X n) := by
      simp only [γc, complexSquare, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app, HomologicalComplex.comp_f,
        Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
        NatTrans.mapHomologicalComplex_app_f,
        Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
      change 𝟙 _ ≫ γ.hom.app (P.X n) ≫ 𝟙 _ = γ.hom.app (P.X n)
      rw [Category.id_comp]
      exact Category.comp_id (γ.hom.app (P.X n))
    have hd : (δc.hom.app I).f n = δ0.hom.app (I.X n) := by
      simp only [δc, complexSquare, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app, HomologicalComplex.comp_f,
        Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
        NatTrans.mapHomologicalComplex_app_f,
        Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
      change 𝟙 _ ≫ δ0.hom.app (I.X n) ≫ 𝟙 _ = δ0.hom.app (I.X n)
      rw [Category.id_comp]
      exact Category.comp_id (δ0.hom.app (I.X n))
    rw [hg, hd]
    exact mate_adjunct aa a0 rV rU γ.hom (P.X n) (I.X n) (c.f n)
  apply localizedMateIso (aa.mapHomologicalComplex (.up ℤ))
    (a0.mapHomologicalComplex (.up ℤ))
    (rV.mapHomologicalComplex (.up ℤ)) (rU.mapHomologicalComplex (.up ℤ))
    γc δc ht LA LZ RA RZ aA aZ qA qZ βA βZ tA tZ cA cZ
    (fun I hI ↦ by
      let : I.IsKInjective := hI
      exact Functor.PreservesKInjectiveComplexes.isKInjective_map I)
    dV dU qV qU b
  intro P
  have hg : γc.hom.app P = (NatTrans.mapHomologicalComplex γ.hom (.up ℤ)).app P := by
    ext n
    simp only [γc, complexSquare, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
        NatTrans.mapHomologicalComplex_app_f,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    change 𝟙 _ ≫ γ.hom.app (P.X n) ≫ 𝟙 _ = γ.hom.app (P.X n)
    rw [Category.id_comp]
    exact Category.comp_id (γ.hom.app (P.X n))
  rw [hg]
  exact hb P


private theorem scalarFormulaAll
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : AdicCoefficientDatum A)
    (bal : Balancing d) (p : PullCompatibility f d (bal.ρ Y) (bal.ρ X))
    (P : Cx (ring Y d true)) :
    DerivedPullComparisonFormula (Q (ring Y d true)) (Q (ring Y d false))
      (Q (ring X d true)) (Q (ring X d false))
      (res (scalar Y d)) (res (scalar X d)) (modulePull f d false) (modulePull f d true)
      (resFactors (scalar Y d)) p.constant.ordinaryFactors.hom p.ordinaryScalar.inv
      p.completed.ordinaryFactors.hom (resFactors (scalar X d)) p.a.inv P := by
  let r := (res (scalar Y d)).mapHomologicalComplex (.up ℤ)
  let b := (modulePull f d true).mapHomologicalComplex (.up ℤ)
  let s := (res (scalar X d)).mapHomologicalComplex (.up ℤ)
  let γ := complexSquare (res (scalar Y d)) (modulePull f d false)
    (modulePull f d true) (res (scalar X d)) p.ordinaryScalar.symm
  let F := dres (scalar Y d) ⋙ p.constant.ordinary
  let G := b ⋙ s ⋙ Q (ring X d false)
  let l : Q (ring Y d true) ⋙ F ⟶ G :=
    Functor.whiskerRight (resFactors (scalar Y d)).inv p.constant.ordinary ≫
      Functor.whiskerLeft r p.constant.ordinaryFactors.hom ≫
      Functor.whiskerRight γ.hom (Q (ring X d false))
  let z : Q (ring Y d true) ⋙ F ⟶ G :=
    Functor.whiskerLeft (Q (ring Y d true)) p.a.inv ≫
      Functor.whiskerRight p.completed.ordinaryFactors.hom (dres (scalar X d)) ≫
      Functor.whiskerLeft b (resFactors (scalar X d)).inv
  have good (K : Cx (ring Y d true)) (hK : K.IsAcyclicTensorKFlat)
      (hf : ∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) : l.app K = z.app K := by
    exact p.a_computes K hK hf
  obtain ⟨K, k, hK, hflat, hk, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  have hK' : K.IsAcyclicTensorKFlat :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K).1 hK
  have hflat' : ∀ i : ℤ, SheafOfModules.IsFlat (K.X i) := hflat
  have : QuasiIso k := hk
  have : IsIso ((Q (ring Y d true) ⋙ F).map k) := by
    change IsIso (F.map ((Q (ring Y d true)).map k))
    infer_instance
  have hP : l.app P = z.app P := by
    apply (cancel_epi ((Q (ring Y d true) ⋙ F).map k)).mp
    rw [l.naturality k, z.naturality k, good K hK' hflat']
  exact hP


private theorem ordinaryRingMateIso
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {J : GrothendieckTopology C} {H : GrothendieckTopology E}
    {L : Sheaf J (Type u) ⥤ Sheaf H (Type u)}
    (V : Sheaf H (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    (F : InverseImageData L)
    (Ra Sa : Sheaf J CommRingCat.{u}) (Rb Sb : Sheaf H CommRingCat.{u})
    (a : Ra ⟶ Sa) (b : Rb ⟶ Sb)
    (cR : F.rings.obj Ra ⟶ Rb) (cS : F.rings.obj Sa ⟶ Sb)
    (γ : res a ⋙ pull F cR ⟶ pull F cS ⋙ res b)
    (hn : ∀ M, pullInsertion F cR ((res a).obj M) ≫
      (underlying Rb).map (γ.app M) = pullInsertion F cS M)
    (Ga : Mod Sb ⥤ Mod Sa) (G0 : Mod Rb ⥤ Mod Ra)
    (aa : pull F cS ⊣ Ga) (a0 : pull F cR ⊣ G0)
    (ea : Ga ⋙ underlying Sa ≅ underlying Sb ⋙ V)
    (e0 : G0 ⋙ underlying Ra ≅ underlying Rb ⋙ V)
    (ha : ∀ M N t, (underlying Sa).map (aa.homEquiv M N t) ≫ ea.hom.app N =
      adj.homEquiv _ _ (pullInsertion F cS M ≫ (underlying Sb).map t))
    (h0 : ∀ M N t, (underlying Ra).map (a0.homEquiv M N t) ≫ e0.hom.app N =
      adj.homEquiv _ _ (pullInsertion F cR M ≫ (underlying Rb).map t)) :
    IsIso (mateEquiv aa a0 (TwoSquare.mk _ _ _ _ γ)).natTrans := by
  let δ := (mateEquiv aa a0 (TwoSquare.mk _ _ _ _ γ)).natTrans
  have hi (N : Mod Sb) : (underlying Ra).map (δ.app N) ≫
      e0.hom.app ((res b).obj N) = ea.hom.app N := by
    have hc : aa.homEquiv (Ga.obj N) N (aa.counit.app N) = 𝟙 (Ga.obj N) := by
      rw [← aa.homEquiv_symm_id N]
      exact Equiv.apply_symm_apply _ _
    have hm := mate_adjunct aa a0 (res a) (res b) γ (Ga.obj N) N (aa.counit.app N)
    rw [hc, (res a).map_id, Category.id_comp] at hm
    change a0.homEquiv ((res a).obj (Ga.obj N)) ((res b).obj N)
      (γ.app (Ga.obj N) ≫ (res b).map (aa.counit.app N)) = δ.app N at hm
    have hcomp : pullInsertion F cR ((res a).obj (Ga.obj N)) ≫
        (underlying Rb).map (γ.app (Ga.obj N) ≫ (res b).map (aa.counit.app N)) =
        pullInsertion F cS (Ga.obj N) ≫ (underlying Sb).map (aa.counit.app N) := by
      rw [Functor.map_comp, ← Category.assoc]
      change (pullInsertion F cR ((res a).obj (Ga.obj N)) ≫
        (underlying Rb).map (γ.app (Ga.obj N))) ≫
          (underlying Sb).map (aa.counit.app N) = _
      exact congrArg (fun t ↦ t ≫ (underlying Sb).map (aa.counit.app N)) (hn (Ga.obj N))
    calc
      (underlying Ra).map (δ.app N) ≫ e0.hom.app ((res b).obj N) =
          (underlying Ra).map (a0.homEquiv _ _
            (γ.app (Ga.obj N) ≫ (res b).map (aa.counit.app N))) ≫
              e0.hom.app ((res b).obj N) :=
        congrArg (fun t ↦ (underlying Ra).map t ≫ e0.hom.app ((res b).obj N)) hm.symm
      _ = adj.homEquiv ((underlying Sa).obj (Ga.obj N)) ((underlying Sb).obj N)
          (pullInsertion F cR ((res a).obj (Ga.obj N)) ≫
            (underlying Rb).map (γ.app (Ga.obj N) ≫ (res b).map (aa.counit.app N))) :=
        h0 _ _ _
      _ = adj.homEquiv ((underlying Sa).obj (Ga.obj N)) ((underlying Sb).obj N)
          (pullInsertion F cS (Ga.obj N) ≫ (underlying Sb).map (aa.counit.app N)) :=
        congrArg (adj.homEquiv ((underlying Sa).obj (Ga.obj N))
          ((underlying Sb).obj N)) hcomp
      _ = (underlying Sa).map (aa.homEquiv _ _ (aa.counit.app N)) ≫ ea.hom.app N :=
        (ha (Ga.obj N) N (aa.counit.app N)).symm
      _ = ea.hom.app N := by
        have hh := congrArg (fun t : Ga.obj N ⟶ Ga.obj N ↦
          (underlying Sa).map t ≫ ea.hom.app N) hc
        exact hh.trans ((congrArg (fun t ↦ t ≫ ea.hom.app N)
          ((underlying Sa).map_id (Ga.obj N))).trans (Category.id_comp _))
  have : ∀ N, IsIso (δ.app N) := by
    intro N
    have : IsIso ((underlying Ra).map (δ.app N) ≫ e0.hom.app ((res b).obj N)) := by
      rw [hi]
      infer_instance
    have : IsIso ((underlying Ra).map (δ.app N)) := IsIso.of_isIso_comp_right _
      (e0.hom.app ((res b).obj N))
    exact isIso_of_reflects_iso _ (underlying Ra)
  exact NatIso.isIso_of_isIso_app δ

private theorem restrictionKInjective
    (T : Scheme.{u}) (d : AdicCoefficientDatum A) :
    (res (scalar T d)).PreservesKInjectiveComplexes ∧
      (tres (scalar T d)).PreservesKInjectiveComplexes := by
  let := d.noetherian
  have hf := change_exact (scalar T d) (flat_and_quotients (topology T) A d.ideal).1
  have : PreservesFiniteLimits (change (scalar T d)) := hf.1
  have : PreservesFiniteColimits (change (scalar T d)) := hf.2
  have : (change (scalar T d)).PreservesHomology := {}
  let adj0 : change (scalar T d) ⊣ res (scalar T d) :=
    SheafOfModules.RingedTensor.tensorAdjunction (scalar T d)
  have h1 := adj0.preservesKInjectiveComplexes
  let E := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (change (scalar T d))
  have : E.Additive := inferInstance
  have : PreservesFiniteLimits E := ⟨fun K _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits E := ⟨fun K _ _ ↦ inferInstance⟩
  have : E.PreservesHomology := {}
  have adj : E ⊣ tres (scalar T d) := Adjunction.whiskerRight ℕᵒᵖ
    (SheafOfModules.RingedTensor.tensorAdjunction (scalar T d))
  exact ⟨h1, adj.preservesKInjectiveComplexes⟩

private theorem towerMateIso
    {B₁ B₂ C₁ C₂ : Type (u + 2)}
    [Category.{u + 1} B₁] [Category.{u + 1} B₂]
    [Category.{u + 1} C₁] [Category.{u + 1} C₂]
    {La : B₁ ⥤ C₁} {L0 : B₂ ⥤ C₂} {Ga : C₁ ⥤ B₁} {G0 : C₂ ⥤ B₂}
    (aa : La ⊣ Ga) (a0 : L0 ⊣ G0)
    (rV : B₁ ⥤ B₂) (rU : C₁ ⥤ C₂)
    (γ : rV ⋙ L0 ≅ La ⋙ rU)
    (hi : IsIso (mateEquiv aa a0 (TwoSquare.mk _ _ _ _ γ.hom)).natTrans) :
    IsIso (mateEquiv (Adjunction.whiskerRight ℕᵒᵖ aa)
      (Adjunction.whiskerRight ℕᵒᵖ a0)
      (TwoSquare.mk _ _ _ _ (towerSquare rV L0 La rU γ).hom)).natTrans := by
  have := hi
  let δ := asIso (mateEquiv aa a0 (TwoSquare.mk _ _ _ _ γ.hom)).natTrans
  have he : (mateEquiv (Adjunction.whiskerRight ℕᵒᵖ aa)
      (Adjunction.whiskerRight ℕᵒᵖ a0)
      (TwoSquare.mk _ _ _ _ (towerSquare rV L0 La rU γ).hom)).natTrans =
      (towerSquare Ga rV rU G0 δ).hom := by
    ext N j
    simp [mateEquiv, towerSquare, δ]
  rw [he]
  infer_instance

/-- The normalized ordinary and strict-tower scalar direct-image mates are invertible.

Source: Stacks 03D2, 03D3, 0FND and 0DVC; main-20261015, proper-base-change,
completed-exchange-coherence, second paragraph, scalar setup.
(blueprint: lem-weil-pbc-strict-quotient-scalar-direct-isomorphisms).

Proof: construct the ordinary module right adjoints with their underlying geometric
adjunction and scalar-insertion normalization. Transpose the counit across the scalar
square. The insertion equation identifies its underlying mate with the identity
geometric direct-image comparison, so the mate is invertible. Whiskering this calculation
by the full natural-number-opposite category gives the same assertion for strict towers.
Flat scalar extension is exact, so its right adjoint, scalar restriction, preserves
K-injective complexes, also for towers. Construct the normalized derived right adjunction
and transport it to any supplied right adjoint by uniqueness. On a K-injective target,
the ordinary mate and the derived comparison maps are all isomorphisms. The derived
adjunct equation therefore makes the supplied derived mate invertible there, and every
derived object is isomorphic to a K-injective representative. The specified comparison
is the one used in this calculation: its ordinary computation formula extends from
flat-term K-flat complexes to every complex by a flat-term resolution, naturality, and
cancellation of the localized quasi-isomorphism; the tower formula is supplied on every
representative already. All arguments take place in the full categories of strict
towers and retain transition arrows. Zero rings and the terminal or zero ideal require
no change. -/
theorem strictQuotientScalarDirectIsomorphisms
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : AdicCoefficientDatum A)
    (bal : Balancing d) (p : PullCompatibility f d (bal.ρ Y) (bal.ρ X))
    (Ra : D (ring X d true) ⥤ D (ring Y d true))
    (R0 : D (ring X d false) ⥤ D (ring Y d false))
    (Ha : TD (ring X d true) ⥤ TD (ring Y d true))
    (H0 : TD (ring X d false) ⥤ TD (ring Y d false))
    (ordinaryAdjA : p.completed.ordinary ⊣ Ra)
    (ordinaryAdj0 : p.constant.ordinary ⊣ R0)
    (diagramAdjA : p.completed.diagrams ⊣ Ha)
    (diagramAdj0 : p.constant.diagrams ⊣ H0) :
    IsIso (mateEquiv ordinaryAdjA ordinaryAdj0
      (TwoSquare.mk _ _ _ _ p.a.inv)).natTrans ∧
    IsIso (mateEquiv diagramAdjA diagramAdj0
      (TwoSquare.mk _ _ _ _ p.p.inv)).natTrans := by
  let V := (proEtaleModelBaseChange f).sheafPushforwardContinuous (Type (u + 1))
    (topology Y) (topology X)
  let adj := (proEtaleModelBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
    (topology Y) (topology X)
  obtain ⟨Ga, ea, aa, ha⟩ := module_adjunction_exists V adj (inverseData f)
    (coefficient f d true)
  obtain ⟨G0, e0, a0, h0⟩ := module_adjunction_exists V adj (inverseData f)
    (coefficient f d false)
  have hn (M : Mod (ring Y d true)) :
      pullInsertion (inverseData f) (coefficient f d false) ((res (scalar Y d)).obj M) ≫
        (underlying (ring X d false)).map (p.ordinaryScalar.inv.app M) =
      pullInsertion (inverseData f) (coefficient f d true) M := by
    rw [p.ordinaryScalar_normalized]
    dsimp only [coefficient, modulePull]
    exact (ordinaryPullComparison_existsUnique (inverseData f) A d.ideal).exists.choose_spec M
  have hi := ordinaryRingMateIso V adj (inverseData f)
    (ring Y d false) (ring Y d true) (ring X d false) (ring X d true)
    (scalar Y d) (scalar X d) (coefficient f d false) (coefficient f d true)
    p.ordinaryScalar.inv hn Ga.obj G0.obj aa a0 ea e0 ha h0
  have : (res (scalar X d)).PreservesKInjectiveComplexes := (restrictionKInjective X d).1
  have : (tres (scalar X d)).PreservesKInjectiveComplexes := (restrictionKInjective X d).2
  have groth (b : Bool) : IsGrothendieckAbelian.{u + 1} (Mod (ring X d b)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      (topology X) (ring X d b)).1
  have := groth true
  have := groth false
  let : HasDerivedCategory.{u + 2} (Mod (ring X d true)) := HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 2} (Mod (ring X d false)) := HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 2} (Mod (ring Y d true)) := HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 2} (Mod (ring Y d false)) := HasDerivedCategory.standard _
  constructor
  · exact moduleDerivedMateIso
      (B₁ := Mod (ring Y d true)) (B₂ := Mod (ring Y d false))
      (C₁ := Mod (ring X d true)) (C₂ := Mod (ring X d false))
      (modulePull f d true) (modulePull f d false)
      Ga.obj G0.obj aa a0 (res (scalar Y d)) (res (scalar X d))
      p.ordinaryScalar.symm hi p.completed.ordinary p.constant.ordinary Ra R0
      ordinaryAdjA ordinaryAdj0 p.completed.ordinaryFactors p.constant.ordinaryFactors
      p.completed.ordinaryUniversal p.constant.ordinaryUniversal
      (dres (scalar Y d)) (dres (scalar X d))
      (resFactors (scalar Y d)).symm (resFactors (scalar X d)).symm p.a
      (scalarFormulaAll f d bal p)
  · have grothT (b : Bool) : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ Mod (ring X d b)) := by
      have := smallModuleDiagrams_isGrothendieckAbelian (topology X)
        (siteModuleRings (ring X d b)) (ULiftHom.{u + 1} (ULift.{u + 1} ℕᵒᵖ))
      exact IsGrothendieckAbelian.of_equivalence
        (ULiftHomULiftCategory.equiv.{u + 1, u + 1} ℕᵒᵖ).congrLeft.symm
    have := grothT true
    have := grothT false
    let : HasDerivedCategory.{u + 2} (ℕᵒᵖ ⥤ Mod (ring X d true)) := HasDerivedCategory.standard _
    let : HasDerivedCategory.{u + 2} (ℕᵒᵖ ⥤ Mod (ring X d false)) := HasDerivedCategory.standard _
    let : HasDerivedCategory.{u + 2} (ℕᵒᵖ ⥤ Mod (ring Y d true)) := HasDerivedCategory.standard _
    let : HasDerivedCategory.{u + 2} (ℕᵒᵖ ⥤ Mod (ring Y d false)) := HasDerivedCategory.standard _
    let ga := (Functor.whiskeringRight ℕᵒᵖ _ _).obj Ga.obj
    let g0 := (Functor.whiskeringRight ℕᵒᵖ _ _).obj G0.obj
    let γ : tres (scalar Y d) ⋙ towerPull f d false ≅
        towerPull f d true ⋙ tres (scalar X d) :=
      towerSquare (res (scalar Y d)) (modulePull f d false)
      (modulePull f d true) (res (scalar X d)) p.ordinaryScalar.symm
    have hit := towerMateIso aa a0 (res (scalar Y d)) (res (scalar X d))
      p.ordinaryScalar.symm hi
    have : Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ Mod (ring X d true)) := inferInstance
    have : Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ Mod (ring X d false)) := inferInstance
    refine moduleDerivedMateIso
      (B₁ := ℕᵒᵖ ⥤ Mod (ring Y d true)) (B₂ := ℕᵒᵖ ⥤ Mod (ring Y d false))
      (C₁ := ℕᵒᵖ ⥤ Mod (ring X d true)) (C₂ := ℕᵒᵖ ⥤ Mod (ring X d false))
      (towerPull f d true) (towerPull f d false)
      ga g0 (Adjunction.whiskerRight ℕᵒᵖ aa) (Adjunction.whiskerRight ℕᵒᵖ a0)
      (tres (scalar Y d)) (tres (scalar X d)) γ hit
      p.completed.diagrams p.constant.diagrams Ha H0 diagramAdjA diagramAdj0
      p.completed.diagramFactors p.constant.diagramFactors
      p.completed.diagramUniversal p.constant.diagramUniversal
      (tdres (scalar Y d)) (tdres (scalar X d))
      (tresFactors (scalar Y d)).symm (tresFactors (scalar X d)).symm p.p ?_
    intro P
    exact p.p_computes P

end AlgebraicGeometry.Scheme.StrictScalarBalancing
