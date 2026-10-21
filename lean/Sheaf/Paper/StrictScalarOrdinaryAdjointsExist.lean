/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import Sheaf.Paper.StrictQuotientScalarBalancing
public import Mathlib.CategoryTheory.Adjunction.Mates
import all Sheaf.Paper.CompletedPullbackAdjunction
import all Sheaf.CategoryTheory.FlatRestrictionDerivedMate
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Sheaf.Paper.StrictQuotientScalarBalancing
import all Sheaf.Paper.ConstantCompletionEquivalence

/-! # Ordinary normalized adjoints on the transported pro-etale model

Source: Stacks 07A6 (sites-cohomology.tex, lemma-adjoint); scalar supplement, Step 6.
(blueprint: lem-weil-pbc-strict-scalar-ordinary-adjoints-exist).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits ConstantCompletion
namespace AlgebraicGeometry.Scheme.StrictScalarBalancing
variable {A : Type (u + 1)} [CommRing A]

private theorem completed_pull_exact (d : AdicCoefficientDatum A) (B : Balancing d)
    {U V : Scheme.{u}} (f : U ⟶ V)
    (P : PullCompatibility f d (B.ρ V) (B.ρ U)) :
    PreservesFiniteLimits (modulePull f d true) := by
  have : IsIso (constantMap (inverseData f) A) := by
    dsimp only [constantMap]
    infer_instance
  have : PreservesFiniteLimits (modulePull f d false) :=
    pull_finiteLimits_of_isIso (inverseData f) (constantMap (inverseData f) A)
  have := (siteRestrictScalars_exact (scalar V d)).1
  have := (siteRestrictScalars_exact (scalar U d)).1
  have : PreservesFiniteLimits (modulePull f d true ⋙ res (scalar U d)) :=
    preservesFiniteLimits_of_natIso P.ordinaryScalar.symm
  have : (res (scalar U d)).ReflectsIsomorphisms :=
    siteRestrictScalars_reflectsIsomorphisms (scalar U d)
  have : ReflectsFiniteLimits (res (scalar U d)) :=
    { reflects := fun _ _ _ ↦ reflectsLimitsOfShape_of_reflectsIsomorphisms }
  exact preservesFiniteLimits_of_reflects_of_preserves _ (res (scalar U d))

private theorem ordinary_mate_iso (d : AdicCoefficientDatum A) (B : Balancing d)
    {U V : Scheme.{u}} (f : U ⟶ V)
    (P : PullCompatibility f d (B.ρ V) (B.ρ U))
    (GA : Mod (ring U d true) ⥤ Mod (ring V d true))
    (G0 : Mod (ring U d false) ⥤ Mod (ring V d false))
    (aA : modulePull f d true ⊣ GA) (a0 : modulePull f d false ⊣ G0)
    (eA : GA ⋙ underlying (ring V d true) ≅ underlying (ring U d true) ⋙
      (proEtaleModelBaseChange f).sheafPushforwardContinuous (Type (u + 1))
        (topology V) (topology U))
    (e0 : G0 ⋙ underlying (ring V d false) ≅ underlying (ring U d false) ⋙
      (proEtaleModelBaseChange f).sheafPushforwardContinuous (Type (u + 1))
        (topology V) (topology U))
    (hA : ∀ M N k, (underlying (ring V d true)).map (aA.homEquiv M N k) ≫
      eA.hom.app N =
      ((proEtaleModelBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
        (topology V) (topology U)).homEquiv _ _
        (pullInsertion (inverseData f) (coefficient f d true) M ≫
          (underlying (ring U d true)).map k))
    (h0 : ∀ M N k, (underlying (ring V d false)).map (a0.homEquiv M N k) ≫
      e0.hom.app N =
      ((proEtaleModelBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
        (topology V) (topology U)).homEquiv _ _
        (pullInsertion (inverseData f) (coefficient f d false) M ≫
          (underlying (ring U d false)).map k)) :
    IsIso (mateEquiv aA a0 (TwoSquare.mk _ _ _ _ P.ordinaryScalar.inv)).natTrans := by
  let δ := (mateEquiv aA a0 (TwoSquare.mk _ _ _ _ P.ordinaryScalar.inv)).natTrans
  have hd : ∀ N, IsIso (δ.app N) := by
    intro N
    have ht := FlatRingedDiagramInput.adjunct_mate aA a0 _ _ P.ordinaryScalar
      (GA.obj N) N (aA.counit.app N)
    have htri : aA.homEquiv _ N (aA.counit.app N) = 𝟙 _ := by
      rw [← aA.homEquiv_symm_id N]
      exact Equiv.apply_symm_apply _ _
    rw [htri] at ht
    erw [CategoryTheory.Functor.map_id, Category.id_comp] at ht
    have hi := (ordinaryPullComparison_existsUnique (inverseData f) A d.ideal).exists.choose_spec
      (GA.obj N)
    change pullInsertion (inverseData f) (constantMap (inverseData f) A)
        ((res (scalar V d)).obj (GA.obj N)) ≫
        (underlying (ring U d false)).map
          ((ordinaryPullComparison (inverseData f) A d.ideal).app (GA.obj N)) = _ at hi
    erw [← P.ordinaryScalar_normalized] at hi
    have hh : (underlying (ring V d false)).map (δ.app N) ≫
        e0.hom.app ((res (scalar U d)).obj N) = eA.hom.app N := by
      erw [← ht, h0]
      simp only [Functor.map_comp]
      erw [← Category.assoc, hi, Category.assoc, ← hA, htri]
      exact (CategoryTheory.Functor.map_id (underlying (ring V d true)) (GA.obj N)) ▸
        Category.id_comp _
    have : IsIso ((underlying (ring V d false)).map (δ.app N) ≫
        e0.hom.app ((res (scalar U d)).obj N)) := by rw [hh]; infer_instance
    have : IsIso ((underlying (ring V d false)).map (δ.app N)) :=
      IsIso.of_isIso_comp_right _ (e0.hom.app ((res (scalar U d)).obj N))
    exact isIso_of_reflects_iso (δ.app N) (underlying (ring V d false))
  exact NatIso.isIso_of_isIso_app δ

private theorem derived_mate_iso
    {C E C₀ E₀ : Type*} [Category C] [Category E] [Category C₀] [Category E₀]
    [Abelian C] [Abelian E] [Abelian C₀] [Abelian E₀]
    [HasDerivedCategory C] [HasDerivedCategory E]
    [HasDerivedCategory C₀] [HasDerivedCategory E₀]
    [Abelian.HasKInjectiveResolutions E]
    (F : C ⥤ E) (G : E ⥤ C) (F₀ : C₀ ⥤ E₀) (G₀ : E₀ ⥤ C₀)
    (r : C ⥤ C₀) (s : E ⥤ E₀)
    [F.Additive] [G.Additive] [F₀.Additive] [G₀.Additive] [r.Additive] [s.Additive]
    (aM : F ⊣ G) (aM₀ : F₀ ⊣ G₀)
    (LF : DerivedCategory C ⥤ DerivedCategory E)
    (RF : DerivedCategory E ⥤ DerivedCategory C)
    (LF₀ : DerivedCategory C₀ ⥤ DerivedCategory E₀)
    (RF₀ : DerivedCategory E₀ ⥤ DerivedCategory C₀)
    (rD : DerivedCategory C ⥤ DerivedCategory C₀)
    (sD : DerivedCategory E ⥤ DerivedCategory E₀)
    (α : DerivedCategory.Q ⋙ LF ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₀ : DerivedCategory.Q ⋙ LF₀ ≅ F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (β : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (β₀ : G₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF₀)
    (qR : DerivedCategory.Q ⋙ rD ≅ r.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qS : DerivedCategory.Q ⋙ sD ≅ s.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (a : LF ⊣ RF) (a₀ : LF₀ ⊣ RF₀)
    (hβ : ∀ I : CochainComplex E ℤ, I.IsKInjective → IsIso (β.app I))
    (hβ₀ : ∀ I : CochainComplex E₀ ℤ, I.IsKInjective → IsIso (β₀.app I))
    (hs : ∀ I : CochainComplex E ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((s.mapHomologicalComplex (.up ℤ)).obj I))
    (ht : ∀ (P : CochainComplex C ℤ) (I : CochainComplex E ℤ)
      (k : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
      a.homEquiv _ _ (α.hom.app P ≫ DerivedCategory.Q.map k) =
        DerivedCategory.Q.map ((aM.mapHomologicalComplex (.up ℤ)).homEquiv P I k) ≫ β.app I)
    (ht₀ : ∀ (P : CochainComplex C₀ ℤ) (I : CochainComplex E₀ ℤ)
      (k : (F₀.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
      a₀.homEquiv _ _ (α₀.hom.app P ≫ DerivedCategory.Q.map k) =
        DerivedCategory.Q.map ((aM₀.mapHomologicalComplex (.up ℤ)).homEquiv P I k) ≫ β₀.app I)
    (b₀ : F ⋙ s ≅ r ⋙ F₀)
    (hi : IsIso (mateEquiv aM aM₀ (TwoSquare.mk _ _ _ _ b₀.inv)).natTrans)
    (b : LF ⋙ sD ≅ rD ⋙ LF₀)
    (hb : ∀ P : CochainComplex C ℤ,
      sD.map (α.hom.app P) ≫ qS.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b₀ (.up ℤ)).hom.app P) =
      b.hom.app (DerivedCategory.Q.obj P) ≫ LF₀.map (qR.hom.app P) ≫
        α₀.hom.app ((r.mapHomologicalComplex (.up ℤ)).obj P)) :
    IsIso (mateEquiv a a₀ (TwoSquare.mk _ _ _ _ b.inv)).natTrans := by
  let δ := (mateEquiv a a₀ (TwoSquare.mk _ _ _ _ b.inv)).natTrans
  let d₀ := (mateEquiv aM aM₀ (TwoSquare.mk _ _ _ _ b₀.inv)).natTrans
  have : IsIso d₀ := hi
  have hn (I : CochainComplex E ℤ) :
      rD.map (β.app I) ≫ δ.app (DerivedCategory.Q.obj I) ≫ RF₀.map (qS.hom.app I) =
      qR.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex d₀ (.up ℤ)).app I) ≫
        β₀.app ((s.mapHomologicalComplex (.up ℤ)).obj I) := by
    let P := (G.mapHomologicalComplex (.up ℤ)).obj I
    let c := (aM.mapHomologicalComplex (.up ℤ)).counit.app I
    have htc := ht P I c
    have hc : (aM.mapHomologicalComplex (.up ℤ)).homEquiv P I c = 𝟙 P := by
      dsimp only [c]
      erw [← (aM.mapHomologicalComplex (.up ℤ)).homEquiv_symm_id I]
      exact Equiv.apply_symm_apply _ _
    rw [hc, DerivedCategory.Q.map_id, Category.id_comp] at htc
    have hm := FlatRingedDiagramInput.adjunct_mate a a₀ rD sD b
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
      (α.hom.app P ≫ DerivedCategory.Q.map c)
    rw [htc] at hm
    change _ = rD.map (β.app I) ≫ δ.app (DerivedCategory.Q.obj I) at hm
    erw [← Category.assoc, ← hm, ← a₀.homEquiv_naturality_right]
    have hb' : b.inv.app (DerivedCategory.Q.obj P) ≫ sD.map (α.hom.app P) ≫
        qS.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
        LF₀.map (qR.hom.app P) ≫ α₀.hom.app ((r.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b₀ (.up ℤ)).inv.app P) := by
      apply (cancel_mono (DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex b₀ (.up ℤ)).hom.app P))).mp
      simp only [Category.assoc, ← DerivedCategory.Q.map_comp, Iso.inv_hom_id_app]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
      erw [hb]
      exact Iso.inv_hom_id_app_assoc b _ _
    have hq := qS.hom.naturality c
    change sD.map (DerivedCategory.Q.map c) ≫ qS.hom.app I =
      qS.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((s.mapHomologicalComplex (.up ℤ)).map c) at hq
    rw [← Category.assoc] at hb'
    erw [sD.map_comp, Category.assoc, Category.assoc, hq,
      ← Category.assoc, ← Category.assoc, hb']
    rw [Category.assoc, Category.assoc, ← DerivedCategory.Q.map_comp]
    erw [a₀.homEquiv_naturality_left, ht₀]
    have hordinary :
        (aM₀.mapHomologicalComplex (.up ℤ)).homEquiv _ _
          ((NatIso.mapHomologicalComplex b₀ (.up ℤ)).inv.app P ≫
            (s.mapHomologicalComplex (.up ℤ)).map c) =
        (NatTrans.mapHomologicalComplex d₀ (.up ℤ)).app I := by
      ext n : 1
      have h := FlatRingedDiagramInput.adjunct_mate aM aM₀ r s b₀
        (G.obj (I.X n)) (I.X n) (aM.counit.app (I.X n))
      have hc' : aM.homEquiv _ _ (aM.counit.app (I.X n)) = 𝟙 _ := by
        rw [← aM.homEquiv_symm_id]
        exact Equiv.apply_symm_apply _ _
      erw [hc', r.map_id, Category.id_comp] at h
      exact h
    erw [hordinary]
  have hki (I : CochainComplex E ℤ) (hI : I.IsKInjective) :
      IsIso (δ.app (DerivedCategory.Q.obj I)) := by
    have : IsIso (β.app I) := hβ I hI
    have : IsIso (β₀.app ((s.mapHomologicalComplex (.up ℤ)).obj I)) := hβ₀ _ (hs I hI)
    have : IsIso ((NatTrans.mapHomologicalComplex d₀ (.up ℤ)).app I) := by
      change IsIso ((NatIso.mapHomologicalComplex (asIso d₀) (.up ℤ)).hom.app I)
      infer_instance
    have : IsIso (rD.map (β.app I) ≫ δ.app (DerivedCategory.Q.obj I) ≫
        RF₀.map (qS.hom.app I)) := by rw [hn]; infer_instance
    have : IsIso (δ.app (DerivedCategory.Q.obj I) ≫ RF₀.map (qS.hom.app I)) :=
      IsIso.of_isIso_comp_left (rD.map (β.app I)) _
    exact IsIso.of_isIso_comp_right _ (RF₀.map (qS.hom.app I))
  have : ∀ M, IsIso (δ.app M) := by
    intro M
    let Q := DerivedCategory.Q (C := E)
    let K := Q.objPreimage M
    obtain ⟨I, hI, i, _, hi⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
    have := hi
    have : IsIso (Q.map i) := by dsimp [Q]; infer_instance
    have : IsIso (δ.app (Q.obj I)) := hki I hI
    have : IsIso (δ.app (Q.obj K)) :=
      (NatTrans.isIso_app_iff_of_iso δ (asIso (Q.map i))).mpr inferInstance
    exact (NatTrans.isIso_app_iff_of_iso δ (Q.objObjPreimageIso M)).mp inferInstance
  exact NatIso.isIso_of_isIso_app δ

private theorem pull_computation_all (d : AdicCoefficientDatum A) (B : Balancing d)
    {U V : Scheme.{u}} (f : U ⟶ V)
    (P : PullCompatibility f d (B.ρ V) (B.ρ U))
    (K : Cx (ring V d true)) :
    (dres (scalar U d)).map (P.completed.ordinaryFactors.hom.app K) ≫
        (resFactors (scalar U d)).inv.app
          (((modulePull f d true).mapHomologicalComplex (.up ℤ)).obj K) ≫
        (Q (ring U d false)).map
          ((NatIso.mapHomologicalComplex P.ordinaryScalar (.up ℤ)).hom.app K) =
      P.a.hom.app ((Q (ring V d true)).obj K) ≫
        P.constant.ordinary.map ((resFactors (scalar V d)).inv.app K) ≫
        P.constant.ordinaryFactors.hom.app
          (((res (scalar V d)).mapHomologicalComplex (.up ℤ)).obj K) := by
  let := HasDerivedCategory.standard (Mod (ring V d true))
  let FC := (modulePull f d true).mapHomologicalComplex (.up ℤ)
  let RC := (res (scalar V d)).mapHomologicalComplex (.up ℤ)
  let SC := (res (scalar U d)).mapHomologicalComplex (.up ℤ)
  let FC₀ := (modulePull f d false).mapHomologicalComplex (.up ℤ)
  let lhs : (Q (ring V d true) ⋙ P.completed.ordinary) ⋙ dres (scalar U d) ⟶
      (RC ⋙ FC₀) ⋙ Q (ring U d false) :=
    Functor.whiskerRight P.completed.ordinaryFactors.hom (dres (scalar U d)) ≫
      Functor.whiskerLeft FC (resFactors (scalar U d)).inv ≫
      Functor.whiskerRight (NatIso.mapHomologicalComplex P.ordinaryScalar (.up ℤ)).hom
        (Q (ring U d false))
  let rhs : (Q (ring V d true) ⋙ P.completed.ordinary) ⋙ dres (scalar U d) ⟶
      (RC ⋙ FC₀) ⋙ Q (ring U d false) :=
    Functor.whiskerLeft (Q (ring V d true)) P.a.hom ≫
      Functor.whiskerRight (resFactors (scalar V d)).inv P.constant.ordinary ≫
      Functor.whiskerLeft RC P.constant.ordinaryFactors.hom
  have he : lhs = rhs := by
    apply NatTrans.ext
    funext M
    obtain ⟨N, k, hN, hk⟩ := flat_resolution V d M
    have := hk
    have : IsIso (((Q (ring V d true) ⋙ P.completed.ordinary) ⋙
        dres (scalar U d)).map k) := by
      change IsIso ((dres (scalar U d)).map
        (P.completed.ordinary.map ((Q (ring V d true)).map k)))
      infer_instance
    apply (cancel_epi (((Q (ring V d true) ⋙ P.completed.ordinary) ⋙
      dres (scalar U d)).map k)).mp
    rw [lhs.naturality, rhs.naturality]
    suffices lhs.app N = rhs.app N by rw [this]
    dsimp only [lhs, rhs, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    have hn := P.a_computes N hN.1 hN.2
    dsimp only [DerivedPullComparisonFormula] at hn
    apply (cancel_epi (P.a.inv.app ((Q (ring V d true)).obj N))).mp
    apply (cancel_mono ((Q (ring U d false)).map
      ((NatIso.mapHomologicalComplex P.ordinaryScalar (.up ℤ)).inv.app N))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    erw [← (Q (ring U d false)).map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
    exact hn.symm
  exact congrArg (fun t ↦ t.app K) he

private theorem exact_derived_adjunction
    {C E : Type*} [Category C] [Abelian C] [Category E] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E] [IsGrothendieckAbelian E]
    (F : C ⥤ E) (G : E ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (aM : F ⊣ G)
    (LF : DerivedCategory C ⥤ DerivedCategory E)
    (α : DerivedCategory.Q ⋙ LF ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hLF : LF.IsLeftDerivedFunctor α.hom (HomologicalComplex.quasiIso C (.up ℤ))) :
    ∃ (RF : DerivedCategory E ⥤ DerivedCategory C)
      (β : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
      (a : LF ⊣ RF),
      (∀ I : CochainComplex E ℤ, I.IsKInjective → IsIso (β.app I)) ∧
      ∀ (P : CochainComplex C ℤ) (I : CochainComplex E ℤ)
        (f : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
        a.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
          (α.hom.app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((aM.mapHomologicalComplex (.up ℤ)).homEquiv P I f) ≫
          β.app I := by
  let H := G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  let W := HomologicalComplex.quasiIso C (.up ℤ)
  let W' := HomologicalComplex.quasiIso E (.up ℤ)
  let Φ := CochainComplex.KInjectives.localizerMorphism E
  have hd : Φ.Derives H := by
    intro K I f hf
    have : K.obj.IsKInjective := K.property
    have : I.obj.IsKInjective := I.property
    have hq : QuasiIso f.hom := hf
    obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp hq
    have he' : HomologicalComplex.homotopyEquivalences C (.up ℤ)
        ((G.mapHomologicalComplex (.up ℤ)).map f.hom) :=
      ⟨G.mapHomotopyEquiv e, congrArg (G.mapHomologicalComplex (.up ℤ)).map he⟩
    have : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map f.hom) :=
      homotopyEquivalences_le_quasiIso _ _ _ he'
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map
      ((G.mapHomologicalComplex (.up ℤ)).map f.hom)))
  have := hd.hasPointwiseRightDerivedFunctor
  let RF := H.totalRightDerived DerivedCategory.Q W'
  let β := H.totalRightDerivedUnit DerivedCategory.Q W'
  have : RF.IsRightDerivedFunctor β W' := by dsimp only [RF, β]; infer_instance
  have hβ : ∀ I : CochainComplex E ℤ, I.IsKInjective → IsIso (β.app I) := by
    intro I hI
    let : I.IsKInjective := hI
    exact hd.isIso_of_isRightDerivedFunctor β (.mk I)
  have := hLF
  have : (LF ⋙ RF).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α.hom RF) W :=
    Functor.isLeftDerivedFunctor_of_inverts W _
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α RF)
  have : (RF ⋙ LF).IsRightDerivedFunctor
      (Functor.whiskerRight β LF ≫ (Functor.associator _ _ _).hom) W' :=
    Φ.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure β
      (fun I ↦ hd.isIso_of_isRightDerivedFunctor β I) LF
  let a := (aM.mapHomologicalComplex (.up ℤ)).derived W W' α.hom β
  refine ⟨RF, β, a, hβ, ?_⟩
  intro P I f
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  change (((aM.mapHomologicalComplex (.up ℤ)).derivedη W α.hom β).app
    (DerivedCategory.Q.obj P) ≫ RF.map (α.hom.app P)) ≫
      RF.map (DerivedCategory.Q.map f) = _
  rw [Adjunction.derivedη_fac_app, Category.assoc]
  have hn := β.naturality f
  change DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f) ≫ β.app I =
    β.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫ RF.map (DerivedCategory.Q.map f) at hn
  rw [← hn, ← Category.assoc, ← Functor.map_comp, Adjunction.homEquiv_unit]

/-- The actual ordinary geometric operations admit normalized derived right adjoints.
Source: Stacks 07A6 (sites-cohomology.tex, lemma-adjoint), and the normalized
scalar mate calculation in completed-exchange-coherence, strict supplement Step 6.
(blueprint: lem-weil-pbc-strict-scalar-ordinary-adjoints-exist).
Proof: the structural coefficient identifications transport algebraic inverse image
and its module adjunction to the published small pro-etale model. Pullback is exact,
so its termwise localization and K-injective derived direct image are adjoint.
Universality identifies their left adjoints with the two supplied PullModels.
The coefficient square identifies the ordinary direct-image actions on the same
underlying additive sheaves. Flat restriction preserves K-injective resolutions;
thus this ordinary isomorphism descends to chi on unbounded derived categories.
Compute the Hom transpose on a flat-term K-flat source and K-injective target:
both maps are the underlying geometric transpose with the same scalar action.
This gives chi as the mate of the inverse of P.a. Its representative computation
agrees with P.a_computes and P.ordinaryScalar_normalized; localization extends the
equality to all objects. The universal properties make the transport independent
of choices. No completeness assumption is used here. -/
theorem strictScalarOrdinaryAdjointsExist (d : AdicCoefficientDatum A) (B : Balancing d)
    {U V : Scheme.{u}} (f : U ⟶ V)
    (P : PullCompatibility f d (B.ρ V) (B.ρ U)) :
    ∃ (rightA : D (ring U d true) ⥤ D (ring V d true))
      (right0 : D (ring U d false) ⥤ D (ring V d false))
      (adjA : P.completed.ordinary ⊣ rightA)
      (adj0 : P.constant.ordinary ⊣ right0)
      (χ : rightA ⋙ dres (scalar V d) ≅ dres (scalar U d) ⋙ right0),
      χ.hom = (mateEquiv adjA adj0 (TwoSquare.mk _ _ _ _ P.a.inv)).natTrans := by
  let := d.noetherian
  let := HasDerivedCategory.standard (Mod (ring V d true))
  let := HasDerivedCategory.standard (Mod (ring U d true))
  let := HasDerivedCategory.standard (Mod (ring V d false))
  let := HasDerivedCategory.standard (Mod (ring U d false))
  have : IsGrothendieckAbelian.{u + 1} (Mod (ring U d true)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      (topology U) (ring U d true)).1
  have : IsGrothendieckAbelian.{u + 1} (Mod (ring U d false)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      (topology U) (ring U d false)).1
  let push := (proEtaleModelBaseChange f).sheafPushforwardContinuous (Type (u + 1))
    (topology V) (topology U)
  let adj := (proEtaleModelBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
    (topology V) (topology U)
  obtain ⟨GA, eA, aMA, hA⟩ := module_adjunction_exists push adj (inverseData f)
    (coefficient f d true)
  obtain ⟨G0, e0, aM0, h0⟩ := module_adjunction_exists push adj (inverseData f)
    (coefficient f d false)
  have := aMA.leftAdjoint_preservesColimits
  have := aM0.leftAdjoint_preservesColimits
  have := completed_pull_exact d B f P
  have : IsIso (constantMap (inverseData f) A) := by dsimp only [constantMap]; infer_instance
  have : PreservesFiniteLimits (modulePull f d false) :=
    pull_finiteLimits_of_isIso (inverseData f) (constantMap (inverseData f) A)
  obtain ⟨RA, βA, aA, hβA, htA⟩ := exact_derived_adjunction
    (modulePull f d true) GA.obj aMA P.completed.ordinary P.completed.ordinaryFactors
    P.completed.ordinaryUniversal
  obtain ⟨R0, β0, a0, hβ0, ht0⟩ := exact_derived_adjunction
    (modulePull f d false) G0.obj aM0 P.constant.ordinary P.constant.ordinaryFactors
    P.constant.ordinaryUniversal
  have hr := (siteRestrictScalars_exact (scalar V d)).1
  have hc := (siteRestrictScalars_exact (scalar V d)).2
  have hs := (siteRestrictScalars_exact (scalar U d)).1
  have hsc := (siteRestrictScalars_exact (scalar U d)).2
  have hsK : (res (scalar U d)).PreservesKInjectiveComplexes := by
    have hex := change_exact (scalar U d) (flat_and_quotients (topology U) A d.ideal).1
    have : PreservesFiniteLimits (change (scalar U d)) := hex.1
    have : PreservesFiniteColimits (change (scalar U d)) := hex.2
    have : (SheafOfModules.RingedTensor.tensorFunctor (scalar U d)).Additive :=
      (SheafOfModules.RingedTensor.tensorAdjunction (scalar U d)).left_adjoint_additive
    have : PreservesFiniteLimits (SheafOfModules.RingedTensor.tensorFunctor (scalar U d)) :=
      hex.1
    have : PreservesFiniteColimits (SheafOfModules.RingedTensor.tensorFunctor (scalar U d)) :=
      hex.2
    have : (SheafOfModules.RingedTensor.tensorFunctor (scalar U d)).PreservesHomology := {}
    exact (SheafOfModules.RingedTensor.tensorAdjunction (scalar U d)).preservesKInjectiveComplexes
  have hi := ordinary_mate_iso d B f P GA.obj G0.obj aMA aM0 eA e0 hA h0
  have hδ := derived_mate_iso (modulePull f d true) GA.obj
    (modulePull f d false) G0.obj (res (scalar V d)) (res (scalar U d))
    aMA aM0 P.completed.ordinary RA P.constant.ordinary R0
    (dres (scalar V d)) (dres (scalar U d))
    P.completed.ordinaryFactors P.constant.ordinaryFactors βA β0
    (resFactors (scalar V d)).symm (resFactors (scalar U d)).symm
    aA a0 hβA hβ0
    (fun I hI ↦ by have := hI; infer_instance)
    htA ht0 P.ordinaryScalar hi P.a (pull_computation_all d B f P)
  let δ := (mateEquiv aA a0 (TwoSquare.mk _ _ _ _ P.a.inv)).natTrans
  have : IsIso δ := hδ
  exact ⟨RA, R0, aA, a0, asIso δ, rfl⟩

end AlgebraicGeometry.Scheme.StrictScalarBalancing
