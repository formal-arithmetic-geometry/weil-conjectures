/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NQ and NJ
-/
module

public import Sheaf.Paper.CompletedTowerPullback
public import Sheaf.Paper.FiniteStagePairCategory
public import Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.LeftDerivedEquivalence
import all Sheaf.Paper.CompletedTowerDirectImage
import Sheaf.Paper.PbcActualRingedExchange
import Sheaf.Paper.PbcActualStrictPullback

/-!
# Completed coefficient transport and Weil categories

Source: Weil conjectures blueprint, finite coefficient and Weil-category definitions
(blueprint: def-wf-automorphism-completed-transport).

The finite coefficient stages use `pbcStageDatum` and `pbcStageUniformizer`:
these are the valuation-ring data transported along `Shrink.algEquiv`, with the
actual field inclusions conjugated by that canonical equivalence.

## Main definitions

- `pbcIsoModulePullback`, `pbcIsoAmbientPullback`: exact coefficient transport.
- `pbcIsoCompletedPullback_identification`: the completed-pullback identification.
- `pbcRationalIsoPullback`: transport on the raw rational coefficient category.
- `pbcIsoRationalScalarComparison`: the normalized scalar/transport comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u c
open CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isoTransportCochainDerivedCounit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (G : A ⥤ B) [G.Additive]
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ L ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ))] :
    ∃ εc : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
      L.IsLeftDerivedFunctor εc (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      ∀ P, εc.app P = Functor.leftDerivedCounitOnComplex G L ε P := by
  let π := HomotopyCategory.quotient A (.up ℤ)
  let εc : DerivedCategory.Q ⋙ L ⟶
      G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    { app := fun P ↦ ε.app (π.obj P)
      naturality := fun _ _ f ↦ ε.naturality (π.map f) }
  refine ⟨εc, ?_, ?_⟩
  swap
  · intro P
    simp only [εc, Functor.leftDerivedCounitOnComplex,
      DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
      Functor.mapHomotopyCategoryFactors]
    erw [L.map_id, DerivedCategory.Qh.map_id]
    change ε.app (π.obj P) = 𝟙 _ ≫ ε.app (π.obj P) ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  · refine ⟨⟨⟨?_⟩⟩⟩
    let lift (Z : DerivedCategory A ⥤ DerivedCategory B)
        (τ : DerivedCategory.Q ⋙ Z ⟶
          G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
        DerivedCategory.Qh ⋙ Z ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
      { app := fun X ↦ τ.app X.as
        naturality := by
          intro X Y f
          obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
          obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
          obtain ⟨f, rfl⟩ := π.map_surjective f
          exact τ.naturality f }
    refine IsTerminal.ofUniqueHom (fun Z ↦ CostructuredArrow.homMk
      (L.leftDerivedLift ε (HomotopyCategory.quasiIso A (.up ℤ)) Z.left
        (lift Z.left Z.hom)) (by
          apply NatTrans.ext
          funext P
          exact L.leftDerived_fac_app ε (HomotopyCategory.quasiIso A (.up ℤ))
            Z.left (lift Z.left Z.hom) (π.obj P))) ?_
    intro Z m
    apply CostructuredArrow.hom_ext
    apply L.leftDerived_ext ε (HomotopyCategory.quasiIso A (.up ℤ))
    apply NatTrans.ext
    funext X
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    have hm := NatTrans.congr_app m.w P
    have hm' : m.left.app (DerivedCategory.Q.obj P) ≫ ε.app (π.obj P) =
        Z.hom.app P := by simpa using hm
    exact hm'.trans
      (L.leftDerived_fac_app ε (HomotopyCategory.quasiIso A (.up ℤ))
        Z.left (lift Z.left Z.hom) (π.obj P)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isoTransportDerivedSquare
    {A B AD BD : Type*} [Category A] [Category B] [Category AD] [Category BD]
    (QA : A ⥤ AD) (QB : B ⥤ BD) (G : A ⥤ B) (L : AD ⥤ BD)
    (ε : QA ⋙ L ⟶ G ⋙ QB) [L.IsRightKanExtension ε]
    (U : A ⥤ A) [U.IsEquivalence] (V : B ⥤ B)
    (HA : AD ⥤ AD) [HA.IsEquivalence] (HB : BD ⥤ BD) [HB.IsEquivalence]
    (θA : QA ⋙ HA ≅ U ⋙ QA) (θB : QB ⋙ HB ≅ V ⋙ QB)
    (τ : G ⋙ V ≅ U ⋙ G) :
    ∃! c : L ⋙ HB ≅ HA ⋙ L, ∀ P : A,
      c.hom.app (QA.obj P) ≫ L.map (θA.hom.app P) ≫ ε.app (U.obj P) =
        HB.map (ε.app P) ≫ θB.hom.app (G.obj P) ≫ QB.map (τ.hom.app P) := by
  let εU := (Functor.associator U QA L).hom ≫ Functor.whiskerLeft U ε
  have : L.IsRightKanExtension εU :=
    (Functor.isRightKanExtension_iff_precomp L U ε).mp inferInstance
  let δ := (Functor.associator QA HA L).inv ≫
    Functor.whiskerRight θA.hom L ≫ εU
  have : (HA ⋙ L).IsRightKanExtension δ :=
    (Functor.isRightKanExtension_iff_postcomp₁ HA θA εU).mp inferInstance
  let σ := (Functor.associator QA L HB).inv ≫ Functor.whiskerRight ε HB
  have : (L ⋙ HB).IsRightKanExtension σ :=
    Functor.isRightKanExtension_comp_of_isEquivalence L ε HB
  let ζ : (G ⋙ QB) ⋙ HB ≅ U ⋙ G ⋙ QB :=
    Functor.associator G QB HB ≪≫ Functor.isoWhiskerLeft G θB ≪≫
      (Functor.associator G V QB).symm ≪≫ Functor.isoWhiskerRight τ QB ≪≫
      Functor.associator U G QB
  let c := Functor.rightKanExtensionUniqueOfIso (L ⋙ HB) σ ζ (HA ⋙ L) δ
  have hc (P : A) :
      c.hom.app (QA.obj P) ≫ L.map (θA.hom.app P) ≫ ε.app (U.obj P) =
        HB.map (ε.app P) ≫ θB.hom.app (G.obj P) ≫ QB.map (τ.hom.app P) := by
    have h := (HA ⋙ L).liftOfIsRightKanExtension_fac_app δ (L ⋙ HB) (σ ≫ ζ.hom) P
    change c.hom.app (QA.obj P) ≫ δ.app P = (σ ≫ ζ.hom).app P at h
    simpa only [δ, εU, σ, ζ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.map_id, Category.id_comp,
      Category.comp_id, Category.assoc] using h
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  apply Iso.ext
  apply (HA ⋙ L).hom_ext_of_isRightKanExtension δ
  apply NatTrans.ext
  funext P
  simpa only [δ, εU, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc] using (hc' P).trans (hc P).symm


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isoTransportCochainSquare
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (G : A ⥤ B) [hG : G.Additive] (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ L ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)))
    (FE : A ⥤ A) (FF : B ⥤ B) [hFA : FE.Additive] [hFB : FF.Additive]
    [hEA : FE.IsEquivalence] [hEB : FF.IsEquivalence]
    (τ : G.mapHomologicalComplex (.up ℤ) ⋙ FF.mapHomologicalComplex (.up ℤ) ≅
      FE.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ)) :
    ∃! c : L ⋙ FF.mapDerivedCategory ≅ FE.mapDerivedCategory ⋙ L,
      ∀ P : CochainComplex A ℤ,
        c.hom.app (DerivedCategory.Q.obj P) ≫
          L.map (FE.mapDerivedCategoryFactors.hom.app P) ≫
          Functor.leftDerivedCounitOnComplex G L ε
            ((FE.mapHomologicalComplex (.up ℤ)).obj P) =
        FF.mapDerivedCategory.map (Functor.leftDerivedCounitOnComplex G L ε P) ≫
          FF.mapDerivedCategoryFactors.hom.app
            ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (τ.hom.app P) := by
  let : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) := hL
  obtain ⟨εc, hεc, hεapp⟩ := isoTransportCochainDerivedCounit G L ε
  let : L.IsLeftDerivedFunctor εc (HomologicalComplex.quasiIso A (.up ℤ)) := hεc
  let : L.IsRightKanExtension εc := Functor.IsLeftDerivedFunctor.isRightKanExtension
    L εc (HomologicalComplex.quasiIso A (.up ℤ))
  let : (FE.mapHomologicalComplex (.up ℤ)).IsEquivalence :=
    (FE.asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  obtain ⟨c, hc, hu⟩ := isoTransportDerivedSquare DerivedCategory.Q DerivedCategory.Q
    (G.mapHomologicalComplex (.up ℤ)) L εc
    (FE.mapHomologicalComplex (.up ℤ)) (FF.mapHomologicalComplex (.up ℤ))
    FE.mapDerivedCategory FF.mapDerivedCategory FE.mapDerivedCategoryFactors
    FF.mapDerivedCategoryFactors τ
  refine ⟨c, ?_, ?_⟩
  · intro P
    simpa only [hεapp] using hc P
  · intro c' hc'
    apply hu c'
    intro P
    simpa only [hεapp] using hc' P


private theorem isoTransportDerivedCounitComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))] :
    ∃! e : L ≅ F.mapDerivedCategory, ∀ P : CochainComplex C ℤ,
      e.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P =
        CategoryTheory.Functor.leftDerivedCounitOnComplex F L ε P := by
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom W :=
    CategoryTheory.Functor.isLeftDerivedFunctor_of_inverts W _ F.mapDerivedCategoryFactorsh
  let e := CategoryTheory.Functor.leftDerivedUnique F.mapDerivedCategory L ε
    F.mapDerivedCategoryFactorsh.hom W
  have hc (P : CochainComplex C ℤ) :
      e.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P =
        CategoryTheory.Functor.leftDerivedCounitOnComplex F L ε P := by
    have he := CategoryTheory.Functor.leftDerivedNatTrans_app L F.mapDerivedCategory ε
      F.mapDerivedCategoryFactorsh.hom W (𝟙 _)
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)
    have hn := e.hom.naturality ((DerivedCategory.quotientCompQhIso C).inv.app P)
    dsimp at hn
    simp only [NatTrans.id_app, Category.comp_id] at he
    change e.hom.app _ ≫ _ = _ at he
    simp only [CategoryTheory.Functor.leftDerivedCounitOnComplex]
    rw [← he, F.mapDerivedCategoryFactorsh_hom_app]
    simp only [← Category.assoc]
    rw [hn]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    simp
  refine ⟨e, hc, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hp : e'.hom.app (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K)) =
      e.hom.app (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K)) := by
    apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app
      (DerivedCategory.Q.objPreimage K))).1
    rw [he', hc]
  apply (cancel_epi (L.map (DerivedCategory.Q.objObjPreimageIso K).hom)).1
  rw [e'.hom.naturality, e.hom.naturality, hp]


private theorem isoTransportDerivedCounitComparisonOfEq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (he : F = G)
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))] :
    ∃! e : L ≅ G.mapDerivedCategory, ∀ P : CochainComplex C ℤ,
      e.hom.app (DerivedCategory.Q.obj P) ≫ G.mapDerivedCategoryFactors.hom.app P =
        CategoryTheory.Functor.leftDerivedCounitOnComplex F L ε P ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (eqToIso he) (.up ℤ)).hom.app P) := by
  cases he
  simpa only [eqToIso_refl, NatIso.mapHomologicalComplex, Iso.refl_hom,
    NatTrans.mapHomologicalComplex_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.comp_id] using isoTransportDerivedCounitComparison F L ε

private theorem isoTransportModulePushforwardEquivalence
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
    (R : Sheaf J RingCat.{u + 1}) (S : Sheaf K RingCat.{u + 1})
    (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R) :
    (SheafOfModules.pushforward.{u + 1} (F := e.inverse) c.hom).IsEquivalence := by
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S :=
    { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
        Functor.whiskerLeft e.functor.op c.inv.hom }
  have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      ψ.hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map _ =
      (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
    rw [Category.assoc]
    have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
    have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
        c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
    change R.obj.map (e.unitInv.app U.unop).op =
      R.obj.map (e.unitInv.app U.unop).op ≫
        (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)
  have H₂ : c.hom.hom ≫ e.inverse.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    change c.hom.hom.app U ≫
      (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
        S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
    rw [Category.assoc]
    have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
    change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
      c.inv.hom.app U =
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
        S.obj.map (e.counitInv.app U.unop).op at hn
    rw [← hn]
    have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp]
      simp
    rw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
    change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
    have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
      (Category.id_comp (c.inv.hom.app U))).trans hc
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  exact inferInstanceAs
    (SheafOfModules.pushforwardPushforwardEquivalence e.symm c.hom ψ H₁ H₂).functor.IsEquivalence


private theorem isoTransportLocalization_naturality
    {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (p : R) {D : Type*} [Category D]
    (F G : ScalarLocalization R C p ⥤ D)
    (a : ∀ K : C, F.obj ⟨K⟩ ⟶ G.obj ⟨K⟩)
    (ha : ∀ {K L : C} (f : K ⟶ L),
      F.map ((ScalarLocalization.localization R C p).map f) ≫ a L =
        a K ≫ G.map ((ScalarLocalization.localization R C p).map f))
    (K L : C) (f : ScalarLocalization.mk (R := R) (p := p) K ⟶ ⟨L⟩) :
    F.map f ≫ a L = a K ≫ G.map f := by
  let Q := ScalarLocalization.localization R C p
  obtain ⟨⟨u, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers p)
    (TensorProduct.mk R (Localization.Away p) (K ⟶ L) 1) f
  have hs' : (s : R) • f = Q.map u := hs
  obtain ⟨v, hv⟩ := IsLocalization.map_units (Localization.Away p) s
  let z : Q.obj K ≅ Q.obj K :=
    { hom := (v : Localization.Away p) • 𝟙 _
      inv := (↑(v⁻¹) : Localization.Away p) • 𝟙 _
      hom_inv_id := by
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul,
          Units.inv_mul, one_smul]
      inv_hom_id := by
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul,
          Units.mul_inv, one_smul] }
  have hz : Q.map ((s : R) • 𝟙 K) = z.hom := by
    change (1 : Localization.Away p) ⊗ₜ[R] ((s : R) • 𝟙 K) =
      (v : Localization.Away p) • ((1 : Localization.Away p) ⊗ₜ[R] (𝟙 K))
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [TensorProduct.tmul_smul, hv]
    change (s : R) • ((1 : Localization.Away p) ⊗ₜ[R] 𝟙 K) = _
    rw [TensorProduct.smul_tmul' (s : R), Algebra.smul_def, mul_one]
  let : IsIso (Q.map ((s : R) • 𝟙 K)) := by
    rw [hz]
    exact z.isIso_hom
  have hf : Q.map ((s : R) • 𝟙 K) ≫ f = Q.map u := by
    simpa only [Q.map_smul, Q.map_id, Linear.smul_comp, Category.id_comp] using hs'
  apply (cancel_epi (F.map (Q.map ((s : R) • 𝟙 K)))).1
  rw [← F.map_comp_assoc, hf, ha u, ← hf, G.map_comp, ← Category.assoc,
    ← ha ((s : R) • 𝟙 K), Category.assoc]



private theorem isoTransportRationalComparison
    {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (p : R) {C' D : Type*} [Category C'] [Category D]
    (I : C ⥤ C') (IE : C ⥤ C) (IF : C' ⥤ C') (QF : C' ⥤ D)
    (S : ScalarLocalization R C p ⥤ D)
    (PE : ScalarLocalization R C p ⥤ ScalarLocalization R C p) (PF : D ⥤ D)
    (b : ScalarLocalization.localization R C p ⋙ S ≅ I ⋙ QF)
    (t : I ⋙ IF ≅ IE ⋙ I)
    (eE : ScalarLocalization.localization R C p ⋙ PE ≅
      IE ⋙ ScalarLocalization.localization R C p)
    (eF : QF ⋙ PF ≅ IF ⋙ QF) :
    ∃! c : S ⋙ PF ≅ PE ⋙ S, ∀ K : C,
      c.hom.app ⟨K⟩ = PF.map (b.hom.app K) ≫ eF.hom.app (I.obj K) ≫
        QF.map (t.hom.app K) ≫ b.inv.app (IE.obj K) ≫ S.map (eE.inv.app K) := by
  let QE := ScalarLocalization.localization R C p
  let a : QE ⋙ (S ⋙ PF) ≅ QE ⋙ (PE ⋙ S) :=
    (Functor.associator QE S PF).symm ≪≫
      Functor.isoWhiskerRight b PF ≪≫ Functor.associator I QF PF ≪≫
      Functor.isoWhiskerLeft I eF ≪≫ (Functor.associator I IF QF).symm ≪≫
      Functor.isoWhiskerRight t QF ≪≫ Functor.associator IE I QF ≪≫
      Functor.isoWhiskerLeft IE b.symm ≪≫ (Functor.associator IE QE S).symm ≪≫
      Functor.isoWhiskerRight eE.symm S ≪≫ Functor.associator QE PE S
  let c : S ⋙ PF ≅ PE ⋙ S :=
    NatIso.ofComponents (fun K ↦ a.app K.obj) (fun {K L} f ↦
      isoTransportLocalization_naturality p (S ⋙ PF) (PE ⋙ S)
        (fun K ↦ a.hom.app K) (fun f ↦ a.hom.naturality f) K.obj L.obj f)
  have hc (K : C) : c.hom.app ⟨K⟩ =
      PF.map (b.hom.app K) ≫ eF.hom.app (I.obj K) ≫ QF.map (t.hom.app K) ≫
        b.inv.app (IE.obj K) ≫ S.map (eE.inv.app K) := by
    change a.hom.app K = _
    simp only [a, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp]
    change PF.map (b.hom.app K) ≫ eF.hom.app (I.obj K) ≫
      QF.map (t.hom.app K) ≫ b.inv.app (IE.obj K) ≫ 𝟙 _ ≫
      S.map (eE.inv.app K) ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  obtain ⟨K⟩ := K
  exact (hc' K).trans (hc K).symm

private theorem isoTransportFullSubcategoryEquivalence
    {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (H : C ⥤ D) [H.IsEquivalence]
    (hH : ∀ K : P.FullSubcategory, Q (H.obj K.obj))
    (J : D ⥤ C) (hJ : ∀ K : Q.FullSubcategory, P (J.obj K.obj))
    (a : J ⋙ H ≅ 𝟭 D) : (Q.lift (P.ι ⋙ H) hH).IsEquivalence := by
  let F := Q.lift (P.ι ⋙ H) hH
  have : F.Full := inferInstance
  have : F.Faithful := inferInstance
  have : F.EssSurj :=
    ⟨fun M ↦ ⟨⟨J.obj M.obj, hJ M⟩, ⟨ObjectProperty.isoMk Q (a.app M.obj)⟩⟩⟩
  exact {}

private theorem isoTransportCompletionUnit
    {C : Type*} [Category C] (P : ObjectProperty C) [P.ι.IsRightAdjoint]
    {M N K : C} (e : M ≅ N) (hN : P N) (u : M ⟶ K)
    (c : K ≅ (P.ι.leftAdjoint ⋙ P.ι).obj M)
    (hc : u ≫ c.hom = (Adjunction.ofIsRightAdjoint P.ι).unit.app M) : IsIso u := by
  let adj := Adjunction.ofIsRightAdjoint P.ι
  let L : P.FullSubcategory := ⟨N, hN⟩
  have : IsIso (adj.unit.app N) := adj.isIso_unit_app_of_iso (X := L) (Iso.refl N)
  have : IsIso (adj.unit.app M) :=
    (NatTrans.isIso_app_iff_of_iso adj.unit e).mpr inferInstance
  have : IsIso (u ≫ c.hom) := by
    rw [hc]
    infer_instance
  exact IsIso.of_isIso_comp_right _ c.hom


namespace AlgebraicGeometry.Scheme

private theorem isoTransportComplexCounitEq {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P : CochainComplex (pbcModules X R) ℤ) :
    pbcComplexCounit φ P = Functor.leftDerivedCounitOnComplex (pbcExtend φ)
      (pbcDerivedExtend φ) (pbcExtensionCounit φ) P := rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [hf : IsIso f]
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

attribute [local irreducible] completedCoefficientMap proEtaleRingModulePullback
  proEtaleIsoPostcompose pbcScalarExtension pbcIntegralScalarExtension

include hf in
/-- The coefficient map is invertible for a scheme isomorphism.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: apply the existing completedCoefficient_isIso theorem. Its proof uses
the finite quotient constant-ring tower and the canonical profinite coefficient
inverse-image comparison. The finite projection equations identify its limit
isomorphism with exactly the recorded completedCoefficientMap. -/
@[instance] theorem pbcIsoCoefficientMap_isIso : IsIso (completedCoefficientMap f d) := by
  have _ := hf
  exact completedCoefficient_isIso f d

/-- Exact module transport: inverse image followed by the canonical scalar identification.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
abbrev pbcIsoModulePullback :
    pbcModules Y (pbcAdicCompletion Y d) ⥤ pbcModules X (pbcAdicCompletion X d) :=
  proEtaleRingModulePullback f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
    (asIso (completedCoefficientMap f d))

/-- The module pullback is an exact equivalence with inverse transport along f inverse.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: inverse-image equivalences for the two inverse site functors identify
the completed coefficient sheaves by the finite projection equations. The
unit and counit of their site equivalence therefore lift to modules. Both
functors are exact, since site equivalences and ring identifications are exact. -/
@[instance] theorem pbcIsoModulePullback_isEquivalence :
    (pbcIsoModulePullback f d).IsEquivalence := by
  let : (proEtaleIsoPostcompose f).IsEquivalence :=
    (proEtaleIsoPostcompose_equivalence f).1
  let a : proEtaleIsoPostcompose f ⊣ proEtaleBaseChange f :=
    by
      unfold proEtaleIsoPostcompose
      exact MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f
        (inferInstance : WeaklyEtale f) trivial
  let : (proEtaleBaseChange f).IsEquivalence :=
    a.isEquivalence_right_of_isEquivalence_left
  let e := a.toEquivalence
  let : e.functor.IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
    Functor.IsCoverDense.isContinuous (ProEt.topology X) (ProEt.topology Y)
      (proEtaleIsoPostcompose f)
      (proEtaleIsoPostcompose_equivalence f).2.2.2.1.some
  let : e.inverse.IsContinuous (ProEt.topology Y) (ProEt.topology X) :=
    proEtaleBaseChange_isContinuous f
  let R := pbcAdicCompletion Y d
  let S := pbcAdicCompletion X d
  let c := asIso (completedCoefficientMap f d)
  let : IsIso (proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit :=
    (proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0} f CommRingCat.{u + 1}).2.1
  let : IsIso (proEtaleRingDirectImageMap f R S c) := by
    unfold proEtaleRingDirectImageMap
    infer_instance
  let rc := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (asIso (proEtaleRingDirectImageMap f R S c))
  let R' := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let S' := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let rc' : R' ≅ ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology Y) (ProEt.topology X)).obj S' := rc
  let he := isoTransportModulePushforwardEquivalence (ProEt.topology X) (ProEt.topology Y)
    e S' R' rc'
  let : (proEtaleRingModuleDirectImage f R S c).IsEquivalence := by
    unfold proEtaleRingModuleDirectImage
    exact he
  exact (proEtaleRingModuleAdjunction f R S c).isEquivalence_left_of_isEquivalence_right

/-- The exact equivalence transported to complexes and localized at quasi-isomorphisms.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
abbrev pbcIsoAmbientPullback : PbcCompletedDerived Y d ⥤ PbcCompletedDerived X d :=
  (pbcIsoModulePullback f d).mapDerivedCategory

/-- The two recorded ordinary inverse images have the same tensor object and map formulas.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: both coefficient maps are the existing completedCoefficientMap. The ordinary
scalar extension in completedModulePullback is fixed on objects and maps by the
change-of-rings universal pair, so its formulas are precisely changeOfRings and
changeOfRingsHom. Functor extensionality gives the displayed equality.
-/
theorem pbcIsoModulePullback_eq_completed :
    pbcIsoModulePullback f d = completedModulePullback f d := by
  symm
  unfold pbcIsoModulePullback proEtaleRingModulePullback
  apply CategoryTheory.Functor.ext
  · intro M N a
    exact (completedAdicChangeData X (completedCoefficientMap f d)).choose_spec.choose_spec.choose
      ((proEtaleModuleInverseImage f (pbcAdicCompletion Y d)).map a)

/-- Exact descent is the unique ordinary derived inverse image with its universal counit.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: exactness makes the termwise descent with its localization factorization a
left-derived pair. Transport its counit through the equality of the two ordinary
functors. The universal property of the recorded left-derived pair gives a unique
isomorphism satisfying the displayed complex-counit equation.
-/
theorem pbcIsoOrdinaryDerivedComparison_exists :
    ∃! alpha : completedOrdinaryPullback f d ≅ pbcIsoAmbientPullback f d,
      ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ,
        alpha.hom.app (DerivedCategory.Q.obj P) ≫
            (pbcIsoModulePullback f d).mapDerivedCategoryFactors.hom.app P =
          completedOrdinaryPullbackComplexCounit f d P ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (eqToIso (pbcIsoModulePullback_eq_completed f d)).symm (.up ℤ)).hom.app P) := by
  let ε := completedOrdinaryPullbackCounit f d
  let : (completedOrdinaryPullback f d).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) :=
    by
      unfold completedOrdinaryPullback ε completedOrdinaryPullbackCounit
      exact (completedOrdinaryPullback_exists f d).choose_spec.choose_spec.1
  exact isoTransportDerivedCounitComparisonOfEq (completedModulePullback f d)
      (pbcIsoModulePullback f d) (pbcIsoModulePullback_eq_completed f d).symm
      (completedOrdinaryPullback f d) ε

/-- The comparison fixed by the two derived counits on every complex.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoOrdinaryDerivedComparison :=
  (pbcIsoOrdinaryDerivedComparison_exists f d).exists.choose

/-- Transport preserves the specified integral full subcategory.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: the exact site equivalence and its exact inverse preserve K-injective
resolutions of strict towers, so derived inverse limits transport. The finite
quotient projections identify the reduction towers including transitions.
Thus the Koszul completeness condition is preserved. Transport every stratum,
every common local bounded model, and every etale origin and its comparison.
All normalization equations are functorial images of the original equations;
bounds and the number of strata remain unchanged. -/
theorem pbcIsoAmbientPullback_preserves
    (K : PbcBoundedConstructibleComplete Y d) :
    PbcIsBoundedConstructibleComplete X d ((pbcIsoAmbientPullback f d).obj K.obj) := by
  sorry

include hf in
/-- The completed comparison is invertible on the stipulated integral complete objects.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: pbcIsoAmbientPullback_preserves makes the exact inverse image intrinsically
complete. Transport completeness through the ordinary derived comparison. The
normalized strict-tower comparison identifies completedPullbackComparison with
the intrinsic completion-reflector unit. This unit is invertible on a complete
object, hence the specified completed comparison is invertible.
-/
@[instance] theorem pbcIsoCompletedComparison_isIso
    (K : PbcBoundedConstructibleComplete Y d) :
    IsIso (completedPullbackComparison f d K.obj) := by
  let M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y d) :=
    ⟨K.obj, K.property.1⟩
  obtain ⟨c, hc, _⟩ := pbcActualCompletedPullback_tower d f
  have hs : (pbcActualStrictCompletedPullUnit d f).app K.obj =
      completedPullbackComparison f d K.obj := by
    simp only [pbcActualStrictCompletedPullUnit, NatTrans.comp_app,
      Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Category.id_comp]
    rfl
  apply isoTransportCompletionUnit (PbcIsIntrinsicallyComplete X d)
    ((pbcIsoOrdinaryDerivedComparison f d).app K.obj)
    (pbcIsoAmbientPullback_preserves f d K).1
    (completedPullbackComparison f d K.obj) (c.app M)
  simpa only [M, hs, pbcActualCompletedPullUnit, Functor.whiskerLeft_app,
    pbcActualCompletionUnit, Iso.app_hom] using hc M

/-- Completed pullback is the same coefficient transport, with its normalized comparison.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoCompletedPullback_identification (K : PbcBoundedConstructibleComplete Y d) :
    completedPullbackObject f d K.obj ≅ (pbcIsoAmbientPullback f d).obj K.obj :=
  (asIso (completedPullbackComparison f d K.obj)).symm ≪≫
    (pbcIsoOrdinaryDerivedComparison f d).app K.obj

/-- Restriction to the full subcategory, retaining all ambient derived morphisms.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoIntegralPullback :
    PbcBoundedConstructibleComplete Y d ⥤ PbcBoundedConstructibleComplete X d :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete X d)
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete Y d) ⋙ pbcIsoAmbientPullback f d)
    (pbcIsoAmbientPullback_preserves f d)

/-- The inverse coefficient transport preserves the same integral conditions.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: apply preservation to the inverse scheme isomorphism. The normalized
ordinary derived comparisons, pullback composition comparison and identity
comparison identify inverse transport followed by transport with the identity.
The ambient equivalence is fully faithful on the full subcategories. Its inverse
therefore supplies an integral preimage of every target object, proving essential
surjectivity and hence the restricted equivalence. -/
@[instance] theorem pbcIsoIntegralPullback_isEquivalence :
    (pbcIsoIntegralPullback f d).IsEquivalence := by
  let H := pbcIsoAmbientPullback f d
  let J := pbcIsoAmbientPullback (inv f) d
  let a : J ⋙ H ≅ 𝟭 (PbcCompletedDerived X d) :=
    Functor.isoWhiskerRight (pbcIsoOrdinaryDerivedComparison (inv f) d).symm H ≪≫
      Functor.isoWhiskerLeft (completedOrdinaryPullback (inv f) d)
        (pbcIsoOrdinaryDerivedComparison f d).symm ≪≫
      (pbcActualDerivedPullCompIso f (inv f) d).symm ≪≫
      eqToIso (congrArg (fun q : X ⟶ X ↦ completedOrdinaryPullback q d)
        (IsIso.hom_inv_id f)) ≪≫ pbcActualDerivedPullIdIso d X
  exact isoTransportFullSubcategoryEquivalence
    (PbcIsBoundedConstructibleComplete Y d) (PbcIsBoundedConstructibleComplete X d)
    H (pbcIsoAmbientPullback_preserves f d) J (pbcIsoAmbientPullback_preserves (inv f) d) a

set_option backward.isDefEq.respectTransparency false in
private theorem isoTransportScalar_projection (T : Scheme.{u}) (n : ℕ) :
    pbcCompletedScalar T d ≫ pbcAdicProjection T d n =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≫
          (pbcLevelConstantComparison T d n).hom := by
  dsimp only [pbcCompletedScalar, pbcCompletedComparison, pbcAdicProjection]
  rw [Category.assoc]
  erw [HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc]
  erw [(adicDatumScalar_exists T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite }).exists.choose_spec n]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem isoTransportScalar_pullback :
    proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of A) ≫
        pbcCompletedScalar X d =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (pbcCompletedScalar Y d) ≫ completedCoefficientMap f d := by
  let F := proEtaleSheafInverseImage f CommRingCat.{u + 1}
  apply limit.hom_ext (F := pbcAdicRings X d)
  intro n
  change _ ≫ pbcAdicProjection X d n.unop = _ ≫ pbcAdicProjection X d n.unop
  rw [Category.assoc, isoTransportScalar_projection]
  rw [Category.assoc]
  have hp : completedCoefficientMap f d ≫ pbcAdicProjection X d n.unop =
      completedCoefficientComponent f d n.unop := by
    unfold completedCoefficientMap
    exact limit.lift_π _ n
  rw [hp]
  dsimp only [completedCoefficientComponent, completedFiniteCoefficientMap]
  rw [← F.map_comp_assoc, isoTransportScalar_projection]
  rw [F.map_comp]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc _ (pbcLevelConstantComparison Y d n.unop).hom
    (pbcLevelConstantComparison Y d n.unop).inv, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ (pbcLevelConstantComparison X d n.unop).hom)
    ((proEtaleIso_constantComparison f CommRingCat.{u + 1}).2
      (CommRingCat.of A) (CommRingCat.of (A ⧸ d.ideal ^ (n.unop + 1)))
      (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n.unop + 1)))))

set_option backward.isDefEq.respectTransparency false in
private theorem isoTransportScalar_directImage :
    pbcCompletedScalar Y d ≫ proEtaleRingDirectImageMap f
        (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
          (asIso (completedCoefficientMap f d)) =
      proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A) ≫
        (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
          (pbcCompletedScalar X d) := by
  let G := proEtaleSheafDirectImage f CommRingCat.{u + 1}
  let adj := proEtaleSheafAdjunction f CommRingCat.{u + 1}
  dsimp only [proEtaleRingDirectImageMap, asIso_hom]
  have hn := adj.unit.naturality (pbcCompletedScalar Y d)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  rw [Category.assoc, ← G.map_comp, ← isoTransportScalar_pullback f d, G.map_comp,
    ← Category.assoc]
  congr 1
  exact (adj.homEquiv _ _).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
private theorem isoTransportSection_directImage (U : Y.ProEtᵒᵖ) (b : A) :
    (proEtaleRingDirectImageMap f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (asIso (completedCoefficientMap f d))).hom.app U (pbcCompletedSection Y d U b) =
        pbcCompletedSection X d ((proEtaleBaseChange f).op.obj U) b := by
  have hn := Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))
      ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A))))
    (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
  change _ ≫ (proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
    (CommRingCat.of A)).hom = _ at hn
  have hu := ConcreteCategory.congr_hom (congr_app hn U) b
  change (proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of A)).hom.app U
        ((toSheafify (ProEt.topology Y)
          ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))).app U b) =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app
        ((proEtaleBaseChange f).op.obj U) b at hu
  have h := ConcreteCategory.congr_hom
    (congrArg (fun z ↦ z.hom.app U) (isoTransportScalar_directImage f d))
      ((toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))).app U b)
  change _ = (pbcCompletedScalar X d).hom.app
    ((proEtaleBaseChange f).op.obj U)
      ((proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of A)).hom.app U _) at h
  rw [hu] at h
  exact h

/-- Coefficient transport is additive and linear for the original constant-section action.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: inverse image and scalar identification respect sums sectionwise. The
finite comparisons send each constant scalar to itself; their limit therefore
intertwines the recorded constant-section actions. The same equations hold on
complexes, descend to derived morphisms, and restrict to the full subcategories. -/
theorem pbcIsoIntegralPullback_linear :
    (pbcIsoIntegralPullback f d).Additive ∧ (pbcIsoIntegralPullback f d).Linear A := by
  have : (pbcIsoAmbientPullback f d).Additive := inferInstance
  constructor
  · constructor
    intro M N a b
    apply ObjectProperty.hom_ext
    exact (pbcIsoAmbientPullback f d).map_add
  · let G := proEtaleRingModuleDirectImage f (pbcAdicCompletion Y d)
      (pbcAdicCompletion X d) (asIso (completedCoefficientMap f d))
    have : G.Linear A := by
      constructor
      intro M N a b
      ext U x
      change pbcCompletedSection X d ((proEtaleBaseChange f).op.obj U) b •
          ((a.val.app ((proEtaleBaseChange f).op.obj U)).hom x) =
        (proEtaleRingDirectImageMap f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
          (asIso (completedCoefficientMap f d))).hom.app U
            (pbcCompletedSection Y d U b) •
              ((a.val.app ((proEtaleBaseChange f).op.obj U)).hom x)
      rw [isoTransportSection_directImage]
    have : (pbcIsoModulePullback f d).Linear A :=
      (proEtaleRingModuleAdjunction f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (asIso (completedCoefficientMap f d))).left_adjoint_linear
    have : (pbcIsoAmbientPullback f d).Linear A := inferInstance
    constructor
    intro M N a b
    apply ObjectProperty.hom_ext
    exact (pbcIsoAmbientPullback f d).map_smul b a.hom

/-- Additivity supplied by the named coefficient-transport theorem.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
instance pbcIsoIntegralPullback_additive : (pbcIsoIntegralPullback f d).Additive :=
  (pbcIsoIntegralPullback_linear f d).1

/-- Linearity supplied by the named constant-section compatibility theorem.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
instance pbcIsoIntegralPullback_isLinear : (pbcIsoIntegralPullback f d).Linear A :=
  (pbcIsoIntegralPullback_linear f d).2

/-- On the raw rationalization transport sends a tensor a tensor u to a tensor P(u).
This construction retains precisely the original integral object representatives.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
abbrev pbcRationalIsoPullback {T : Scheme.{u}} (e : Aut T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (p : A) :
    PbcRationalCategory T d p ⥤ PbcRationalCategory T d p :=
  ScalarLocalization.map A (PbcBoundedConstructibleComplete T d) p
    (pbcIsoIntegralPullback e.hom d)


set_option backward.isDefEq.respectTransparency false in
private theorem isoTransportFiniteMap_naturality
    {B : Type (u + 1)} [CommRing B] (dB : AdicCoefficientDatum B) (n : ℕ)
    (a : CommRingCat.of (A ⧸ d.ideal ^ (n + 1)) ⟶
      CommRingCat.of (B ⧸ dB.ideal ^ (n + 1))) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        ((pbcLevelConstantComparison Y d n).inv ≫
          (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map a ≫
          (pbcLevelConstantComparison Y dB n).hom) ≫
        completedFiniteCoefficientMap f dB n =
      completedFiniteCoefficientMap f d n ≫
        (pbcLevelConstantComparison X d n).inv ≫
          (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map a ≫
          (pbcLevelConstantComparison X dB n).hom := by
  let L := proEtaleSheafInverseImage f CommRingCat.{u + 1}
  dsimp only [completedFiniteCoefficientMap]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← L.map_comp_assoc (pbcLevelConstantComparison Y dB n).hom
    (pbcLevelConstantComparison Y dB n).inv, Iso.hom_inv_id, L.map_id,
    Category.id_comp, Iso.hom_inv_id_assoc]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ L.map (pbcLevelConstantComparison Y d n).inv ≫ z ≫
      (pbcLevelConstantComparison X dB n).hom)
    ((proEtaleIso_constantComparison f CommRingCat.{u + 1}).2 _ _ a).symm

set_option backward.isDefEq.respectTransparency false in
omit hf in
private theorem isoTransportCompletedMap_naturality
    {B : Type (u + 1)} [CommRing B] (dB : AdicCoefficientDatum B)
    (aY : ∀ n, (pbcAdicRings Y d).obj (op n) ⟶ (pbcAdicRings Y dB).obj (op n))
    (aX : ∀ n, (pbcAdicRings X d).obj (op n) ⟶ (pbcAdicRings X dB).obj (op n))
    (ha : ∀ n, (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (aY n) ≫
      completedFiniteCoefficientMap f dB n = completedFiniteCoefficientMap f d n ≫ aX n)
    (φY : pbcAdicCompletion Y d ⟶ pbcAdicCompletion Y dB)
    (φX : pbcAdicCompletion X d ⟶ pbcAdicCompletion X dB)
    (hY : ∀ n, φY ≫ pbcAdicProjection Y dB n = pbcAdicProjection Y d n ≫ aY n)
    (hX : ∀ n, φX ≫ pbcAdicProjection X dB n = pbcAdicProjection X d n ≫ aX n) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map φY ≫
        completedCoefficientMap f dB = completedCoefficientMap f d ≫ φX := by
  let L := proEtaleSheafInverseImage f CommRingCat.{u + 1}
  have hp {D : Type (u + 1)} [CommRing D] (dD : AdicCoefficientDatum D) (n : ℕ) :
      completedCoefficientMap f dD ≫ pbcAdicProjection X dD n =
        L.map (pbcAdicProjection Y dD n) ≫ completedFiniteCoefficientMap f dD n := by
    unfold completedCoefficientMap
    exact limit.lift_π _ (op n)
  apply limit.hom_ext
  intro n
  change _ ≫ pbcAdicProjection X dB n.unop = _ ≫ pbcAdicProjection X dB n.unop
  rw [Category.assoc, hp, ← L.map_comp_assoc, hY, L.map_comp, Category.assoc,
    ha, ← Category.assoc, ← hp]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ completedCoefficientMap f d ≫ z) (hX n.unop).symm

set_option backward.isDefEq.respectTransparency false in
private theorem isoTransportScalarRightComparison
    {B : Type (u + 1)} [CommRing B] (dB : AdicCoefficientDatum B)
    (φY : pbcAdicCompletion Y d ⟶ pbcAdicCompletion Y dB)
    (φX : pbcAdicCompletion X d ⟶ pbcAdicCompletion X dB)
    (hφ : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map φY ≫
        completedCoefficientMap f dB = completedCoefficientMap f d ≫ φX) :
    ∃! r : pbcRestrict φX ⋙
        proEtaleRingModuleDirectImage f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
          (asIso (completedCoefficientMap f d)) ≅
      proEtaleRingModuleDirectImage f (pbcAdicCompletion Y dB) (pbcAdicCompletion X dB)
          (asIso (completedCoefficientMap f dB)) ⋙ pbcRestrict φY,
      ∀ (M : pbcModules X (pbcAdicCompletion X dB)) (U : Y.ProEtᵒᵖ)
        (x : ((pbcRestrict φX ⋙
          proEtaleRingModuleDirectImage f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
            (asIso (completedCoefficientMap f d))).obj M).val.obj U),
        HEq ((r.hom.app M).val.app U x) x := by
  let cR := proEtaleRingDirectImageMap f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
    (asIso (completedCoefficientMap f d))
  let cS := proEtaleRingDirectImageMap f (pbcAdicCompletion Y dB) (pbcAdicCompletion X dB)
    (asIso (completedCoefficientMap f dB))
  have hc : φY ≫ cS = cR ≫
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map φX := by
    let G := proEtaleSheafDirectImage f CommRingCat.{u + 1}
    let η := (proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit
    dsimp only [cR, cS, proEtaleRingDirectImageMap, asIso_hom]
    have hη := η.naturality φY
    simp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] at hη
    rw [← Category.assoc, hη]
    simp only [Category.assoc]
    rw [← G.map_comp, hφ, G.map_comp]
  let GE := proEtaleRingModuleDirectImage f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
    (asIso (completedCoefficientMap f d))
  let GF := proEtaleRingModuleDirectImage f (pbcAdicCompletion Y dB) (pbcAdicCompletion X dB)
    (asIso (completedCoefficientMap f dB))
  have hs (U : Y.ProEtᵒᵖ) :
      (φX.hom.app ((proEtaleBaseChange f).op.obj U)).hom.comp (cR.hom.app U).hom =
        (cS.hom.app U).hom.comp (φY.hom.app U).hom :=
    congrArg (fun z ↦ (z.hom.app U).hom) hc.symm
  let rM (M : pbcModules X (pbcAdicCompletion X dB)) :
      ((pbcRestrict φX) ⋙ GE).obj M ≅ (GF ⋙ pbcRestrict φY).obj M :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        (ModuleCat.restrictScalarsCongr (hs U)).app
          (M.val.obj ((proEtaleBaseChange f).op.obj U)))
        (fun {U V} g ↦ by ext x; rfl))
  let r : pbcRestrict φX ⋙ GE ≅ GF ⋙ pbcRestrict φY :=
    NatIso.ofComponents rM (fun g ↦ by ext U x; rfl)
  refine ⟨r, ?_, ?_⟩
  · intro M U x
    rfl
  · intro r' hr'
    apply Iso.ext
    ext M U x
    exact eq_of_heq (hr' M U x)

variable (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {T : Scheme.{u}} (e : Aut T)
  {E F : Padic.FiniteCoefficientFields l Ω}

/-- Exact transport's right adjoints commute with restriction of coefficients.
The section equation fixes the comparison, not just its isomorphism class.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: both functors have exactly the same underlying sheaf, evaluated on the
postcomposition functor of the site isomorphism. The coefficient actions agree
by the finite constant comparisons and their limit projection equations.
Identity on sections gives the isomorphism and determines it uniquely. -/
theorem pbcIsoScalarRightComparison_exists (h : E ≤ F) :
    ∃! r :
      pbcRestrict (pbcCompletedScalarMap l Ω T h) ⋙
          proEtaleRingModuleDirectImage e.hom
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (asIso (completedCoefficientMap e.hom (pbcStageDatum.{u} l Ω E))) ≅
        proEtaleRingModuleDirectImage e.hom
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F))
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F))
            (asIso (completedCoefficientMap e.hom (pbcStageDatum.{u} l Ω F))) ⋙
          pbcRestrict (pbcCompletedScalarMap l Ω T h),
      ∀ (M : pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F)))
        (U : T.ProEtᵒᵖ) (x : ((pbcRestrict (pbcCompletedScalarMap l Ω T h) ⋙
          proEtaleRingModuleDirectImage e.hom
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (asIso (completedCoefficientMap e.hom (pbcStageDatum.{u} l Ω E)))).obj M).val.obj U),
        HEq ((r.hom.app M).val.app U x) x := by
  let dE := pbcStageDatum.{u} l Ω E
  let dF := pbcStageDatum.{u} l Ω F
  let φ := pbcCompletedScalarMap l Ω T h
  have hn (n : ℕ) :
      (proEtaleSheafInverseImage e.hom CommRingCat.{u + 1}).map
          (pbcFiniteScalarMap l Ω T h n) ≫ completedFiniteCoefficientMap e.hom dF n =
        completedFiniteCoefficientMap e.hom dE n ≫ pbcFiniteScalarMap l Ω T h n := by
    simpa only [pbcFiniteScalarMap] using
      isoTransportFiniteMap_naturality e.hom dE dF n
        (CommRingCat.ofHom (pbcQuotientInclusion l Ω h n))
  have hφ : (proEtaleSheafInverseImage e.hom CommRingCat.{u + 1}).map φ ≫
      completedCoefficientMap e.hom dF = completedCoefficientMap e.hom dE ≫ φ :=
    isoTransportCompletedMap_naturality e.hom dE dF
      (pbcFiniteScalarMap l Ω T h) (pbcFiniteScalarMap l Ω T h) hn φ φ
      (pbcCompletedScalarMap_exists l Ω T h).exists.choose_spec
      (pbcCompletedScalarMap_exists l Ω T h).exists.choose_spec
  exact isoTransportScalarRightComparison e.hom dE dF φ φ hφ

/-- The right-adjoint comparison fixed by identity on sections.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoScalarRightComparison (h : E ≤ F) :
    pbcRestrict (pbcCompletedScalarMap l Ω T h) ⋙
          proEtaleRingModuleDirectImage e.hom
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (asIso (completedCoefficientMap e.hom (pbcStageDatum.{u} l Ω E))) ≅
        proEtaleRingModuleDirectImage e.hom
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F))
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F))
            (asIso (completedCoefficientMap e.hom (pbcStageDatum.{u} l Ω F))) ⋙
          pbcRestrict (pbcCompletedScalarMap l Ω T h) :=
  (pbcIsoScalarRightComparison_exists l Ω e h).exists.choose

/-- The ordinary comparison is the mate of the sectionwise identity comparison.
This pins down its tensor normalization.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoOrdinaryScalarComparison (h : E ≤ F) :
    pbcExtend (pbcCompletedScalarMap l Ω T h) ⋙
        pbcIsoModulePullback e.hom (pbcStageDatum.{u} l Ω F) ≅
      pbcIsoModulePullback e.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcExtend (pbcCompletedScalarMap l Ω T h) :=
  (conjugateIsoEquiv
    ((proEtaleRingModuleAdjunction e.hom _ _
        (asIso (completedCoefficientMap e.hom (pbcStageDatum.{u} l Ω E)))).comp
      (pbcScalarAdjunction (pbcCompletedScalarMap l Ω T h)))
    ((pbcScalarAdjunction (pbcCompletedScalarMap l Ω T h)).comp
      (proEtaleRingModuleAdjunction e.hom _ _
        (asIso (completedCoefficientMap e.hom (pbcStageDatum.{u} l Ω F)))))).symm
    (pbcIsoScalarRightComparison l Ω e h)

/-- The ordinary comparison on nested complex functors, using the canonical
composition isomorphisms on both sides.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoOrdinaryComplexComparison (h : E ≤ F) :
    (pbcExtend (pbcCompletedScalarMap l Ω T h)).mapHomologicalComplex (.up ℤ) ⋙
        (pbcIsoModulePullback e.hom (pbcStageDatum.{u} l Ω F)).mapHomologicalComplex
        (.up ℤ) ≅
      (pbcIsoModulePullback e.hom (pbcStageDatum.{u} l Ω E)).mapHomologicalComplex
        (.up ℤ) ⋙
        (pbcExtend (pbcCompletedScalarMap l Ω T h)).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
      (Iso.refl (pbcExtend (pbcCompletedScalarMap l Ω T h) ⋙
        pbcIsoModulePullback e.hom (pbcStageDatum.{u} l Ω F))) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex (pbcIsoOrdinaryScalarComparison l Ω e h) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (pbcIsoModulePullback e.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcExtend (pbcCompletedScalarMap l Ω T h))) (.up ℤ)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isoTransportAmbientScalarComparison
    (T' : Scheme.{u}) (f' : T' ⟶ T') [IsIso f']
    {A' B' : Type (u + 1)} [CommRing A'] [CommRing B']
    (dA : AdicCoefficientDatum A') (dB : AdicCoefficientDatum B')
    (φ : pbcAdicCompletion T' dA ⟶ pbcAdicCompletion T' dB)
    (τ : (pbcExtend φ).mapHomologicalComplex (.up ℤ) ⋙
        (pbcIsoModulePullback f' dB).mapHomologicalComplex (.up ℤ) ≅
      (pbcIsoModulePullback f' dA).mapHomologicalComplex (.up ℤ) ⋙
        (pbcExtend φ).mapHomologicalComplex (.up ℤ)) :
    ∃! c : pbcDerivedExtend φ ⋙ pbcIsoAmbientPullback f' dB ≅
        pbcIsoAmbientPullback f' dA ⋙ pbcDerivedExtend φ,
      ∀ P : CochainComplex (pbcModules T' (pbcAdicCompletion T' dA)) ℤ,
        c.hom.app (DerivedCategory.Q.obj P) ≫
          (pbcDerivedExtend φ).map
            ((pbcIsoModulePullback f' dA).mapDerivedCategoryFactors.hom.app P) ≫
          pbcComplexCounit φ
            (((pbcIsoModulePullback f' dA).mapHomologicalComplex (.up ℤ)).obj P) =
        (pbcIsoAmbientPullback f' dB).map (pbcComplexCounit φ P) ≫
          (pbcIsoModulePullback f' dB).mapDerivedCategoryFactors.hom.app
            (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (τ.hom.app P) := by
  have hc := isoTransportCochainSquare
    (hG := pbcExtend_additive φ)
    (hFA := inferInstanceAs (pbcIsoModulePullback f' dA).Additive)
    (hFB := inferInstanceAs (pbcIsoModulePullback f' dB).Additive)
    (hEA := pbcIsoModulePullback_isEquivalence f' dA)
    (hEB := pbcIsoModulePullback_isEquivalence f' dB)
    (pbcExtend φ) (pbcDerivedExtend φ)
    (pbcExtensionCounit φ) (pbcDerivedExtension_universal φ)
    (pbcIsoModulePullback f' dA) (pbcIsoModulePullback f' dB) τ
  simpa only [isoTransportComplexCounitEq] using hc


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ambient comparison is fixed by the ordinary tensor comparison and the
specified universal derived counits, on complexes before localization.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: the scalar-extension pair is a right Kan extension along derived
localization. Precomposition and postcomposition by the exact transport
equivalences preserve that universal property. The ordinary complex comparison
identifies the two underived squares. Uniqueness of right Kan extensions gives
the derived isomorphism and its factorization identity on every complex.
The same universal property proves uniqueness with the specified counit equation. -/
theorem pbcIsoAmbientScalarComparison_exists (h : E ≤ F) :
    ∃! c : pbcAmbientScalarExtension l Ω T h ⋙
        pbcIsoAmbientPullback e.hom (pbcStageDatum.{u} l Ω F) ≅
      pbcIsoAmbientPullback e.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcAmbientScalarExtension l Ω T h,
      ∀ P : CochainComplex
          (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) ℤ,
        c.hom.app (DerivedCategory.Q.obj P) ≫
          (pbcAmbientScalarExtension l Ω T h).map
            ((pbcIsoModulePullback e.hom
              (pbcStageDatum.{u} l Ω E)).mapDerivedCategoryFactors.hom.app P) ≫
          pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
            (((pbcIsoModulePullback e.hom (pbcStageDatum.{u} l Ω E)).mapHomologicalComplex
              (.up ℤ)).obj P) =
        (pbcIsoAmbientPullback e.hom (pbcStageDatum.{u} l Ω F)).map
            (pbcComplexCounit (pbcCompletedScalarMap l Ω T h) P) ≫
          (pbcIsoModulePullback e.hom (pbcStageDatum.{u} l Ω F)).mapDerivedCategoryFactors.hom.app
              (((pbcExtend (pbcCompletedScalarMap l Ω T h)).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((pbcIsoOrdinaryComplexComparison l Ω e h).hom.app P) := by
  exact isoTransportAmbientScalarComparison T e.hom
    (pbcStageDatum.{u} l Ω E) (pbcStageDatum.{u} l Ω F)
    (pbcCompletedScalarMap l Ω T h) (pbcIsoOrdinaryComplexComparison l Ω e h)

/-- The ambient Frobenius/scalar comparison with its representative normalization.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoAmbientScalarComparison (h : E ≤ F) :
    pbcAmbientScalarExtension l Ω T h ⋙
        pbcIsoAmbientPullback e.hom (pbcStageDatum.{u} l Ω F) ≅
      pbcIsoAmbientPullback e.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcAmbientScalarExtension l Ω T h :=
  (pbcIsoAmbientScalarComparison_exists l Ω e h).exists.choose

variable [IsNoetherian T] (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
  (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

attribute [local semireducible] pbcScalarExtension pbcIntegralScalarExtension

/-- Fullness restricts the normalized ambient comparison uniquely.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: both tensor extension and transport preserve the defining full
subcategories. Lift ambient components and inverses by fullness; faithfulness
proves the naturality, inverse and uniqueness equations. -/
theorem pbcIsoIntegralScalarComparison_exists (h : E ≤ F) :
    ∃! c : pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcIsoIntegralPullback e.hom (pbcStageDatum.{u} l Ω F) ≅
      pbcIsoIntegralPullback e.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcIntegralScalarExtension l Ω T hdim hl h,
      Functor.whiskerRight c.hom
          (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F))) =
        Functor.whiskerLeft
          (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)))
          (pbcIsoAmbientScalarComparison l Ω e h).hom := by
  let c : pbcIntegralScalarExtension l Ω T hdim hl h ⋙
      pbcIsoIntegralPullback e.hom (pbcStageDatum.{u} l Ω F) ≅
      pbcIsoIntegralPullback e.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcIntegralScalarExtension l Ω T hdim hl h :=
    NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk _ ((pbcIsoAmbientScalarComparison l Ω e h).app K.obj))
      (fun a ↦ by
        apply ObjectProperty.hom_ext
        exact (pbcIsoAmbientScalarComparison l Ω e h).hom.naturality a.hom)
  refine ⟨c, rfl, ?_⟩
  intro c' hc'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact congrArg (fun η ↦ η.app K) hc'

/-- The integral comparison retaining its ambient normalization.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoIntegralScalarComparison (h : E ≤ F) :
    pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcIsoIntegralPullback e.hom (pbcStageDatum.{u} l Ω F) ≅
      pbcIsoIntegralPullback e.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcIntegralScalarExtension l Ω T hdim hl h :=
  (pbcIsoIntegralScalarComparison_exists l Ω e hdim hl h).exists.choose

set_option linter.unusedSectionVars false in
/-- Integral localization commutes with the explicitly linear coefficient transport.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: both functors have the same object function. On morphisms they both send
1 tensor u to 1 tensor P(u); the base-change linear map defining transport gives
the asserted equality of functors. -/
theorem pbcIsoRationalization (E : Padic.FiniteCoefficientFields l Ω) :
    pbcRationalization T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E) ⋙
        pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E) =
      pbcIsoIntegralPullback e.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcRationalization T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E) := by
  have _ := ‹IsAlgClosure (Padic l) Ω›
  have _ := ‹IsNoetherian T›
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The rational comparison is fixed on every original integral object.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: conjugate rationalization of the integral comparison by the displayed
integral/localization comparisons. Naturality on fractions follows by inverting
the coefficient uniformizer; all objects are integral objects, so uniqueness follows. -/
theorem pbcIsoRationalScalarComparison_exists (h : E ≤ F) :
    ∃! c : pbcScalarExtension l Ω T hdim hl h ⋙
        pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω F) (pbcStageUniformizer.{u} l Ω F) ≅
      pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E) ⋙
        pbcScalarExtension l Ω T hdim hl h,
      ∀ K : PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E),
        c.hom.app
            ((pbcRationalization T (pbcStageDatum.{u} l Ω E)
              (pbcStageUniformizer.{u} l Ω E)).obj K) =
          (pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω F) (pbcStageUniformizer.{u} l Ω F)).map
            ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K) ≫
          (eqToIso (pbcIsoRationalization l Ω e F)).hom.app
            ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K) ≫
          (pbcRationalization T (pbcStageDatum.{u} l Ω F) (pbcStageUniformizer.{u} l Ω F)).map
            ((pbcIsoIntegralScalarComparison l Ω e hdim hl h).hom.app K) ≫
          (pbcScalarIntegralComparison l Ω T hdim hl h).inv.app
            ((pbcIsoIntegralPullback e.hom (pbcStageDatum.{u} l Ω E)).obj K) ≫
          (pbcScalarExtension l Ω T hdim hl h).map
            ((eqToIso (pbcIsoRationalization l Ω e E)).inv.app K) := by
  exact isoTransportRationalComparison
    (R := PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (C := PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E))
    (C' := PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F))
    (D := PbcRationalCategory T (pbcStageDatum.{u} l Ω F)
      (pbcStageUniformizer.{u} l Ω F)) (pbcStageUniformizer.{u} l Ω E)
    (pbcIntegralScalarExtension l Ω T hdim hl h)
    (pbcIsoIntegralPullback e.hom (pbcStageDatum.{u} l Ω E))
    (pbcIsoIntegralPullback e.hom (pbcStageDatum.{u} l Ω F))
    (pbcStageLocalization l Ω T F) (pbcScalarExtension l Ω T hdim hl h)
    (pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E))
    (pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω F) (pbcStageUniformizer.{u} l Ω F))
    (pbcScalarIntegralComparison l Ω T hdim hl h)
    (pbcIsoIntegralScalarComparison l Ω e hdim hl h)
    (eqToIso (pbcIsoRationalization l Ω e E)) (eqToIso (pbcIsoRationalization l Ω e F))

/-- The Frobenius/scalar comparison determined by canonical tensor transport.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoRationalScalarComparison (h : E ≤ F) :
    pbcScalarExtension l Ω T hdim hl h ⋙
        pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω F) (pbcStageUniformizer.{u} l Ω F) ≅
      pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E) ⋙
        pbcScalarExtension l Ω T hdim hl h :=
  (pbcIsoRationalScalarComparison_exists l Ω e hdim hl h).exists.choose

end AlgebraicGeometry.Scheme
