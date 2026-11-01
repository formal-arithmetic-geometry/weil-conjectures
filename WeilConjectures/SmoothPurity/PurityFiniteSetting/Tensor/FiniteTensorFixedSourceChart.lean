/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorFixedComparisons
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.IdIso

/-! # Fixed-coordinate normalization of the finite source comparison

The intrinsic root-normalization identity is transported through the prescribed
scalar presentation and realization units, preserving the native scalar shifts.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

private instance uniq_shift
    {V W : Type*} [Category V] [Category W] [HasShift V ℤ] [HasShift W ℤ]
    {G H : V ⥤ W} [G.CommShift ℤ] [H.CommShift ℤ]
    {R : W ⥤ V} [R.CommShift ℤ] (a : G ⊣ R) (b : H ⊣ R)
    [ha : a.CommShift ℤ] [hb : b.CommShift ℤ] :
    NatTrans.CommShift (a.leftAdjointUniq b).hom ℤ := by
  have he : (a.leftAdjointUniq b).hom =
      (Functor.leftUnitor _).inv ≫ Functor.whiskerRight b.unit G ≫
        (Functor.associator H R G).hom ≫ Functor.whiskerLeft H a.counit ≫
        (Functor.rightUnitor _).hom := by
    ext X
    apply (a.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.rightUnitor_hom_app,
      Category.id_comp]
    erw [Category.comp_id]
    change _ = a.homEquiv _ _ (G.map (b.unit.app X) ≫ a.counit.app _)
    rw [show (G.map (b.unit.app X) ≫ a.counit.app _) =
      (a.homEquiv _ _).symm (b.unit.app X) by
        rw [Adjunction.homEquiv_counit]]
    exact (Equiv.apply_symm_apply _ _).symm
  rw [he]
  infer_instance

private instance presentation_realization_shift
    (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) :
    (sfIntrinsicDerivedEquivalence T A).functor.CommShift ℤ :=
  inferInstanceAs ((sfIntrinsicModuleEquivalence T A).functor.mapDerivedCategory.CommShift ℤ)

private instance presentation_inverse_realization_shift
    (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) :
    (sfIntrinsicDerivedEquivalence T A).inverse.CommShift ℤ :=
  inferInstanceAs ((sfIntrinsicModuleEquivalence T A).inverse.mapDerivedCategory.CommShift ℤ)

private instance presentation_equivalence_shift
    (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) :
    (sfIntrinsicDerivedEquivalence T A).CommShift ℤ := by
  apply Equivalence.CommShift.mk''
  change NatTrans.CommShift
    (((Functor.mapDerivedCategoryCompIso
        (sfIntrinsicModuleEquivalence T A).inverse
        (sfIntrinsicModuleEquivalence T A).functor).symm ≪≫
      Functor.mapDerivedCategoryNatIso (sfIntrinsicModuleEquivalence T A).counitIso ≪≫
      Functor.mapDerivedCategoryIdIso _).hom) ℤ
  simp only [Iso.trans_hom, Iso.symm_hom]
  with_unfolding_all exact inferInstance

private instance presentation_ofNatIsoRight_shift
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {G H : D ⥤ C} [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (a : F ⊣ G) (e : G ≅ H) [a.CommShift ℤ] [NatTrans.CommShift e.hom ℤ] :
    (a.ofNatIsoRight e).CommShift ℤ where
  commShift_unit := by dsimp only [Adjunction.ofNatIsoRight]; infer_instance
  commShift_counit := by dsimp only [Adjunction.ofNatIsoRight]; infer_instance

private theorem presentation_exactSquare_shift
    {C₁ : Type*} {C₂ : Type*} {C₃ : Type*} {C₄ : Type*}
    [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
    [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    {F₁ : C₁ ⥤ C₂} {F₂ : C₂ ⥤ C₄} {G₁ : C₁ ⥤ C₃} {G₂ : C₃ ⥤ C₄}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    NatTrans.CommShift
      (ProEtale.SupportedEtaleTensorOrigin.exactSquare e).hom ℤ := by
  unfold ProEtale.SupportedEtaleTensorOrigin.exactSquare
    Functor.mapDerivedCategorySquareIso
  simp only [Iso.trans_hom, Iso.symm_hom]
  infer_instance

private theorem presentation_rightIso_shift
    {C A D B : Type*} [Category* C] [Category* A] [Category* D] [Category* B]
    [HasShift C ℤ] [HasShift A ℤ] [HasShift D ℤ] [HasShift B ℤ]
    (EA : C ≌ A) (EB : D ≌ B)
    [EA.functor.CommShift ℤ] [EA.inverse.CommShift ℤ] [EA.CommShift ℤ]
    [EB.functor.CommShift ℤ] [EB.inverse.CommShift ℤ] [EB.CommShift ℤ]
    (R : B ⥤ A) (V : D ⥤ C) [R.CommShift ℤ] [V.CommShift ℤ]
    (e : EB.functor ⋙ R ≅ V ⋙ EA.functor) [NatTrans.CommShift e.hom ℤ] :
    let r : R ⋙ EA.inverse ≅ EB.inverse ⋙ V :=
      Functor.isoWhiskerRight EB.counitIso.symm (R ⋙ EA.inverse) ≪≫
        Functor.isoWhiskerLeft EB.inverse (Functor.isoWhiskerRight e EA.inverse) ≪≫
        Functor.isoWhiskerLeft (EB.inverse ⋙ V) EA.unitIso.symm
    NatTrans.CommShift r.hom ℤ := by
  let r : R ⋙ EA.inverse ≅ EB.inverse ⋙ V :=
    Functor.isoWhiskerRight EB.counitIso.symm (R ⋙ EA.inverse) ≪≫
      Functor.isoWhiskerLeft EB.inverse (Functor.isoWhiskerRight e EA.inverse) ≪≫
      Functor.isoWhiskerLeft (EB.inverse ⋙ V) EA.unitIso.symm
  let n : R ⋙ EA.inverse ≅ EB.inverse ⋙ V :=
    (Functor.leftUnitor (R ⋙ EA.inverse)).symm ≪≫
      Functor.isoWhiskerRight EB.counitIso.symm (R ⋙ EA.inverse) ≪≫
      Functor.associator EB.inverse EB.functor (R ⋙ EA.inverse) ≪≫
      Functor.isoWhiskerLeft EB.inverse
        (Functor.associator EB.functor R EA.inverse).symm ≪≫
      Functor.isoWhiskerLeft EB.inverse (Functor.isoWhiskerRight e EA.inverse) ≪≫
      Functor.isoWhiskerLeft EB.inverse (Functor.associator V EA.functor EA.inverse) ≪≫
      (Functor.associator EB.inverse V (EA.functor ⋙ EA.inverse)).symm ≪≫
      Functor.isoWhiskerLeft (EB.inverse ⋙ V) EA.unitIso.symm ≪≫
      Functor.rightUnitor (EB.inverse ⋙ V)
  have hn : NatTrans.CommShift n.hom ℤ := by
    dsimp only [n, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom]
    infer_instance
  have he : n.hom = r.hom := by
    ext X
    simp only [n, r, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Iso.symm_hom, Functor.comp_obj, Functor.comp_map,
      Category.id_comp]
    erw [Category.comp_id]
  change NatTrans.CommShift r.hom ℤ
  rw [← he]
  exact hn

private theorem presentation_scalar_uniq_shift
    {C A D B : Type*} [Category* C] [Category* A] [Category* D] [Category* B]
    [HasShift C ℤ] [HasShift A ℤ] [HasShift D ℤ] [HasShift B ℤ]
    (EA : C ≌ A) (EB : D ≌ B)
    [EA.functor.CommShift ℤ] [EA.inverse.CommShift ℤ] [hEA : EA.CommShift ℤ]
    [EB.functor.CommShift ℤ] [EB.inverse.CommShift ℤ] [hEB : EB.CommShift ℤ]
    (R : B ⥤ A) (V : D ⥤ C) {L : A ⥤ B} {W : C ⥤ D}
    [R.CommShift ℤ] [V.CommShift ℤ] [L.CommShift ℤ] [W.CommShift ℤ]
    (adj : L ⊣ R) (adjV : W ⊣ V) [ha : adj.CommShift ℤ] [hb : adjV.CommShift ℤ]
    (e : EB.functor ⋙ R ≅ V ⋙ EA.functor) [he : NatTrans.CommShift e.hom ℤ] :
    let rightIso :=
      Functor.isoWhiskerRight EB.counitIso.symm (R ⋙ EA.inverse) ≪≫
        Functor.isoWhiskerLeft EB.inverse (Functor.isoWhiskerRight e EA.inverse) ≪≫
        Functor.isoWhiskerLeft (EB.inverse ⋙ V) EA.unitIso.symm
    NatTrans.CommShift (((EA.toAdjunction.comp adj).ofNatIsoRight rightIso).leftAdjointUniq
      (adjV.comp EB.toAdjunction) : EA.functor ⋙ L ≅ W ⋙ EB.functor).hom ℤ := by
  intro rightIso
  let r : R ⋙ EA.inverse ≅ EB.inverse ⋙ V := rightIso
  have hr : NatTrans.CommShift r.hom ℤ := presentation_rightIso_shift EA EB R V e
  have hc : (EA.toAdjunction.comp adj).CommShift ℤ :=
    Adjunction.CommShift.instComp (adj := EA.toAdjunction) (adj' := adj) (A := ℤ)
  let a₀ : (EA.functor ⋙ L) ⊣ (EB.inverse ⋙ V) := (EA.toAdjunction.comp adj).ofNatIsoRight r
  have hca : a₀.CommShift ℤ := presentation_ofNatIsoRight_shift _ r
  have hcomp : (adjV.comp EB.toAdjunction).CommShift ℤ :=
    Adjunction.CommShift.instComp (adj := adjV) (adj' := EB.toAdjunction) (A := ℤ)
  exact uniq_shift a₀ _ (ha := hca) (hb := hcomp)

private theorem scalar_presentation_shift (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u}) :
    letI : (ProEtale.scalarExtensionFunctor (P.finiteReductionRingHom m hm hmn) T).CommShift ℤ :=
      P.finiteReductionCommShift m hm hmn T
    letI : (ProEtale.SupportedEtaleTensorOrigin.fixedScalar
        (P.finiteReductionRingHom m hm hmn) T).CommShift ℤ :=
      P.finiteTensorReductionCommShift m hm hmn T
    NatTrans.CommShift
      (ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
        (P.finiteReductionRingHom m hm hmn) T).hom ℤ := by
  let : (ProEtale.scalarExtensionFunctor (P.finiteReductionRingHom m hm hmn) T).CommShift ℤ :=
    P.finiteReductionCommShift m hm hmn T
  let : (ProEtale.SupportedEtaleTensorOrigin.fixedScalar
      (P.finiteReductionRingHom m hm hmn) T).CommShift ℤ :=
    P.finiteTensorReductionCommShift m hm hmn T
  let φ := P.finiteReductionRingHom m hm hmn
  let : (ProEtale.scalarRestriction φ T).CommShift ℤ :=
    inferInstanceAs ((proEtaleCoefficientRestrictScalars T φ).mapDerivedCategory.CommShift ℤ)
  let : (proEtaleRingDerivedExtension
      (proEtaleConstantRingMap (T := T) φ)).CommShift ℤ :=
    P.finiteReductionCommShift m hm hmn T
  have ha : (proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := T) φ)).CommShift ℤ :=
    Adjunction.commShift_of_rightAdjoint
      (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ)) ℤ
  let : (ProEtale.SupportedEtaleTensorOrigin.fixedRestriction φ T).leftAdjoint.CommShift ℤ :=
    P.finiteTensorReductionCommShift m hm hmn T
  have hb : (Adjunction.ofIsRightAdjoint
      (ProEtale.SupportedEtaleTensorOrigin.fixedRestriction φ T)).CommShift ℤ :=
    Adjunction.commShift_of_rightAdjoint _ ℤ
  have he : NatTrans.CommShift
      (ProEtale.SupportedEtaleTensorOrigin.restrictionPresentation φ T).hom ℤ := by
    with_unfolding_all exact presentation_exactSquare_shift _
  have hEB : (sfIntrinsicDerivedEquivalence T
      (P.finiteReductionSetting m hm).Ring).CommShift ℤ :=
    presentation_equivalence_shift _ T
  have hEA : (sfIntrinsicDerivedEquivalence T P.Ring).CommShift ℤ :=
    presentation_equivalence_shift _ T
  with_unfolding_all exact (presentation_scalar_uniq_shift
    (sfIntrinsicDerivedEquivalence T P.Ring)
    (sfIntrinsicDerivedEquivalence T (P.finiteReductionSetting m hm).Ring)
    (ProEtale.scalarRestriction φ T) (ProEtale.SupportedEtaleTensorOrigin.fixedRestriction φ T)
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ))
    (Adjunction.ofIsRightAdjoint (ProEtale.SupportedEtaleTensorOrigin.fixedRestriction φ T))
    (ProEtale.SupportedEtaleTensorOrigin.restrictionPresentation φ T)
    (hEA := hEA) (hEB := hEB) (ha := ha) (hb := hb) (he := he))

@[instance_reducible] private def presentation_compShift
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (G : D ⥤ E) (sF : F.CommShift ℤ) (sG : G.CommShift ℤ) :
    (F ⋙ G).CommShift ℤ :=
  let := sF
  let := sG
  Functor.CommShift.comp F G

private theorem transport_chart
    {C D B : Type*} [Category* C] [Category* D] [Category* B]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift B ℤ]
    (G : C ⥤ B) (F : C ⥤ D) (E : D ⥤ B) [hE : E.Faithful]
    [hG : G.CommShift ℤ] [hF : F.CommShift ℤ] [hShiftE : E.CommShift ℤ]
    (α : G ≅ F ⋙ E) [hα : NatTrans.CommShift α.hom ℤ]
    (TC : C ⥤ C) (TD : D ⥤ D) (s : ℤ)
    (c : TC ≅ shiftFunctor C s) (d : TD ≅ shiftFunctor D s)
    {M₀ M : C} {N₀ N : D} (u : M₀ ≅ M) (v : N₀ ≅ N)
    (S : F.obj (TC.obj M) ⟶ TD.obj N) (P : F.obj M ⟶ N)
    (a : G.obj (TC.obj M₀) ⟶ E.obj (TD.obj N₀))
    (b : G.obj M₀ ⟶ E.obj N₀)
    (hS : α.hom.app (TC.obj M) ≫ E.map S =
      G.map (TC.map u.inv) ≫ a ≫ E.map (TD.map v.hom))
    (hP : α.hom.app M ≫ E.map P = G.map u.inv ≫ b ≫ E.map v.hom)
    (hN : a ≫ E.map (d.hom.app N₀) ≫ (E.commShiftIso s).hom.app N₀ =
      G.map (c.hom.app M₀) ≫ (G.commShiftIso s).hom.app M₀ ≫ b⟦s⟧') :
    S ≫ d.hom.app N = F.map (c.hom.app M) ≫ (F.commShiftIso s).hom.app M ≫ P⟦s⟧' := by
  apply E.map_injective
  apply (cancel_mono ((E.commShiftIso s).hom.app N)).1
  apply (cancel_epi (α.hom.app (TC.obj M))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (α.hom.app (TC.obj M)), hS]
  have hv := d.hom.naturality v.hom
  change TD.map v.hom ≫ d.hom.app N = d.hom.app N₀ ≫ v.hom⟦s⟧' at hv
  have hu := c.hom.naturality u.inv
  change TC.map u.inv ≫ c.hom.app M₀ = c.hom.app M ≫ u.inv⟦s⟧' at hu
  have hEv := E.commShiftIso_hom_naturality v.hom s
  have hGu := G.commShiftIso_hom_naturality u.inv s
  have hαeq := NatTrans.shift_app_comm α.hom s M
  have hEP := E.commShiftIso_hom_naturality P s
  have hαc := α.hom.naturality (c.hom.app M)
  simp only [Functor.comp_map] at hαc
  simp only [Category.assoc]
  rw [← E.map_comp_assoc, hv, E.map_comp]
  simp only [Category.assoc]
  rw [hEv, reassoc_of% hN]
  rw [← G.map_comp_assoc, hu, G.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hGu]
  rw [← (shiftFunctor B s).map_comp, ← (shiftFunctor B s).map_comp, ← hP]
  simp only [Functor.map_comp]
  rw [reassoc_of% hαeq, reassoc_of% hαc]
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc]
  rw [← hEP]

private theorem presentation_realize_twist
    {C D B : Type*} [Category* C] [Category* D] [Category* B]
    (E : D ⥤ B) [hfull : E.Full] [hfaithful : E.Faithful]
    (F : C ⥤ D) (G : C ⥤ B) (α : G ≅ F ⋙ E)
    (TC : C ⥤ C) (TD : D ⥤ D)
    {M₀ M : C} {N₀ N₁ N : D} (u : M₀ ≅ M) (v : N₀ ≅ N₁) (w : N₁ ≅ N)
    (a : G.obj (TC.obj M₀) ≅ E.obj (TD.obj N₀)) :
    α.hom.app (TC.obj M) ≫
        E.map (E.preimageIso
          ((((α.app (TC.obj M)).symm ≪≫ (G.mapIso (TC.mapIso u)).symm) ≪≫
            (a ≪≫ E.mapIso (TD.mapIso v))) ≪≫ E.mapIso (TD.mapIso w))).hom =
      G.map (TC.map u.inv) ≫ a.hom ≫ E.map (TD.map (v ≪≫ w).hom) := by
  simp only [Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_inv,
    Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem presentation_composite_normalization
    {C D A B : Type*} [Category* C] [Category* D] [Category* A] [Category* B]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift A ℤ] [HasShift B ℤ]
    (G : C ⥤ A) (R : A ⥤ B) (E : D ⥤ B)
    [hG : G.CommShift ℤ] [hR : R.CommShift ℤ] [hShiftE : E.CommShift ℤ]
    (s : ℤ) {M A₀ : C} {N B₀ : D} (c : A₀ ⟶ M⟦s⟧) (d : B₀ ⟶ N⟦s⟧)
    (a : R.obj (G.obj A₀) ⟶ E.obj B₀) (b : R.obj (G.obj M) ⟶ E.obj N)
    (h : a ≫ (E.map d ≫ (E.commShiftIso s).hom.app N) =
      R.map (G.map c ≫ (G.commShiftIso s).hom.app M) ≫
        (R.commShiftIso s).hom.app (G.obj M) ≫ b⟦s⟧') :
    a ≫ E.map d ≫ (E.commShiftIso s).hom.app N =
      (G ⋙ R).map c ≫ ((G ⋙ R).commShiftIso s).hom.app M ≫ b⟦s⟧' := by
  simpa only [Functor.map_comp, Functor.comp_map, Functor.comp_obj,
    Functor.commShiftIso_comp_hom_app, Category.assoc] using h

private theorem presentation_reassociation_naturality (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (d : ℕ)
    {M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))}
    (a : M ⟶ N) :
    (P.compositionTwistShift X d).map a ≫ (P.smoothPurityReassociation X d N).hom =
      (P.smoothPurityReassociation X d M).hom ≫
        ((smoothPurityTensor P.Coefficient X).map a).app (P.diagonalTwist X d) := by
  have he (U) : P.smoothPurityReassociation X d U =
      smoothPurityTensorShiftGeneric
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
        (2 * (d : ℤ)) U (P.diagonalTwist X d) :=
    eq_of_heq (existsUnique_smoothPurityTensorShift
      (ModuleCat.{u + 1} P.Coefficient) X (2 * (d : ℤ)) U
      (P.diagonalTwist X d)).exists.choose_spec
  rw [he, he]
  dsimp only [smoothPurityTensorShiftGeneric, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    compositionTwistShift, Functor.comp_map]
  let T := curriedTensor (_root_.DerivedCategory
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
  have h := NatTrans.shift_app_comm (T.map a) (2 * (d : ℤ))
    ((P.diagonalTwist X d)⟦-(2 * (d : ℤ))⟧)
  apply (cancel_epi (((T.obj M).commShiftIso (2 * (d : ℤ))).hom.app
    ((P.diagonalTwist X d)⟦-(2 * (d : ℤ))⟧))).1
  simp only [← Category.assoc]
  erw [h]
  simp only [Category.assoc]
  change (T.map a).app _ ≫
      ((T.obj N).commShiftIso (2 * (d : ℤ))).hom.app _ ≫
      ((T.obj N).commShiftIso (2 * (d : ℤ))).inv.app _ ≫ _ =
    ((T.obj M).commShiftIso (2 * (d : ℤ))).hom.app _ ≫
      ((T.obj M).commShiftIso (2 * (d : ℤ))).inv.app _ ≫ _
  simp only [Iso.hom_inv_id_app_assoc]
  exact ((T.map a).naturality
    ((shiftFunctorCompIsoId _ (-(2 * (d : ℤ))) (2 * (d : ℤ))
      (neg_add_cancel _)).hom.app (P.diagonalTwist X d))).symm

private theorem presentation_tensorUnitGeneric_naturality
    (C : Type v) [Category.{w} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    {M N : _root_.DerivedCategory C} (a : M ⟶ N) (r : ℤ) :
    ((curriedTensor (_root_.DerivedCategory C)).map a).app
        ((𝟙_ (_root_.DerivedCategory C))⟦r⟧) ≫
      (finiteReductionTensorUnitGeneric C N r).hom =
    (finiteReductionTensorUnitGeneric C M r).hom ≫ a⟦r⟧' := by
  let F := curriedTensor (_root_.DerivedCategory C)
  let := _root_.DerivedCategory.commShiftTensorLeft C M
  let := _root_.DerivedCategory.commShiftTensorLeft C N
  have hs := NatTrans.shift_app_comm (F.map a) r (𝟙_ (_root_.DerivedCategory C))
  dsimp only [finiteReductionTensorUnitGeneric, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom]
  rw [← Category.assoc, ← hs, Category.assoc, ← (shiftFunctor _ r).map_comp]
  have hn : (F.map a).app (𝟙_ (_root_.DerivedCategory C)) ≫ (ρ_ N).hom =
      (ρ_ M).hom ≫ a := MonoidalCategory.rightUnitor_naturality a
  rw [hn, Functor.map_comp, Category.assoc]

private theorem presentation_tensorUnit_naturality
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (a : M ⟶ N) (r : ℤ) :
    ((smoothPurityTensor A X).map a).app
        ((𝟙_ (_root_.DerivedCategory
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))))⟦r⟧) ≫
      (finiteReductionTensorUnit (ModuleCat.{u + 1} A) X N r).hom =
    (finiteReductionTensorUnit (ModuleCat.{u + 1} A) X M r).hom ≫ a⟦r⟧' := by
  have hM := (existsUnique_finiteReductionTensorUnit
    (ModuleCat.{u + 1} A) X M r).choose_spec.1
  have hN := (existsUnique_finiteReductionTensorUnit
    (ModuleCat.{u + 1} A) X N r).choose_spec.1
  have eM := eq_of_heq hM
  have eN := eq_of_heq hN
  unfold finiteReductionTensorUnit
  rw [eM, eN]
  exact presentation_tensorUnitGeneric_naturality _ a r

set_option allowUnsafeReducibility true in
attribute [local reducible] compositionTwistShift

private theorem presentation_fixedChart_naturality (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))] (d : ℕ)
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    {M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))}
    (a : M ⟶ N) :
    (P.compositionTwistShift X d).map a ≫ (P.finiteReductionFixedChart X d ζ hζ N).hom =
      (P.finiteReductionFixedChart X d ζ hζ M).hom ≫ a⟦2 * (d : ℤ)⟧' := by
  have he (U) := eq_of_heq
    (P.existsUnique_finiteReductionFixedChart X d ζ hζ U).choose_spec.1
  change ∀ U, P.finiteReductionFixedChart X d ζ hζ U = _ at he
  rw [he M, he N]
  dsimp only [finiteReductionChartComposite, Iso.trans_hom, Functor.mapIso_hom]
  change (P.compositionTwistShift X d).map a ≫
      (P.smoothPurityReassociation X d N).hom ≫ _ = _
  rw [← Category.assoc, presentation_reassociation_naturality]
  rw [Category.assoc, ← Category.assoc
    (((smoothPurityTensor P.Coefficient X).map a).app (P.diagonalTwist X d)),
    ← NatTrans.naturality]
  rw [Category.assoc, presentation_tensorUnit_naturality]
  simp only [Category.assoc, smoothPurityReassociation]

private def presentation_fixedChartNatIso (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))] (d : ℕ)
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    P.compositionTwistShift X d ≅ shiftFunctor _ (2 * (d : ℤ)) :=
  NatIso.ofComponents (P.finiteReductionFixedChart X d ζ hζ)
    (fun a ↦ presentation_fixedChart_naturality P X d ζ hζ a)

-- Keep the elaborator from unfolding the derived functors while matching the presentations.
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.Scheme.reductionDerivedChange
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtension in
/-- The canonical fixed-coordinate source comparison has its prescribed root normalization.
Source: finite reduction of purity, proof Steps 1–2; the intrinsic source comparison
and its specified realization in `finiteTensorPuritySourceComparison`.
(blueprint: lem-pur-finite-tensor-fixed-source-chart).
Proof: derived realization and its inverse inherit the shifts of their exact
ordinary functors. The derived composition and identity comparisons commute with
shifts, so the realization equivalence, its unit and its counit do too. The
restriction presentation is an exact-derived square. It therefore commutes with
shifts. Transporting the scalar adjunction along this right comparison, and then
using the unit/counit formula for uniqueness of left adjoints, proves compatibility
of scalarPresentation with the specified scalar shifts. The native tensor-shift
cancellation and shifted right unitor are natural in the untwisted input, so the
fixed root charts form a natural isomorphism to the even shift. Apply the faithful
realization functor to the desired equality. The defining preimage composites of
the fixed source and pullback comparisons cancel their leading scalarPresentation
maps and give the intrinsic comparisons, with the two input realization units.
Use naturality of the fixed charts and the scalar shift to move these units across.
The defining root-normalization equation for the intrinsic source comparison now
supplies the middle square; shift compatibility of scalarPresentation supplies the
remaining square. Cancel the scalarPresentation and the realization shift, then
use faithfulness to descend the equality. No Tor, finite-type or smoothness
assumption is needed for this categorical transport. -/
theorem finiteTensorFixedSourceChart (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] (f : X ⟶ Y) (d : ℕ)
    (K : _root_.DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (ζ η : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent)
    (hroot : η = ζ ^ (P.coefficients.l ^ (P.level - m))) :
    let F := P.finiteTensorReduction m hm hmn X
    let M := (P.smoothPurityPullback f).obj K
    let M' := ((P.finiteReductionSetting m hm).smoothPurityPullback f).obj
      ((P.finiteTensorReduction m hm hmn Y).obj K)
    (P.finiteTensorPuritySourceComparison m hm hmn f d K).hom ≫
        ((P.finiteReductionSetting m hm).finiteReductionFixedChart X d η hη M').hom =
      F.map (P.finiteReductionFixedChart X d ζ hζ M).hom ≫
        (P.finiteTensorScalarShift m hm hmn X (2 * (d : ℤ))).hom.app M ≫
        (P.finiteTensorPullbackComparison m hm hmn f K).hom⟦2 * (d : ℤ)⟧' := by
  let Q := P.finiteReductionSetting m hm
  let EA := sfIntrinsicDerivedEquivalence X P.Ring
  let EB := sfIntrinsicDerivedEquivalence X Q.Ring
  let EY := sfIntrinsicDerivedEquivalence Y P.Ring
  let EY' := sfIntrinsicDerivedEquivalence Y Q.Ring
  let RX := P.finiteReduction m hm hmn X
  let FY := P.finiteTensorReduction m hm hmn Y
  let F := P.finiteTensorReduction m hm hmn X
  let α := ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
    (P.finiteReductionRingHom m hm hmn) X
  let β := ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
    (P.finiteReductionRingHom m hm hmn) Y
  let M := (P.smoothPurityPullback f).obj K
  let M' := (Q.smoothPurityPullback f).obj (FY.obj K)
  let u := (P.smoothPurityPullback f).mapIso (EY.unitIso.symm.app K)
  let v := (EY'.inverse ⋙ Q.smoothPurityPullback f).mapIso (β.app K) ≪≫
    (Q.smoothPurityPullback f).mapIso (EY'.unitIso.symm.app (FY.obj K))
  let a := P.finiteReductionSourceComparison m hm hmn f d (EY.functor.obj K)
  let b := P.finiteReductionPullbackComparison m hm hmn f (EY.functor.obj K)
  let shiftEA : EA.functor.CommShift ℤ := presentation_realization_shift _ X
  let shiftEB : EB.functor.CommShift ℤ := presentation_realization_shift _ X
  let : EB.functor.Faithful := EB.faithful_functor
  let shiftRX : RX.CommShift ℤ := P.finiteReductionCommShift m hm hmn X
  let shiftF : F.CommShift ℤ := P.finiteTensorReductionCommShift m hm hmn X
  let : (ProEtale.scalarExtensionFunctor (P.finiteReductionRingHom m hm hmn) X).CommShift ℤ :=
    P.finiteReductionCommShift m hm hmn X
  let : (ProEtale.SupportedEtaleTensorOrigin.fixedScalar
      (P.finiteReductionRingHom m hm hmn) X).CommShift ℤ :=
    P.finiteTensorReductionCommShift m hm hmn X
  have shiftα : NatTrans.CommShift α.hom ℤ := scalar_presentation_shift P m hm hmn X
  let v₀ := (EY'.inverse ⋙ Q.smoothPurityPullback f).mapIso (β.app K)
  let v₁ := (Q.smoothPurityPullback f).mapIso (EY'.unitIso.symm.app (FY.obj K))
  have hS : α.hom.app ((P.compositionTwistShift X d).obj M) ≫
      EB.functor.map (P.finiteTensorPuritySourceComparison m hm hmn f d K).hom =
      (EA.functor ⋙ RX).map ((P.compositionTwistShift X d).map u.inv) ≫ a.hom ≫
        EB.functor.map ((Q.compositionTwistShift X d).map v.hom) := by
    exact (presentation_realize_twist EB.functor F (EA.functor ⋙ RX) α
      (P.compositionTwistShift X d) (Q.compositionTwistShift X d) u v₀ v₁ a
      (hfull := EB.full_functor) (hfaithful := EB.faithful_functor))
  have hP : α.hom.app M ≫ EB.functor.map
      (P.finiteTensorPullbackComparison m hm hmn f K).hom =
      (EA.functor ⋙ RX).map u.inv ≫ b.hom ≫ EB.functor.map v.hom := by
    exact (presentation_realize_twist EB.functor F (EA.functor ⋙ RX) α
      (𝟭 _) (𝟭 _) u v₀ v₁ b
      (hfull := EB.full_functor) (hfaithful := EB.faithful_functor))
  have hN := (P.existsUnique_finiteReductionSourceComparison m hm hmn f d
    (EY.functor.obj K)).choose_spec.1 ζ η hζ hη hroot
  let M₀ := (P.smoothPurityPullback f).obj (EY.inverse.obj (EY.functor.obj K))
  let N₀ := (Q.smoothPurityPullback f).obj
    (EY'.inverse.obj ((P.finiteReduction m hm hmn Y).obj (EY.functor.obj K)))
  exact (transport_chart (EA.functor ⋙ RX) F EB.functor α
    (P.compositionTwistShift X d) (Q.compositionTwistShift X d) (2 * (d : ℤ))
    (presentation_fixedChartNatIso P X d ζ hζ)
    (presentation_fixedChartNatIso Q X d η hη)
    u v (P.finiteTensorPuritySourceComparison m hm hmn f d K).hom
    (P.finiteTensorPullbackComparison m hm hmn f K).hom a.hom b.hom hS hP
    (presentation_composite_normalization EA.functor RX EB.functor (2 * (d : ℤ))
      (P.finiteReductionFixedChart X d ζ hζ M₀).hom
      (Q.finiteReductionFixedChart X d η hη N₀).hom a.hom b.hom (by exact hN)
      (hG := shiftEA) (hR := shiftRX) (hShiftE := shiftEB))
    (hE := EB.faithful_functor)
    (hG := presentation_compShift EA.functor RX shiftEA shiftRX)
    (hF := shiftF) (hShiftE := shiftEB) (hα := shiftα))

end WeilConjectures.PurityFiniteSetting
