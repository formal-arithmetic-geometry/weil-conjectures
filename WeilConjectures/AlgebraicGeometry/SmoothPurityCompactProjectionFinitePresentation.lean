/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityCompactProjectionData
import all WeilConjectures.AlgebraicGeometry.RingedProjectionGlobalModel
import all WeilConjectures.AlgebraicGeometry.RingedProjectionTensorComparison
import all WeilConjectures.SixFunctors.OpenOperationModels
import all WeilConjectures.SixFunctors.OpenTensorSupportAux

/-! # Normalized compact-projection presentations

Source: Stacks 03D7, 07A4, 03DI, 0GL1 and the finite/tower construction in
blueprint `lem-sp-compact-projection-base-change`, proof step 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization
open AlgebraicGeometry.Scheme.ProjectionRestriction
open CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.CompactProjectionBaseChange

attribute [local implicit_reducible] Site topology baseChange openInclusion
attribute [local implicit_reducible] finiteCoefficients constantSheaf
set_option synthInstance.maxSize 4096


private theorem finiteSiteSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local instance] finiteSiteSmall

private abbrev finiteRing (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A)

private abbrev finiteModuleRing (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (finiteRing A X)

private abbrev finiteMap (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finiteRing A Y ⟶ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (finiteRing A X) :=
  proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A)

private abbrev finiteModuleMap (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (finiteRing A Y) ⟶
    ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology Y) (ProEt.topology X)).obj
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (finiteRing A X)) :=
  ⟨Functor.whiskerRight (finiteMap A f).hom (forget₂ CommRingCat RingCat)⟩

private theorem finiteOpenContinuous {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (proEtaleOpenComposition j).IsContinuous (ProEt.topology U) (ProEt.topology X) :=
  ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)

attribute [local instance] finiteOpenContinuous

private abbrev finiteRestrictedRing (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Sheaf (ProEt.topology U) CommRingCat.{u + 1} :=
  ((proEtaleOpenComposition j).sheafPushforwardContinuous CommRingCat.{u + 1}
    (ProEt.topology U) (ProEt.topology X)).obj (finiteRing A X)

private abbrev finiteRestriction (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Mod.{u} (finiteRing A X) ⥤ Mod.{u} (finiteRestrictedRing A j) :=
  SheafOfModules.pushforward (F := proEtaleOpenComposition j) (𝟙 _)

private theorem constantInverse_isIso (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of A)) := by
  let D := CommRingCat.{u + 1}
  let T : Y.ProEt := ProEt.mk (𝟙 Y)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Y
  let hGT : IsTerminal ((proEtaleBaseChange f).obj T) :=
    hT.isTerminalObj (proEtaleBaseChange f)
  let eR : proEtaleSheafDirectImage f D ⋙
      (sheafSections (ProEt.topology Y) D).obj (op T) ≅
        (sheafSections (ProEt.topology X) D).obj (op ((proEtaleBaseChange f).obj T)) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  let adj₁ := ((constantSheafAdj (ProEt.topology Y) D hT).comp
    (proEtaleSheafAdjunction f D)).ofNatIsoRight eR
  let adj₂ := constantSheafAdj (ProEt.topology X) D hGT
  let e := adj₁.leftAdjointUniq adj₂
  have he : proEtaleConstantInverseImageMap f D (CommRingCat.of A) =
      e.hom.app (CommRingCat.of A) := by
    apply (adj₁.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [adj₁, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    unfold proEtaleConstantInverseImageMap
    rw [← Adjunction.homEquiv_symm_apply]
    dsimp only [D, proEtaleSheafDirectImage, ProEtale.lowerStar, Functor.comp_obj] at *
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, eR,
      NatIso.ofComponents_hom_app, Iso.refl_hom]
    change (constantSheafAdj (ProEt.topology Y) D hT).homEquiv _ _
      (proEtaleConstantDirectImageMap f D (CommRingCat.of A)) = adj₂.unit.app _
    unfold proEtaleConstantDirectImageMap
    rw [constantSheafAdj, Adjunction.comp_homEquiv]
    change (constantPresheafAdj D hT).homEquiv _ _
      ((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _
        (((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    simp only [adj₂, constantSheafAdj, Adjunction.comp_unit_app,
      constantPresheafAdj_unit_app, Category.id_comp, sheafificationAdjunction_unit_app]
    rfl
  rw [he]
  infer_instance

private def finiteCoefficientIso (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (finiteRing A Y) ≅
      (finiteRing A X) := by
  have := constantInverse_isIso A f
  exact asIso (proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of A))

private theorem finiteCoefficientIso_direct (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingDirectImageMap f _ _ (finiteCoefficientIso A f) =
      (finiteMap A f) := by
  exact (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
    |>.apply_symm_apply (proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of A))

private def finiteOperation (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Operation.{u} (proEtaleBaseChange f) (finiteRing A Y)
      (finiteRing A X) :=
  globalOperation f _ _ (finiteCoefficientIso A f)

private theorem finiteOperation_coefficient (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (finiteOperation A f).coefficient = (finiteModuleMap A f) := by
  dsimp only [finiteOperation, globalOperation]
  rw [finiteCoefficientIso_direct]

private def finiteTensorModel (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    TensorModel.{u} (finiteRing A X) :=
  (tensorModelWithShifts_nonempty (finiteRing A X)).choose

private def finiteOrdinaryTensor (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (finiteOperation A f).OrdinaryTensor :=
  globalOrdinaryTensor f _ _ (finiteCoefficientIso A f)

private theorem finiteTensorComparison_exists (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Nonempty (TensorComparison (finiteOperation A f).pullback (finiteOperation A f).leftModel
      (finiteTensorModel A Y) (finiteTensorModel A X) (finiteOrdinaryTensor A f).iso) := by
  apply tensor_core
  exact preserves_resolving f _ _ (finiteCoefficientIso A f) (finiteOperation A f) rfl
    (finiteTensorModel A Y) (finiteTensorModel A X)

private abbrev constantSections (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))

private theorem constantMap_sections (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.ProEtᵒᵖ) :
    (constantSections A Y).app W ≫ (finiteMap A f).hom.app W =
      (constantSections A X).app ((proEtaleBaseChange f).op.obj W) := by
  have h := (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1})
    |>.homEquiv ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))
      ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (finiteRing A X))
    |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange f).op
      (constantSections A X))
  exact congrArg (fun t ↦ t.app W) h

set_option maxHeartbeats 800000 in
-- The explicit sheaf and derived-category comparisons need extra reduction budget.
private theorem finiteRightSquare_exists (A : Type (u + 1)) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : CommSq a b f g) :
    ∃ e : (finiteOperation A b).pushforward ⋙ (finiteOperation A g).pushforward ≅
        (finiteOperation A a).pushforward ⋙ (finiteOperation A f).pushforward,
      ∀ (M : Mod.{u} (finiteRing A X')) (W : Y.ProEtᵒᵖ),
        HEq (fun x ↦ (e.hom.app M).val.app W x)
          (fun x ↦ M.val.map ((siteSquare .ordinary s).inv.app W.unop).op x) := by
  let G := proEtaleBaseChange g ⋙ proEtaleBaseChange b
  let F := proEtaleBaseChange f ⋙ proEtaleBaseChange a
  have : G.IsContinuous (ProEt.topology Y) (ProEt.topology X') :=
    Functor.isContinuous_comp _ _ _ (ProEt.topology Y') _
  have : F.IsContinuous (ProEt.topology Y) (ProEt.topology X') :=
    Functor.isContinuous_comp _ _ _ (ProEt.topology X) _
  let cg := (finiteMap A g) ≫ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map (finiteMap A b)
  let cf := (finiteMap A f) ≫ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map (finiteMap A a)
  let e : G ≅ F := siteSquare .ordinary s
  have hc : cg ≫ (Functor.sheafPushforwardContinuousNatTrans e.inv CommRingCat.{u + 1}
      (ProEt.topology Y) (ProEt.topology X')).app (finiteRing A X') = cf := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (ProEt.topology Y) _ _
      ((F.sheafPushforwardContinuous CommRingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X')).obj (finiteRing A X')).property
    apply NatTrans.ext
    funext W
    change (constantSections A Y).app W ≫
      (((finiteMap A g).hom.app W ≫ (finiteMap A b).hom.app ((proEtaleBaseChange g).op.obj W)) ≫
        (finiteRing A X').obj.map (e.inv.app W.unop).op) =
      (constantSections A Y).app W ≫
        ((finiteMap A f).hom.app W ≫ (finiteMap A a).hom.app ((proEtaleBaseChange f).op.obj W))
    simp only [← Category.assoc]
    rw [constantMap_sections, constantMap_sections, constantMap_sections,
      constantMap_sections]
    have hn := (constantSections A X').naturality (e.inv.app W.unop).op
    exact hn.symm.trans (Category.id_comp _)
  let cmg := (finiteModuleMap A g) ≫
    ((proEtaleBaseChange g).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology Y) (ProEt.topology Y')).map (finiteModuleMap A b)
  let cmf := (finiteModuleMap A f) ≫
    ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology Y) (ProEt.topology X)).map (finiteModuleMap A a)
  have hcm : cmg ≫ (Functor.sheafPushforwardContinuousNatTrans e.inv RingCat.{u + 1}
      (ProEt.topology Y) (ProEt.topology X')).app
        ((sheafCompose (ProEt.topology X')
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (finiteRing A X')) = cmf := by
    apply Sheaf.hom_ext
    exact congrArg (fun t ↦ Functor.whiskerRight t.hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) hc
  let egc := SheafOfModules.pushforwardComp
    (F := proEtaleBaseChange g) (G := proEtaleBaseChange b)
    (J := ProEt.topology Y) (K := ProEt.topology Y') (K' := ProEt.topology X')
    (S := finiteModuleRing A Y) (R := finiteModuleRing A Y') (R' := finiteModuleRing A X')
    (finiteModuleMap A g) (finiteModuleMap A b)
  let efc := SheafOfModules.pushforwardComp
    (F := proEtaleBaseChange f) (G := proEtaleBaseChange a)
    (J := ProEt.topology Y) (K := ProEt.topology X) (K' := ProEt.topology X')
    (S := finiteModuleRing A Y) (R := finiteModuleRing A X) (R' := finiteModuleRing A X')
    (finiteModuleMap A f) (finiteModuleMap A a)
  let en := SheafOfModules.pushforwardNatIso (F := F) (G := G)
    (J := ProEt.topology Y) (K := ProEt.topology X')
    (T := finiteModuleRing A Y) (S := finiteModuleRing A X') cmg e.symm
  let ec := SheafOfModules.pushforwardCongr (F := F)
    (J := ProEt.topology Y) (K := ProEt.topology X')
    (S := finiteModuleRing A Y) (R := finiteModuleRing A X') hcm
  let e₀ : SheafOfModules.pushforward (finiteModuleMap A b) ⋙
      SheafOfModules.pushforward (finiteModuleMap A g) ≅
        SheafOfModules.pushforward (finiteModuleMap A a) ⋙
          SheafOfModules.pushforward (finiteModuleMap A f) := egc ≪≫ en ≪≫ ec ≪≫ efc.symm
  let eb (j : X' ⟶ Y') : (finiteOperation A j).pushforward ≅
      SheafOfModules.pushforward (finiteModuleMap A j) :=
    SheafOfModules.pushforwardCongr (finiteOperation_coefficient A j)
  let eg : (finiteOperation A g).pushforward ≅
      SheafOfModules.pushforward (finiteModuleMap A g) :=
    SheafOfModules.pushforwardCongr (finiteOperation_coefficient A g)
  let ea : (finiteOperation A a).pushforward ≅
      SheafOfModules.pushforward (finiteModuleMap A a) :=
    SheafOfModules.pushforwardCongr (finiteOperation_coefficient A a)
  let ef : (finiteOperation A f).pushforward ≅
      SheafOfModules.pushforward (finiteModuleMap A f) :=
    SheafOfModules.pushforwardCongr (finiteOperation_coefficient A f)
  refine ⟨Functor.isoWhiskerRight (eb b) _ ≪≫ Functor.isoWhiskerLeft _ eg ≪≫ e₀ ≪≫
    Functor.isoWhiskerLeft _ ef.symm ≪≫ Functor.isoWhiskerRight ea.symm _, ?_⟩
  intro M W
  exact HEq.rfl

private def finiteOpenRingIso (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (finiteRing A U) ≅ finiteRestrictedRing A j := by
  let F := proEtaleOpenComposition j
  have : F.IsContinuous (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)
  have : F.IsCocontinuous (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  exact (F.pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
    (ProEt.topology U) (ProEt.topology X)).app
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))

private theorem finiteOpenRingIso_sections (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (W : U.ProEtᵒᵖ) :
    (constantSections A U).app W ≫ (finiteOpenRingIso A j).hom.hom.app W =
      (constantSections A X).app ((proEtaleOpenComposition j).op.obj W) := by
  let F := proEtaleOpenComposition j
  have : F.IsContinuous (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)
  have : F.IsCocontinuous (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  exact congrArg (fun t ↦ t.app W)
    (F.toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
      (ProEt.topology U) (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)))

private def finiteOpenEquivalence (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Mod.{u} (finiteRestrictedRing A j) ≌
      Mod.{u} (finiteRing A U) := by
  let c := (sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (finiteOpenRingIso A j)
  have : (CategoryTheory.Equivalence.refl : U.ProEt ≌ U.ProEt).functor.IsContinuous
      (ProEt.topology U) (ProEt.topology U) := by
    change (𝟭 U.ProEt).IsContinuous (ProEt.topology U) (ProEt.topology U)
    infer_instance
  have : (CategoryTheory.Equivalence.refl : U.ProEt ≌ U.ProEt).inverse.IsContinuous
      (ProEt.topology U) (ProEt.topology U) := by
    change (𝟭 U.ProEt).IsContinuous (ProEt.topology U) (ProEt.topology U)
    infer_instance
  refine SheafOfModules.pushforwardPushforwardEquivalence
    (CategoryTheory.Equivalence.refl : U.ProEt ≌ U.ProEt) c.hom c.inv ?_ ?_
  · ext W : 2
    change ((sheafCompose (ProEt.topology U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (finiteRestrictedRing A j)).obj.map (𝟙 W.unop).op =
          c.inv.hom.app W ≫ c.hom.hom.app W
    rw [op_id, CategoryTheory.Functor.map_id]
    exact congrArg (fun t ↦ t.hom.app W) c.inv_hom_id.symm
  · ext W : 2
    change (c.hom.hom.app W ≫ c.inv.hom.app W) ≫
      ((sheafCompose (ProEt.topology U)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (finiteRing A U)).obj.map (𝟙 W.unop).op = 𝟙 _
    rw [op_id, CategoryTheory.Functor.map_id, Category.comp_id]
    exact congrArg (fun t ↦ t.hom.app W) c.hom_inv_id

set_option maxHeartbeats 800000 in
-- The explicit sheaf and derived-category comparisons need extra reduction budget.
private theorem finiteOpenPullbackIso_exists (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty ((finiteOperation A j).pullback ≅
      finiteRestriction A j ⋙
        (finiteOpenEquivalence A j).functor) := by
  let R := (finiteRing A X)
  let S := (finiteRing A U)
  let F := proEtaleOpenComposition j
  have : F.IsContinuous (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)
  let G := proEtaleBaseChange j
  let a : F ⊣ G := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  let c := (finiteOpenRingIso A j).hom
  let φ : (sheafCompose (ProEt.topology U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S ⟶
      (F.sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology U) (ProEt.topology X)).obj
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) :=
    (sheafCompose (ProEt.topology U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c
  let ψ := (finiteModuleMap A j)
  have H₁c : Functor.whiskerRight (NatTrans.op a.counit) R.obj =
      (finiteMap A j).hom ≫ G.op.whiskerLeft c.hom := by
    apply sheafify_hom_ext (ProEt.topology X) _ _
      ((G.sheafPushforwardContinuous CommRingCat.{u + 1}
        (ProEt.topology X) (ProEt.topology U)).obj
          ((F.sheafPushforwardContinuous CommRingCat.{u + 1}
            (ProEt.topology U) (ProEt.topology X)).obj R)).property
    apply NatTrans.ext
    funext V
    change (constantSections A X).app V ≫ R.obj.map (a.counit.app V.unop).op =
      (constantSections A X).app V ≫ ((finiteMap A j).hom.app V ≫
        c.hom.app (G.op.obj V))
    rw [← Category.assoc, constantMap_sections, finiteOpenRingIso_sections]
    exact (constantSections A X).naturality (a.counit.app V.unop).op
      |>.symm.trans (Category.id_comp _)
  have H₂c : c.hom ≫ F.op.whiskerLeft (finiteMap A j).hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) S.obj = 𝟙 S.obj := by
    apply sheafify_hom_ext (ProEt.topology U) _ _ S.property
    apply NatTrans.ext
    funext W
    change (constantSections A U).app W ≫
      ((c.hom.app W ≫ (finiteMap A j).hom.app (F.op.obj W)) ≫
        S.obj.map (a.unit.app W.unop).op) = (constantSections A U).app W ≫ 𝟙 _
    simp only [← Category.assoc, Category.comp_id]
    rw [finiteOpenRingIso_sections, constantMap_sections]
    have hn := (constantSections A U).naturality (a.unit.app W.unop).op
    exact hn.symm.trans (Category.id_comp _)
  have H₁ : Functor.whiskerRight (NatTrans.op a.counit)
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom :=
    congrArg (fun t ↦ Functor.whiskerRight t
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) H₁c
  have H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit)
        ((sheafCompose (ProEt.topology U)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj = 𝟙 _ :=
    congrArg (fun t ↦ Functor.whiskerRight t
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) H₂c
  let radj := SheafOfModules.pushforwardPushforwardAdj
    (J := ProEt.topology U) (K := ProEt.topology X) (F := F) (G := G) a φ ψ H₁ H₂
  let o := finiteOperation A j
  let adj := o.moduleAdjunction.ofNatIsoRight
    (SheafOfModules.pushforwardCongr (finiteOperation_coefficient A j))
  let q := finiteOpenEquivalence A j
  let e := (SheafOfModules.pushforwardComp
    (F := 𝟭 U.ProEt) (G := proEtaleOpenComposition j)
    (J := ProEt.topology U) (K := ProEt.topology U) (K' := ProEt.topology X)
    (S := finiteModuleRing A U)
    (R := (sheafCompose (ProEt.topology U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (finiteRestrictedRing A j))
    (R' := finiteModuleRing A X)
    ((sheafCompose (ProEt.topology U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c) (𝟙 _)).symm
  exact ⟨adj.leftAdjointUniq radj ≪≫ e⟩

private def finiteOpenPullbackIso (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (finiteOpenPullbackIso_exists A j).some

private def finiteOpenExtension (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (ordinaryOpenExtension_exists j (finiteRing A X)).some

private def finiteOpenModel (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    OpenModel.{u} (m := .ordinary) (c := finiteCoefficients A) j (finiteOperation A j) := by
  let q := finiteOpenEquivalence A j
  let z := finiteOpenExtension A j
  have : z.ordinary.Additive := z.additive
  have : PreservesFiniteLimits z.ordinary := z.limits
  have : PreservesFiniteColimits z.ordinary := z.colimits
  have : q.inverse.Additive := Functor.additive_of_preserves_binary_products q.inverse
  let L := q.inverse ⋙ z.ordinary
  let a := (q.symm.toAdjunction.comp z.adjunction).ofNatIsoRight
    (finiteOpenPullbackIso A j).symm
  have hunit (M : Mod.{u} (finiteRestrictedRing A j)) :
      IsIso (z.adjunction.unit.app M) :=
    SheafOfModules.OpenTensorNormalization.ordinaryUnit_isIso z M
  have : IsIso z.adjunction.unit := NatIso.isIso_of_isIso_app _
  have : z.ordinary.Full := z.adjunction.fullyFaithfulLOfIsIsoUnit.full
  have : z.ordinary.Faithful := z.adjunction.fullyFaithfulLOfIsIsoUnit.faithful
  have : L.Full := by dsimp only [L]; infer_instance
  have : L.Faithful := by dsimp only [L]; infer_instance
  have : IsIso a.unit := a.unit_isIso_of_L_fully_faithful
  exact {
    functor := L
    adjunction := a
    additive := inferInstance
    limits := inferInstance
    colimits := inferInstance
    unit := fun _ ↦ inferInstance }


private def finitePresentation (A : Type (u + 1)) [CommRing A] :
    Presentation (finiteCoefficients A) where
  operation := finiteOperation A
  coefficient := finiteOperation_coefficient A
  tensor := finiteTensorModel A
  ordinaryTensor := finiteOrdinaryTensor A
  tensorComparison f := (finiteTensorComparison_exists A f).some
  openModel := finiteOpenModel A
  rightSquare s := (finiteRightSquare_exists A s).choose
  rightSections s := (finiteRightSquare_exists A s).choose_spec

set_option maxHeartbeats 800000 in
-- The explicit sheaf and derived-category comparisons need extra reduction budget.
private theorem finiteTensor_supported (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : Der.{u} (finiteRing A U)) (N : Der.{u} (finiteRing A X)) :
    ((finitePresentation A).shriek j).essImage
      ((finiteTensorModel A X).functor.obj (((finitePresentation A).shriek j).obj M, N)) := by
  let q := finiteOpenEquivalence A j
  let z := finiteOpenExtension A j
  have : z.ordinary.Additive := z.additive
  have : PreservesFiniteLimits z.ordinary := z.limits
  have : PreservesFiniteColimits z.ordinary := z.colimits
  have : q.functor.Additive := Functor.additive_of_preserves_binary_products q.functor
  have : q.inverse.Additive := Functor.additive_of_preserves_binary_products q.inverse
  let e := Functor.mapDerivedCategoryCompIso q.inverse z.ordinary
  let eM := e.app M
  have hs := derivedTensor_supported_of_underived z (finiteTensorModel A X)
    (ordinaryTensor_supported z) (q.inverse.mapDerivedCategory.obj M) N
  obtain ⟨P, ⟨i⟩⟩ := hs
  refine ⟨q.functor.mapDerivedCategory.obj P, ⟨?_⟩⟩
  exact e.app _ ≪≫ z.ordinary.mapDerivedCategory.mapIso
    ((q.mapDerivedCategory).unitIso.app P).symm ≪≫ i ≪≫
      ((finiteTensorModel A X).functor.mapIso (eM.prod (Iso.refl N))).symm

set_option maxHeartbeats 800000 in
-- The explicit sheaf and derived-category comparisons need extra reduction budget.
private theorem finiteOpenDerivedUnit_isIso (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : Der.{u} (finiteRing A U)) :
    IsIso (((finitePresentation A).openAdjunction j).unit.app M) := by
  let o := (finitePresentation A).openModel j
  let a := (finitePresentation A).openAdjunction j
  have hQ (P : CochainComplex (Mod.{u} (finiteRing A U)) ℤ) :
      IsIso (a.unit.app (DerivedCategory.Q.obj P)) := by
    have hn (n : ℤ) :
        IsIso (((o.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P).f n) :=
      o.unit (P.X n)
    have hP : IsIso ((o.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P) :=
      HomologicalComplex.Hom.isIso_of_components _
    have hu : a.unit.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((o.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
          (finiteOperation A j).pullback.mapDerivedCategoryFactors.inv.app _ ≫
            (finiteOperation A j).left.map (o.functor.mapDerivedCategoryFactors.inv.app P) := by
      simp only [a, Presentation.openAdjunction, exactDerivedAdjunction,
        Adjunction.localization_unit_app]
      rfl
    rw [hu]
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso a.unit (DerivedCategory.Q.objObjPreimageIso M)).mp
    (hQ (DerivedCategory.Q.objPreimage M))

private theorem finiteMixedSquare_exists (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j g) :
    Nonempty ((finiteOperation A g).pushforward ⋙ (finiteOperation A j).pullback ≅
      (finiteOperation A j').pullback ⋙ (finiteOperation A a).pushforward) := by
  let cp := MorphismProperty.Over.pullbackMapComparison
    (inferInstance : WeaklyEtale j) (inferInstance : WeaklyEtale j') s.toCommSq
  have : IsIso cp := MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
    (inferInstance : WeaklyEtale j) (inferInstance : WeaklyEtale j') s
  let F := proEtaleOpenComposition j ⋙ proEtaleBaseChange g
  let G := proEtaleBaseChange a ⋙ proEtaleOpenComposition j'
  let e : F ≅ G := (asIso cp).symm
  have : F.IsContinuous (ProEt.topology U) (ProEt.topology X') :=
    Functor.isContinuous_comp _ _ _ (ProEt.topology X) _
  have : G.IsContinuous (ProEt.topology U) (ProEt.topology X') :=
    Functor.isContinuous_comp _ _ _ (ProEt.topology U') _
  let cj := (finiteOpenRingIso A j).hom
  let cj' := (finiteOpenRingIso A j').hom
  let cf := cj ≫ ((proEtaleOpenComposition j).sheafPushforwardContinuous
    CommRingCat.{u + 1} (ProEt.topology U) (ProEt.topology X)).map (finiteMap A g)
  let cg := (finiteMap A a) ≫ ((proEtaleBaseChange a).sheafPushforwardContinuous
    CommRingCat.{u + 1} (ProEt.topology U) (ProEt.topology U')).map cj'
  have hc : cf ≫ (Functor.sheafPushforwardContinuousNatTrans e.inv CommRingCat.{u + 1}
      (ProEt.topology U) (ProEt.topology X')).app (finiteRing A X') = cg := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (ProEt.topology U) _ _
      ((G.sheafPushforwardContinuous CommRingCat.{u + 1}
        (ProEt.topology U) (ProEt.topology X')).obj (finiteRing A X')).property
    apply NatTrans.ext
    funext W
    change (constantSections A U).app W ≫
      ((cj.hom.app W ≫ (finiteMap A g).hom.app ((proEtaleOpenComposition j).op.obj W)) ≫
        (finiteRing A X').obj.map (e.inv.app W.unop).op) =
      (constantSections A U).app W ≫
        ((finiteMap A a).hom.app W ≫ cj'.hom.app ((proEtaleBaseChange a).op.obj W))
    simp only [← Category.assoc]
    rw [finiteOpenRingIso_sections, constantMap_sections, constantMap_sections,
      finiteOpenRingIso_sections]
    have hn := (constantSections A X').naturality (e.inv.app W.unop).op
    exact hn.symm.trans (Category.id_comp _)
  let φ : finiteModuleRing A U ⟶
      ((proEtaleOpenComposition j).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology U) (ProEt.topology X)).obj (finiteModuleRing A X) :=
    (sheafCompose (ProEt.topology U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map cj
  let φ' : finiteModuleRing A U' ⟶
      ((proEtaleOpenComposition j').sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology U') (ProEt.topology X')).obj (finiteModuleRing A X') :=
    (sheafCompose (ProEt.topology U')
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map cj'
  let cmf := φ ≫ ((proEtaleOpenComposition j).sheafPushforwardContinuous RingCat.{u + 1}
    (ProEt.topology U) (ProEt.topology X)).map (finiteModuleMap A g)
  let cmg := (finiteModuleMap A a) ≫ ((proEtaleBaseChange a).sheafPushforwardContinuous
    RingCat.{u + 1} (ProEt.topology U) (ProEt.topology U')).map φ'
  have hcm : cmf ≫ (Functor.sheafPushforwardContinuousNatTrans e.inv RingCat.{u + 1}
      (ProEt.topology U) (ProEt.topology X')).app
        ((sheafCompose (ProEt.topology X')
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (finiteRing A X')) = cmg := by
    apply Sheaf.hom_ext
    exact congrArg (fun t ↦ Functor.whiskerRight t.hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) hc
  let ejc := SheafOfModules.pushforwardComp
    (F := 𝟭 U.ProEt) (G := proEtaleOpenComposition j)
    (J := ProEt.topology U) (K := ProEt.topology U) (K' := ProEt.topology X)
    (S := finiteModuleRing A U)
    (R := (sheafCompose (ProEt.topology U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (finiteRestrictedRing A j))
    (R' := finiteModuleRing A X) φ (𝟙 _)
  let ejc' := SheafOfModules.pushforwardComp
    (F := 𝟭 U'.ProEt) (G := proEtaleOpenComposition j')
    (J := ProEt.topology U') (K := ProEt.topology U') (K' := ProEt.topology X')
    (S := finiteModuleRing A U')
    (R := (sheafCompose (ProEt.topology U')
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (finiteRestrictedRing A j'))
    (R' := finiteModuleRing A X') φ' (𝟙 _)
  let ej : (finiteOperation A j).pullback ≅
      SheafOfModules.pushforward (F := proEtaleOpenComposition j) φ :=
    finiteOpenPullbackIso A j ≪≫ ejc
  let ej' : (finiteOperation A j').pullback ≅
      SheafOfModules.pushforward (F := proEtaleOpenComposition j') φ' :=
    finiteOpenPullbackIso A j' ≪≫ ejc'
  let eg : (finiteOperation A g).pushforward ≅
      SheafOfModules.pushforward (finiteModuleMap A g) :=
    SheafOfModules.pushforwardCongr (finiteOperation_coefficient A g)
  let ea : (finiteOperation A a).pushforward ≅
      SheafOfModules.pushforward (finiteModuleMap A a) :=
    SheafOfModules.pushforwardCongr (finiteOperation_coefficient A a)
  let c₁ := SheafOfModules.pushforwardComp
    (F := proEtaleOpenComposition j) (G := proEtaleBaseChange g)
    (J := ProEt.topology U) (K := ProEt.topology X) (K' := ProEt.topology X')
    (S := finiteModuleRing A U) (R := finiteModuleRing A X) (R' := finiteModuleRing A X')
    φ (finiteModuleMap A g)
  let c₂ := SheafOfModules.pushforwardComp
    (F := proEtaleBaseChange a) (G := proEtaleOpenComposition j')
    (J := ProEt.topology U) (K := ProEt.topology U') (K' := ProEt.topology X')
    (S := finiteModuleRing A U) (R := finiteModuleRing A U') (R' := finiteModuleRing A X')
    (finiteModuleMap A a) φ'
  let en := SheafOfModules.pushforwardNatIso (F := G) (G := F)
    (J := ProEt.topology U) (K := ProEt.topology X')
    (T := finiteModuleRing A U) (S := finiteModuleRing A X') cmf e.symm
  let ec := SheafOfModules.pushforwardCongr (F := G)
    (J := ProEt.topology U) (K := ProEt.topology X')
    (S := finiteModuleRing A U) (R := finiteModuleRing A X') hcm
  exact ⟨Functor.isoWhiskerRight eg _ ≪≫ Functor.isoWhiskerLeft _ ej ≪≫ c₁ ≪≫ en ≪≫ ec ≪≫ c₂.symm ≪≫
    Functor.isoWhiskerLeft _ ea.symm ≪≫ Functor.isoWhiskerRight ej'.symm _⟩

set_option maxHeartbeats 800000 in
-- The explicit sheaf and derived-category comparisons need extra reduction budget.
private theorem finitePullback_supported (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j g) (M : Der.{u} (finiteRing A U)) :
    ((finitePresentation A).shriek j').essImage
      ((finiteOperation A g).left.obj (((finitePresentation A).shriek j).obj M)) := by
  let o := finitePresentation A
  let L := (finiteOpenModel A j).functor
  let L' := (finiteOpenModel A j').functor
  have : L.Additive := (finiteOpenModel A j).additive
  have : PreservesFiniteLimits L := (finiteOpenModel A j).limits
  have : PreservesFiniteColimits L := (finiteOpenModel A j).colimits
  have : L'.Additive := (finiteOpenModel A j').additive
  have : PreservesFiniteLimits L' := (finiteOpenModel A j').limits
  have : PreservesFiniteColimits L' := (finiteOpenModel A j').colimits
  obtain ⟨h⟩ := finiteMixedSquare_exists A s
  let aa := (finiteOpenModel A j).adjunction.comp (finiteOperation A g).moduleAdjunction
  let bb := (finiteOperation A a).moduleAdjunction.comp (finiteOpenModel A j').adjunction
  let k := (aa.ofNatIsoRight h).leftAdjointUniq bb
  let e : L.mapDerivedCategory ⋙ (finiteOperation A g).left ≅
      (finiteOperation A a).left ⋙ L'.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso L (finiteOperation A g).pullback).symm ≪≫
      Functor.mapDerivedCategoryNatIso k ≪≫
        Functor.mapDerivedCategoryCompIso (finiteOperation A a).pullback L'
  exact ⟨(finiteOperation A a).left.obj M, ⟨(e.app M).symm⟩⟩

private theorem iso_of_supported_adjunct
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) [IsIso a.unit] {X : D} {Y : C} (f : F.obj Y ⟶ X)
    (hf : IsIso (a.homEquiv _ _ f)) (hs : F.essImage X) : IsIso f := by
  have : F.Full := a.fullyFaithfulLOfIsIsoUnit.full
  have : F.Faithful := a.fullyFaithfulLOfIsIsoUnit.faithful
  have : IsIso (a.counit.app X) := a.isIso_counit_app_iff_mem_essImage.mpr hs
  have := hf
  rw [← (a.homEquiv _ _).symm_apply_apply f, Adjunction.homEquiv_counit]
  infer_instance

private theorem finiteOpenComparisons (A : Type (u + 1)) [CommRing A] :
    OpenComparisons (finitePresentation A) := by
  let o := finitePresentation A
  have hunit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
      IsIso (o.openAdjunction j).unit := by
    have (M : Der.{u} (finiteRing A U)) :
        IsIso ((o.openAdjunction j).unit.app M) := finiteOpenDerivedUnit_isIso A j M
    exact NatIso.isIso_of_isIso_app _
  constructor
  · intro U X j _ M N
    have := hunit j
    obtain ⟨Z, ⟨e⟩⟩ := finiteTensor_supported A j M N
    exact (o.openAdjunction j).isIso_projectionMap_app_app_of_iso
      (o.operation j).left (Functor.curry.obj (o.tensor U).functor)
      (Functor.curry.obj (o.tensor X).functor) (o.curriedTensorComparison j).inv
      M N Z e.symm
  · intro U' U X' X a j' j g _ _ s M
    have := hunit j
    have := hunit j'
    apply iso_of_supported_adjunct (o.openAdjunction j') (o.betaInv s M) _
      (finitePullback_supported A s M)
    have he := unit_mateEquiv_symm (o.openAdjunction j) (o.openAdjunction j')
      (TwoSquare.mk _ _ _ _ (o.square s.toCommSq).inv) M
    change (o.operation a).left.map ((o.openAdjunction j).unit.app M) ≫
      (o.square s.toCommSq).inv.app ((o.shriek j).obj M) =
      (o.openAdjunction j').unit.app ((o.operation a).left.obj M) ≫
        (o.operation j').left.map (o.betaInv s M) at he
    rw [Adjunction.homEquiv_unit, ← he]
    infer_instance

/-- Simultaneous canonical module operations and normalized open comparisons for a
constant finite ring. The operations are fixed by their displayed section maps,
module adjunctions, exact localization, and pure-tensor/K-flat normalizations.
Source: Stacks 0H7J, 03D7, 03DI, 07A4 and 0GL1
(blueprint: lem-sp-compact-projection-finite-presentation).

Proof: take the actual constant ring sheaves and constant-section structural maps.
The constant-ring inverse-image identification identifies module pullback with exact
inverse image of A-module sheaves. Its sectionwise right adjoint and K-injective
resolutions give `Operation`. Construct the same derived tensor at every scheme by
localizing signed total tensor on flat-term K-flat complexes. Pure scalar-extension
tensors give `OrdinaryTensor`, and totalization and descent give `TensorComparison`.
Use exact extension by zero as the module left adjoint to open restriction; its unit
is invertible on sections. For every commutative square the fibre-product comparison
induces the direct-image isomorphism on sections, with precisely `rightSections`.
Tensor support and pullback support show that the targets of the open projection
and open-square mates lie in the essential image of open extension. The invertible
unit and the unit-mate identity make their adjuncts invertible; the counit is
invertible on this essential image. Thus the presentation has `OpenComparisons`.
All choices are of adjoints or
localized functors with their stated universal properties and normalizations. -/
theorem finite_presentation_exists (A : Type (u + 1)) [CommRing A] [Finite A] :
    ∃ o : Presentation (finiteCoefficients A), Nonempty (OpenComparisons o) := by
  exact ⟨finitePresentation A, ⟨finiteOpenComparisons A⟩⟩

end AlgebraicGeometry.ProEtale.CompactProjectionBaseChange
