/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.Paper.SmoothPurityTowerInjectiveComponents
import Sheaf.CategoryTheory.ModuleInverseImageAdjunction
import Sheaf.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat

/-! # Ordinary coefficient-tower inverse-image ingredients -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {T S : Scheme.{t}} (g : T ⟶ S)

open CategoryTheory.Functor.sheafPullbackConstruction

private abbrev site (X : Scheme.{t}) := Scheme.coefficientProEtaleSiteModel.{t, u} X
private abbrev top (X : Scheme.{t}) := Scheme.coefficientProEtaleModelTopology.{t, u} X
private instance modelForgetCompose (X : Scheme.{t}) :
    (top.{t, u} X).HasSheafCompose (CategoryTheory.forget RingCat.{max u (t + 1)}) :=
  hasSheafCompose_of_preservesLimitsOfSize (top.{t, u} X)

private abbrev base := Scheme.coefficientProEtaleModelBaseChange.{t, u} g

private def ringEquiv (X : Scheme.{t}) :
    Sheaf (top.{t, u} X) CommRingCat.{max u (t + 1)} ≌
      Sheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)} :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : X.ProEt ⥤ site.{t, u} X).sheafPushforwardContinuous _
      (Scheme.ProEt.topology X) (top.{t, u} X))
    ((AsSmall.down : site.{t, u} X ⥤ X.ProEt).sheafPushforwardContinuous _
      (top.{t, u} X) (Scheme.ProEt.topology X)) (Iso.refl _) (Iso.refl _)

private instance ringColimits :
    HasColimitsOfSize.{t, t + 1} CommRingCat.{max u (t + 1)} :=
  hasColimitsOfSizeShrink.{t, t + 1, max u (t + 1), max u (t + 1)} _

private instance originalKan (P : S.ProEtᵒᵖ ⥤ CommRingCat.{max u (t + 1)}) :
    (Scheme.proEtaleBaseChange g).op.HasLeftKanExtension P := by
  let : (Scheme.proEtaleBaseChange g).op.HasPointwiseLeftKanExtension P :=
    fun V ↦ by
      let : HasColimitsOfShape (CostructuredArrow (Scheme.proEtaleBaseChange g).op V)
          CommRingCat.{max u (t + 1)} :=
        HasColimitsOfSize.has_colimits_of_shape _
      exact HasColimitsOfShape.has_colimit _
  exact Functor.HasLeftKanExtension.mk _
    (Functor.pointwiseLeftKanExtensionUnit (Scheme.proEtaleBaseChange g).op P)

private abbrev originalPull := sheafPullback (Scheme.proEtaleBaseChange g)
  CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology S) (Scheme.ProEt.topology T)
private abbrev originalAdj := sheafAdjunctionContinuous (Scheme.proEtaleBaseChange g)
  CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology S) (Scheme.ProEt.topology T)

private def ringMap (A : CommRingCat.{max u (t + 1)}) :=
  Scheme.coefficientProEtaleDirectRingMap.{t, u} g A

private theorem comparison_iso (A : CommRingCat.{max u (t + 1)}) :
    IsIso (((originalAdj.{t, u} g).homEquiv _ _).symm (ringMap.{t, u} g A)) := by
  let U : S.ProEt := Scheme.ProEt.mk (𝟙 S)
  let hU : IsTerminal U := MorphismProperty.Over.mkIdTerminal _ S
  let hV : IsTerminal ((Scheme.proEtaleBaseChange g).obj U) :=
    hU.isTerminalObj (Scheme.proEtaleBaseChange g)
  let eR : (Scheme.proEtaleBaseChange g).sheafPushforwardContinuous
      CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology S) (Scheme.ProEt.topology T) ⋙
      (sheafSections _ _).obj (op U) ≅
        (sheafSections _ _).obj (op ((Scheme.proEtaleBaseChange g).obj U)) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  let a := ((constantSheafAdj (Scheme.ProEt.topology S)
    CommRingCat.{max u (t + 1)} hU).comp (originalAdj.{t, u} g)).ofNatIsoRight eR
  let b := constantSheafAdj (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)} hV
  let e := a.leftAdjointUniq b
  have he : ((originalAdj.{t, u} g).homEquiv _ _).symm (ringMap.{t, u} g A) =
      e.hom.app A := by
    apply (a.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [a, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    simp only [eR,
      NatIso.ofComponents_hom_app, Iso.refl_hom]
    change (constantSheafAdj (Scheme.ProEt.topology S) _ hU).homEquiv _ _
      ((originalAdj.{t, u} g).homEquiv _ _
        (((originalAdj.{t, u} g).homEquiv _ _).symm (ringMap.{t, u} g A)))
        ≫ 𝟙 _ = _
    rw [Equiv.apply_symm_apply, Category.comp_id]
    change (constantSheafAdj (Scheme.ProEt.topology S) _ hU).homEquiv _ _
      (ringMap.{t, u} g A) = b.unit.app A
    unfold ringMap Scheme.coefficientProEtaleDirectRingMap
    rw [constantSheafAdj, Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{max u (t + 1)} hU).homEquiv _ _
      ((sheafificationAdjunction (Scheme.ProEt.topology S) CommRingCat.{max u (t + 1)}).homEquiv _ _
        (((sheafificationAdjunction (Scheme.ProEt.topology S)
          CommRingCat.{max u (t + 1)}).homEquiv _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    simp only [b, constantSheafAdj, Adjunction.comp_unit_app,
      constantPresheafAdj_unit_app, Category.id_comp, sheafificationAdjunction_unit_app]
    rfl
  rw [he]
  infer_instance

@[irreducible] private def modelAdj :
    (ringEquiv.{t, u} S).functor ⋙ originalPull.{t, u} g ⋙
      (ringEquiv.{t, u} T).inverse ⊣
      (base.{t, u} g).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
        (top.{t, u} S) (top.{t, u} T) :=
  (originalAdj.{t, u} g).restrictFullyFaithful
    (ringEquiv.{t, u} S).fullyFaithfulFunctor (ringEquiv.{t, u} T).fullyFaithfulFunctor
    (Iso.refl _) (Iso.refl _)

@[irreducible] private def moduleEquiv (X : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{max u (t + 1)}) :
    SheafOfModules.{max u (t + 1)} R ≌
      SheafOfModules.{max u (t + 1)}
        (((AsSmall.down : site.{t, u} X ⥤ X.ProEt).sheafPushforwardContinuous
          RingCat.{max u (t + 1)} (top.{t, u} X) (Scheme.ProEt.topology X)).obj R) := by
  let B := ((AsSmall.down : site.{t, u} X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{max u (t + 1)} (top.{t, u} X) (Scheme.ProEt.topology X)).obj R
  let : (AsSmall.equiv.{t, t + 1, max u (t + 1)} (C := X.ProEt)).functor.IsContinuous
      (Scheme.ProEt.topology X) (top.{t, u} X) :=
    Scheme.coefficientProEtaleModelUp_isContinuous X
  let : (AsSmall.equiv.{t, t + 1, max u (t + 1)} (C := X.ProEt)).inverse.IsContinuous
      (top.{t, u} X) (Scheme.ProEt.topology X) := by
    change AsSmall.down.IsContinuous (top.{t, u} X) (Scheme.ProEt.topology X)
    infer_instance
  exact (SheafOfModules.pushforwardPushforwardEquivalence
    (AsSmall.equiv.{t, t + 1, max u (t + 1)} (C := X.ProEt)) (𝟙 R) (𝟙 B)
    (by ext U : 2; exact B.obj.map_id _)
    (by ext U : 2; exact R.obj.map_id _)).symm

private theorem modelAdj_unit
    (R : Sheaf (Scheme.ProEt.topology S) CommRingCat.{max u (t + 1)}) :
    (modelAdj.{t, u} g).unit.app ((ringEquiv.{t, u} S).inverse.obj R) =
      ⟨Functor.whiskerLeft AsSmall.down.op ((originalAdj.{t, u} g).unit.app R).hom⟩ := by
  apply (ringEquiv.{t, u} S).functor.map_injective
  rw [modelAdj, Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Iso.refl_hom, NatTrans.id_app]
  rfl

private abbrev constantRing (X : Scheme.{t}) (A : CommRingCat.{max u (t + 1)}) :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A

private abbrev modelConstant (X : Scheme.{t}) (A : CommRingCat.{max u (t + 1)}) :=
  (ringEquiv.{t, u} X).inverse.obj (constantRing X A)

private instance modelDownEquivalence (X : Scheme.{t}) :
    (AsSmall.down : site.{t, u} X ⥤ X.ProEt).IsEquivalence :=
  (AsSmall.equiv.{t, t + 1, max u (t + 1)} (C := X.ProEt)).isEquivalence_inverse

private instance modelUpEquivalence (X : Scheme.{t}) :
    (AsSmall.up : X.ProEt ⥤ site.{t, u} X).IsEquivalence :=
  (AsSmall.equiv.{t, t + 1, max u (t + 1)} (C := X.ProEt)).isEquivalence_functor

private instance modelFlat : RepresentablyFlat (base.{t, u} g) := by
  have : PreservesFiniteLimits (base.{t, u} g) := by
    dsimp [base, Scheme.coefficientProEtaleModelBaseChange]
    infer_instance
  exact flat_of_preservesFiniteLimits _

private theorem modelPresentation (A : CommRingCat.{max u (t + 1)}) :
    ∃ pr : SheafPullbackUnitPresentation (F := base.{t, u} g)
      ((sheafCompose (top.{t, u} S) (CategoryTheory.forget CommRingCat.{max u (t + 1)})).obj
        (modelConstant S A))
      ((sheafCompose (top.{t, u} T) (CategoryTheory.forget CommRingCat.{max u (t + 1)})).obj
        (modelConstant T A)),
      pr.unit = (sheafCompose (top.{t, u} S)
        (CategoryTheory.forget RingCat.{max u (t + 1)})).map
          (Scheme.coefficientProEtaleModelRingMap.{t, u} g A) := by
  let F := base.{t, u} g
  let J := top.{t, u} S
  let K := top.{t, u} T
  let R := constantRing S A
  let Rm := modelConstant S A
  let Bm := modelConstant T A
  let c := ((originalAdj.{t, u} g).homEquiv _ _).symm (ringMap.{t, u} g A)
  have : IsIso c := comparison_iso g A
  let q := (ringEquiv.{t, u} T).inverse.mapIso (asIso c)
  let e := (modelAdj.{t, u} g).leftAdjointUniq
    (sheafAdjunctionContinuous F CommRingCat.{max u (t + 1)} J K)
  let cf := sheafPullbackForgetIso J K F (CategoryTheory.forget CommRingCat.{max u (t + 1)})
  let UK := sheafCompose K (CategoryTheory.forget CommRingCat.{max u (t + 1)})
  let iso := UK.mapIso q.symm ≪≫ UK.mapIso (e.app Rm) ≪≫ cf.app Rm
  let unit := (sheafCompose J (CategoryTheory.forget RingCat.{max u (t + 1)})).map
    (Scheme.coefficientProEtaleModelRingMap.{t, u} g A)
  have hunit : unit =
      (sheafCompose J (CategoryTheory.forget CommRingCat.{max u (t + 1)})).map
        ((modelAdj.{t, u} g).unit.app Rm) ≫
      (F.sheafPushforwardContinuous (Type (max u (t + 1))) J K).map (UK.map q.hom) := by
    have h := (originalAdj.{t, u} g).homEquiv_unit R (constantRing T A) c
    have hc : (originalAdj.{t, u} g).unit.app R ≫
        ((Scheme.proEtaleBaseChange g).sheafPushforwardContinuous
          CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology S)
          (Scheme.ProEt.topology T)).map c = ringMap.{t, u} g A := by
      exact h.symm.trans ((originalAdj.{t, u} g).homEquiv _ _ |>.apply_symm_apply _)
    rw [modelAdj_unit]
    ext U x
    exact (congrArg (fun z ↦ z.hom.app (AsSmall.down.op.obj U) x) hc).symm
  refine ⟨⟨unit, iso, ?_⟩, rfl⟩
  intro U x
  have he := Adjunction.unit_leftAdjointUniq_hom_app (modelAdj.{t, u} g)
    (sheafAdjunctionContinuous F CommRingCat.{max u (t + 1)} J K) Rm
  have hf := sheafPullbackForgetIso_unit J K F
    (CategoryTheory.forget CommRingCat.{max u (t + 1)}) Rm
  have hx := congrArg (fun z ↦ z.hom.app U x) hunit
  have he0 := congrArg (fun z ↦ z.hom.app U x) he
  have hf0 := congrArg (fun z ↦ z.hom.app U x) hf
  change (cf.hom.app Rm).hom.app (F.op.obj U)
    ((e.hom.app Rm).hom.app (F.op.obj U)
      (q.inv.hom.app (F.op.obj U) (unit.hom.app U x))) = _
  change unit.hom.app U x = q.hom.hom.app (F.op.obj U)
    (((modelAdj.{t, u} g).unit.app Rm).hom.app U x) at hx
  rw [hx]
  have hq := ConcreteCategory.congr_hom
    (congrArg (fun z ↦ z.hom.app (F.op.obj U)) q.hom_inv_id)
      (((modelAdj.{t, u} g).unit.app Rm).hom.app U x)
  change q.inv.hom.app (F.op.obj U) (q.hom.hom.app (F.op.obj U) _) = _ at hq
  dsimp only [ObjectProperty.FullSubcategory.id_hom] at hq
  rw [hq]
  exact (congrArg (fun y ↦ (cf.hom.app Rm).hom.app (F.op.obj U) y) he0).trans hf0

private abbrev originalModuleRing (X : Scheme.{t})
    (A : CommRingCat.{max u (t + 1)}) :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj (constantRing X A)

private theorem modelPullbackLimits (A : CommRingCat.{max u (t + 1)}) :
    PreservesFiniteLimits (SheafOfModules.pullback.{max u (t + 1)}
      (Scheme.coefficientProEtaleModelRingMap.{t, u} g A)) := by
  obtain ⟨pr, hpr⟩ := modelPresentation g A
  obtain ⟨e, _⟩ := inverseImage_underlying_of_ring_presentation
    (Scheme.coefficientProEtaleModelRingMap.{t, u} g A) pr hpr
  have : PreservesFiniteLimits
      (SheafOfModules.pullback.{max u (t + 1)}
        (Scheme.coefficientProEtaleModelRingMap.{t, u} g A) ⋙ toSheaf _) :=
    preservesFiniteLimits_of_natIso e.symm
  have : ReflectsFiniteLimits (toSheaf (originalModuleRing T A |>
      ((AsSmall.down : site.{t, u} T ⥤ T.ProEt).sheafPushforwardContinuous
        RingCat.{max u (t + 1)} (top.{t, u} T) (Scheme.ProEt.topology T)).obj)) :=
    reflectsFiniteLimits_of_reflectsIsomorphisms _
  exact preservesFiniteLimits_of_reflects_of_preserves _ (toSheaf _)

private def modulePushComparison
    (R : Sheaf (Scheme.ProEt.topology S) RingCat.{max u (t + 1)})
    (B : Sheaf (Scheme.ProEt.topology T) RingCat.{max u (t + 1)})
    (φ₀ : R ⟶ ((Scheme.proEtaleBaseChange g).sheafPushforwardContinuous
      RingCat.{max u (t + 1)} (Scheme.ProEt.topology S) (Scheme.ProEt.topology T)).obj B) :
    let Rm := ((AsSmall.down : site.{t, u} S ⥤ S.ProEt).sheafPushforwardContinuous
      RingCat.{max u (t + 1)} (top.{t, u} S) (Scheme.ProEt.topology S)).obj R
    let Bm := ((AsSmall.down : site.{t, u} T ⥤ T.ProEt).sheafPushforwardContinuous
      RingCat.{max u (t + 1)} (top.{t, u} T) (Scheme.ProEt.topology T)).obj B
    let φ : Rm ⟶ ((base.{t, u} g).sheafPushforwardContinuous
      RingCat.{max u (t + 1)} (top.{t, u} S) (top.{t, u} T)).obj Bm :=
      ⟨Functor.whiskerLeft AsSmall.down.op φ₀.hom⟩
    (moduleEquiv T B).functor ⋙ pushforward.{max u (t + 1)} φ ⋙
      (moduleEquiv S R).inverse ≅ pushforward.{max u (t + 1)} φ₀ := by
  intro Rm Bm φ
  let iT : Bm ⟶ ((AsSmall.down : site.{t, u} T ⥤ T.ProEt).sheafPushforwardContinuous
    RingCat.{max u (t + 1)} (top.{t, u} T) (Scheme.ProEt.topology T)).obj B := 𝟙 _
  let iS : R ⟶ ((AsSmall.up : S.ProEt ⥤ site.{t, u} S).sheafPushforwardContinuous
    RingCat.{max u (t + 1)} (Scheme.ProEt.topology S) (top.{t, u} S)).obj Rm := 𝟙 _
  let ψ := φ ≫ ((base.{t, u} g).sheafPushforwardContinuous
    RingCat.{max u (t + 1)} (top.{t, u} S) (top.{t, u} T)).map iT
  have ht : (moduleEquiv T B).functor = pushforward iT := by rw [moduleEquiv]; rfl
  have hs : (moduleEquiv S R).inverse = pushforward iS := by rw [moduleEquiv]; rfl
  rw [ht, hs]
  letI : (base.{t, u} g ⋙ AsSmall.down).IsContinuous
      (top.{t, u} S) (Scheme.ProEt.topology T) :=
    Functor.isContinuous_comp _ _ _ (top.{t, u} T) _
  let c₁ := SheafOfModules.pushforwardComp.{max u (t + 1)}
    (F := base.{t, u} g) (G := AsSmall.down)
    (J := top.{t, u} S) (K := top.{t, u} T) (K' := Scheme.ProEt.topology T) φ iT
  let c₂ := SheafOfModules.pushforwardComp.{max u (t + 1)}
    (F := AsSmall.up) (G := base.{t, u} g ⋙ AsSmall.down)
    (J := Scheme.ProEt.topology S) (K := top.{t, u} S)
    (K' := Scheme.ProEt.topology T) iS ψ
  refine (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight c₁ _ ≪≫ c₂ ≪≫ ?_
  exact SheafOfModules.pushforwardCongr
    (F := Scheme.proEtaleBaseChange g)
    (J := Scheme.ProEt.topology S) (K := Scheme.ProEt.topology T)
    (S := R) (R := B) (by ext U x; rfl)

private theorem originalPullbackLimits (A : CommRingCat.{max u (t + 1)}) :
    PreservesFiniteLimits
      (Scheme.coefficientProEtaleModuleDirectImage.{t, u} g A).leftAdjoint := by
  let eS := moduleEquiv S (originalModuleRing S A)
  let eT := moduleEquiv T (originalModuleRing T A)
  let φ := Scheme.coefficientProEtaleModelRingMap.{t, u} g A
  have := modelPullbackLimits g A
  let a := (eS.toAdjunction.comp (pullbackPushforwardAdjunction φ)).comp
    eT.symm.toAdjunction
  let b := a.ofNatIsoRight (modulePushComparison g (originalModuleRing S A)
    (originalModuleRing T A) ⟨Functor.whiskerRight (ringMap g A).hom
      (forget₂ CommRingCat RingCat)⟩)
  exact preservesFiniteLimits_of_natIso
    (b.leftAdjointUniq (Adjunction.ofIsRightAdjoint _))

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Constant-coefficient module inverse image preserves finite limits in the common
coefficient universe. Source: Stacks 04JC, and the preliminary operations clause of
blueprint sk-lem-sp-tower-levels (blueprint: lem-sp-level-pullback-exact).
Proof: transport the sites to their coefficient-sized AsSmall models. Inverse image
of the constant ring is canonically the same constant ring: both are left adjoint
to sections at the base-changed terminal object. The canonical constant-section map
is the transpose of this isomorphism. The module inverse image therefore has the
underlying abelian inverse image, with its scalar action transported through that
ring isomorphism. Abelian inverse image is left exact. Forgetting module scalars
reflects finite limits, so the module inverse image is left exact as well. Transport
back along the model equivalences and use uniqueness of left adjoints to identify
it with the specified left adjoint of spLevelPush. -/
theorem sp_level_pullback_exact (n : ℕ) :
    PreservesFiniteLimits (spLevelPush l E g n).leftAdjoint := by
  exact originalPullbackLimits g _

end AlgebraicGeometry.ProEtale
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
