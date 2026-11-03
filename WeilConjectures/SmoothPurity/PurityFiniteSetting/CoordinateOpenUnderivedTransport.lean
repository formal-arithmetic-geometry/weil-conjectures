/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateGlobalSectionsUnit
import all WeilConjectures.AlgebraicGeometry.EtaleChartSectionsObjectComparison
import all Mathlib.CategoryTheory.Iso
import all Mathlib.CategoryTheory.Equivalence
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-! # Underived localization of coordinate transport
Source: Stacks Tags 03CF and 03EF, inverse-image adjunction units.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry.Etale

attribute [local implicit_reducible] Scheme.Etale Scheme.Hom.Etale Scheme.instCategoryEtale
  MorphismProperty MorphismProperty.Comma.instCategory Etale.lowerStar
  Functor.sheafPushforwardContinuous

private theorem restriction_unit (P : PurityFiniteSetting.{u})
    {T Y : Scheme.{u}} (f : T ⟶ Y) [Etale f]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    (b : Y.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj b) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) f).unit.app F).hom.app (op b) ≫
        ((upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj F).obj.map ψ.op ≫
        ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} P.Coefficient) f
          inferInstance).hom.app
          F).hom.app (op c) =
      F.obj.map (((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f inferInstance
        _root_.trivial).homEquiv c b).symm ψ).op := by
  exact AlgebraicGeometry.Etale.restriction_unit P.Coefficient f F b c ψ

-- Pointwise form of the composition unit equation, after restriction.
-- Adapted from the proved helper in EtaleChartSectionsObjectComparison.
private theorem composition_unit (P : PurityFiniteSetting.{u})
    {T Y R : Scheme.{u}}
    (f : T ⟶ Y) (g : Y ⟶ R) (t : T ⟶ R) (ht : t = f ≫ g)
    (F : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    (b : R.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t).obj b) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) t).unit.app F).hom.app (op b) ≫
        ((upperStar (ModuleCat.{u + 1} P.Coefficient) t).obj F).obj.map ψ.op ≫
        ((upperStarComp (ModuleCat.{u + 1} P.Coefficient) f g t ht).hom.app F).hom.app (op c) =
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) g).unit.app
        F).hom.app (op b) ≫
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) f).unit.app
          ((upperStar (ModuleCat.{u + 1} P.Coefficient) g).obj F)).hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj b)) ≫
        ((upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
          ((upperStar (ModuleCat.{u + 1} P.Coefficient) g).obj F)).obj.map
          (ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g t ht).hom.app
            b).op := by
  exact AlgebraicGeometry.Etale.composition_unit P.Coefficient f g t ht F b c ψ


/-- Evaluation on an etale object commutes with pullback along a pointed map
into that object. This is an equality on sheaves before passing to complexes.
Source: Stacks Tags 03CF and 03EF.
Proof: compare the composition adjunction unit at the pointed terminal object.
The diagonal section and localization adjunction identify the open inverse-image
unit with the restriction comparison. Pullback extensionality identifies the two
pointed arrows in the composition formula. The constant-sheaf adjunction mate on
global sections is its terminal evaluation, giving the claimed formula.
(blueprint: aux-lem-pur-coordinate-open-underived-transport). -/
theorem coordinateOpenSections_pointed (P : PurityFiniteSetting.{u})
    {T U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (a : T ⟶ X) (m : T ⟶ U) (ha : a = m ≫ j)
    (ψ : Scheme.Etale.mk (𝟙 T) ⟶ a.Etale.obj (Scheme.Etale.mk j))
    (hm : ψ.left ≫ pullback.fst j a = m)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) a).unit.app
        F).hom.app (op (Scheme.Etale.mk j)) ≫
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).obj F).obj.map ψ.op =
    (P.coordinateOpenSectionsIso j).inv.app F ≫
      (P.coordinateGlobalSectionsUnit m).app
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).obj F) ≫
      (Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) T).map
        ((Etale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) m j a ha).inv.app F) := by
  let V := Scheme.Etale.mk j
  let A := (ModuleCat.{u + 1} P.Coefficient)
  let wT : T.Etale := Scheme.Etale.mk (𝟙 T)
  let wV : V.left.Etale := Scheme.Etale.mk (𝟙 V.left)
  let FV := (upperStar A V.hom).obj F
  let FT := (upperStar A a).obj F
  let K := (upperStar A m).obj FV
  let eV : (MorphismProperty.Over.map ⊤ (inferInstance : Etale V.hom)).obj wV ≅ V :=
    MorphismProperty.Over.isoMk (Iso.refl V.left) (by simp [wV])
  let rV := (upperStarIsoLocalizationRestriction A V.hom inferInstance).app F
  let δ : wV ⟶ V.hom.Etale.obj V :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 V.left) (𝟙 V.left) (by rfl))
      (by change _ ≫ pullback.snd _ _ = _; simp [wV])
  let θ : wT ⟶ m.Etale.obj wV :=
    MorphismProperty.Over.homMk (pullback.lift m (𝟙 T)
      ((Category.comp_id m).trans (Category.id_comp m).symm))
      (by change _ ≫ pullback.snd _ _ = _; simp only [pullback.lift_snd]; rfl)
  let c := (upperStarComp A m V.hom a ha).app F
  have hδ := restriction_unit P V.hom F V wV δ
  have hδmap : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ V.hom inferInstance
      _root_.trivial).homEquiv wV V).symm δ = eV.hom := by
    ext
    simp [δ, eV, Adjunction.homEquiv_counit]
  rw [hδmap] at hδ
  have hδ' : ((upperStarLowerStarAdjunction A V.hom).unit.app F).hom.app (op V) ≫
      FV.obj.map δ.op = F.obj.map eV.hom.op ≫ rV.inv.hom.app (op wV) := by
    apply (cancel_mono (rV.hom.hom.app (op wV))).1
    simp only [Category.assoc]
    have hr : rV.inv.hom.app (op wV) ≫ rV.hom.hom.app (op wV) = 𝟙 _ :=
      congrArg (fun z ↦ z.hom.app (op wV)) rV.inv_hom_id
    conv_rhs => rw [hr]
    erw [Category.comp_id]
    exact hδ
  have hψ : ψ.left ≫ pullback.snd V.hom a = 𝟙 T := ψ.w
  have hχ : ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      m V.hom a ha).hom.app V = θ ≫ m.Etale.map δ := by
    apply MorphismProperty.Over.Hom.ext
    change ψ.left ≫ _ = θ.left ≫ _
    dsimp only [Scheme.Hom.Etale]
    simp only [MorphismProperty.Over.pullbackComp_hom_app_left,
      MorphismProperty.Over.pullback_map_left]
    have hs : ((MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj V).hom =
        pullback.snd V.hom V.hom := rfl
    dsimp only [MorphismProperty.Over.pullback_obj_hom]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [θ, δ, MorphismProperty.Over.homMk_hom, Over.homMk_left,
          MorphismProperty.Over.mk_left, Functor.const_obj_obj, Functor.id_obj,
          MorphismProperty.Over.pullback_obj_left, MorphismProperty.Over.pullback_obj_hom,
          Functor.comp_obj, Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
          wV, MorphismProperty.Over.mk_hom, pullback.lift_fst_assoc,
          limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Category.comp_id]
        exact hm
      · dsimp only [MorphismProperty.Over.pullback, MorphismProperty.Over.mk, Functor.comp_obj]
        simp only [θ, δ, MorphismProperty.Over.homMk_hom, Over.homMk_left,
          Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd,
          pullback.lift_fst, pullback.lift_snd]
        simp only [pullback.map, pullback.lift_snd_assoc, pullback.lift_fst_assoc, Category.comp_id]
        rw [← Category.assoc, hψ]
        exact (Category.id_comp m).trans (Category.comp_id m).symm
    · dsimp only [MorphismProperty.Over.pullback, MorphismProperty.Over.mk, Functor.comp_obj]
      simp only [θ, MorphismProperty.Over.homMk_hom, Over.homMk_left,
        Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, pullback.lift_snd]
      rw [Category.comp_id, hψ]
  have hc := composition_unit P m V.hom a ha F V wT ψ
  rw [hχ, op_comp, Functor.map_comp] at hc
  change _ = ((upperStarLowerStarAdjunction A V.hom).unit.app F).hom.app (op V) ≫
    ((upperStarLowerStarAdjunction A m).unit.app FV).hom.app
      (op (V.hom.Etale.obj V)) ≫ ((lowerStar A m).obj K).obj.map δ.op ≫ K.obj.map θ.op at hc
  erw [← ((upperStarLowerStarAdjunction A m).unit.app FV).hom.naturality_assoc,
    reassoc_of% hδ'] at hc
  have hθ : θ = (coordinateTerminalPullbackIso m).inv :=
    ((Scheme.Etale.isTerminalMkId V.left).isTerminalObj m.Etale).hom_ext _ _
  have ht := P.coordinateGlobalSectionsUnit_eval m FV
  change (P.coordinateGlobalSectionsUnit m).app FV =
    ((upperStarLowerStarAdjunction A m).unit.app FV).hom.app (op wV) ≫
      K.obj.map (coordinateTerminalPullbackIso m).inv.op at ht
  rw [← hθ] at ht
  apply (cancel_mono (c.hom.hom.app (op wT))).1
  simp only [Category.assoc]
  erw [hc]
  change _ = (P.coordinateOpenSectionsIso j).inv.app F ≫
    (P.coordinateGlobalSectionsUnit m).app FV ≫ c.inv.hom.app (op wT) ≫
      c.hom.hom.app (op wT)
  have hi : c.inv.hom.app (op wT) ≫ c.hom.hom.app (op wT) = 𝟙 _ :=
    congrArg (fun z ↦ z.hom.app (op wT)) c.inv_hom_id
  rw [hi]
  erw [Category.comp_id]
  erw [← ht]
  rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
-- Localized inverse-image comparisons require additional elaboration steps.
/-- Open localization carries the actual section pullback to the global-section
mate on the two open schemes. The site arrow is specified by its first projection.
Source: Stacks Tags 03CF and 03EF.
Proof: apply the pointed-section formula to the composite open map. The composition
unit formula expresses this in terms of the ambient pullback unit. The terminal
section in the iterated pullback transposes to the recorded site arrow: both
projections agree by the two pullback equations. Apply the open restriction unit
formula and cancel its isomorphism.
(blueprint: aux-lem-pur-coordinate-open-underived-transport). -/
theorem coordinateOpenSections_square (P : PurityFiniteSetting.{u})
    {U U' X X' : Scheme.{u}} (j : U ⟶ X) (j' : U' ⟶ X')
    [IsOpenImmersion j] [IsOpenImmersion j'] (f : X' ⟶ X) (k : U' ⟶ U)
    (w : j' ≫ f = k ≫ j)
    (ψ : Scheme.Etale.mk j' ⟶ f.Etale.obj (Scheme.Etale.mk j))
    (hψ : ψ.left ≫ pullback.fst j f = k)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    (P.coordinateOpenSectionsIso j).inv.app F ≫
        (P.coordinateGlobalSectionsUnit k).app
          ((upperStar (ModuleCat.{u + 1} P.Coefficient) j).obj F) ≫
        (sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) U').map
          ((upperStarComp (ModuleCat.{u + 1} P.Coefficient) k j).inv.app F ≫
            (upperStarComp (ModuleCat.{u + 1} P.Coefficient) j' f (k ≫ j) w.symm).hom.app F) =
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) f).unit.app
          F).hom.app (op (Scheme.Etale.mk j)) ≫
        ((upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj F).obj.map ψ.op ≫
        (P.coordinateOpenSectionsIso j').inv.app
          ((upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj F) := by
  let A := (ModuleCat.{u + 1} P.Coefficient)
  let V := Scheme.Etale.mk j
  let V' := Scheme.Etale.mk j'
  let wU' := Scheme.Etale.mk (𝟙 U')
  let a := k ≫ j
  let ψ₀ : wU' ⟶ a.Etale.obj V :=
    MorphismProperty.Over.homMk
      (pullback.lift k (𝟙 U') (by change k ≫ j = 𝟙 U' ≫ (k ≫ j); simp))
      (pullback.lift_snd _ _ _)
  let δ := ψ₀ ≫
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) j' f a w.symm).hom.app V
  let eW : (MorphismProperty.Over.map ⊤ (inferInstance : Etale j')).obj wU' ≅ V' :=
    MorphismProperty.Over.isoMk (Iso.refl U') (by simp [wU', V'])
  let G := (upperStar A f).obj F
  let ρ := (upperStarIsoLocalizationRestriction A j' inferInstance).app G
  have hp := P.coordinateOpenSections_pointed j a k rfl ψ₀
    (pullback.lift_fst _ _ _) F
  have hc := composition_unit P j' f a w.symm F V wU' ψ₀
  have hd : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j' inferInstance
      _root_.trivial).homEquiv wU' (f.Etale.obj V)).symm δ = eW.hom ≫ ψ := by
    apply MorphismProperty.Over.Hom.ext
    change δ.left ≫ pullback.fst (f.Etale.obj V).hom j' =
      eW.hom.left ≫ ψ.left
    change (ψ₀.left ≫ ((MorphismProperty.Over.pullbackComp
      (P := @Etale) (Q := ⊤) j' f a w.symm).hom.app V).left) ≫
        pullback.fst (pullback.snd V.hom f) j' = (𝟙 U') ≫ ψ.left
    simp only [MorphismProperty.Over.pullbackComp_hom_app_left]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
        pullback.lift_fst, Category.id_comp]
      simpa [ψ₀, a, V, wU'] using! hψ.symm
    · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd,
        Category.id_comp]
      have hw : ψ.left ≫ pullback.snd j f = j' := ψ.w
      simpa [ψ₀, a, V, wU'] using! hw.symm
  have hr := restriction_unit P j' G (f.Etale.obj V) wU' δ
  rw [hd] at hr
  conv_rhs at hr => rw [op_comp, Functor.map_comp]
  change ((upperStarLowerStarAdjunction A j').unit.app G).hom.app
      (op (f.Etale.obj V)) ≫ ((upperStar A j').obj G).obj.map δ.op ≫
      ρ.hom.hom.app (op wU') = G.obj.map ψ.op ≫ G.obj.map eW.hom.op at hr
  simp only [Functor.map_comp]
  erw [← reassoc_of% hp, hc]
  apply (cancel_mono (ρ.hom.hom.app (op wU'))).1
  simp only [Category.assoc]
  change _ ≫ (((upperStarLowerStarAdjunction A j').unit.app G).hom.app
    (op (f.Etale.obj V)) ≫ ((upperStar A j').obj G).obj.map δ.op ≫
    ρ.hom.hom.app (op wU')) = _
  have hr' := congrArg
    (fun z ↦ ((upperStarLowerStarAdjunction A f).unit.app F).hom.app (op V) ≫ z) hr
  simpa [coordinateOpenSectionsIso, eW, ρ, V', wU', A, Category.assoc] using hr'



end WeilConjectures.PurityFiniteSetting
