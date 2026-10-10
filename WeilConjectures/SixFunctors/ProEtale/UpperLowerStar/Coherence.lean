/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso

/-!
# Coherence of the composition isomorphisms of pro-étale pushforwards and pullbacks

The composition isomorphisms `ProEtale.lowerStarComp` and `ProEtale.upperStarComp` satisfy the
associativity law of a pseudofunctor. For pushforwards this is the associativity of the pullback
pasting isomorphisms on the sites (`MorphismProperty.Over.pullbackComp_assoc`), transported by
`CategoryTheory.Functor.sheafPushforwardContinuousComp'_assoc`; it is transported to pullbacks by
conjugation along the adjunctions `g^* ⊣ g_*`.

## Main results

- `AlgebraicGeometry.ProEtale.lowerStarComp_assoc` and
  `AlgebraicGeometry.ProEtale.upperStarComp_assoc`: the associativity laws.
-/

@[expose] public section

universe w v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u' u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']
  (A : Type u) [Category.{w} A]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {M : GrothendieckTopology E'}
  {F : C ⥤ D} {G : D ⥤ E} {H : E ⥤ E'} {FG : C ⥤ E} {GH : D ⥤ E'} {FGH : C ⥤ E'}
  [F.IsContinuous J K] [G.IsContinuous K L] [H.IsContinuous L M] [FG.IsContinuous J L]
  [GH.IsContinuous K M] [FGH.IsContinuous J M]

set_option backward.isDefEq.respectTransparency.types false in
/-- The associativity of the composition isomorphisms `sheafPushforwardContinuousComp'`,
given the associativity of the isomorphisms of functors of sites. -/
lemma sheafPushforwardContinuousComp'_assoc (e₁ : F ⋙ G ≅ FG) (e₂ : G ⋙ H ≅ GH)
    (e₃ : FG ⋙ H ≅ FGH) (e₄ : F ⋙ GH ≅ FGH)
    (h : isoWhiskerRight e₁ H ≪≫ e₃ = associator F G H ≪≫ isoWhiskerLeft F e₂ ≪≫ e₄) :
    isoWhiskerLeft (H.sheafPushforwardContinuous A L M)
        (sheafPushforwardContinuousComp' e₁ A J K L) ≪≫
      sheafPushforwardContinuousComp' e₃ A J L M =
    ((H.sheafPushforwardContinuous A L M).associator (G.sheafPushforwardContinuous A K L)
        (F.sheafPushforwardContinuous A J K)).symm ≪≫
      isoWhiskerRight (sheafPushforwardContinuousComp' e₂ A K L M)
        (F.sheafPushforwardContinuous A J K) ≪≫
      sheafPushforwardContinuousComp' e₄ A J K M := by
  ext P U
  have := congr_app (congrArg Iso.inv h) U.unop
  simp only [Iso.trans_inv, NatTrans.comp_app, isoWhiskerRight_inv, whiskerRight_app,
    isoWhiskerLeft_inv, whiskerLeft_app, associator_inv_app, Category.comp_id] at this
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    ObjectProperty.FullSubcategory.comp_hom, sheafPushforwardContinuousComp'_hom_app_hom_app,
    Iso.symm_hom, associator_inv_app, isoWhiskerRight_hom, whiskerRight_app,
    sheafPushforwardContinuous_map_hom_app, Category.id_comp,
    sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op]
  refine ((P.obj.map_comp _ _).symm.trans ?_).trans (P.obj.map_comp _ _)
  rw [← op_comp, ← op_comp, this]


set_option backward.isDefEq.respectTransparency.types false in
lemma sheafPushforwardContinuousComp'_trans {FG' : C ⥤ E} [FG'.IsContinuous J L]
    (e : F ⋙ G ≅ FG) (e' : FG ≅ FG') :
    sheafPushforwardContinuousComp' (e ≪≫ e') A J K L =
      sheafPushforwardContinuousComp' e A J K L ≪≫ sheafPushforwardContinuousIso e' A J L := by
  ext P U
  simp [sheafPushforwardContinuousComp']


section Unit

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃]
  {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂} {J₃ : GrothendieckTopology C₃}

set_option backward.isDefEq.respectTransparency.types false in
/-- Abstract form of the compatibility of the units of the pushforward equivalences with
composition (sites `C₁, C₂, C₃` for `X, Y, Z`). -/
lemma sheafPushforwardContinuous_unit_comp
    {F₁ : C₂ ⥤ C₁} {G₁ : C₁ ⥤ C₂} {F₂ : C₃ ⥤ C₂} {G₂ : C₂ ⥤ C₃}
    {K₂ I₃ K₁₂ : C₃ ⥤ C₃} {K₁ I₂ : C₂ ⥤ C₂} {F₁₂ : C₃ ⥤ C₁} {G₂₁ : C₁ ⥤ C₃}
    [F₁.IsContinuous J₂ J₁] [G₁.IsContinuous J₁ J₂] [F₂.IsContinuous J₃ J₂]
    [G₂.IsContinuous J₂ J₃] [K₂.IsContinuous J₃ J₃] [I₃.IsContinuous J₃ J₃]
    [K₁₂.IsContinuous J₃ J₃] [K₁.IsContinuous J₂ J₂] [I₂.IsContinuous J₂ J₂]
    [F₁₂.IsContinuous J₃ J₁] [G₂₁.IsContinuous J₁ J₃]
    (e₂ : F₂ ⋙ G₂ ≅ K₂) (c₂ : K₂ ≅ I₃) (i₃ : I₃ ≅ 𝟭 C₃)
    (e₁ : F₁ ⋙ G₁ ≅ K₁) (c₁ : K₁ ≅ I₂) (i₂ : I₂ ≅ 𝟭 C₂)
    (e₁₂ : F₂ ⋙ F₁ ≅ F₁₂) (e₂₁ : G₁ ⋙ G₂ ≅ G₂₁) (e : F₁₂ ⋙ G₂₁ ≅ K₁₂) (c : K₁₂ ≅ I₃)
    (h : ∀ U : C₃, G₂.map (G₁.map (e₁₂.inv.app U)) ≫ G₂.map (e₁.hom.app (F₂.obj U)) ≫
      G₂.map (c₁.hom.app (F₂.obj U)) ≫ G₂.map (i₂.hom.app (F₂.obj U)) ≫ e₂.hom.app U ≫
      c₂.hom.app U ≫ i₃.hom.app U =
      e₂₁.hom.app (F₁₂.obj U) ≫ e.hom.app U ≫ c.hom.app U ≫ i₃.hom.app U)
    (M : Sheaf J₃ A) :
    (sheafPushforwardContinuousComp' e₂ A J₃ J₂ J₃ ≪≫ sheafPushforwardContinuousIso c₂ A J₃ J₃ ≪≫
      sheafPushforwardContinuousId' i₃ A J₃).inv.app M ≫
      (F₂.sheafPushforwardContinuous A J₃ J₂).map
        ((sheafPushforwardContinuousComp' e₁ A J₂ J₁ J₂ ≪≫
          sheafPushforwardContinuousIso c₁ A J₂ J₂ ≪≫ sheafPushforwardContinuousId' i₂ A J₂).inv.app
          ((G₂.sheafPushforwardContinuous A J₂ J₃).obj M)) ≫
      (sheafPushforwardContinuousComp' e₁₂ A J₃ J₂ J₁).hom.app
        ((G₁.sheafPushforwardContinuous A J₁ J₂).obj ((G₂.sheafPushforwardContinuous A J₂ J₃).obj M)) =
    (sheafPushforwardContinuousComp' e A J₃ J₁ J₃ ≪≫ sheafPushforwardContinuousIso c A J₃ J₃ ≪≫
      sheafPushforwardContinuousId' i₃ A J₃).inv.app M ≫
      (F₁₂.sheafPushforwardContinuous A J₃ J₁).map
        ((sheafPushforwardContinuousComp' e₂₁ A J₁ J₂ J₃).inv.app M) := by
  ext U
  simp [sheafPushforwardContinuousComp', sheafPushforwardContinuousId']
  have h' := congrArg (fun φ => M.obj.map φ.op) (h U.unop)
  simp only [op_comp, Functor.map_comp, Category.assoc] at h'
  repeat erw [Category.id_comp]
  erw [Category.comp_id]
  exact h'

set_option backward.isDefEq.respectTransparency.types false in
/-- Abstract form of the left unit law for the pushforward composition isomorphisms. -/
lemma sheafPushforwardContinuous_id_left {F K Kc : C₂ ⥤ C₁} {G I : C₁ ⥤ C₁}
    [F.IsContinuous J₂ J₁] [K.IsContinuous J₂ J₁] [Kc.IsContinuous J₂ J₁]
    [G.IsContinuous J₁ J₁] [I.IsContinuous J₁ J₁]
    (e : F ⋙ G ≅ K) (c₁ : Kc ≅ K) (cₐ : G ≅ I) (i : I ≅ 𝟭 C₁) (c_b : Kc ≅ F)
    (h : ∀ U : C₂, i.inv.app (F.obj U) ≫ cₐ.inv.app (F.obj U) ≫ e.hom.app U ≫ c₁.inv.app U =
      c_b.inv.app U)
    (M : Sheaf J₁ A) :
    (sheafPushforwardContinuousIso c₁ A J₂ J₁).hom.app M ≫
      (sheafPushforwardContinuousComp' e A J₂ J₁ J₁).inv.app M ≫
      (F.sheafPushforwardContinuous A J₂ J₁).map
        ((sheafPushforwardContinuousIso cₐ A J₁ J₁).hom.app M ≫
          (sheafPushforwardContinuousId' i A J₁).hom.app M) =
    (sheafPushforwardContinuousIso c_b A J₂ J₁).hom.app M := by
  ext U
  have h' := congrArg (fun φ => M.obj.map φ.op) (h U.unop)
  simp only [op_comp, Functor.map_comp, Category.assoc] at h'
  simp [sheafPushforwardContinuousComp', sheafPushforwardContinuousId']
  erw [Category.id_comp, Category.comp_id]
  exact h'


end Unit

end CategoryTheory.Functor

namespace CategoryTheory.MorphismProperty

variable {T : Type*} [Category T] {P Q : MorphismProperty T} [Q.IsMultiplicative]
  [Q.RespectsIso] [Q.IsStableUnderBaseChange]

lemma Over.pullbackComp_eq_pullbackCongr_trans {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z)
    [P.IsStableUnderBaseChangeAlong f] [P.IsStableUnderBaseChangeAlong g]
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g]
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    haveI : P.HasPullbacksAlong fg := by subst hfg; infer_instance
    haveI : P.IsStableUnderBaseChangeAlong fg := by subst hfg; infer_instance
    Over.pullbackComp (P := P) (Q := Q) f g fg hfg =
      Over.pullbackCongr hfg ≪≫ Over.pullbackComp f g := by
  subst hfg
  rw [Over.pullbackCongr_refl, Iso.refl_trans]

lemma Over.pullbackCongr_trans_pullbackCongr {X Y : T} {f g : X ⟶ Y}
    [P.IsStableUnderBaseChangeAlong f] [P.HasPullbacksAlong f] (h : f = g) :
    haveI : P.HasPullbacksAlong g := by subst h; infer_instance
    haveI : P.IsStableUnderBaseChangeAlong g := by subst h; infer_instance
    Over.pullbackCongr (P := P) (Q := Q) h ≪≫ Over.pullbackCongr h.symm = Iso.refl _ := by
  subst h
  rw [Over.pullbackCongr_refl, Iso.refl_trans]

/-- The associativity law for `MorphismProperty.Over.pullbackComp`, in the form of inverses
followed by the congruence `(f ≫ g) ≫ h = f ≫ g ≫ h`. -/
lemma Over.pullbackComp_symm_assoc {X Y Z W : T} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    [P.IsStableUnderBaseChangeAlong f] [P.IsStableUnderBaseChangeAlong g]
    [P.IsStableUnderBaseChangeAlong h] [P.HasPullbacksAlong f] [P.HasPullbacksAlong g]
    [P.HasPullbacksAlong h] :
    Functor.isoWhiskerRight (Over.pullbackComp (P := P) (Q := Q) g h).symm (Over.pullback P Q f) ≪≫
        (Over.pullbackComp f (g ≫ h)).symm =
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (Over.pullback P Q h)
        (Over.pullbackComp f g).symm ≪≫ (Over.pullbackComp (f ≫ g) h).symm ≪≫
        Over.pullbackCongr (Category.assoc f g h) := by
  have := Over.pullbackComp_assoc (P := P) (Q := Q) f g h
  rw [MorphismProperty.Over.pullbackComp_eq_pullbackCongr_trans (f ≫ g) h] at this
  simp only [Iso.trans_assoc] at this
  have h2 : Functor.associator (Over.pullback P Q h) (Over.pullback P Q g) (Over.pullback P Q f) =
      (Functor.isoWhiskerRight (Over.pullbackComp g h) (Over.pullback P Q f)).symm ≪≫
        (Over.pullbackComp f (g ≫ h)).symm ≪≫
        Over.pullbackCongr (Category.assoc f g h).symm ≪≫ Over.pullbackComp (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (Over.pullback P Q h) (Over.pullbackComp f g) := by
    rw [← this]
    simp only [Iso.symm_self_id_assoc]
  rw [h2]
  simp only [Iso.trans_assoc, Functor.isoWhiskerRight_symm, Functor.isoWhiskerLeft_symm]
  rw [← Functor.isoWhiskerLeft_trans_assoc, Iso.self_symm_id, Functor.isoWhiskerLeft_refl,
    Iso.refl_trans, Iso.self_symm_id_assoc, MorphismProperty.Over.pullbackCongr_trans_pullbackCongr,
    Iso.trans_refl]


section Unit

variable [∀ {A B : T} (f : A ⟶ B), P.IsStableUnderBaseChangeAlong f]
  [∀ {A B : T} (f : A ⟶ B), P.HasPullbacksAlong f]

/-- The associativity law for `MorphismProperty.Over.pullbackComp`, with all composites free. -/
lemma Over.pullbackComp_assoc' {X Y Z W : T} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (gh : Y ⟶ W) (hgh : gh = g ≫ h) (fgh : X ⟶ W)
    (hfgh : fgh = f ≫ gh) :
    Over.pullbackComp (P := P) (Q := Q) f gh fgh hfgh ≪≫
        Functor.isoWhiskerRight (Over.pullbackComp g h gh hgh) (Over.pullback P Q f) ≪≫
          Functor.associator _ _ _ =
      Over.pullbackComp fg h fgh (by rw [hfgh, hgh, hfg, Category.assoc]) ≪≫
        Functor.isoWhiskerLeft (Over.pullback P Q h) (Over.pullbackComp f g fg hfg) := by
  subst hfg hgh hfgh
  exact Over.pullbackComp_assoc f g h

/-- The units `B(f) ⋙ B(g) ≅ 𝟭` of base change along a section `g` of `f` compose. -/
lemma Over.pullback_unit_comp {X Y Z : T} (f₁ : X ⟶ Y) (g₁ : Y ⟶ X) (f₂ : Y ⟶ Z)
    (g₂ : Z ⟶ Y) (h₁ : 𝟙 Y = g₁ ≫ f₁) (h₂ : 𝟙 Z = g₂ ≫ f₂)
    (h₁₂ : 𝟙 Z = (g₂ ≫ g₁) ≫ f₁ ≫ f₂) :
    Functor.isoWhiskerRight (Functor.isoWhiskerRight (Over.pullbackComp (P := P) (Q := Q) f₁ f₂)
        (Over.pullback P Q g₁)) (Over.pullback P Q g₂) ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (Over.pullback P Q f₂)
          ((Over.pullbackComp g₁ f₁ (𝟙 Y) h₁).symm ≪≫ Over.pullbackId P Q Y) ≪≫
          Functor.rightUnitor _) (Over.pullback P Q g₂) ≪≫
      (Over.pullbackComp g₂ f₂ (𝟙 Z) h₂).symm ≪≫ Over.pullbackId P Q Z =
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Over.pullback P Q (f₁ ≫ f₂)) (Over.pullbackComp g₂ g₁).symm ≪≫
      (Over.pullbackComp (g₂ ≫ g₁) (f₁ ≫ f₂) (𝟙 Z) h₁₂).symm ≪≫ Over.pullbackId P Q Z := by
  have X1 := congr_app (congrArg Iso.hom (Over.pullbackComp_assoc' (P := P) (Q := Q) g₁ f₁ f₂
    (𝟙 Y) h₁ (f₁ ≫ f₂) rfl f₂ (by rw [← Category.assoc, ← h₁, Category.id_comp])))
  have X2 := congr_app (congrArg Iso.hom (Over.pullbackComp_assoc' (P := P) (Q := Q) g₂ g₁
    (f₁ ≫ f₂) (g₂ ≫ g₁) rfl f₂ (by rw [← Category.assoc, ← h₁, Category.id_comp]) (𝟙 Z) h₂))
  rw [Over.pullbackComp_id_left f₂ f₂ (Category.id_comp f₂).symm] at X1
  apply Iso.ext
  apply NatTrans.ext
  funext U
  have e1 := X1 U
  have e2 := X2 U
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id, Category.id_comp,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom, Functor.comp_obj,
    Over.pullbackCongr_refl, Iso.refl_hom, Functor.rightUnitor_inv_app,
    Functor.rightUnitor_hom_app] at e1 e2 ⊢
  have e1' : (Over.pullback P Q g₁).map ((Over.pullbackComp f₁ f₂).hom.app U) ≫
      (Over.pullbackComp g₁ f₁ (𝟙 Y) h₁).inv.app ((Over.pullback P Q f₂).obj U) ≫
      (Over.pullbackId P Q Y).hom.app ((Over.pullback P Q f₂).obj U) =
      (Over.pullbackComp g₁ (f₁ ≫ f₂) f₂
        (by rw [← Category.assoc, ← h₁, Category.id_comp])).inv.app U := by
    rw [← cancel_epi ((Over.pullbackComp g₁ (f₁ ≫ f₂) f₂
      (by rw [← Category.assoc, ← h₁, Category.id_comp])).hom.app U), reassoc_of% e1]
    simp
  have e2' : (Over.pullback P Q g₂).map ((Over.pullbackComp g₁ (f₁ ≫ f₂) f₂
        (by rw [← Category.assoc, ← h₁, Category.id_comp])).inv.app U) ≫
      (Over.pullbackComp g₂ f₂ (𝟙 Z) h₂).inv.app U =
      (Over.pullbackComp g₂ g₁).inv.app ((Over.pullback P Q (f₁ ≫ f₂)).obj U) ≫
        (Over.pullbackComp (g₂ ≫ g₁) (f₁ ≫ f₂) (𝟙 Z) h₁₂).inv.app U := by
    have e2'' := e2 =≫ (Over.pullback P Q g₂).map ((Over.pullbackComp g₁ (f₁ ≫ f₂) f₂
        (by rw [← Category.assoc, ← h₁, Category.id_comp])).inv.app U)
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id,
      Category.comp_id] at e2''
    rw [← cancel_mono ((Over.pullbackComp g₂ f₂ (𝟙 Z) h₂).hom.app U)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [e2'']
    simp
  dsimp only [Functor.comp_obj] at *
  erw [Category.comp_id]
  rw [← Functor.map_comp_assoc, e1', reassoc_of% e2']

lemma Over.pullbackComp_eq_pullbackCongr_trans' {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    Over.pullbackComp (P := P) (Q := Q) f g fg hfg =
      Over.pullbackCongr hfg ≪≫ Over.pullbackComp f g := by
  subst hfg
  rw [Over.pullbackCongr_refl, Iso.refl_trans]

lemma Over.pullbackCongr_inv_eq {X Y : T} {f g : X ⟶ Y} (h : f = g) :
    (Over.pullbackCongr (P := P) (Q := Q) h).inv = (Over.pullbackCongr h.symm).hom := by
  subst h
  simp

/-- `Over.pullback_unit_comp` in components, with the default composites. -/
lemma Over.pullback_unit_comp_app {X Y Z : T} (f₁ : X ⟶ Y) (g₁ : Y ⟶ X) (f₂ : Y ⟶ Z)
    (g₂ : Z ⟶ Y) (h₁ : g₁ ≫ f₁ = 𝟙 Y) (h₂ : g₂ ≫ f₂ = 𝟙 Z)
    (h₁₂ : (g₂ ≫ g₁) ≫ f₁ ≫ f₂ = 𝟙 Z) (U : P.Over Q Z) :
    (Over.pullback P Q g₂).map ((Over.pullback P Q g₁).map
        ((Over.pullbackComp f₁ f₂).hom.app U)) ≫
      (Over.pullback P Q g₂).map ((Over.pullbackComp g₁ f₁).inv.app
        ((Over.pullback P Q f₂).obj U)) ≫
      (Over.pullback P Q g₂).map ((Over.pullbackCongr h₁).hom.app ((Over.pullback P Q f₂).obj U)) ≫
      (Over.pullback P Q g₂).map ((Over.pullbackId P Q Y).hom.app ((Over.pullback P Q f₂).obj U)) ≫
      (Over.pullbackComp g₂ f₂).inv.app U ≫ (Over.pullbackCongr h₂).hom.app U ≫
      (Over.pullbackId P Q Z).hom.app U =
    (Over.pullbackComp g₂ g₁).inv.app ((Over.pullback P Q (f₁ ≫ f₂)).obj U) ≫
      (Over.pullbackComp (g₂ ≫ g₁) (f₁ ≫ f₂)).inv.app U ≫ (Over.pullbackCongr h₁₂).hom.app U ≫
      (Over.pullbackId P Q Z).hom.app U := by
  have := congr_app (congrArg Iso.hom (Over.pullback_unit_comp (P := P) (Q := Q) f₁ g₁ f₂ g₂
    h₁.symm h₂.symm h₁₂.symm)) U
  simp only [Over.pullbackComp_eq_pullbackCongr_trans' _ _ (𝟙 _), Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Functor.comp_obj, Category.id_comp, Category.comp_id,
    Category.assoc, Functor.map_comp, Over.pullbackCongr_inv_eq] at this
  erw [Functor.map_id, Category.id_comp] at this
  exact this

/-- The left unit law for `MorphismProperty.Over.pullbackComp`, along a morphism equal to the
identity, in components. -/
lemma Over.pullback_id_left_app {X Y : T} (a : X ⟶ X) (b c : X ⟶ Y) (ha : a = 𝟙 X)
    (hc : c = a ≫ b) (hb : c = b) (U : P.Over Q Y) :
    (Over.pullbackId P Q X).inv.app ((Over.pullback P Q b).obj U) ≫
      (Over.pullbackCongr ha).inv.app ((Over.pullback P Q b).obj U) ≫
      (Over.pullbackComp a b).inv.app U ≫ (Over.pullbackCongr hc).inv.app U =
    (Over.pullbackCongr hb).inv.app U := by
  subst ha hc
  rw [Over.pullbackComp_id_left b (𝟙 X ≫ b) rfl]
  simp


end Unit

end CategoryTheory.MorphismProperty

namespace CategoryTheory



variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} (a₁ : L₁ ⊣ R₁) (b₁ : L₁' ⊣ R₁)
  {L₂ L₂' : D ⥤ E} {R₂ : E ⥤ D} (a₂ : L₂ ⊣ R₂) (b₂ : L₂' ⊣ R₂)
  {L₁₂ L₁₂' : C ⥤ E} {R₁₂ : E ⥤ C} (a₁₂ : L₁₂ ⊣ R₁₂) (b₁₂ : L₁₂' ⊣ R₁₂)

/-- The uniqueness isomorphisms of left adjoints are compatible with composition, the
composition isomorphisms of the left adjoints being conjugate to a common isomorphism
`ρ : R₂ ⋙ R₁ ≅ R₁₂` of right adjoints. -/
lemma Adjunction.leftAdjointUniq_trans_conjugateIsoEquiv_symm (ρ : R₂ ⋙ R₁ ≅ R₁₂) :
    a₁₂.leftAdjointUniq b₁₂ ≪≫ (conjugateIsoEquiv (b₁.comp b₂) b₁₂).symm ρ =
      (conjugateIsoEquiv (a₁.comp a₂) a₁₂).symm ρ ≪≫
        Functor.isoWhiskerRight (a₁.leftAdjointUniq b₁) L₂ ≪≫
        Functor.isoWhiskerLeft L₁' (a₂.leftAdjointUniq b₂) := by
  apply (conjugateIsoEquiv (b₁.comp b₂) a₁₂).injective
  rw [conjugateIsoEquiv_trans _ b₁₂ _, conjugateIsoEquiv_trans _ (a₁.comp a₂) _,
    conjugateIsoEquiv_trans _ (b₁.comp a₂) _]
  simp only [Equiv.apply_symm_apply]
  rw [conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_isoWhiskerRight]
  ext : 2
  simp [conjugateEquiv_leftAdjointUniq_hom]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

instance isStableUnderBaseChangeAlong_weaklyEtale {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong @WeaklyEtale f :=
  MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStableUnderBaseChange (P := @WeaklyEtale) f

instance hasPullbacksAlong_weaklyEtale {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong @WeaklyEtale f :=
  MorphismProperty.instHasPullbacksAlongOfHasPullbacksAlong (P := @WeaklyEtale) f

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The associativity law for `ProEtale.lowerStarComp`. -/
lemma lowerStarComp_assoc {X Y Z V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V) :
    Functor.isoWhiskerRight (lowerStarComp A f g) (h)_*[A] ≪≫ lowerStarComp A (f ≫ g) h ≪≫
        lowerStarCongr A (Category.assoc f g h) =
      ((f)_*[A]).associator (g)_*[A] (h)_*[A] ≪≫
        Functor.isoWhiskerLeft (f)_*[A] (lowerStarComp A g h) ≪≫ lowerStarComp A f (g ≫ h) := by
  have key := @Functor.sheafPushforwardContinuousComp'_assoc _ _ _ _ _ _ _ _ A _
    (ProEt.topology V) (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X) _ _ _ _ _ _
    (Scheme.ProEt.isContinuous_overPullback h) (Scheme.ProEt.isContinuous_overPullback g)
    (Scheme.ProEt.isContinuous_overPullback f) (Scheme.ProEt.isContinuous_overPullback (g ≫ h))
    (Scheme.ProEt.isContinuous_overPullback (f ≫ g))
    (Scheme.ProEt.isContinuous_overPullback (f ≫ g ≫ h))
    (MorphismProperty.Over.pullbackComp g h).symm (MorphismProperty.Over.pullbackComp f g).symm
    (MorphismProperty.Over.pullbackComp f (g ≫ h)).symm
    ((MorphismProperty.Over.pullbackComp (f ≫ g) h).symm ≪≫
      MorphismProperty.Over.pullbackCongr (Category.assoc f g h))
    (MorphismProperty.Over.pullbackComp_symm_assoc f g h)
  have ht := @Functor.sheafPushforwardContinuousComp'_trans _ _ _ _ _ _ A _
    (ProEt.topology V) (ProEt.topology Z) (ProEt.topology X) _ _ _
    (Scheme.ProEt.isContinuous_overPullback h) (Scheme.ProEt.isContinuous_overPullback (f ≫ g))
    (Scheme.ProEt.isContinuous_overPullback ((f ≫ g) ≫ h)) _
    (Scheme.ProEt.isContinuous_overPullback (f ≫ g ≫ h))
    (MorphismProperty.Over.pullbackComp (f ≫ g) h).symm
    (MorphismProperty.Over.pullbackCongr (Category.assoc f g h))
  rw [ht] at key
  have key' : Functor.isoWhiskerLeft (f)_*[A] (lowerStarComp A g h) ≪≫
      lowerStarComp A f (g ≫ h) = (((f)_*[A]).associator (g)_*[A] (h)_*[A]).symm ≪≫
      Functor.isoWhiskerRight (lowerStarComp A f g) (h)_*[A] ≪≫ lowerStarComp A (f ≫ g) h ≪≫
      lowerStarCongr A (Category.assoc f g h) := by
    rw [lowerStarCongr_eq]
    exact key
  rw [key', Iso.self_symm_id_assoc]

/-- Under conjugation, the composition isomorphism of pullbacks corresponds to the composition
isomorphism of pushforwards. -/
lemma conjugateIsoEquiv_upperStarComp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    conjugateIsoEquiv ((upperStarLowerStarAdjunction A h₂).comp
        (upperStarLowerStarAdjunction A h₁)) (upperStarLowerStarAdjunction A (h₁ ≫ h₂))
      (upperStarComp A h₁ h₂) = lowerStarComp A h₁ h₂ := by
  ext : 1
  exact conjugateEquiv_upperStarComp_hom A h₁ h₂

/-- Under conjugation, the congruence isomorphism of pullbacks corresponds to the congruence
isomorphism of pushforwards. -/
lemma conjugateIsoEquiv_upperStarCongr {Z W : Scheme.{u}} {g g' : Z ⟶ W} (h : g = g') :
    conjugateIsoEquiv (upperStarLowerStarAdjunction A g) (upperStarLowerStarAdjunction A g')
      (upperStarCongr A h).symm = lowerStarCongr A h := by
  ext : 1
  exact conjugateEquiv_upperStarCongr_inv A h

/-- The associativity law for `ProEtale.upperStarComp`, obtained from
`ProEtale.lowerStarComp_assoc` by conjugation. -/
lemma upperStarComp_assoc {X Y Z V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V) :
    upperStarComp A f (g ≫ h) ≪≫ Functor.isoWhiskerRight (upperStarComp A g h) (f)^*[A] ≪≫
        ((h)^*[A]).associator (g)^*[A] (f)^*[A] =
      (upperStarCongr A (Category.assoc f g h)).symm ≪≫ upperStarComp A (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (h)^*[A] (upperStarComp A f g) := by
  refine (conjugateIsoEquiv ((upperStarLowerStarAdjunction A h).comp
    ((upperStarLowerStarAdjunction A g).comp (upperStarLowerStarAdjunction A f)))
    (upperStarLowerStarAdjunction A (f ≫ g ≫ h))).injective ?_
  rw [conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A (g ≫ h)).comp
      (upperStarLowerStarAdjunction A f)) _,
    conjugateIsoEquiv_trans _ (((upperStarLowerStarAdjunction A h).comp
      (upperStarLowerStarAdjunction A g)).comp (upperStarLowerStarAdjunction A f)) _,
    conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction A ((f ≫ g) ≫ h)) _,
    conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A h).comp
      (upperStarLowerStarAdjunction A (f ≫ g))) _]
  simp only [conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator, conjugateIsoEquiv_upperStarCongr,
    Iso.trans_assoc]
  exact (lowerStarComp_assoc A f g h).symm

section

variable {C D : Type*} [Category* C] [Category* D] {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

/-- A natural transformation `β : R₁ ⟶ R₂` is the conjugate of `α : L₂ ⟶ L₁` as soon as it
satisfies the unit identity of the conjugate, provided the unit and the counit of `adj₁` are
invertible. -/
lemma _root_.CategoryTheory.conjugateEquiv_eq_of_unit (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    [∀ c, IsIso (adj₁.unit.app c)] [∀ d, IsIso (adj₁.counit.app d)] (α : L₂ ⟶ L₁)
    (β : R₁ ⟶ R₂)
    (h : ∀ c, adj₁.unit.app c ≫ β.app (L₁.obj c) = adj₂.unit.app c ≫ R₂.map (α.app c)) :
    conjugateEquiv adj₁ adj₂ α = β := by
  have key (c : C) : (conjugateEquiv adj₁ adj₂ α).app (L₁.obj c) = β.app (L₁.obj c) := by
    rw [← cancel_epi (adj₁.unit.app c), unit_conjugateEquiv, h]
  ext d
  have n₁ := (conjugateEquiv adj₁ adj₂ α).naturality (adj₁.counit.app d)
  have n₂ := β.naturality (adj₁.counit.app d)
  dsimp only [Functor.id_obj, Functor.comp_obj] at n₁ n₂
  rw [← cancel_epi (R₁.map (adj₁.counit.app d)), n₁, n₂, key]

end

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The unit of the adjunction `(e.inv)_* ⊣ (e.hom)_*` of the pushforward equivalence. -/
lemma lowerStarEquivalence_symm_toAdjunction_unit_app {X Y : Scheme.{u}} (e : X ≅ Y)
    (M : Sheaf (ProEt.topology Y) A) :
    (lowerStarEquivalence A e).symm.toAdjunction.unit.app M =
      (lowerStarComp A e.inv e.hom ≪≫ lowerStarCongr A e.inv_hom_id ≪≫ lowerStarId A Y).inv.app M :=
  by
  simp only [Equivalence.toAdjunction_unit, Equivalence.symm_unit]
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
set_option maxHeartbeats 2000000 in
/-- The units of the pushforward equivalences along `g₁` and `g₂` compose to the unit of the
pushforward equivalence along `g₂ ≫ g₁`. -/
lemma lowerStarComp_unit_aux {X Y Z : Scheme.{u}} (f₁ : X ⟶ Y) (g₁ : Y ⟶ X) (f₂ : Y ⟶ Z)
    (g₂ : Z ⟶ Y) (h₁ : g₁ ≫ f₁ = 𝟙 Y) (h₂ : g₂ ≫ f₂ = 𝟙 Z) (h₁₂ : (g₂ ≫ g₁) ≫ f₁ ≫ f₂ = 𝟙 Z)
    (M : Sheaf (Scheme.ProEt.topology Z) A) :
    (lowerStarComp A g₂ f₂ ≪≫ lowerStarCongr A h₂ ≪≫ lowerStarId A Z).inv.app M ≫
        (f₂)_*[A].map ((lowerStarComp A g₁ f₁ ≪≫ lowerStarCongr A h₁ ≪≫ lowerStarId A Y).inv.app
          ((g₂)_*[A].obj M)) ≫
        (lowerStarComp A f₁ f₂).hom.app ((g₁)_*[A].obj ((g₂)_*[A].obj M)) =
      (lowerStarComp A (g₂ ≫ g₁) (f₁ ≫ f₂) ≪≫ lowerStarCongr A h₁₂ ≪≫ lowerStarId A Z).inv.app M ≫
        (f₁ ≫ f₂)_*[A].map ((lowerStarComp A g₂ g₁).inv.app M) := by
  have key := @Functor.sheafPushforwardContinuous_unit_comp A _ _ _ _ _ _ _
    (ProEt.topology X) (ProEt.topology Y) (ProEt.topology Z) _ _ _ _ _ _ _ _ _ _ _
    (Scheme.ProEt.isContinuous_overPullback f₁) (Scheme.ProEt.isContinuous_overPullback g₁)
    (Scheme.ProEt.isContinuous_overPullback f₂) (Scheme.ProEt.isContinuous_overPullback g₂)
    (Scheme.ProEt.isContinuous_overPullback (g₂ ≫ f₂))
    (Scheme.ProEt.isContinuous_overPullback (𝟙 Z))
    (Scheme.ProEt.isContinuous_overPullback ((g₂ ≫ g₁) ≫ f₁ ≫ f₂))
    (Scheme.ProEt.isContinuous_overPullback (g₁ ≫ f₁))
    (Scheme.ProEt.isContinuous_overPullback (𝟙 Y))
    (Scheme.ProEt.isContinuous_overPullback (f₁ ≫ f₂))
    (Scheme.ProEt.isContinuous_overPullback (g₂ ≫ g₁))
    (MorphismProperty.Over.pullbackComp g₂ f₂).symm (MorphismProperty.Over.pullbackCongr h₂)
    (MorphismProperty.Over.pullbackId _ _ Z)
    (MorphismProperty.Over.pullbackComp g₁ f₁).symm (MorphismProperty.Over.pullbackCongr h₁)
    (MorphismProperty.Over.pullbackId _ _ Y)
    (MorphismProperty.Over.pullbackComp f₁ f₂).symm (MorphismProperty.Over.pullbackComp g₂ g₁).symm
    (MorphismProperty.Over.pullbackComp (g₂ ≫ g₁) (f₁ ≫ f₂)).symm
    (MorphismProperty.Over.pullbackCongr h₁₂)
    (fun U ↦ MorphismProperty.Over.pullback_unit_comp_app f₁ g₁ f₂ g₂ h₁ h₂ h₁₂ U) M
  rw [lowerStarCongr_eq, lowerStarCongr_eq, lowerStarCongr_eq]
  exact key

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
set_option maxHeartbeats 8000000 in
/-- Under conjugation along the adjunctions `(e.inv)_* ⊣ (e.hom)_*` of the pushforward
equivalences, the composition isomorphism of the pushforwards along the inverses corresponds to
the composition isomorphism of the pushforwards along the morphisms. -/
lemma conjugateIsoEquiv_lowerStarComp_symm {X Y Z : Scheme.{u}} (e : X ≅ Y) (e' : Y ≅ Z) :
    conjugateIsoEquiv ((lowerStarEquivalence A e').symm.toAdjunction.comp
        (lowerStarEquivalence A e).symm.toAdjunction)
      (lowerStarEquivalence A (e ≪≫ e')).symm.toAdjunction (lowerStarComp A e'.inv e.inv).symm =
      lowerStarComp A e.hom e'.hom := by
  ext : 1
  refine conjugateEquiv_eq_of_unit _ _ _ _ fun M ↦ ?_
  simp only [Adjunction.comp_unit_app, lowerStarEquivalence_symm_toAdjunction_unit_app]
  exact (Category.assoc _ _ _).trans
    (lowerStarComp_unit_aux A e.hom e.inv e'.hom e'.inv e.inv_hom_id e'.inv_hom_id _ M)


/-- The pullback along an isomorphism is conjugate to the identity of the pushforward. -/
lemma conjugateIsoEquiv_upperStarIsoLowerStarInv {X Y : Scheme.{u}} (e : X ≅ Y) :
    conjugateIsoEquiv (lowerStarEquivalence A e).symm.toAdjunction
      (upperStarLowerStarAdjunction A e.hom) (upperStarIsoLowerStarInv A e) = Iso.refl _ := by
  ext : 1
  exact conjugateEquiv_leftAdjointUniq_hom _ _


set_option maxHeartbeats 1000000 in
/-- The identification `e^* ≅ (e⁻¹)_*` of the pullback along an isomorphism with the pushforward
along its inverse is compatible with composition:
`(e ≫ e')^* ≅ e'^* ⋙ e^* ≅ (e'⁻¹)_* ⋙ (e⁻¹)_* ≅ (e'⁻¹ ≫ e⁻¹)_*`. -/
lemma upperStarIsoLowerStarInv_trans {X Y Z : Scheme.{u}} (e : X ≅ Y) (e' : Y ≅ Z) :
    upperStarIsoLowerStarInv A (e ≪≫ e') ≪≫ (lowerStarComp A e'.inv e.inv).symm =
      upperStarComp A e.hom e'.hom ≪≫
        Functor.isoWhiskerRight (upperStarIsoLowerStarInv A e') (e.hom)^*[A] ≪≫
        Functor.isoWhiskerLeft (e'.inv)_*[A] (upperStarIsoLowerStarInv A e) := by
  have key := Adjunction.leftAdjointUniq_trans_conjugateIsoEquiv_symm
    (upperStarLowerStarAdjunction A e'.hom) (lowerStarEquivalence A e').symm.toAdjunction
    (upperStarLowerStarAdjunction A e.hom) (lowerStarEquivalence A e).symm.toAdjunction
    (upperStarLowerStarAdjunction A (e ≪≫ e').hom)
    (lowerStarEquivalence A (e ≪≫ e')).symm.toAdjunction (lowerStarComp A e.hom e'.hom)
  have h2 : (conjugateIsoEquiv ((lowerStarEquivalence A e').symm.toAdjunction.comp
      (lowerStarEquivalence A e).symm.toAdjunction)
      (lowerStarEquivalence A (e ≪≫ e')).symm.toAdjunction).symm (lowerStarComp A e.hom e'.hom) =
      (lowerStarComp A e'.inv e.inv).symm :=
    (Equiv.symm_apply_eq _).2 (conjugateIsoEquiv_lowerStarComp_symm A e e').symm
  refine Eq.trans ?_ key
  show _ = (upperStarLowerStarAdjunction A (e ≪≫ e').hom).leftAdjointUniq
    (lowerStarEquivalence A (e ≪≫ e')).symm.toAdjunction ≪≫
    (conjugateIsoEquiv ((lowerStarEquivalence A e').symm.toAdjunction.comp
      (lowerStarEquivalence A e).symm.toAdjunction)
      (lowerStarEquivalence A (e ≪≫ e')).symm.toAdjunction).symm (lowerStarComp A e.hom e'.hom)
  rw [h2]
  rfl

/-- Transport of the identification `e^* ≅ (e⁻¹)_*` along an equality of isomorphisms. -/
lemma upperStarIsoLowerStarInv_congr {X Y : Scheme.{u}} {e₁ e₂ : X ≅ Y} (h : e₁ = e₂) :
    upperStarIsoLowerStarInv A e₁ ≪≫ lowerStarCongr A (congrArg Iso.inv h) =
      upperStarCongr A (congrArg Iso.hom h) ≪≫ upperStarIsoLowerStarInv A e₂ := by
  subst h
  ext : 2
  simp [upperStarCongr]


omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The left unit law for the composition isomorphism of pushforwards, along a morphism `a`
equal to the identity. -/
lemma lowerStarComp_id_left_aux {X Y : Scheme.{u}} (a : X ⟶ X) (b c : X ⟶ Y) (ha : a = 𝟙 X)
    (hc : c = a ≫ b) (hb : c = b) (M : Sheaf (Scheme.ProEt.topology X) A) :
    (lowerStarCongr A hc).hom.app M ≫ (lowerStarComp A a b).inv.app M ≫
        (b)_*[A].map ((lowerStarCongr A ha).hom.app M ≫ (lowerStarId A X).hom.app M) =
      (lowerStarCongr A hb).hom.app M := by
  have key := @Functor.sheafPushforwardContinuous_id_left A _ _ _ _ _
    (ProEt.topology X) (ProEt.topology Y) _ _ _ _ _
    (Scheme.ProEt.isContinuous_overPullback b) (Scheme.ProEt.isContinuous_overPullback (a ≫ b))
    (Scheme.ProEt.isContinuous_overPullback c) (Scheme.ProEt.isContinuous_overPullback a)
    (Scheme.ProEt.isContinuous_overPullback (𝟙 X))
    (MorphismProperty.Over.pullbackComp a b).symm (MorphismProperty.Over.pullbackCongr hc)
    (MorphismProperty.Over.pullbackCongr ha) (MorphismProperty.Over.pullbackId _ _ X)
    (MorphismProperty.Over.pullbackCongr hb)
    (fun U ↦ MorphismProperty.Over.pullback_id_left_app a b c ha hc hb U) M
  rw [lowerStarCongr_eq, lowerStarCongr_eq, lowerStarCongr_eq]
  exact key

end AlgebraicGeometry.ProEtale
