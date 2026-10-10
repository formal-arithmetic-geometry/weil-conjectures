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
  rfl

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

end CategoryTheory.MorphismProperty

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

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarId_hom_app_hom_app (X : Scheme.{u}) (M : Sheaf (ProEt.topology X) A)
    (V : X.ProEtᵒᵖ) :
    ((lowerStarId A X).hom.app M).hom.app V =
      M.obj.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app V.unop).op := by
  simp [lowerStarId, Functor.sheafPushforwardContinuousId']
  exact Category.comp_id _

section

variable {C D : Type*} [Category* C] [Category* D] {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarId_inv_app_hom_app (X : Scheme.{u}) (M : Sheaf (ProEt.topology X) A)
    (V : X.ProEtᵒᵖ) :
    ((lowerStarId A X).inv.app M).hom.app V =
      M.obj.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V.unop).op := by
  simp [lowerStarId, Functor.sheafPushforwardContinuousId']

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarCongr_inv_app_hom_app {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g')
    (G : Sheaf (ProEt.topology Z) A) (V : Y.ProEtᵒᵖ) :
    ((lowerStarCongr A h).inv.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackCongr h).hom.app V.unop).op := by
  subst h
  simp only [lowerStarCongr_rfl, Iso.refl_inv, NatTrans.id_app]
  rw [show (MorphismProperty.Over.pullbackCongr (rfl : g = g)).hom.app V.unop = 𝟙 _ from
    MorphismProperty.Over.Hom.ext (by simp [MorphismProperty.Over.pullbackCongr]; rfl), op_id,
    G.obj.map_id]
  rfl

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
  ext W
  simp only [Iso.trans_inv, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom]


  simp only [lowerStar_map_hom_app', NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    lowerStarComp_hom_app_hom_app, lowerStarComp_inv_app_hom_app, lowerStarCongr_inv_app_hom_app,
    lowerStarId_inv_app_hom_app]
  simp only [lowerStar, Functor.sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op,
    ← Functor.map_comp, ← op_comp, Category.assoc]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  repeat' apply pullback.hom_ext
  all_goals simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
    MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp,
    MorphismProperty.Over.pullbackId]

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
  refine (conjugateIsoEquiv ((lowerStarEquivalence A e').symm.toAdjunction.comp
    (lowerStarEquivalence A e).symm.toAdjunction)
    (upperStarLowerStarAdjunction A (e.hom ≫ e'.hom))).injective ?_
  rw [conjugateIsoEquiv_trans _ (lowerStarEquivalence A (e ≪≫ e')).symm.toAdjunction _,
    conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A e'.hom).comp
      (upperStarLowerStarAdjunction A e.hom)) _,
    conjugateIsoEquiv_trans _ ((lowerStarEquivalence A e').symm.toAdjunction.comp
      (upperStarLowerStarAdjunction A e.hom)) _,
    conjugateIsoEquiv_lowerStarComp_symm]
  erw [conjugateIsoEquiv_upperStarIsoLowerStarInv A (e ≪≫ e')]
  erw [conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_upperStarIsoLowerStarInv, conjugateIsoEquiv_upperStarIsoLowerStarInv,
    conjugateIsoEquiv_upperStarComp]
  ext : 2
  simp

/-- Transport of the identification `e^* ≅ (e⁻¹)_*` along an equality of isomorphisms. -/
lemma upperStarIsoLowerStarInv_congr {X Y : Scheme.{u}} {e₁ e₂ : X ≅ Y} (h : e₁ = e₂) :
    upperStarIsoLowerStarInv A e₁ ≪≫ lowerStarCongr A (congrArg Iso.inv h) =
      upperStarCongr A (congrArg Iso.hom h) ≪≫ upperStarIsoLowerStarInv A e₂ := by
  subst h
  ext : 2
  simp [upperStarCongr]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
set_option maxHeartbeats 2000000 in
/-- The left unit law for the composition isomorphism of pushforwards, along a morphism `a`
equal to the identity. -/
lemma lowerStarComp_id_left_aux {X Y : Scheme.{u}} (a : X ⟶ X) (b c : X ⟶ Y) (ha : a = 𝟙 X)
    (hc : c = a ≫ b) (hb : c = b) (M : Sheaf (Scheme.ProEt.topology X) A) :
    (lowerStarCongr A hc).hom.app M ≫ (lowerStarComp A a b).inv.app M ≫
        (b)_*[A].map ((lowerStarCongr A ha).hom.app M ≫ (lowerStarId A X).hom.app M) =
      (lowerStarCongr A hb).hom.app M := by
  ext W
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp,
    lowerStarComp_inv_app_hom_app, lowerStarCongr_hom_app_hom_app, lowerStarId_hom_app_hom_app,
    lowerStar_map_hom_app']
  simp only [lowerStar, Functor.sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op,
    ← Functor.map_comp, ← op_comp]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  repeat' apply pullback.hom_ext
  all_goals simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
    MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp,
    MorphismProperty.Over.pullbackId]
  all_goals exact Category.id_comp _

end AlgebraicGeometry.ProEtale
