/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Normalized transport of a local module isomorphism

Source: Stacks Project, Modules on Sites, Tag 04J0, lemma-localize-morphism-ringed-sites.
(blueprint: lem-sfb-normalized-local-module-pullback).
-/

@[expose] public noncomputable section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

private def postStarIso {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D] (F : C ⥤ D) [PreservesFiniteLimits F]
    (V : C) : F ⋙ Over.star (F.obj V) ≅ Over.star V ⋙ Over.post F :=
  NatIso.ofComponents (fun U ↦ Over.isoMk (PreservesLimitPair.iso F V U).symm
    (by simp)) (by
      intro U U' f
      ext
      apply (cancel_mono (PreservesLimitPair.iso F V U').hom).1
      change (prod.map (𝟙 _) (F.map f) ≫ (PreservesLimitPair.iso F V U').inv) ≫
        (PreservesLimitPair.iso F V U').hom =
        ((PreservesLimitPair.iso F V U).inv ≫ F.map (prod.map (𝟙 V) f)) ≫
          (PreservesLimitPair.iso F V U').hom
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply prod.hom_ext <;>
        simp only [Category.assoc, PreservesLimitPair.iso_hom, prodComparison_fst,
          prodComparison_snd, ← F.map_comp, prod.map_fst, prod.map_snd,
          Category.comp_id,
          PreservesLimitPair.iso_inv_fst]
      rw [F.map_comp, ← Category.assoc, PreservesLimitPair.iso_inv_snd])

private def localMap {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (rho : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj S) (V : C)
    [(Over.post (X := V) F).IsContinuous (J.over V) (K.over (F.obj V))] :
    R.over V ⟶ ((Over.post (X := V) F).sheafPushforwardContinuous
      RingCat.{u} (J.over V) (K.over (F.obj V))).obj (S.over (F.obj V)) :=
  ⟨{ app T := rho.hom.app (op T.unop.left)
     naturality _ _ f := rho.hom.naturality ((Over.forget V).op.map f) }⟩

private def localRightIso {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] [PreservesFiniteLimits F]
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (rho : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj S) (V : C)
    [(Over.post (X := V) F).IsContinuous (J.over V) (K.over (F.obj V))] :
    pushforward (pushforwardOver (R := S) (F.obj V)) ⋙ pushforward rho ≅
      pushforward (localMap J K F rho V) ⋙ pushforward (pushforwardOver (R := R) V) := by
  letI := Functor.isContinuous_comp F (Over.star (F.obj V)) J K (K.over (F.obj V))
  letI := Functor.isContinuous_comp (Over.star V) (Over.post F)
    J (J.over V) (K.over (F.obj V))
  refine pushforwardComp rho _ ≪≫ (pushforwardCongr₂ _ (postStarIso F V).symm ?_) ≪≫
    (pushforwardComp (pushforwardOver (R := R) V) (localMap J K F rho V)).symm
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  change (rho.hom.app U ≫ S.obj.map (prod.snd).op) ≫
    S.obj.map ((PreservesLimitPair.iso F V U.unop).hom).op =
      R.obj.map prod.snd.op ≫ rho.hom.app (op (V ⨯ U.unop))
  rw [Category.assoc, ← S.obj.map_comp, ← op_comp]
  simp only [PreservesLimitPair.iso_hom, prodComparison_snd]
  exact (rho.hom.naturality prod.snd.op).symm

@[irreducible] private def localHomEquiv {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] [PreservesFiniteLimits F]
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (rho : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj S) (V : C)
    [(Over.post (X := V) F).IsContinuous (J.over V) (K.over (F.obj V))]
    (G : SheafOfModules.{u} R) (Q : SheafOfModules.{u} (S.over (F.obj V))) :
    (((pullback rho).obj G).over (F.obj V) ⟶ Q) ≃
      (G.over V ⟶ (pushforward (localMap J K F rho V)).obj Q) :=
  ((((pullbackPushforwardAdjunction rho).comp
      (overPushforwardOverAdj (R := S) (F.obj V))).ofNatIsoRight
        (localRightIso J K F rho V)).homEquiv G Q).trans
    ((overPushforwardOverAdj (R := R) V).homEquiv _ _).symm

private theorem localHomEquiv_apply {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] [PreservesFiniteLimits F]
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (rho : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj S) (V : C)
    [(Over.post (X := V) F).IsContinuous (J.over V) (K.over (F.obj V))]
    (G : SheafOfModules.{u} R) (Q : SheafOfModules.{u} (S.over (F.obj V)))
    (z : ((pullback rho).obj G).over (F.obj V) ⟶ Q) (W : Over V)
    (x : G.val.obj (op W.left)) :
    (localHomEquiv J K F rho V G Q z).val.app (op W) x =
      z.val.app (op ((Over.post F).obj W))
        ((((pullbackPushforwardAdjunction rho).unit.app G).val.app (op W.left)) x) := by
  unfold localHomEquiv
  dsimp only [Equiv.trans_apply]
  erw [Adjunction.homEquiv_counit, Adjunction.homEquiv_ofNatIsoRight_apply]
  erw [Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply]
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hu (M : SheafOfModules.{u} S) (U : Dᵒᵖ) (y : M.val.obj U) :
      ((overPushforwardOverAdj (R := S) (F.obj V)).unit.app M).val.app U y =
        M.val.map prod.snd.op y := by
    unfold overPushforwardOverAdj
    rw [pushforwardPushforwardAdj_unit_app_val_app, Over.forgetAdjStar_counit_app]
    rfl
  change Q.val.map
      ((Over.post F).map ((Over.forgetAdjStar V).unit.app W)).op
      (Q.val.map ((postStarIso F V).inv.app W.left).op
        (z.val.app (op ((Over.star (F.obj V)).obj (F.obj W.left)))
          (((overPushforwardOverAdj (R := S) (F.obj V)).unit.app
            ((pullback rho).obj G)).val.app (op (F.obj W.left))
              ((((pullbackPushforwardAdjunction rho).unit.app G).val.app (op W.left)) x)))) = _
  rw [hu]
  let t : (Over.post F).obj W ⟶ (Over.star (F.obj V)).obj (F.obj W.left) :=
    (Over.post F).map ((Over.forgetAdjStar V).unit.app W) ≫
      (postStarIso F V).inv.app W.left
  erw [← PresheafOfModules.map_comp_apply, ← op_comp]
  change Q.val.map t.op (z.val.app _ _) = _
  erw [← PresheafOfModules.naturality_apply]
  change z.val.app (op ((Over.post F).obj W))
    (((pullback rho).obj G).val.map t.left.op
      (((pullback rho).obj G).val.map
        (prod.snd (X := F.obj V) (Y := F.obj W.left)).op
          ((((pullbackPushforwardAdjunction rho).unit.app G).val.app (op W.left)) x))) = _
  erw [← PresheafOfModules.map_comp_apply, ← op_comp]
  have ht : t.left ≫ prod.snd = 𝟙 (F.obj W.left) := by
    change (F.map ((Over.forgetAdjStar V).unit.app W).left ≫
      (PreservesLimitPair.iso F V W.left).hom) ≫ prod.snd = _
    rw [Category.assoc, PreservesLimitPair.iso_hom, prodComparison_snd, ← F.map_comp,
      Over.forgetAdjStar_unit_app_left, prod.lift_snd]
    exact F.map_id W.left
  erw [ht, op_id, PresheafOfModules.map_id]
  rfl

private theorem localHomEquiv_naturality {C D : Type u}
    [SmallCategory C] [SmallCategory D] [HasFiniteLimits C] [HasFiniteLimits D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] [PreservesFiniteLimits F]
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (rho : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj S) (V : C)
    [(Over.post (X := V) F).IsContinuous (J.over V) (K.over (F.obj V))]
    (G : SheafOfModules.{u} R) (Q Q' : SheafOfModules.{u} (S.over (F.obj V)))
    (z : ((pullback rho).obj G).over (F.obj V) ⟶ Q) (t : Q ⟶ Q') :
    localHomEquiv J K F rho V G Q' (z ≫ t) =
      localHomEquiv J K F rho V G Q z ≫ (pushforward (localMap J K F rho V)).map t := by
  ext W x
  erw [localHomEquiv_apply]
  change t.val.app _ (z.val.app _ _) =
    t.val.app _ ((localHomEquiv J K F rho V G Q z).val.app W x)
  erw [localHomEquiv_apply]
  rfl

/-- The normalized unit equation for transport of a local module trivialization.
Source: Stacks 093R. This shared predicate keeps the scalar restrictions abstract.
(blueprint: lem-sfb-normalized-local-module-pullback). -/
def NormalizedLocalModuleTrivialization
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (rho : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj S)
    (A G : SheafOfModules.{u} R) (B P : SheafOfModules.{u} S)
    (c : (pullback rho).obj A ⟶ B) (b : P ≅ (pullback rho).obj G)
    (V : C) (e : G.over V ≅ A.over V) : Prop :=
    ∃! d : P.over (F.obj V) ≅ B.over (F.obj V),
      ∀ (W : Over V) (x : G.val.obj (op W.left)),
        (d.hom.val.app (op ((Over.post F).obj W)))
          ((b.inv.val.app (op (F.obj W.left)))
            ((((pullbackPushforwardAdjunction rho).unit.app G).val.app (op W.left)) x)) =
          (((pullbackPushforwardAdjunction rho).homEquiv _ _ c).val.app (op W.left))
            ((e.hom.val.app (op W)) x)

/-- A chosen local isomorphism transports along the localized inverse image. The
normalization fixes the transport on the adjunction unit and determines it uniquely.
Source: Stacks Project, Modules on Sites, Tags 04J0 and 093R.
(blueprint: lem-sfb-normalized-local-module-pullback).

Proof: localize the continuous finite-limit-preserving functor at V. Its direct image
commutes with restriction, by the identity section maps. The mate of this comparison
identifies localized inverse image with restriction of inverse image. Apply localized
inverse image to e, then compose with the restriction of c and the restriction of b.
The mate identity gives the displayed equation on the adjunction unit. Conversely,
that equation determines the adjunct on the slice; injectivity of the localized
adjunction gives uniqueness. The construction and its inverse are module morphisms
with the prescribed scalar action rho, so the result is an isomorphism of modules. -/
theorem normalized_local_module_pullback
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] [PreservesFiniteLimits F]
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (rho : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj S)
    (A G : SheafOfModules.{u} R) (B P : SheafOfModules.{u} S)
    (c : (pullback rho).obj A ≅ B) (b : P ≅ (pullback rho).obj G)
    (V : C) (e : G.over V ≅ A.over V) :
    NormalizedLocalModuleTrivialization J K F rho A G B P c.hom b V e := by
  unfold NormalizedLocalModuleTrivialization
  have : RepresentablyFlat (Over.post (X := V) F) :=
    flat_of_preservesFiniteLimits _
  have : (Over.post (X := V) F).IsContinuous (J.over V) (K.over (F.obj V)) :=
    Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfFlat _ _) ((CoverPreserving.of_isContinuous F J K).overPost V)
  let C := (overFunctor S (F.obj V)).mapIso c
  let H := localHomEquiv J K F rho V A _ C.hom
  let z := (localHomEquiv J K F rho V G _).symm (e.hom ≫ H)
  have hz : localHomEquiv J K F rho V G _ z = e.hom ≫ H :=
    Equiv.apply_symm_apply _ _
  have hcompat (Q : SheafOfModules.{u} (S.over (F.obj V)))
      (t : B.over (F.obj V) ⟶ Q) :
      localHomEquiv J K F rho V G Q (z ≫ t) =
        e.hom ≫ localHomEquiv J K F rho V A Q (C.hom ≫ t) := by
    rw [localHomEquiv_naturality, hz, localHomEquiv_naturality, Category.assoc]
  have iz : IsIso z := by
    apply isIso_of_coyoneda_map_bijective z
    intro Q
    constructor
    · intro t t' ht
      apply (cancel_epi C.hom).1
      apply (localHomEquiv J K F rho V A Q).injective
      apply (cancel_epi e.hom).1
      rw [← hcompat, ← hcompat]
      exact congrArg (localHomEquiv J K F rho V G Q) ht
    · intro y
      let t := C.inv ≫ (localHomEquiv J K F rho V A Q).symm
        (e.inv ≫ localHomEquiv J K F rho V G Q y)
      refine ⟨t, ?_⟩
      apply (localHomEquiv J K F rho V G Q).injective
      rw [hcompat]
      dsimp only [t]
      rw [C.hom_inv_id_assoc, Equiv.apply_symm_apply, e.hom_inv_id_assoc]
  let d := (overFunctor S (F.obj V)).mapIso b ≪≫ asIso z
  have hd : (b.inv.over (F.obj V)) ≫ d.hom = z := by
    dsimp only [d, Iso.trans_hom, asIso_hom]
    change (overFunctor S (F.obj V)).map b.inv ≫
      (overFunctor S (F.obj V)).map b.hom ≫ z = z
    rw [← Functor.map_comp_assoc, b.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  refine ⟨d, ?_, ?_⟩
  · intro W x
    have h := congrArg (fun k ↦ k.val.app (op W) x) hz
    rw [localHomEquiv_apply] at h
    rw [← hd] at h
    have hc := localHomEquiv_apply J K F rho V A _ C.hom W
      (e.hom.val.app (op W) x)
    exact h.trans hc
  · intro d' hd'
    apply Iso.ext
    apply (cancel_epi (b.inv.over (F.obj V))).1
    rw [hd]
    apply (localHomEquiv J K F rho V G _).injective
    rw [hz]
    ext W x
    rw [localHomEquiv_apply]
    exact (hd' W.unop x).trans
      (localHomEquiv_apply J K F rho V A _ C.hom W.unop
        (e.hom.val.app W x)).symm

end SheafOfModules
