/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.CategoryTheory.ColimitSiteRawFiniteEqualityStabilization
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sigma

/-! # Finite raw overlap refinement

Source: Stacks Project, Sites, Tag 0A35.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem raw_arrow_transport {C : Type u} [Category.{u} C]
    (H : Cᵒᵖ ⥤ Type u) {X Y : C} (e : X = Y) {S : Type u}
    (a : S ⟶ H.obj (op Y)) (b : S ⟶ H.obj (op X))
    (h : Arrow.mk a = Arrow.mk b) : b = a ≫ H.map (eqToHom e).op := by
  subst Y
  obtain ⟨hx, hy, hh⟩ := (Arrow.mk_eq_mk_iff a b).mp h
  simpa using hh.symm

set_option linter.unusedVariables false in
/-- Stage sections `s` on a finite stage cover of `W` whose images in the colimit of the
Kan-extended stage presheaves `B` form a compatible family are, at some later stage `t'`,
represented by a compatible family `s'` of stage sections with the same images.

Source: Stacks Project, Sites, Tag 0A35, the finite overlap-equation calculation before stage
gluing. -/
theorem colimit_site_raw_finite_matching_refinement
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasPullbacks]
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck (Type u))
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
                        (sheafPullback (F.map t.hom).toFunctor (Type u)
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor (Type u)
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))))
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
    (β : ∀ t : Under i,
      ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' b).hom.app (op X) ≫
        (β t').app (op ((F.map b.right).toFunctor.obj X))))
    (t : Under i) (W : F.obj t.right) (I : Type u) [Finite I]
    (Y : I → F.obj t.right) (f : ∀ p, Y p ⟶ W)
    (hf : Presieve.ofArrows Y f ∈ P t.right W)
    (s : ∀ p, ((sheafPullback (F.map t.hom).toFunctor (Type u)
      (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj (op (Y p)))
    (hs : Presieve.Arrows.Compatible ((V.ι.app t.right).toFunctor.op ⋙ colimit B) f
      (fun p ↦ (colimit.ι B t).app (op ((V.ι.app t.right).toFunctor.obj (Y p)))
        ((β t).app (op (Y p)) (s p)))) :
    ∃ (t' : Under i) (b : t ⟶ t')
      (e : ∀ U : F.obj t.right,
        (V.ι.app t'.right).toFunctor.obj ((F.map b.right).toFunctor.obj U) =
          (V.ι.app t.right).toFunctor.obj U)
      (s' : ∀ p, ((sheafPullback (F.map t'.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj.obj
          (op ((F.map b.right).toFunctor.obj (Y p)))),
      Presieve.Arrows.Compatible
        ((sheafPullback (F.map t'.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj
        (fun p ↦ (F.map b.right).toFunctor.map (f p)) s' ∧
      ∀ p, (colimit.ι B t').app
        (op ((V.ι.app t'.right).toFunctor.obj ((F.map b.right).toFunctor.obj (Y p))))
        ((β t').app (op ((F.map b.right).toFunctor.obj (Y p))) (s' p)) =
      (colimit B).map (eqToHom (e (Y p))).op
        ((colimit.ι B t).app (op ((V.ι.app t.right).toFunctor.obj (Y p)))
          ((β t).app (op (Y p)) (s p))) := by
  classical
  clear hcover
  let A : ∀ v : Under i, (F.obj v.right)ᵒᵖ ⥤ Type u := fun v ↦
    ((sheafPullback (F.map v.hom).toFunctor (Type u)
      (P i).toGrothendieck (P v.right).toGrothendieck).obj G).obj
  let ρ : A t ⟶ (V.ι.app t.right).toFunctor.op ⋙ colimit B :=
    β t ≫ Functor.whiskerLeft (V.ι.app t.right).toFunctor.op (colimit.ι B t)
  let : (Presieve.ofArrows Y f).HasPairwisePullbacks :=
    (P t.right).hasPairwisePullbacks_of_mem hf
  let X : I × I → F.obj t.right := fun p ↦ pullback (f p.1) (f p.2)
  let r : ∀ p, (A t).obj (op (X p)) := fun p ↦
    (A t).map (pullback.fst (f p.1) (f p.2)).op (s p.1)
  let z : ∀ p, (A t).obj (op (X p)) := fun p ↦
    (A t).map (pullback.snd (f p.1) (f p.2)).op (s p.2)
  have hsρ : Presieve.Arrows.Compatible
      ((V.ι.app t.right).toFunctor.op ⋙ colimit B) f
      (fun p ↦ ρ.app (op (Y p)) (s p)) := by
    simpa [ρ, NatTrans.comp_app, Functor.whiskerLeft] using hs
  have hrz : ∀ p, ρ.app (op (X p)) (r p) = ρ.app (op (X p)) (z p) := by
    intro p
    have h₁ := congrArg (fun k ↦ k (s p.1))
      (ρ.naturality (pullback.fst (f p.1) (f p.2)).op)
    have h₂ := congrArg (fun k ↦ k (s p.2))
      (ρ.naturality (pullback.snd (f p.1) (f p.2)).op)
    simp only [types_comp_apply] at h₁ h₂
    exact h₁.trans ((hsρ p.1 p.2 _ _ _ pullback.condition).trans h₂.symm)
  obtain ⟨t', b, hb⟩ := colimit_site_raw_finite_equality_stabilization
    J F P V hobjects harrows Q i G θ hθ B β hβ hβmap t (I × I) X r z
      (by simpa [ρ, NatTrans.comp_app, Functor.whiskerLeft] using hrz)
  let T := (F.map b.right).toFunctor
  let s' : ∀ p, (A t').obj (op (T.obj (Y p))) := fun p ↦
    (θ t t' b).hom.app (op (Y p)) (s p)
  have he : ∀ U : F.obj t.right,
      (V.ι.app t'.right).toFunctor.obj (T.obj U) =
        (V.ι.app t.right).toFunctor.obj U := by
    intro U
    exact congrArg (fun c : F.obj t.right ⟶ V.pt ↦ c.toFunctor.obj U)
      (V.w b.right)
  refine ⟨t', b, he, s', ?_, ?_⟩
  · intro p q Z gp gq hpq
    let : PreservesLimit (cospan (f p) (f q)) T :=
      hpullback t.right t'.right b.right W (Y p) (Y q)
        (Presieve.ofArrows Y f) hf (f p) (f q) (Presieve.ofArrows.mk p)
    let L := isLimitOfHasPullbackOfPreservesLimit T (f p) (f q)
    let l := PullbackCone.IsLimit.lift L gp gq hpq
    have h₁ := congrArg (fun k ↦ k (s p))
      ((θ t t' b).hom.naturality (pullback.fst (f p) (f q)).op)
    have h₂ := congrArg (fun k ↦ k (s q))
      ((θ t t' b).hom.naturality (pullback.snd (f p) (f q)).op)
    have hx : (A t').map (T.map (pullback.fst (f p) (f q))).op (s' p) =
        (A t').map (T.map (pullback.snd (f p) (f q))).op (s' q) :=
      h₁.symm.trans ((hb (p, q)).trans h₂)
    have hl₁ : l ≫ T.map (pullback.fst (f p) (f q)) = gp :=
      PullbackCone.IsLimit.lift_fst L gp gq hpq
    have hl₂ : l ≫ T.map (pullback.snd (f p) (f q)) = gq :=
      PullbackCone.IsLimit.lift_snd L gp gq hpq
    rw [← hl₁, ← hl₂, op_comp, op_comp, Functor.map_comp, Functor.map_comp]
    exact congrArg (fun a ↦ (A t').map l.op a) hx
  · intro p
    have hβeq := raw_arrow_transport (B.obj t') (he (Y p))
      ((β t).app (op (Y p)) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj (Y p))))
      ((θ t t' b).hom.app (op (Y p)) ≫
        (β t').app (op (T.obj (Y p)))) (hβmap t t' b (Y p))
    have hn := (colimit.ι B t').naturality (eqToHom (he (Y p))).op
    have hw := congrArg
      (fun τ ↦ τ.app (op ((V.ι.app t.right).toFunctor.obj (Y p)))) (colimit.w B b)
    simp only [NatTrans.comp_app] at hw
    change (((θ t t' b).hom.app (op (Y p)) ≫
      (β t').app (op (T.obj (Y p)))) ≫
      (colimit.ι B t').app (op ((V.ι.app t'.right).toFunctor.obj (T.obj (Y p)))))
        (s p) = _
    rw [hβeq, Category.assoc, hn, ← Category.assoc]
    rw [Category.assoc ((β t).app (op (Y p))), hw]
    rfl

end CategoryTheory
