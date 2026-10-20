/- Copyright (c) 2026 The SHEAF contributors. All rights reserved. -/
module

public import Sheaf.Paper.RingedRefinementData

/-!
# Canonical proper/open refinement shape

(blueprint: lem-pur-ringed-refinement-coefficient-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedRefinement

set_option backward.isDefEq.respectTransparency true in
/-- The actual scheme pullback and its distinguished clopen section, regarded over T.
Source: Bhatt--Scholze 6.7.6--6.7.7; Stacks 0F7B
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def canonicalShape {T : Scheme.{u}} {X Y Z : Over T} (f : Y ⟶ Z)
    (j₁ : X ⟶ Y) (j₂ : X ⟶ Z) [IsProper f.left]
    [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left] (h : j₁ ≫ f = j₂) :
    Shape f j₁ j₂ := by
  let h' : j₁.left ≫ f.left = j₂.left := congrArg (fun a ↦ a.left) h
  let P := Limits.pullback f.left j₂.left
  let b : P ⟶ Y.left := pullback.fst _ _
  let q : P ⟶ X.left := pullback.snd _ _
  let s := Etale.properOpenSection f.left j₁.left j₂.left h'
  have hb : b ≫ Y.hom = q ≫ X.hom := by
    rw [← Over.w f, ← Category.assoc, pullback.condition, Category.assoc, Over.w j₂]
  let V : Over T := Over.mk (b ≫ Y.hom)
  let b' : V ⟶ Y := Over.homMk b
  let q' : V ⟶ X := Over.homMk q hb.symm
  have hs : s ≫ b = j₁.left := by
    unfold s Etale.properOpenSection b
    exact pullback.lift_fst _ _ _
  let s' : X ⟶ V := Over.homMk s (by simp [V, ← Category.assoc, hs])
  obtain ⟨hsopen, hsret, hsclopen, _, hbopen, _⟩ :=
    Etale.properOpenSectionProperties f.left j₁.left j₂.left h'
  refine { V := V
           b := b'
           q := q'
           s := s'
           pullback := ?_
           schemePullback := IsPullback.of_hasPullback _ _
           retraction := ?_
           openFactor := ?_
           b_open := hbopen
           s_open := hsopen
           clopen := hsclopen }
  · have comm : b' ≫ f = q' ≫ j₂ := by
      apply Over.OverMorphism.ext
      exact pullback.condition
    refine ⟨⟨comm⟩, ⟨?_⟩⟩
    refine PullbackCone.IsLimit.mk comm (fun t ↦
      Over.homMk (pullback.lift t.fst.left t.snd.left
        (congrArg (fun a ↦ a.left) t.condition)) ?_) ?_ ?_ ?_
    · change pullback.lift _ _ _ ≫ (b ≫ Y.hom) = t.pt.hom
      rw [← Category.assoc, pullback.lift_fst]
      exact Over.w t.fst
    · intro t
      apply Over.OverMorphism.ext
      exact pullback.lift_fst t.fst.left t.snd.left _
    · intro t
      apply Over.OverMorphism.ext
      exact pullback.lift_snd t.fst.left t.snd.left _
    · intro t a ha hb
      apply Over.OverMorphism.ext
      apply pullback.hom_ext (f := f.left) (g := j₂.left)
      · exact (congrArg (fun a ↦ a.left) ha).trans
          (pullback.lift_fst (f := f.left) (g := j₂.left) t.fst.left t.snd.left _).symm
      · exact (congrArg (fun a ↦ a.left) hb).trans
          (pullback.lift_snd (f := f.left) (g := j₂.left) t.fst.left t.snd.left _).symm
  · apply Over.OverMorphism.ext
    exact hsret
  · apply Over.OverMorphism.ext
    exact hs


end SheafOfModules.RingedRefinement
