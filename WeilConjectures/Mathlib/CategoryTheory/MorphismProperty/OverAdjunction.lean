/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Fully faithfulness of `MorphismProperty.Over.map`, and base change squares

The functor `MorphismProperty.Over.map` given by post-composition with a morphism
satisfying `P` is always faithful (`CategoryTheory.MorphismProperty.Over.faithful_map`),
and it is full when the morphism is a monomorphism
(`CategoryTheory.MorphismProperty.Over.full_map`).

Base change along a morphism `f : X ⟶ Y` sends a morphism of `P.Over Q Y` to a cartesian
square (`CategoryTheory.MorphismProperty.Over.isPullback_map_left`). Base change along an equality
`f = g` is compatible with the second projections
(`CategoryTheory.MorphismProperty.Over.pullbackCongr_hom_app_left_snd`).
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory

variable {T : Type*} [Category T] {P Q : MorphismProperty T} [Q.IsMultiplicative]
  {X Y : T}

section Map

variable [P.IsStableUnderComposition] {f : X ⟶ Y} (hPf : P f)

/-- The functor `MorphismProperty.Over.map` given by post-composition with `f` is always
faithful: it acts as the identity on the underlying morphisms. -/
instance MorphismProperty.Over.faithful_map : (MorphismProperty.Over.map Q hPf).Faithful where
  map_injective {A B} {φ ψ} h := by
    apply MorphismProperty.Over.Hom.ext
    have h' : ((MorphismProperty.Over.map Q hPf).map φ).left =
        ((MorphismProperty.Over.map Q hPf).map ψ).left := by rw [h]
    simpa using h'

/-- For a monomorphism `f`, the functor `MorphismProperty.Over.map` given by
post-composition with `f` is full: the compatibility with the structure morphisms over
the target can be cancelled along `f`. -/
instance MorphismProperty.Over.full_map [Mono f] : (MorphismProperty.Over.map Q hPf).Full where
  map_surjective {A B} ψ := by
    refine ⟨MorphismProperty.Over.homMk ψ.left ?_ ψ.prop_hom_left, ?_⟩
    · rw [← cancel_mono f]
      simpa using MorphismProperty.Over.w ψ
    · apply MorphismProperty.Over.Hom.ext
      simp

end Map

section Pullback

variable [Q.IsStableUnderBaseChange] (f : X ⟶ Y) [P.HasPullbacksAlong f]
  [P.IsStableUnderBaseChangeAlong f]

/-- Base change along `f : X ⟶ Y` sends a morphism `φ : A ⟶ B` of `P.Over Q Y` to a
cartesian square: it exhibits `A ×_Y X` as the fibre product of `A` and `B ×_Y X` over `B`.

```
  A ×_Y X ──(Over.pullback P Q f).map φ──→ B ×_Y X
     │                                        │
     │ pullback.fst A.hom f                   │ pullback.fst B.hom f
     ↓                                        ↓
     A ──────────────── φ.left ─────────────→ B
```
-/
lemma MorphismProperty.Over.isPullback_map_left {A B : P.Over Q Y} (φ : A ⟶ B) :
    IsPullback (pullback.fst A.hom f) ((MorphismProperty.Over.pullback P Q f).map φ).left φ.left
      (pullback.fst B.hom f) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback B.hom f)
  have h : ((MorphismProperty.Over.pullback P Q f).map φ).left ≫ pullback.snd B.hom f =
      pullback.snd A.hom f := by
    simp
  rw [h, MorphismProperty.Over.w φ]
  exact IsPullback.of_hasPullback A.hom f

end Pullback

section PullbackCongr

set_option backward.defeqAttrib.useBackward true in
/-- The base change isomorphism along an equality `f = g` is compatible with the second
projections. This complements mathlib's
`CategoryTheory.MorphismProperty.Over.pullbackCongr_hom_app_left_fst`. -/
@[reassoc (attr := simp)]
lemma MorphismProperty.Over.pullbackCongr_hom_app_left_snd {f g : X ⟶ Y}
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] [Q.IsStableUnderBaseChange]
    (h : f = g) (B : P.Over Q Y) :
    haveI : P.HasPullbacksAlong g := by subst h; infer_instance
    ((MorphismProperty.Over.pullbackCongr h).hom.app B).left ≫ pullback.snd B.hom g =
      pullback.snd B.hom f := by
  subst h
  simp [MorphismProperty.Over.pullbackCongr]

end PullbackCongr

end CategoryTheory
