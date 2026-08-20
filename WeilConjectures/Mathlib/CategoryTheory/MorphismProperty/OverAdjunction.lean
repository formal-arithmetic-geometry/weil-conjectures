/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Fully faithfulness of `MorphismProperty.Over.map`

The functor `MorphismProperty.Over.map` given by post-composition with a morphism
satisfying `P` is always faithful (`CategoryTheory.MorphismProperty.Over.faithful_map`),
and it is full when the morphism is a monomorphism
(`CategoryTheory.MorphismProperty.Over.full_map`).
-/

@[expose] public section

open CategoryTheory Category

namespace CategoryTheory

variable {T : Type*} [Category T] {P Q : MorphismProperty T} [Q.IsMultiplicative]
  [P.IsStableUnderComposition] {X Y : T} {f : X ⟶ Y} (hPf : P f)

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

end CategoryTheory
