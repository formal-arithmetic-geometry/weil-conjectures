/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Morphisms of pullbacks induced by a morphism of one leg

If only one of the two legs of a cospan is changed, the induced morphism of pullbacks is a
base change of the morphism of legs: `CategoryTheory.Limits.isPullback_pullback_map` for the
second leg and `CategoryTheory.Limits.isPullback_pullback_map_left` for the first one.
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [HasPullbacks C]

/-- The morphism induced on pullbacks by a morphism of the second leg of the cospan is a base
change of that morphism. -/
lemma isPullback_pullback_map {Y T A B : C} (p : Y ⟶ T) (u : A ⟶ T) (v : B ⟶ T) (w : A ⟶ B)
    (hw : w ≫ v = u) :
    IsPullback (pullback.map p u p v (𝟙 Y) w (𝟙 T) (by simp) (by simp [hw]))
      (pullback.snd p u) (pullback.snd p v) w := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback p v)
  have h : pullback.map p u p v (𝟙 Y) w (𝟙 T) (by simp) (by simp [hw]) ≫ pullback.fst p v =
      pullback.fst p u := by simp
  rw [h]
  simpa [hw] using IsPullback.of_hasPullback p u

/-- The morphism induced on pullbacks by a morphism of the first leg of the cospan is a base
change of that morphism. -/
lemma isPullback_pullback_map_left {A B T S : C} (m : A ⟶ B) (p : B ⟶ T) (π : S ⟶ T) :
    IsPullback (pullback.fst (m ≫ p) π)
      (pullback.map (m ≫ p) π p π m (𝟙 S) (𝟙 T) (by simp) (by simp)) m (pullback.fst p π) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback p π)
  have h : pullback.map (m ≫ p) π p π m (𝟙 S) (𝟙 T) (by simp) (by simp) ≫ pullback.snd p π =
      pullback.snd (m ≫ p) π := by simp
  rw [h]
  exact IsPullback.of_hasPullback (m ≫ p) π

end CategoryTheory.Limits
