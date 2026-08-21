/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# Strong monoidal functors send exact pairings to exact pairings

Mathlib's `Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence` pulls back exact pairings
and duals along (faithful, fully faithful) monoidal functors. This file records the
forward direction: a strong monoidal functor `F` sends an exact pairing `X Y` to an exact
pairing `F.obj X` `F.obj Y`, by conjugating the evaluation and coevaluation with the
monoidal structure isomorphisms of `F`. Consequently `F` sends objects with a (left/right)
dual to objects with a (left/right) dual.

## Main declarations

- `CategoryTheory.ExactPairing.map`: a strong monoidal functor sends an exact pairing to
  an exact pairing.
- `CategoryTheory.HasLeftDual.map`, `CategoryTheory.HasRightDual.map`: a strong monoidal
  functor sends an object with a left (right) dual to an object with a left (right) dual,
  with `ᘁ(F.obj Y) = F.obj ᘁY` and `(F.obj X)ᘁ = F.obj Xᘁ`.

Note that no rigidity image statement is possible for a general strong monoidal functor
(its image need not be closed under duals of objects outside the image), but an
essentially surjective strong monoidal functor out of a rigid category has rigid target;
this follows from the declarations here together with `exactPairingCongrLeft` and
`exactPairingCongrRight`.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- A strong monoidal functor sends an exact pairing to an exact pairing, conjugating the
coevaluation and evaluation with the monoidal structure isomorphisms. -/
@[implicit_reducible]
def ExactPairing.map (X Y : C) [ExactPairing X Y] : ExactPairing (F.obj X) (F.obj Y) where
  coevaluation' := ε F ≫ F.map (η_ X Y) ≫ δ F X Y
  evaluation' := μ F Y X ≫ F.map (ε_ X Y) ≫ η F
  coevaluation_evaluation' := by
    simp only [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight,
      Category.assoc, Functor.Monoidal.map_associator_inv',
      Functor.Monoidal.whiskerLeft_δ_μ_assoc, Functor.Monoidal.whiskerRight_δ_μ_assoc,
      μ_natural_right_assoc, δ_natural_left_assoc]
    slice_lhs 3 5 => rw [← F.map_comp, ← F.map_comp, ExactPairing.coevaluation_evaluation]
    simp
  evaluation_coevaluation' := by
    simp only [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight,
      Category.assoc, Functor.Monoidal.map_associator',
      Functor.Monoidal.whiskerLeft_δ_μ_assoc, Functor.Monoidal.whiskerRight_δ_μ_assoc,
      μ_natural_left_assoc, δ_natural_right_assoc]
    slice_lhs 3 5 => rw [← F.map_comp, ← F.map_comp, ExactPairing.evaluation_coevaluation]
    simp

/-- A strong monoidal functor sends an object with a left dual to an object with a left
dual, with `ᘁ(F.obj Y) = F.obj ᘁY`. -/
@[implicit_reducible]
def HasLeftDual.map (Y : C) [HasLeftDual Y] : HasLeftDual (F.obj Y) where
  leftDual := F.obj (ᘁY)
  exact := ExactPairing.map F (ᘁY) Y

/-- A strong monoidal functor sends an object with a right dual to an object with a right
dual, with `(F.obj X)ᘁ = F.obj Xᘁ`. -/
@[implicit_reducible]
def HasRightDual.map (X : C) [HasRightDual X] : HasRightDual (F.obj X) where
  rightDual := F.obj (Xᘁ)
  exact := ExactPairing.map F X (Xᘁ)

end CategoryTheory
