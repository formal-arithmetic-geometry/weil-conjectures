/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

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
- `CategoryTheory.Functor.Monoidal.mapRightDualIso`,
  `CategoryTheory.Functor.Monoidal.mapLeftDualIso`: a strong monoidal functor commutes
  with duals, i.e. whenever both `X` and `F.obj X` have chosen duals, the image of the
  dual is canonically isomorphic to the dual of the image.
- `CategoryTheory.Functor.Monoidal.ihomNatIsoOfHasLeftDual`,
  `CategoryTheory.Functor.Monoidal.ihomIsoOfHasLeftDual`: a strong monoidal functor
  preserves the internal hom out of a dualizable closed object,
  `F.obj ((ihom Y).obj X) ≅ (ihom (F.obj Y)).obj (F.obj X)`, since on both sides the
  internal hom is tensoring with the left dual
  (`CategoryTheory.MonoidalClosed.leftDualTensorNatIsoIhom`) and `F` commutes with
  tensoring and with duals.

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

namespace Functor.Monoidal

/-- A strong monoidal functor commutes with right duals: if both `X` and `F.obj X` have
chosen right duals, the image of the right dual of `X` is canonically isomorphic to the
right dual of the image, since both are right duals of `F.obj X`. -/
def mapRightDualIso (X : C) [HasRightDual X] [HasRightDual (F.obj X)] :
    F.obj (Xᘁ) ≅ (F.obj X)ᘁ :=
  rightDualIso (ExactPairing.map F X (Xᘁ)) HasRightDual.exact

/-- A strong monoidal functor commutes with left duals: if both `Y` and `F.obj Y` have
chosen left duals, the image of the left dual of `Y` is canonically isomorphic to the
left dual of the image, since both are left duals of `F.obj Y`. -/
def mapLeftDualIso (Y : C) [HasLeftDual Y] [HasLeftDual (F.obj Y)] :
    F.obj (ᘁY) ≅ ᘁ(F.obj Y) :=
  leftDualIso (ExactPairing.map F (ᘁY) Y) HasLeftDual.exact

/-- A strong monoidal functor preserves the internal hom out of a closed object with a
left dual, naturally in the second argument: on both sides the internal hom is tensoring
with the left dual (`CategoryTheory.MonoidalClosed.leftDualTensorNatIsoIhom`), and `F`
commutes with tensoring (`CategoryTheory.Functor.Monoidal.commTensorLeft`) and with
duals (`CategoryTheory.Functor.Monoidal.mapLeftDualIso`). -/
noncomputable def ihomNatIsoOfHasLeftDual (Y : C) [Closed Y] [HasLeftDual Y]
    [Closed (F.obj Y)] [HasLeftDual (F.obj Y)] :
    ihom Y ⋙ F ≅ F ⋙ ihom (F.obj Y) :=
  isoWhiskerRight (MonoidalClosed.leftDualTensorNatIsoIhom Y).symm F ≪≫
    (commTensorLeft F (ᘁY)).symm ≪≫
    isoWhiskerLeft F ((curriedTensor D).mapIso (mapLeftDualIso F Y)) ≪≫
    isoWhiskerLeft F (MonoidalClosed.leftDualTensorNatIsoIhom (F.obj Y))

/-- A strong monoidal functor preserves the internal hom out of a closed object with a
left dual: `F [Y, X] ≅ [F Y, F X]`. -/
noncomputable def ihomIsoOfHasLeftDual (Y X : C) [Closed Y] [HasLeftDual Y]
    [Closed (F.obj Y)] [HasLeftDual (F.obj Y)] :
    F.obj ((ihom Y).obj X) ≅ (ihom (F.obj Y)).obj (F.obj X) :=
  (ihomNatIsoOfHasLeftDual F Y).app X

end Functor.Monoidal

end CategoryTheory
