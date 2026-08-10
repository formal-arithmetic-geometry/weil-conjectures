/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Constant sheaves and localization of sites

The constant sheaf functor commutes with localization of a site at an object
(`CategoryTheory.GrothendieckTopology.overPullbackConstantSheafIso`); in particular the
restriction of a constant sheaf to a localized site is constant
(`CategoryTheory.Sheaf.isConstant_over`).

This file imports both `Mathlib.CategoryTheory.Sites.ConstantSheaf` and
`Mathlib.CategoryTheory.Sites.Over` since neither imports the other.
-/

@[expose] public section

universe v u'

open CategoryTheory Limits

noncomputable section

namespace CategoryTheory

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v} A] (W : C)
  [HasWeakSheafify J A] [HasWeakSheafify (J.over W) A]
  [∀ P : (Over W)ᵒᵖ ⥤ A, (Over.forget W).op.HasPointwiseRightKanExtension P]

/-- The constant sheaf functor commutes with localization of the site at an object:
the restriction of the constant sheaf at `a : A` to `J.over W` is the constant sheaf
at `a`. -/
def GrothendieckTopology.overPullbackConstantSheafIso :
    constantSheaf J A ⋙ J.overPullback A W ≅ constantSheaf (J.over W) A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const Cᵒᵖ)
      ((Over.forget W).pushforwardContinuousSheafificationCompatibility A (J.over W) J).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.constCompWhiskeringLeftIso _ (Over.forget W).op)
      (presheafToSheaf (J.over W) A)

variable {J A} in
/-- The restriction of a constant sheaf to the site localized at an object is
constant. -/
lemma Sheaf.isConstant_over (F : Sheaf J A) [F.IsConstant J] :
    (F.over W).IsConstant (J.over W) := by
  obtain ⟨a, ⟨e⟩⟩ := F.mem_essImage_of_isConstant
  exact Sheaf.isConstant_of_iso _
    ((J.overPullback A W).mapIso e.symm ≪≫ (J.overPullbackConstantSheafIso A W).app a)

end CategoryTheory
