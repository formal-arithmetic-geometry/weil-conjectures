module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {M : D ⥤ C} {R : C ⥤ D} (adj : M ⊣ R) (EX : C ≌ C) (EY : D ≌ D)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
lemma test_aux (β : M ⋙ EX.functor ≅ EY.functor ⋙ M) :
    (mateEquiv EX.symm.toAdjunction EY.symm.toAdjunction
      (mateEquiv adj adj (mateEquiv EY.toAdjunction EX.toAdjunction
        (TwoSquare.mk _ _ _ _ β.hom)))).natTrans ≫
      (mateEquiv adj adj (TwoSquare.mk _ _ _ _ β.inv)).natTrans = 𝟙 _ := by
  ext c
  simp

