/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Tensoring with a zero object in a closed monoidal category

In a monoidal closed category with zero morphisms, `K ⊗ M` is a zero object if `M` is, since
`K ⊗ -` is a left adjoint. If the category is moreover braided, the same holds if `K` is a
zero object.
-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

open Limits

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C] [HasZeroMorphisms C]

/-- In a monoidal closed category, `K ⊗ M` is a zero object if `M` is. -/
lemma isZero_tensorObj_of_isZero_right (K : C) {M : C} (hM : IsZero M) : IsZero (K ⊗ M) := by
  rw [IsZero.iff_id_eq_zero]
  exact ((ihom.adjunction K).homEquiv _ _).injective (hM.eq_of_src _ _)

/-- In a braided monoidal closed category, `K ⊗ M` is a zero object if `K` is. -/
lemma isZero_tensorObj_of_isZero_left [BraidedCategory C] {K : C} (hK : IsZero K) (M : C) :
    IsZero (K ⊗ M) :=
  (isZero_tensorObj_of_isZero_right M hK).of_iso (β_ K M)

end CategoryTheory.MonoidalCategory
