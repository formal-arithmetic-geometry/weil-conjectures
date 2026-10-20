/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-! A small categorical bridge used by the closed-costalk comparison.

Source: the adjunction uniqueness step in the proof of
`lem-weil-closed-costalk-duality`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

/-- Two right adjoints of the same functor are naturally isomorphic.

This is the exact Yoneda/adjunction step needed after the tensor-Hom and
exceptional-adjunction calculations.
(blueprint: lem-weil-common-left-adjunctions-iso). -/
theorem nonempty_iso_of_common_left_adjunctions
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    (F : C ⥤ D) {G H : D ⥤ C} (a : F ⊣ G) (b : F ⊣ H) :
    Nonempty (G ≅ H) := by
  exact ⟨Adjunction.rightAdjointUniq a b⟩

