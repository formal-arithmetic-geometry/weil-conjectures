/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Products.Basic

/-! # The double diagram of fraction numerators

Source: Stacks Project, Derived Categories, Tag 0FND, second and third equalities
(blueprint: def-pc-derived-adjunction-hom-diagram).
-/

@[expose] public section

universe u v u' v'

namespace CategoryTheory

/-- The numerator diagram indexed by an outgoing denominator and an incoming denominator.
A transition postcomposes by `F(a)` and precomposes by `b`.
Source: Stacks Project, Derived Categories, Tag 0FND, second and third equalities
(blueprint: def-pc-derived-adjunction-hom-diagram). -/
def derivedAdjunctionHomDiagram
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (W : MorphismProperty C) (W' : MorphismProperty D) (F : C ⥤ D) (K : C) (M : D) :
    (W.Under ⊤ K × (W'.Over ⊤ M)ᵒᵖ) ⥤ Type v' where
  obj j := j.2.unop.left ⟶ F.obj j.1.right
  map a := ↾fun f => a.2.unop.left ≫ f ≫ F.map a.1.right
  map_id j := by
    ext f
    simp
  map_comp a b := by
    ext f
    simp [Category.assoc]

end CategoryTheory
