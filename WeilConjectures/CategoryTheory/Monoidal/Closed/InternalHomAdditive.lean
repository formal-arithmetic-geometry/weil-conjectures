/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison

/-!
# The internal hom bifunctor of a preadditive monoidal closed category is additive

In a preadditive monoidal closed category with `MonoidalPreadditive`, the internal hom
`MonoidalClosed.internalHom : Cᵒᵖ ⥤ C ⥤ C` is additive in each variable.
-/

@[expose] public section

namespace CategoryTheory.MonoidalClosed

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C]

/-- The internal hom bifunctor is additive in its first variable. -/
instance internalHom_additive : (internalHom (C := C)).Additive where
  map_add {_ _} f g := NatTrans.ext (funext fun X ↦ pre_add_app f.unop g.unop X)

instance (A : Cᵒᵖ) : ((internalHom (C := C)).obj A).Additive :=
  inferInstanceAs (ihom A.unop).Additive

end CategoryTheory.MonoidalClosed
