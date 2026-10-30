/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.FintypeCat

/-!
# Natural isomorphisms of functors to finite types

## Main results

- `CategoryTheory.FintypeCat.inv_app_hom_app_apply`: the components of the inverse of a natural
  isomorphism of functors to `FintypeCat` undo those of the isomorphism, pointwise.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.FintypeCat

/-- The components of the inverse of a natural isomorphism of functors to finite types undo those
of the isomorphism, pointwise. -/
@[simp]
lemma inv_app_hom_app_apply {C : Type u} [Category.{v} C] {F G : C ⥤ FintypeCat.{w}} (e : F ≅ G)
    (X : C) (x : F.obj X) : e.inv.app X (e.hom.app X x) = x :=
  ConcreteCategory.congr_hom (e.hom_inv_id_app X) x

end CategoryTheory.FintypeCat
