/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Morphisms of triangles induced by natural transformations

A natural transformation `τ : F₁ ⟶ F₂` between functors commuting with the shifts by `ℤ`
which is itself compatible with the shifts induces a natural transformation
`F₁.mapTriangle ⟶ F₂.mapTriangle` (`CategoryTheory.NatTrans.mapTriangle`): its component at a
triangle `T` is the morphism of triangles with components `τ.app T.obj₁`, `τ.app T.obj₂` and
`τ.app T.obj₃`. This is the counterpart for morphisms of Mathlib's
`CategoryTheory.Functor.mapTriangleIso`.
-/

@[expose] public section

namespace CategoryTheory.NatTrans

open Category Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  {F₁ F₂ : C ⥤ D} [F₁.CommShift ℤ] [F₂.CommShift ℤ]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A natural transformation `τ : F₁ ⟶ F₂` compatible with the shifts induces a natural
transformation `F₁.mapTriangle ⟶ F₂.mapTriangle`, whose components are the morphisms of
triangles with components `τ.app T.obj₁`, `τ.app T.obj₂` and `τ.app T.obj₃`. -/
@[simps!]
def mapTriangle (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] : F₁.mapTriangle ⟶ F₂.mapTriangle where
  app T := Triangle.homMk _ _ (τ.app _) (τ.app _) (τ.app _) (by simp) (by simp) (by
    dsimp
    simp only [assoc, NatTrans.shift_app_comm τ (1 : ℤ) T.obj₁, NatTrans.naturality_assoc])
  naturality T T' f := by
    apply Triangle.hom_ext <;> simp

end CategoryTheory.NatTrans
