/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
import Sheaf.CategoryTheory.Galois.StacksGaloisCategory
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Morphisms between finite coproducts of connected objects

Source: Stacks Project, Fundamental Groups of Schemes, Lemma 0BN0, item (8) and proof
(blueprint: lem-galois-coproduct-morphism-components).
-/

universe u v w x y

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace CategoryTheory

/-- Source: Stacks Project, Fundamental Groups of Schemes, Lemma 0BN0, item (8)
(blueprint: lem-galois-coproduct-morphism-components). A morphism between finite
coproducts of connected objects is induced by a map of indices and component maps.

Proof: Exactness of `F` sends both coproducts to disjoint unions and an initial
object to the empty set. A connected object has a nonempty fibre, since `F`
reflects isomorphisms. Each target coprojection is mono because `F` sends it to
an injection. For each pair of indices, pull back the target coprojection along
the source component map. Its projection to the connected source component is
mono, so its domain is initial or the projection is an isomorphism. Choose a
point in the source fibre; its image lies in a unique target summand. Exactness
on pullbacks shows that the corresponding pullback has a point, hence is not
initial, so its projection is an isomorphism. Compose the other pullback
projection with its inverse to obtain the component map. The pullback square
gives the displayed equality, and coproduct uniqueness identifies the induced
map with the original morphism. For an empty source index, use the empty map. -/
theorem morphism_coproduct_connected_components
    {C : Type u} [Category.{v} C] (F : C ⥤ Type w)
    (hG : IsStacksGaloisCategory F)
    {α : Type x} {β : Type y} [Finite α] [Finite β]
    {X Y : C} {Xᵢ : α → C} {Yⱼ : β → C}
    {ι : (i : α) → Xᵢ i ⟶ X} {κ : (j : β) → Yⱼ j ⟶ Y}
    (hX : IsColimit (Cofan.mk X ι))
    (hY : IsColimit (Cofan.mk Y κ))
    (hXconn : ∀ i, IsConnected (Xᵢ i))
    (hYconn : ∀ j, IsConnected (Yⱼ j))
    (φ : X ⟶ Y) :
    ∃ (a : α → β) (φᵢ : (i : α) → Xᵢ i ⟶ Yⱼ (a i)),
      ∀ i, ι i ≫ φ = φᵢ i ≫ κ (a i) := by
  sorry

end CategoryTheory
