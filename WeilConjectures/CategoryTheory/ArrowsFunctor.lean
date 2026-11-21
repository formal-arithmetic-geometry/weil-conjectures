/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # The set of arrows as a functor on categories

## Main definitions

* `CategoryTheory.Cat.arrows`: the set-valued functor of all arrows.

## Main results

* `CategoryTheory.Cat.arrows_map_id`: identity preserves every arrow.
* `CategoryTheory.Cat.arrows_map_comp`: composition acts by successive arrow maps.

## References

* Stacks Project, Sites, proof of Tag 09YL.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Cat

/-- The identity functor acts identically on arrows. -/
theorem arrows_map_id (C : Cat.{v, u}) :
    (fun a : Arrow C ↦ Arrow.mk ((𝟭 C).map a.hom)) = id := by
  funext a
  simp

/-- Composition acts by successive arrow maps. -/
theorem arrows_map_comp {C D E : Cat.{v, u}} (f : C ⟶ D) (g : D ⟶ E) :
    (fun a : Arrow C ↦ Arrow.mk ((f ≫ g).toFunctor.map a.hom)) =
      (fun a : Arrow D ↦ Arrow.mk (g.toFunctor.map a.hom)) ∘
        (fun a : Arrow C ↦ Arrow.mk (f.toFunctor.map a.hom)) := by
  funext a
  rfl

/-- A category is sent to the set of all its arrows,
and a functor sends an arrow to its image, including its source and target. -/
def arrows : Cat.{v, u} ⥤ Type (max u v) where
  obj C := Arrow C
  map f := ↾fun a ↦ Arrow.mk (f.toFunctor.map a.hom)
  map_id C := congrArg (fun f ↦ TypeCat.ofHom f) (arrows_map_id C)
  map_comp f g := congrArg (fun f ↦ TypeCat.ofHom f) (arrows_map_comp f g)

end CategoryTheory.Cat
