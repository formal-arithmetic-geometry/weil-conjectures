/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Exact.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v w t

/-- Coordinatewise exactness implies exactness of the induced maps on inverse limits;
with surjective kernel transitions the second induced map is surjective.
Source: Stacks Project, Algebra Lemma 03CA and Homology Lemma 02N1.
(blueprint: new-tower-limit-exact-coordinate-maps).
-/
theorem tower_limit_exact_of_coordinate_maps
    (R : Type u) [CommRing R]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} R) (G : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    (H : ℕᵒᵖ ⥤ ModuleCat.{t} R)
    (α : ∀ n : ℕ, F.obj (Opposite.op n) →ₗ[R] G.obj (Opposite.op n))
    (β : ∀ n : ℕ, G.obj (Opposite.op n) →ₗ[R] H.obj (Opposite.op n))
    (hshort : ∀ n : ℕ, Function.Injective (α n) ∧ Function.Exact (α n) (β n) ∧
      Function.Surjective (β n))
    (U : ↑(limit F) →ₗ[R] ↑(limit G)) (V : ↑(limit G) →ₗ[R] ↑(limit H))
    (hU : ∀ (n : ℕ) (x : ↑(limit F)),
      limit.π G (Opposite.op n) (U x) = α n (limit.π F (Opposite.op n) x))
    (hV : ∀ (n : ℕ) (x : ↑(limit G)),
      limit.π H (Opposite.op n) (V x) = β n (limit.π G (Opposite.op n) x)) :
    Function.Injective U ∧ Function.Exact U V ∧
      ((∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_add_right n 1)).op)) →
        Function.Surjective V) := by
  sorry

end CategoryTheory
