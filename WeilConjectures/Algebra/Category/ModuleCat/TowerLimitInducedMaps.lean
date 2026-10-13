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

/-- Componentwise maps on inverse limits exist and are characterized by their
coordinate projections, under the stated naturality hypotheses.
Source: the componentwise construction in Stacks Project, Algebra Lemma 03CA.
(blueprint: new-tower-limit-induced-maps).
-/
theorem tower_limit_induced_maps
    (R : Type u) [CommRing R]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} R) (G : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    (H : ℕᵒᵖ ⥤ ModuleCat.{t} R)
    (α : ∀ n : ℕ, F.obj (Opposite.op n) →ₗ[R] G.obj (Opposite.op n))
    (β : ∀ n : ℕ, G.obj (Opposite.op n) →ₗ[R] H.obj (Opposite.op n))
    (hα : ∀ (n : ℕ) (x : F.obj (Opposite.op (n + 1))),
      G.map (homOfLE (Nat.le_add_right n 1)).op (α (n + 1) x) =
        α n (F.map (homOfLE (Nat.le_add_right n 1)).op x))
    (hβ : ∀ (n : ℕ) (x : G.obj (Opposite.op (n + 1))),
      H.map (homOfLE (Nat.le_add_right n 1)).op (β (n + 1) x) =
        β n (G.map (homOfLE (Nat.le_add_right n 1)).op x)) :
    ∃ (U : ↑(limit F) →ₗ[R] ↑(limit G)) (V : ↑(limit G) →ₗ[R] ↑(limit H)),
      (∀ (n : ℕ) (x : ↑(limit F)),
        limit.π G (Opposite.op n) (U x) = α n (limit.π F (Opposite.op n) x)) ∧
      (∀ (n : ℕ) (x : ↑(limit G)),
        limit.π H (Opposite.op n) (V x) = β n (limit.π G (Opposite.op n) x)) := by
  sorry

end CategoryTheory
