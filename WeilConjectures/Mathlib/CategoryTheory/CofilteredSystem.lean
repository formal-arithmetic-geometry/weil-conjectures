/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Mittag-Leffler vanishing for towers of finite abelian groups

A tower `⋯ → A₂ → A₁ → A₀` of finite abelian groups is Mittag-Leffler (its images stabilize,
`CategoryTheory.Functor.isMittagLeffler_of_exists_finite_range`), and its `lim¹` vanishes. In
the product-cokernel description `lim¹ Aₙ = coker (∏ Aₙ → ∏ Aₙ, (xₙ) ↦ (xₙ - f(xₙ₊₁)))`, the
vanishing says that this map is surjective. It follows from König's lemma
(`nonempty_sections_of_finite_inverse_system`): the solutions of `xₙ - f(xₙ₊₁) = yₙ` are the
sections of the tower of finite nonempty sets `Aₙ` with the affine transition maps
`a ↦ yₙ + f(a)`.

## Main statements

- `surjective_sub_map_succ_of_finite`: `lim¹` of a tower of finite abelian groups vanishes.
-/

@[expose] public section

open CategoryTheory

/-- *Mittag-Leffler vanishing.* For a tower `⋯ → A₂ → A₁ → A₀` of finite abelian groups with
transition maps `fₙ : Aₙ₊₁ → Aₙ`, the map `∏ Aₙ → ∏ Aₙ`, `(xₙ) ↦ (xₙ - fₙ(xₙ₊₁))`, is
surjective; its cokernel is `lim¹ Aₙ`, so `lim¹ Aₙ = 0`.

The blueprint node also identifies the Milnor map of the sequential derived inverse limit with
the limit map for such a tower; that consequence needs the derived inverse limit over the
pro-étale site, which is not formalised.
(blueprint: `lem-weil-pbc-mittag-leffler`) -/
theorem surjective_sub_map_succ_of_finite {A : ℕ → Type*} [∀ n, AddCommGroup (A n)]
    [∀ n, Finite (A n)] (f : ∀ n, A (n + 1) →+ A n) :
    Function.Surjective fun (x : ∀ n, A n) n ↦ x n - f n (x (n + 1)) := by
  intro y
  -- the tower of finite nonempty sets `Aₙ` with transition maps `a ↦ yₙ + fₙ(a)`
  let G : ℕᵒᵖ ⥤ Type _ := Functor.ofOpSequence (X := A) fun n ↦ TypeCat.ofHom (y n + f n ·)
  have : ∀ n, Finite (G.obj n) := fun n ↦ inferInstanceAs (Finite (A n.unop))
  have : ∀ n, Nonempty (G.obj n) := fun n ↦ ⟨(0 : A n.unop)⟩
  obtain ⟨x, hx⟩ := nonempty_sections_of_finite_inverse_system G
  let x' : ∀ n, A n := fun n ↦ x (.op n)
  refine ⟨x', funext fun n ↦ ?_⟩
  have h := hx (homOfLE (Nat.le_add_right n 1)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  change y n + f n (x' (n + 1)) = x' n at h
  change x' n - f n (x' (n + 1)) = y n
  rw [← h, add_sub_cancel_right]
