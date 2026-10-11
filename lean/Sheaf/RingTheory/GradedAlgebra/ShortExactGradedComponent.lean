/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Exact.Basic

/-!
# Short exact sequences on homogeneous components

Source: Stacks Project, Algebra, Section 00JL (`section-graded`), the graded-module
exactness convention (blueprint: lem-sc-p1-graded-degree-component-exact).

The ring and module gradings are internal direct sums of additive subgroups. The
ring is allowed to have nonzero components in negative degrees, as in the node.
-/

@[expose] public section

universe u v w x

namespace DirectSum

/-- A short exact sequence of degree-preserving maps of integer-graded modules
restricts to a short exact sequence in each degree.
Source: Stacks Project, Algebra, Section 00JL (`section-graded`), the graded-module
exactness convention (blueprint: lem-sc-p1-graded-degree-component-exact).

Proof: First, the restriction of the first map is injective because the original map
is injective. Second, if a homogeneous element of the middle module maps to zero,
exactness gives a preimage in the first module. Decompose that preimage into its
finitely many homogeneous components. Degree preservation and uniqueness of the
middle module's direct-sum decomposition show that the component of the required
degree maps to the original element. The reverse image-to-kernel inclusion follows
from exactness of the original pair. Third, lift a homogeneous element of the last
module using surjectivity of the second map and decompose the lift. Uniqueness of
the last module's decomposition shows that the component of the required degree
is a homogeneous lift. These are the three elementary steps of the node's proof. -/
theorem shortExact_graded_component
    {R : Type u} [CommRing R]
    {A : Type v} [AddCommGroup A] [Module R A]
    {B : Type w} [AddCommGroup B] [Module R B]
    {C : Type x} [AddCommGroup C] [Module R C]
    (ℛ : ℤ → AddSubgroup R) (𝒜 : ℤ → AddSubgroup A)
    (ℬ : ℤ → AddSubgroup B) (𝒞 : ℤ → AddSubgroup C)
    (_hR : IsInternal ℛ) (_hA : IsInternal 𝒜)
    (_hB : IsInternal ℬ) (_hC : IsInternal 𝒞)
    (_hmul : ∀ (a b : ℤ) (r s : R), r ∈ ℛ a → s ∈ ℛ b → r * s ∈ ℛ (a + b))
    (_hsmulA : ∀ (a b : ℤ) (r : R) (m : A), r ∈ ℛ a → m ∈ 𝒜 b → r • m ∈ 𝒜 (a + b))
    (_hsmulB : ∀ (a b : ℤ) (r : R) (m : B), r ∈ ℛ a → m ∈ ℬ b → r • m ∈ ℬ (a + b))
    (_hsmulC : ∀ (a b : ℤ) (r : R) (m : C), r ∈ ℛ a → m ∈ 𝒞 b → r • m ∈ 𝒞 (a + b))
    (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (hi : ∀ (n : ℤ) (a : A), a ∈ 𝒜 n → i a ∈ ℬ n)
    (hp : ∀ (n : ℤ) (b : B), b ∈ ℬ n → p b ∈ 𝒞 n)
    (_hinj : Function.Injective i) (_hexact : Function.Exact i p)
    (_hsurj : Function.Surjective p) (n : ℤ) :
    let iₙ : 𝒜 n → ℬ n := fun a ↦ ⟨i a, hi n a a.property⟩
    let pₙ : ℬ n → 𝒞 n := fun b ↦ ⟨p b, hp n b b.property⟩
    Function.Injective iₙ ∧ Function.Exact iₙ pₙ ∧ Function.Surjective pₙ := by
  sorry

end DirectSum
