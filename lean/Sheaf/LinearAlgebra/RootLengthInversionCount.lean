/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card

/-!
# Simple-reflection length and positive-root inversions

Source: Björner--Brenti, Combinatorics of Coxeter Groups, Lemma 4.4.3 and
Proposition 4.4.4, pp.102--104; Milne, Algebraic Groups, Appendix C.8--C.11,
pp.609--610 (blueprint: lem-sfb-root-length-inversion-count).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace RootPairing

/-- The least length of a simple-reflection expression equals the number of positive
roots sent negative. `IsLeast` specifies the length by its defining minimum property;
`List.foldr` applies the rightmost reflection first. The generators of the subgroup
are specified by their action on every vector, using the displayed reflection formula.
The final implication records the rank-zero case.

Source: Björner--Brenti, Lemma 4.4.3 and Proposition 4.4.4, pp.102--104;
Milne, Algebraic Groups, Appendix C.8--C.11, pp.609--610
(blueprint: lem-sfb-root-length-inversion-count).

Proof: (1) Let P be the roots with nonnegative base coordinates. The coordinate sign
condition, nonzero roots and closure under negation give the disjoint partition
Phi = P union (-P). The reflection formula gives s_a(a) = -a and s_a squared = 1.
Thus every element of the generated subgroup is a word in the simple reflections,
and the nonempty set of its word lengths has a least element.
(2) If beta is positive and different from a simple root a, reducedness implies a
positive coordinate away from a. Reflection in a leaves that coordinate unchanged,
so s_a(beta) is positive and different from a. Involutivity gives a permutation of
P minus {a}.
(3) Induct on the least word length n. At n = 0 the word is the identity and the
inversion set is empty. Write a reduced nonempty word as w = u s_a. Its prefix has
length n - 1. If u(a) were negative, lem-sfb-root-sign-word-deletion, applied to the
prefix and a, would express w by deleting a prefix letter, contradicting minimality.
Consequently u(a) is positive.
(4) The inversion set of w is the disjoint union of s_a applied to the inversion
set of u and {a}, by (2) and u(a) positive. Its cardinality is therefore one more
than that of u; induction gives n.
(5) In the zero space Phi, Delta and P are empty; the generated subgroup is trivial,
and the empty word and empty inversion set both have size zero.
-/
theorem simple_reflection_length_eq_inversion_count
    (V : Type u) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hBsymm : B.IsSymm)
    (hBpos : ∀ x : V, x ≠ 0 → 0 < B x x)
    (Φ : Finset V) (hΦzero : ∀ a ∈ Φ, a ≠ 0)
    (hΦspan : Submodule.span ℝ (Φ : Set V) = ⊤)
    (hΦline : ∀ a ∈ Φ,
      (Φ : Set V) ∩ {x : V | ∃ r : ℝ, r • a = x} = {a, -a})
    (hΦreflect : ∀ a ∈ Φ,
      Set.BijOn (fun x : V ↦ x - (2 * B x a / B a a) • a)
        (Φ : Set V) (Φ : Set V))
    (hΦintegral : ∀ a ∈ Φ, ∀ β ∈ Φ, ∃ z : ℤ, 2 * B β a / B a a = (z : ℝ))
    (Δ : Finset V) (hΔ : Δ ⊆ Φ)
    (b : Module.Basis Δ ℝ V) (hb : ∀ a : Δ, b a = a.val)
    (hcoords : ∀ β ∈ Φ,
      (∀ a : Δ, ∃ z : ℤ, b.repr β a = (z : ℝ)) ∧
        ((∀ a : Δ, 0 ≤ b.repr β a) ∨ (∀ a : Δ, b.repr β a ≤ 0)))
    (w : V ≃ₗ[ℝ] V)
    (hw : w ∈ Subgroup.closure
      {s : V ≃ₗ[ℝ] V | ∃ a ∈ Δ, ∀ x : V, s x = x - (2 * B x a / B a a) • a}) :
    ∃ n : ℕ,
      IsLeast {m : ℕ | ∃ word : List Δ, word.length = m ∧
        ∀ x : V, word.foldr
          (fun a y ↦ y - (2 * B y a.val / B a.val a.val) • a.val) x = w x} n ∧
      n = {β : V | β ∈ Φ ∧ (∀ a : Δ, 0 ≤ b.repr β a) ∧
        -w β ∈ Φ ∧ (∀ a : Δ, 0 ≤ b.repr (-w β) a)}.ncard ∧
      ((∀ x : V, x = 0) → Φ = ∅ ∧ Δ = ∅ ∧ w = 1 ∧ n = 0) := by
  sorry

end RootPairing
