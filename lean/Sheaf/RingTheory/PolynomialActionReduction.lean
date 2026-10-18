/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Reduction of polynomial action coefficients to the base ring

Source: Stacks Project, Algebra, Tag 0561, proof of
`lemma-finitely-presented-over-subring`, the degree-lowering paragraph
(blueprint: lem-trf-polynomial-action-reduction).
-/

@[expose] public section

universe u v w

open scoped BigOperators

namespace Module

/-- Stacks Project, Algebra, Tag 0561, the paragraph beginning with an expression
`z = ∑ b_j y_j` (blueprint: lem-trf-polynomial-action-reduction).
If algebra generators act on specified module generators by matrices over the base ring,
then every module element is a base-ring linear combination of those same generators.

Proof: first write an element as an `S`-linear combination of the `e j`, using
`def-weil-finitely-generated-module`. The algebra generation hypothesis, in the sense of
`def-weil-pbc-finite-type-algebra`, writes every coefficient as a polynomial in the `x i`
with coefficients in `R`. Induct simultaneously for all `j` on the total degree of a
monomial to show that its action on `e j` is an `R`-linear combination of the `e k`.
The degree-zero case is `e j` itself. At positive degree, remove one factor `x i`, use
the displayed action relation, and apply the induction hypothesis to each remaining
monomial acting on `e k`. The scalar-tower identity commutes the `R` coefficients
past this action. Substitute these expressions into the initial finite sum and collect
the coefficient of each `e k`. The same calculation covers both empty generating
families and the zero ring. -/
theorem exists_eq_sum_smul_of_polynomial_action
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {N : Type w} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    {n m : ℕ} (x : Fin n → S) (e : Fin m → N)
    (hx : Algebra.adjoin R (Set.range x) = ⊤)
    (he : Submodule.span S (Set.range e) = ⊤)
    (a : Fin n → Fin m → Fin m → R)
    (ha : ∀ (i : Fin n) (j : Fin m), x i • e j = ∑ k : Fin m, a i j k • e k) :
    ∀ z : N, ∃ c : Fin m → R, z = ∑ k : Fin m, c k • e k := by
  sorry

end Module
