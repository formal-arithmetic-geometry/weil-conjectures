/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.RingTheory.AssociatedGradedRing
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# One-step approximation from homogeneous initial-ideal generators

Source: Stacks Project, Algebra, Lemma 05GH, proof, second and third paragraphs
(blueprint: lem-weil-pbc-associated-graded-ideal-approximation).
-/

@[expose] public section

universe u

open scoped BigOperators

namespace Ideal

/-- Homogeneous generators of the initial ideal give finite one-step approximation data.
Source: Stacks Project, Algebra, Lemma 05GH, proof, second and third paragraphs
(blueprint: lem-weil-pbc-associated-graded-ideal-approximation).

Proof: The degree-`n` images of `K ∩ J^n` form a homogeneous ideal in `gr_J(A)`:
multiplying by a degree-`m` representative in `J^m` gives a representative in
`K ∩ J^(n+m)`. By Noetherianity this ideal has a finite generating set. Replace each
generator by its finitely many homogeneous components. These components still
belong to the initial ideal, and generate it, because their sums recover the old
generators. Lift each resulting generator of degree `d i` to `h i ∈ K ∩ J^(d i)`.
For `x ∈ K ∩ J^n`, express its initial form as a linear combination of these
generators, and compare degree `n`. Only coefficient components of degree `n - d i`
with `d i ≤ n` contribute; lift them to `a i ∈ J^(n - d i)` and take `a i = 0`
otherwise. The degree-`n` equality means `x - ∑ i, a i * h i ∈ J^(n+1)`.
The same difference lies in `K` since `x` and all the `h i` lie in `K`.
No completeness or Noetherianity of `A/J` is used in this finite initial-form step.
An empty family is permitted when the initial ideal is zero. -/
theorem exists_associatedGraded_ideal_approximation {A : Type u} [CommRing A]
    (J K : Ideal A) [IsNoetherianRing (associatedGraded J)] :
    ∃ (t : ℕ) (d : Fin t → ℕ) (h : Fin t → A),
      (∀ i, h i ∈ K) ∧ (∀ i, h i ∈ J ^ (d i)) ∧
      ∀ (n : ℕ) (x : A), x ∈ K → x ∈ J ^ n →
        ∃ a : Fin t → A, (∀ i, a i ∈ J ^ (n - d i)) ∧
          x - ∑ i, a i * h i ∈ K ∧ x - ∑ i, a i * h i ∈ J ^ (n + 1) := by sorry

end Ideal
