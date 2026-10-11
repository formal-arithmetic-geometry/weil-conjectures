/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Prime

/-!
# Graded prime avoidance

Source: Stacks Project, Algebra, Lemma 10.57.6 (Tag 00JS, `algebra-lemma-graded-silly`)
(blueprint: lem-sc-graded-prime-avoidance).
-/

universe u v

namespace HomogeneousIdeal

/-- Graded prime avoidance: a graded ideal contained in the positive-degree ideal and not
contained in any of finitely many homogeneous prime ideals contains a homogeneous element
of positive degree outside all those primes.

Source: Stacks Project, Algebra, Lemma 10.57.6 (Tag 00JS, `algebra-lemma-graded-silly`)
(blueprint: lem-sc-graded-prime-avoidance).

Proof: first discard primes contained in other primes; avoiding the remaining larger primes
avoids the discarded ones. For an empty family, take zero in degree one. Induct on the size
of the remaining family. For one prime, take a homogeneous component outside that prime of
an element of `I` outside it. Homogeneity puts the component in `I`; the containment in the
irrelevant ideal forces its degree to be positive. In the induction step choose homogeneous
`x ∈ I` of positive degree outside all but the last prime. If it also avoids the last prime,
we are done. Otherwise form the graded product ideal `I * p₁ * ... * pᵣ₋₁`. It is not contained
in the last prime: choose an element of each earlier prime outside the last prime, multiply
these together, and use primality to see that containment would force `I` into the last prime.
Choose a homogeneous component `y` in the product ideal outside the last prime. It has positive
degree since the product ideal is contained in `I`. Then `x ^ deg(y) + y ^ deg(x)` belongs to
`I` and is homogeneous of positive degree. At every earlier prime the second summand belongs
to the prime and the first does not; at the last prime the first belongs and the second does
not. Hence the sum avoids all primes. These are the five elementary steps of the DAG proof;
no additional proof-dependency nodes are used. -/
theorem exists_homogeneous_mem_notMem_of_isPrime
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (r : ℕ) (p : Fin r → HomogeneousIdeal 𝒜)
    (hp : ∀ i : Fin r, (p i).toIdeal.IsPrime) (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ HomogeneousIdeal.irrelevant 𝒜) (hIp : ∀ i : Fin r, ¬ I ≤ p i) :
    ∃ (n : ℕ), 0 < n ∧ ∃ (x : A), x ∈ 𝒜 n ∧ x ∈ I ∧ ∀ i : Fin r, x ∉ p i := by
  sorry

end HomogeneousIdeal
