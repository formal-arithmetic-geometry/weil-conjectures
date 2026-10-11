/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Height

/-!
# Associated primes of a fractional principal quotient of a normal domain

Source: Stacks Project, Algebra, Lemma 10.157.6, Tag 031T, clause (3)
(blueprint: lem-weil-pbc-normal-domain-fractional-principal-quotient-ass).
-/

@[expose] public section

universe u v

namespace Ideal

/-- In a Noetherian normal domain, the quotient by `A ∩ yA` has no embedded associated
primes, and every associated prime has height one. The ideal `J = A ∩ yA` is written out
as the inverse image of `Submodule.span A {y}` under the inclusion of `A` in its fraction
field `K` (no `let`, so that stage 3 can unfold it).
Source: Stacks Project, Algebra, Lemma 10.157.6, Tag 031T, clause (3)
(blueprint: lem-weil-pbc-normal-domain-fractional-principal-quotient-ass).

Proof (the node's direct principal-quotient argument):
1. Write `y = a / b` with nonzero `a, b ∈ A`. For `c ∈ A`, membership in `J = A ∩ yA`
   is equivalent to `b * c ∈ aA`. This also shows `aA ≤ J` and `a ∈ J`, with `a ≠ 0`.
2. Multiplication by `b` gives an injective `A`-linear map `A/J → A/aA`:
   it is well-defined and its kernel is zero by the membership equivalence in step 1.
   A nonzero class and its image have the same annihilator, since `r * c ∈ J` is
   equivalent to `b * r * c ∈ aA`.
3. Every associated prime of `A/J` is therefore associated to `A/aA`. Apply
   lem-weil-pbc-normal-domain-principal-quotient-associated-height to the nonzero
   numerator `a` to obtain height one.
4. The associated prime `p` contains `J`. A prime `q` with `J ≤ q < p` contains the
   nonzero element `a`, so `q ≠ (0)`. The chain `(0) < q < p` contradicts height one.
   Hence `p` is minimal over `J`. If `J = A`, the quotient is zero and has no
   associated primes, so both conclusions are vacuous. -/
theorem associatedPrimes_fractionalPrincipalQuotient
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] (y : K) (hy : y ≠ 0) :
    ∀ p ∈ associatedPrimes A
        (A ⧸ (Submodule.span A ({y} : Set K)).comap (Algebra.linearMap A K)),
      p ∈ Ideal.minimalPrimes ((Submodule.span A ({y} : Set K)).comap (Algebra.linearMap A K)) ∧
        p.height = 1 := by
  sorry

end Ideal
