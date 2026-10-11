/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Powers and unique primes in a degree-p root extension

Source: Stacks Project, More on Algebra, Tag 07PR, proof; Algebra, Tags 0BR8 and 00GQ
(blueprint: lem-weil-pbc-radicial-prime-unique-degree-p).
-/

universe u

open Polynomial

namespace AdjoinRoot

/-- Source: Stacks Project, More on Algebra, Tag 07PR, proof, and Algebra, Tags 0BR8 and
00GQ (blueprint: lem-weil-pbc-radicial-prime-unique-degree-p).
For domains `R` and `R[X]/(X^p-f)` with prime `p` zero in `R`, the structure map is
injective and integral, every p-th power comes from `R`, and every prime of `R` has a
unique prime above it.

Proof:
1. The polynomial `X^p-C f` is monic of degree `p`. The quotient is free with basis
   `1, z, ..., z^(p-1)` (lem-weil-pbc-monic-quotient-free). Comparing the coefficient of
   `1` proves injectivity. This finite free algebra is integral
   (lem-weil-pbc-finite-algebra-is-integral; def-weil-pbc-integral-closure).
2. The image of `p` in the quotient is zero. In the binomial expansion of `(x+y)^p`,
   every intermediate binomial coefficient is divisible by the prime `p`, so Frobenius
   is additive; induction gives the same identity for finite sums. It is multiplicative
   because the quotient is commutative.
3. Represent an element as a polynomial sum `sum b_i*z^i` (def-weil-polynomial-ring).
   Raising to `p` and using `z^p=f` gives the image of `sum b_i^p*f^i` in `R`.
4. If primes `q` and `q'` contract to `P` and `c` belongs to `q`, write `c^p` as the
   image of `r` in `R`. Then `r` belongs to `P`, so `c^p` belongs to `q'`, and primality
   with `p>0` puts `c` in `q'`. Symmetry gives equality (Tag 0BR8).
5. Injectivity and integrality give existence by lying over
   (lem-weil-pbc-integral-injective-lying-over; Tag 00GQ). Together with step 4 this
   proves existence and uniqueness for every base prime. -/
theorem radicial_prime_unique_degree_p
    (R : Type u) [CommRing R] [IsDomain R] (p : ℕ) (hp : p.Prime)
    (hchar : (p : R) = 0) (f : R) [IsDomain (AdjoinRoot (X ^ p - C f))] :
    Function.Injective (of (X ^ p - C f)) ∧
      (∀ c : AdjoinRoot (X ^ p - C f), IsIntegral R c) ∧
      (∀ c : AdjoinRoot (X ^ p - C f), c ^ p ∈ (of (X ^ p - C f)).range) ∧
      (∀ P : Ideal R, P.IsPrime →
        ∃! Q : Ideal (AdjoinRoot (X ^ p - C f)),
          Q.IsPrime ∧ Q.comap (of (X ^ p - C f)) = P) := by
  sorry

end AdjoinRoot
