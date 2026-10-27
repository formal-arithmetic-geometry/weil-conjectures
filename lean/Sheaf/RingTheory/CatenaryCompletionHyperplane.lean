/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.GoingDown
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.AdicCompletion.LocalRing
import WeilConjectures.RingTheory.LocalCompletionQuotient
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Operations

/-!
# Hyperplane reduction of a non-equidimensional completion

Source: Stacks Project, More on Algebra, Tag 0AW3, the `d > 1` paragraph of
`lemma-not-formally-catenary`, with its prime-quotient refinement under catenarity
(blueprint: lem-per-catenary-completion-hyperplane).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace IsCatenaryRing

/-- A hyperplane cuts the dimension of a catenary local domain and the dimension of
a chosen least-dimensional component of its completion by one, after a prime quotient.
The completion of the quotient is taken at the image of the original maximal ideal,
which is the maximal ideal of the quotient since `p` is prime in a local ring.
Source: Stacks Project, More on Algebra, Tag 0AW3, `lemma-not-formally-catenary`,
the `d > 1` paragraph and its catenary prime-quotient refinement
(blueprint: lem-per-catenary-completion-hyperplane).

Proof:
1. The completion B is Noetherian and local (lem-weil-pbc-adic-completion-noetherian,
   lem-weil-pbc-local-completion-local-ring). Dimensions are finite by
   lem-weil-pbc-noetherian-local-finite-krull-dimension. There are finitely many minimal
   primes by lem-weil-pbc-noetherian-finitely-many-minimal-primes. Form the finite set R
   of positive-dimensional minimal primes over q + q_i for the other minimal primes q_i,
   using lem-sc-finite-minimal-primes-over-ideal. This set may be empty.
2. Each member of R and q contracts strictly below the maximal ideal m of A.
   Since dim A > d > 1, the domain A has m nonzero. Prime avoidance
   (lem-weil-pbc-prime-avoidance), also avoiding (0), supplies a nonzero f in m
   avoiding q and every member of R after passage to B.
3. In the local domain B/q the image of f is a nonzero nonunit, so its quotient
   has dimension d - 1 (lem-weil-pbc-dimension-quotient-nonzerodivisor). Lift a chain
   attaining this dimension and choose P minimal over q + fB below its first prime
   (lem-weil-pbc-prime-contains-minimal-prime). Then dim(B/P) = d - 1 > 0.
   The one-equation height bound (lem-weil-pbc-noetherian-height-quotient-bound)
   shows that the height of P/q is at most one.
4. Choose T minimal over fB below P, and a minimal prime b below T, by
   lem-weil-pbc-prime-contains-minimal-prime. If b = q, minimality gives T = P.
   Otherwise choose a minimal over q + b below P. Its quotient has positive dimension,
   so a belongs to R. The strict chain q < a < P contradicts the height bound:
   q < a since distinct minimal primes are incomparable, and a < P since f avoids a.
   Hence P is minimal over fB.
5. Contract P to p in A. Completion is flat (lem-weil-pbc-local-completion-faithfully-flat).
   Going down (lem-sc-flat-going-down) and minimality of P show that p is minimal over fA.
   Also P is minimal over pB. Completion commutes with this quotient
   (lem-weil-pbc-local-completion-quotient), giving a minimal prime r in the completion
   of A/p whose quotient is B/P and therefore has dimension d - 1.
6. The one-equation height bound in A gives height(p) at most one. Since A is a domain
   and f is nonzero in p, (0) < p is saturated. A longest chain above p, prepended by
   (0), is a saturated chain from (0) to m. Catenarity identifies its length with dim A.
   Thus dim(A/p) + 1 = dim A, and 1 < d < dim A gives the asserted strict inequalities. -/
theorem exists_hyperplane_prime_quotient
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    (hcat : IsCatenaryRing A)
    (q : Ideal (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (hq : q ∈ minimalPrimes (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (d : ℕ)
    (hdim : ringKrullDim ((AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ q) = d)
    (hleast : ∀ q' ∈ minimalPrimes (AdicCompletion (IsLocalRing.maximalIdeal A) A),
      (d : WithBot ℕ∞) ≤
        ringKrullDim ((AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ q'))
    (hd : 1 < d) (hdA : (d : WithBot ℕ∞) < ringKrullDim A) :
    ∃ f : A, f ≠ 0 ∧ f ∈ IsLocalRing.maximalIdeal A ∧
      ∃ p ∈ (Ideal.span ({f} : Set A)).minimalPrimes,
        ∃ r : Ideal (AdicCompletion
            ((IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk p)) (A ⧸ p)),
          r ∈ minimalPrimes (AdicCompletion
            ((IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk p)) (A ⧸ p)) ∧
          ringKrullDim (A ⧸ p) + 1 = ringKrullDim A ∧
          ringKrullDim ((AdicCompletion
            ((IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk p)) (A ⧸ p)) ⧸ r) =
              ((d - 1 : ℕ) : WithBot ℕ∞) ∧
          0 < d - 1 ∧ ((d - 1 : ℕ) : WithBot ℕ∞) < ringKrullDim (A ⧸ p) := by
  sorry

end IsCatenaryRing
