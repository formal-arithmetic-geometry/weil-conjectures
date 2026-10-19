/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Sheaf.RingTheory.ExcellentRing
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Ideal.Operations
import WeilConjectures.RingTheory.LocalCompletionQuotient
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-!
# Hyperplane reduction of a non-equidimensional completion

Source: Stacks Project, More on Algebra, Tag 0AW3, the `d > 1` paragraph of
`lemma-not-formally-catenary`, with its prime-quotient refinement under catenarity
(blueprint: lem-per-catenary-completion-hyperplane).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AdicCompletion

/-- A least-dimensional component of the completion of a catenary Noetherian local
 domain, of dimension `1 < d < dim A`, gives a prime hyperplane quotient with a
 completed component of dimension `d - 1`. The ideal used to complete `A / p` is
 the image of the maximal ideal of `A`; since `p` is prime, this is precisely the
 maximal ideal of the local quotient. The dimension identity is written with `+ 1`
 to avoid subtraction in `WithBot ℕ∞`.

Source: Stacks Project, More on Algebra, Tag 0AW3, `d > 1` paragraph, with the
prime-quotient refinement and catenary dimension argument of Algebra, Tags 00KW and 00NI
(blueprint: lem-per-catenary-completion-hyperplane).

Proof:
1. The completion `B` is Noetherian and local, with maximal ideal `mB`, by
   lem-weil-pbc-adic-completion-noetherian and lem-weil-pbc-local-completion-local-ring.
   All local quotient dimensions are finite by
   lem-weil-pbc-noetherian-local-finite-krull-dimension. List the minimal primes
   other than `q` using lem-weil-pbc-noetherian-finitely-many-minimal-primes.
   For each such `qᵢ`, list the primes minimal over `q + qᵢ` using
   lem-sc-finite-minimal-primes-over-ideal, keeping those with positive-dimensional
   quotient. Denote this finite collection by `R`.
2. Each prime in `R`, and `q`, is strictly below `mB`; its contraction is strictly
   below `m`, since otherwise it contains `mB`. Also `m` is nonzero since
   `dim A > d > 1`. Apply lem-weil-pbc-prime-avoidance to `m`, avoiding `(0)`,
   the contraction of `q`, and all contractions of primes in `R`. This gives
   `0 ≠ f ∈ m`, whose image is outside `q` and every member of `R`.
3. In the local domain `C = B / q`, the image of `f` is a nonzero nonunit.
   By lem-weil-pbc-dimension-quotient-nonzerodivisor its quotient has dimension
   `d - 1`. Choose a chain of this length and, below its first lifted prime,
   choose `P` minimal over `q + fB` using lem-weil-pbc-prime-contains-minimal-prime.
   Chains give `dim(B / P) = d - 1 > 0`. The single-equation case of
   lem-weil-pbc-noetherian-height-quotient-bound gives height of `P / q` at most one.
4. Choose `T ≤ P` minimal over `fB`, and a minimal prime `b ≤ T`, by
   lem-weil-pbc-prime-contains-minimal-prime. If `b = q`, minimality forces `T = P`.
   Otherwise choose `a ≤ P` minimal over `q + b`. Its quotient has dimension
   at least `d - 1 > 0`, so `a ∈ R`. Distinct minimal primes are incomparable,
   giving `q < a`; and `f ∉ a`, `f ∈ P` give `a < P`. This contradicts the
   height bound. Thus `P` is minimal over `fB`.
5. Set `p = P ∩ A` and choose `p₀ ≤ p` minimal over `fA`. Completion is flat
   by lem-weil-pbc-local-completion-faithfully-flat, so lem-sc-flat-going-down
   gives `T ≤ P` contracting to `p₀`. Since `f ∈ T`, Step 4 gives `T = P`,
   hence `p₀ = p`. Also `P` is minimal over `pB`. By
   lem-weil-pbc-local-completion-quotient, the completion of `A / p` is `B / pB`.
   Its minimal prime `r = P / pB` has quotient `B / P`, of dimension `d - 1`.
6. In `A`, lem-weil-pbc-noetherian-height-quotient-bound gives height of `p`
   at most one. As `A` is a domain and `0 ≠ f ∈ p`, `(0) < p` is saturated.
   Append a saturated maximal-length chain from `p` to `m`; catenarity identifies
   its length plus one with `dim A`. Thus `dim(A / p) + 1 = dim A`.
   Finally `1 < d < dim A` yields `0 < d - 1 < dim(A / p)`. -/
theorem exists_prime_quotient_completion_component_dimension_pred
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    (hcat : IsCatenaryRing A)
    (q : Ideal (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (hq : q ∈ minimalPrimes (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (d : ℕ)
    (hdim : ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ q) =
      (d : WithBot ℕ∞))
    (hleast : ∀ q' ∈ minimalPrimes (AdicCompletion (IsLocalRing.maximalIdeal A) A),
      (d : WithBot ℕ∞) ≤ ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ q'))
    (hd : 1 < d) (hlt : (d : WithBot ℕ∞) < ringKrullDim A) :
    ∃ f : A, f ≠ 0 ∧ f ∈ IsLocalRing.maximalIdeal A ∧
      ∃ p ∈ (Ideal.span {f}).minimalPrimes,
        ∃ r ∈ minimalPrimes
          (AdicCompletion ((IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk p)) (A ⧸ p)),
          ringKrullDim (A ⧸ p) + 1 = ringKrullDim A ∧
          ringKrullDim
            (AdicCompletion ((IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk p))
              (A ⧸ p) ⧸ r) = ((d - 1 : ℕ) : WithBot ℕ∞) ∧
          0 < d - 1 ∧ ((d - 1 : ℕ) : WithBot ℕ∞) < ringKrullDim (A ⧸ p) := by
  sorry

end AdicCompletion
