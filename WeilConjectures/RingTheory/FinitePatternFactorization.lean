/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Finite-pattern factorization in a positive monoid series ring

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé VI, §1.6(i)–(ii),
printed p. 70, and the explicit auxiliary coefficient refinement in the DAG
(blueprint: lem-trf-finite-pattern-factorization).
-/

@[expose] public section

universe u v w

namespace AddMonoidAlgebra

open Classical in
/-- Coefficient orders imply membership in powers of the maximal monomial ideal.

Source: ILO, Exposé VI, §1.6(i)–(ii), printed p. 70, motivates the formal monoid
models; the coefficient refinement and its proof are supplied by the DAG
(blueprint: lem-trf-finite-pattern-factorization).

The literal coefficient-family type is equipped with the ring characterized by the
four displayed operation formulas, rather than its usual pointwise ring structure.
The ideal is the span of the constant maximal ideal and all nonzero monomials.
Natural subtraction is precisely the exponent `max (n - ν p) 0` in the node.

Proof plan:
1. Choose finitely many nonzero generators of `P`. Every decomposition of `p` into
   nonzero summands has length at most `wgt (ι p)`. Thus its maximum `ν p` exists,
   and `ν 0 = 0`. Elements of bounded weight have bounded-length generator words,
   so there are finitely many of them.
2. In a decomposition `u + v = p`, both weights are bounded by the weight of `p`.
   Hence convolution is finite. Associativity follows by summing over the finite
   triples with sum `p`; the other ring laws follow from the same formulas.
   Cancellation in `G` gives the monomial shift formula.
3. The set `S = {p | ν p < n}` is finite: every generator word for such a `p`
   has length less than `n`, and there are only finitely many such words.
4. Noetherianity (`def-weil-pbc-noetherian-ring`) gives finitely many generators
   of the maximal ideal. Expanding products shows that its `k`th power is spanned
   by the products of `k` of those generators, including the empty product for `k=0`.
5. For `p` in `S`, take a maximal decomposition of length `ν p`, and expand `a p`
   using step 4 with `k = n - ν p`. Each resulting term has exactly `n` factors
   in `b`. Thus the finite sum of the coefficients supported on `S` lies in `b^n`.
6. Every remaining exponent has a decomposition of length at least `n`. Choose one
   monoid generator from each of its first `n` nonzero summands. Assign the exponent
   to the first eligible ordered `n`-tuple of generators. These finitely many tuples
   partition the remaining exponents, also when the generator list is empty.
7. For each tuple, form the residual coefficient family on its assigned exponents.
   The shift formula identifies that part with the product of its `n` monomials
   times the residual family. Summing these finitely many elements of `b^n` and
   adding the low-order part from step 5 proves the claim.
-/
theorem finitePattern_factorization
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (P : Type v) [AddCommMonoid P] [AddMonoid.FG P]
    (G : Type w) [AddCommGroup G]
    (ι : P →+ G) (hι : Function.Injective ι)
    (wgt : G →+ ℤ) (hpos : ∀ p : P, p ≠ 0 → 0 < wgt (ι p))
    (hfree : ∃ r : ℕ, Nonempty (G ≃+ (Fin r → ℤ))) :
    ∃ ν : P → ℕ,
      ν 0 = 0 ∧
      (∀ p : P, IsGreatest {k : ℕ | ∃ f : Fin k → P,
        (∀ i : Fin k, f i ≠ 0) ∧ (∑ i, f i) = p} (ν p)) ∧
      (∀ p : P, Set.Finite {q : P × P | q.1 + q.2 = p}) ∧
      ∃ ring : CommRing (P → A),
        (∀ p : P, (@Zero.zero (P → A) ring.toZero) p = 0) ∧
        (∀ p : P, (@One.one (P → A) ring.toOne) p = if p = 0 then 1 else 0) ∧
        (∀ (a c : P → A) (p : P),
          (@Add.add (P → A) ring.toAdd a c) p = a p + c p) ∧
        (∀ (a c : P → A) (p : P),
          (@Mul.mul (P → A) ring.toMul a c) p =
            ∑ᶠ q : {q : P × P // q.1 + q.2 = p}, a q.1.1 * c q.1.2) ∧
        ∀ (b : @Ideal (P → A) ring.toSemiring),
          b = @Ideal.span (P → A) ring.toSemiring
            ({x : P → A | ∃ t : A, t ∈ IsLocalRing.maximalIdeal A ∧
                x = fun p ↦ if p = 0 then t else 0} ∪
              {x : P → A | ∃ q : P, q ≠ 0 ∧ x = fun p ↦ if p = q then 1 else 0}) →
          ∀ (n : ℕ), 1 ≤ n → ∀ a : P → A,
            (∀ p : P, a p ∈ (IsLocalRing.maximalIdeal A) ^ (n - ν p)) →
              a ∈ (@Ideal.instIdemCommSemiring (P → A) ring.toCommSemiring).toMonoid.npow
                n b := by
  sorry

end AddMonoidAlgebra
