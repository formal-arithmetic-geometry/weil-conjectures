/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.RingTheory.CompleteToricModel
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Reconstruction from finite monoid coefficient quotients

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé VI 1.6(i)--(ii),
printed p. 70, formal models; the coefficient refinement and its elementary proof
are supplied by the DAG, using Stacks Tags 00M9 and 0317
(blueprint: lem-trf-filtered-monoid-coefficient-limit).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AddMonoidAlgebra

open Classical in
/-- Reconstruction over a complete coefficient ring, with stabilized residues,
finite inverse truncations, monomial normalization and uniqueness.

Source: ILO, Exposé VI 1.6(i)--(ii), printed p. 70 (formal models only);
agent-supplied coefficient refinement using Stacks Tags 00M9 and 0317
(blueprint: lem-trf-filtered-monoid-coefficient-limit).

The quantified ring and algebra structures on `P → A` are specified by the
pointwise addition, finite convolution and scalar formulas. Explicit structure
arguments avoid the usual pointwise multiplication on a function type.
Natural subtraction `n - ν p` means `max(n - ν(p), 0)`. The finite sum uses
exactly the sublevel set from `hfinite`, including all degree-zero exponents.
Uniqueness is subject to the coefficient condition alone, for any second
algebra equivalence, rather than to the conjunction of the conclusions.

Proof plan (the seven steps of the DAG node):
1. Apply the ideal-power criterion to differences of representatives. Compatible
   levels have the same p-coefficient modulo I^j once N ≥ j + ν(p). Compare
   arbitrary eligible levels through their maximum. This also proves independence
   of the representative, using `def-weil-pbc-adic-completion`.
2. These stabilized residues form a compatible sequence in A/I^j. The bijection
   of `def-weil-pbc-adically-complete-ring` gives a unique coefficient in A.
   This defines c and proves the condition at every eligible level.
3. For a coefficient family a, truncate to ν(p) < n. Finiteness makes this a
   polynomial. Differences of nested truncations have only coefficients where
   the criterion asks for I^0 = A, so their residue classes are compatible.
   They define d(a) in `def-weil-pbc-adic-completion` with the asserted projections.
4. If N ≥ j + ν(p), then ν(p) < N, so the p-coefficient of the Nth truncation
   is a_p. The coefficient condition and separatedness of A give c(d(a)) = a.
5. Conversely, compare the nth truncation of c(x) to a representative of x at n.
   At ν(p) < n use j = n - ν(p); elsewhere the criterion is automatic.
   Their difference lies in J^n, proving d(c(x)) = x at every projection.
6. Superadditivity bounds ν(u) and ν(v) by ν(p) whenever u + v = p. A common
   eligible level therefore computes all terms of the finite convolution.
   Multiplication of polynomials (`def-trf-complete-toric-model`) and reduction
   modulo I^j give the convolution formula; separatedness gives equality in A.
   Addition is treated in the same way.
7. A fixed polynomial represents its canonical image at every level, hence has
   its original coefficients under c. Apply this to zero, one, scalars and
   monomials. Transporting the ring laws through the bijection gives the specified
   ring and algebra structures. Finally any second equivalence with the
   coefficient condition has identical residues for every p,j; separatedness
   proves equality, independently of the inverse-truncation and monomial clauses.
-/
theorem filteredMonoid_coefficient_limit
    (A : Type u) [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    (P : Type v) [AddCommMonoid P] (ν : P → ℕ)
    (hzero : ν 0 = 0) (hadd : ∀ p q : P, ν p + ν q ≤ ν (p + q))
    (hfinite : ∀ n : ℕ, 1 ≤ n → Set.Finite {p : P | ν p < n})
    (hpairs : ∀ p : P, Set.Finite {q : P × P | q.1 + q.2 = p})
    (J : Ideal (AddMonoidAlgebra A P))
    (hJ : ∀ (n : ℕ), 1 ≤ n → ∀ F : AddMonoidAlgebra A P,
      F ∈ J ^ n ↔ ∀ p : P, F.coeff p ∈ I ^ (n - ν p)) :
    ∃ (ring : CommRing (P → A))
      (alg : @Algebra A (P → A) _ ring.toSemiring)
      (c : @AlgEquiv A (AdicCompletion J (AddMonoidAlgebra A P)) (P → A)
        _ _ ring.toSemiring _ alg),
      (∀ (a b : P → A) (p : P),
        (@Add.add (P → A) ring.toAdd a b) p = a p + b p) ∧
      (∀ (a b : P → A) (p : P),
        (@Mul.mul (P → A) ring.toMul a b) p =
          ∑ᶠ q : {q : P × P // q.1 + q.2 = p}, a q.1.1 * b q.1.2) ∧
      (∀ (a : A) (p : P),
        (@algebraMap A (P → A) _ ring.toSemiring alg) a p = if p = 0 then a else 0) ∧
      (∀ (x : AdicCompletion J (AddMonoidAlgebra A P)) (p : P)
          (j : ℕ), 1 ≤ j → ∀ N : ℕ, j + ν p ≤ N →
          ∀ F : AddMonoidAlgebra A P,
            Ideal.Quotient.mk (J ^ N) F = AdicCompletion.evalₐ J N x →
            Ideal.Quotient.mk (I ^ j) (c x p) =
              Ideal.Quotient.mk (I ^ j) (F.coeff p)) ∧
      (∀ (a : P → A) (n : ℕ) (hn : 1 ≤ n),
        AdicCompletion.evalₐ J n
          ((@AlgEquiv.symm A (AdicCompletion J (AddMonoidAlgebra A P)) (P → A)
            _ _ ring.toSemiring _ alg c) a) =
          Ideal.Quotient.mk (J ^ n)
            (∑ p ∈ (hfinite n hn).toFinset, AddMonoidAlgebra.single p (a p))) ∧
      (∀ (a : A) (p q : P),
        c (AdicCompletion.of J (AddMonoidAlgebra A P)
          (AddMonoidAlgebra.single p a)) q = if q = p then a else 0) ∧
      (∀ d : @AlgEquiv A (AdicCompletion J (AddMonoidAlgebra A P)) (P → A)
          _ _ ring.toSemiring _ alg,
        (∀ (x : AdicCompletion J (AddMonoidAlgebra A P)) (p : P)
            (j : ℕ), 1 ≤ j → ∀ N : ℕ, j + ν p ≤ N →
            ∀ F : AddMonoidAlgebra A P,
              Ideal.Quotient.mk (J ^ N) F = AdicCompletion.evalₐ J N x →
              Ideal.Quotient.mk (I ^ j) (d x p) =
                Ideal.Quotient.mk (I ^ j) (F.coeff p)) → d = c) := by
  sorry

end AddMonoidAlgebra
