/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.RingTheory.FinitePatternFactorization

/-!
# Coefficients in a completed positive monoid algebra

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé VI, §1.6(i)–(ii),
printed p. 70, with the finite-pattern completion calculation of Stacks Project,
Tag 05GG (blueprint: lem-trf-monoid-completion-coefficients).
-/

@[expose] public section

universe u v w

open scoped DirectSum

namespace AddMonoidAlgebra

open Classical in
/-- Coefficient description and ideal powers in a completed positive monoid algebra.

Source: ILO, Exposé VI, §1.6(i)–(ii), printed p. 70, and Stacks Project, Tag 05GG
(blueprint: lem-trf-monoid-completion-coefficients).

The ring structure on the literal function type `P → A` is quantified together with
its addition and convolution formulas. The explicit structure arguments prevent the
usual pointwise multiplication instance from being used. The coefficient map is an
`A`-algebra equivalence for precisely this ring structure. Natural subtraction on
`ℕ` is the displayed exponent `max (n - ν(p)) 0`.

Proof plan:
1. Choose finitely many nonzero monoid generators, allowing an empty list for the
   zero monoid. Each nonzero summand has positive integral weight, so a decomposition
   of `p` has length at most its weight. Its lengths have an attained maximum `ν p`,
   and no nonempty such decomposition sums to zero. Bounded-weight elements have
   bounded-length generator words, so each set of pairs with sum `p` is finite.
   Every `p` with `ν p < n` has a generator word of length less than `n`, so this set
   is finite too.
2. A finite polynomial belongs to `b ^ n` exactly when its coefficient at `p`
   belongs to `m ^ (n - ν p)`. Expand products of generators for the forward
   implication. Conversely, use a maximal decomposition of `p` and expand its
   coefficient as a finite sum of products from the appropriate power of `m`.
3. A compatible family of polynomial residues determines, for each `p`, residues
   of its coefficient modulo `m ^ k` once the level is at least `k + ν p`.
   Completeness and separatedness (`def-weil-pbc-adically-complete-ring`) give one
   coefficient in `A`. Conversely, any coefficient family gives a residue at level
   `n` by summing over the finite set `ν p < n`. The finite-level criterion shows
   these constructions are inverse in the completion
   (`def-weil-pbc-adic-completion`).
4. Addition is componentwise. Finite decomposition sets identify multiplication
   with convolution by passing the finite-level multiplication formula to each
   coefficient. A monomial has its stated coefficient at its exponent and zero
   elsewhere. These formulas give the specified ring and algebra structures.
5. The projection is surjective (already `AdicCompletion.surjective_evalₐ`). Its
   kernel has exactly the coefficient condition from step 2. For the reverse
   ideal containment use `lem-trf-finite-pattern-factorization`: the finite low-ν
   part factors using generators of `m`; partition the high-ν exponents by the
   first eligible tuple of `n` monoid generators and factor that tuple out of the
   corresponding residual coefficient family. Cancellation follows from the
   embedding into `G`. There are finitely many tuples, so this is a finite sum
   in the extended ideal power. This is also the kernel statement of Tag 05GG.
6. At level `n`, only the finitely many exponents `ν p < n` remain, and their
   coefficients are taken modulo `m ^ (n - ν p)`. Taking these coefficients gives
   the stated `A`-linear equivalence; its inverse is the finite monomial sum.
-/
theorem monoidCompletion_coefficients
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (P : Type v) [AddCommMonoid P] [AddMonoid.FG P]
    (G : Type w) [AddCommGroup G]
    (ι : P →+ G) (hι : Function.Injective ι)
    (wgt : G →+ ℤ)
    (hpos : ∀ p : P, p ≠ 0 → 0 < wgt (ι p))
    (hfree : ∃ r : ℕ, Nonempty (G ≃+ (Fin r → ℤ))) :
    ∃ (ν : P → ℕ),
      ν 0 = 0 ∧
      (∀ p : P,
        IsGreatest {q : ℕ | ∃ p₁ : Fin q → P,
          (∀ i : Fin q, p₁ i ≠ 0) ∧ (∑ i, p₁ i) = p} (ν p)) ∧
      ∃ (b : Ideal (AddMonoidAlgebra A P)),
        b = Ideal.map (algebraMap A (AddMonoidAlgebra A P))
              (IsLocalRing.maximalIdeal A) ⊔
            Ideal.span {x | ∃ p : P, p ≠ 0 ∧
              x = AddMonoidAlgebra.single p (1 : A)} ∧
        ∃ (ring : CommRing (P → A))
          (alg : @Algebra A (P → A) _ ring.toSemiring)
          (c : @AlgEquiv A (AdicCompletion b (AddMonoidAlgebra A P)) (P → A)
            _ _ ring.toSemiring _ alg),
          (∀ (a f : P → A) (p : P),
            (@Add.add (P → A) ring.toAdd a f) p = a p + f p) ∧
          (∀ (a f : P → A) (p : P),
            (@Mul.mul (P → A) ring.toMul a f) p =
              ∑ᶠ q : {q : P × P // q.1 + q.2 = p}, a q.1.1 * f q.1.2) ∧
          (∀ p : P, Set.Finite {q : P × P | q.1 + q.2 = p}) ∧
          (∀ (a : A) (p q : P),
            c (AdicCompletion.of b (AddMonoidAlgebra A P)
              (AddMonoidAlgebra.single p a)) q = if q = p then a else 0) ∧
          (∀ n : ℕ, 1 ≤ n →
            Set.Finite {p : P | ν p < n} ∧
            Function.Surjective (AdicCompletion.evalₐ b n) ∧
            RingHom.ker (AdicCompletion.evalₐ b n) =
              Ideal.map
                (algebraMap (AddMonoidAlgebra A P) (AdicCompletion b (AddMonoidAlgebra A P)))
                (b ^ n) ∧
            (∀ x : AdicCompletion b (AddMonoidAlgebra A P),
              x ∈ RingHom.ker (AdicCompletion.evalₐ b n) ↔
                ∀ p : P, c x p ∈ (IsLocalRing.maximalIdeal A) ^ (n - ν p)) ∧
            Nonempty ((AdicCompletion b (AddMonoidAlgebra A P) ⧸
                Ideal.map
                  (algebraMap (AddMonoidAlgebra A P) (AdicCompletion b (AddMonoidAlgebra A P)))
                  (b ^ n)) ≃ₗ[A]
              ⨁ p : {p : P // ν p < n},
                A ⧸ (IsLocalRing.maximalIdeal A) ^ (n - ν p.1))) := by
  sorry

end AddMonoidAlgebra
