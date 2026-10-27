/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.RingTheory.MonoidCompletionCoefficients

/-!
# Residue and domain properties of a completed positive monoid algebra

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé VI, §1.6(i)–(ii),
printed p. 70, with the agent-supplied coefficient-algebra refinement in the DAG
(blueprint: lem-trf-formal-monoid-residue-domain).
-/

@[expose] public section

universe u v w

namespace AddMonoidAlgebra

open Classical in
/-- Constant coefficients, locality, and the domain property of the completed
positive monoid algebra.

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé VI, §1.6(i)–(ii),
printed p. 70, with the agent-supplied coefficient-algebra refinement in the DAG
(blueprint: lem-trf-formal-monoid-residue-domain).

Proof plan:
1. Apply `lem-trf-monoid-completion-coefficients` to the given data. This supplies
   the algebra equivalence with all coefficient families, finite convolution, and
   the monomial coefficient formula.
2. Define `c f` as the zeroth coefficient. If `u + v = 0`, positivity implies
   `u = v = 0`, so evaluation is multiplicative. Constants split this map, giving
   surjectivity and its extension property on the monoid algebra.
3. Choose finitely many nonzero monoid generators, allowing the empty list.
   Apply `lem-trf-high-length-prefix-division` at length one to a family with
   zero constant coefficient. It is a finite sum of generator monomials times
   residual families, hence lies in `J`. Conversely each nonconstant monomial
   has zero constant coefficient. The quotient map has inverse induced by the
   constant inclusion, since `f - C(c f)` belongs to `J`.
4. A unit maps to a unit. Conversely, for a unit constant coefficient `a`, put
   `h = 1 - C(a⁻¹)f`. The coefficient of `h^k` at `p` vanishes for `k > w(p)`.
   Thus the coefficientwise finite geometric sum defines a family `s`, and
   finite convolution gives `(1-h)s = 1`. This constructs an inverse for `f`.
   Use `lem-trf-positive-monoid-adic-filtration` for finiteness and weight bounds.
5. Nonunits are exactly the inverse image of the maximal ideal of `A`, a proper
   ideal containing every proper ideal. This proves locality. Decomposing
   `f = C(c f) + (f - C(c f))` gives this ideal as the extension of `b`.
   Constant inclusion and `c` induce inverse maps on the residue quotients.
6. If `A` is a domain, order exponents lexicographically by weight and lattice
   coordinates. Finite weight fibres from
   `lem-trf-positive-monoid-adic-filtration` ensure each nonempty support has a
   least exponent. Translation invariance makes the product coefficient at the
   sum of the least supported exponents the product of those two nonzero
   coefficients. It is nonzero, and the constant inclusion also gives `1 ≠ 0`.
7. For the trivial monoid the coefficient families are just `A`, the constant
   inclusion is inverse to `c`, and there are no generators for `J`, so `J = 0`.
-/
theorem formalMonoid_residue_domain
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (P : Type v) [AddCommMonoid P] [AddMonoid.FG P]
    (G : Type w) [AddCommGroup G]
    (ι : P →+ G) (hι : Function.Injective ι)
    (wgt : G →+ ℤ)
    (hpos : ∀ p : P, p ≠ 0 → 0 < wgt (ι p))
    (hfree : ∃ r : ℕ, Nonempty (G ≃+ (Fin r → ℤ))) :
    ∃ (b : Ideal (AddMonoidAlgebra A P)),
      b = Ideal.map (algebraMap A (AddMonoidAlgebra A P))
        (IsLocalRing.maximalIdeal A) ⊔
        Ideal.span {x | ∃ p : P, p ≠ 0 ∧
          x = AddMonoidAlgebra.single p (1 : A)} ∧
      ∃ (ring : CommRing (P → A))
        (alg : @Algebra A (P → A) _ ring.toSemiring)
        (coeff : @AlgEquiv A (AdicCompletion b (AddMonoidAlgebra A P)) (P → A)
          _ _ ring.toSemiring _ alg),
        (∀ (a f : P → A) (p : P),
          (@Add.add (P → A) ring.toAdd a f) p = a p + f p) ∧
        (∀ (a f : P → A) (p : P),
          (@Mul.mul (P → A) ring.toMul a f) p =
            ∑ᶠ q : {q : P × P // q.1 + q.2 = p}, a q.1.1 * f q.1.2) ∧
        (∀ p : P, Set.Finite {q : P × P | q.1 + q.2 = p}) ∧
        (∀ (a : A) (p q : P),
          coeff (AdicCompletion.of b (AddMonoidAlgebra A P)
            (AddMonoidAlgebra.single p a)) q = if q = p then a else 0) ∧
        ∃ (c : AdicCompletion b (AddMonoidAlgebra A P) →ₐ[A] A)
          (J : Ideal (AdicCompletion b (AddMonoidAlgebra A P))),
          J = Ideal.span {x | ∃ p : P, p ≠ 0 ∧
            x = algebraMap (AddMonoidAlgebra A P)
              (AdicCompletion b (AddMonoidAlgebra A P))
              (AddMonoidAlgebra.single p (1 : A))} ∧
          Function.Surjective c ∧
          (∀ x : AdicCompletion b (AddMonoidAlgebra A P), c x = coeff x 0) ∧
          (∀ f : AddMonoidAlgebra A P,
            c (AdicCompletion.of b (AddMonoidAlgebra A P) f) = f.coeff 0) ∧
          RingHom.ker c = J ∧
          (∃ q : (AdicCompletion b (AddMonoidAlgebra A P) ⧸ J) ≃ₐ[A] A,
            ∀ x : AdicCompletion b (AddMonoidAlgebra A P),
              q (Ideal.Quotient.mk J x) = c x) ∧
          (∀ f : AdicCompletion b (AddMonoidAlgebra A P), IsUnit f ↔ IsUnit (c f)) ∧
          ∃ hB : IsLocalRing (AdicCompletion b (AddMonoidAlgebra A P)),
            @IsLocalRing.maximalIdeal _ _ hB =
              Ideal.comap c (IsLocalRing.maximalIdeal A) ∧
            @IsLocalRing.maximalIdeal _ _ hB =
              Ideal.map (algebraMap (AddMonoidAlgebra A P)
                (AdicCompletion b (AddMonoidAlgebra A P))) b ∧
            (∃ res : (AdicCompletion b (AddMonoidAlgebra A P) ⧸
                @IsLocalRing.maximalIdeal _ _ hB) ≃ₐ[A]
                (A ⧸ IsLocalRing.maximalIdeal A),
              ∀ x : AdicCompletion b (AddMonoidAlgebra A P),
                res (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (c x)) ∧
            (IsDomain A → IsDomain (AdicCompletion b (AddMonoidAlgebra A P))) ∧
            (Subsingleton P → Function.Bijective c ∧ J = ⊥) := by
  sorry

end AddMonoidAlgebra
