/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.RingTheory.FormallySmoothAdic
import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Lifting adically formally smooth algebras into complete rings

Source: Stacks Project, More on Algebra, Lemma 15.38.5 (Tag 07NJ), with the base
ring discrete (blueprint: lem-weil-pbc-fs-adic-lift-into-complete).
-/

universe u v w

namespace Algebra

/-- An algebra formally smooth for the `n`-adic topology lifts through a closed ideal `J`
of an `I`-adically complete algebra when a positive power `J ^ t` lies in `I`.
The lift satisfies the explicit continuity bound `f(n ^ (r * t)) ⊆ I`.
Source: Stacks Project, More on Algebra, Lemma 15.38.5 (Tag 07NJ).
(blueprint: lem-weil-pbc-fs-adic-lift-into-complete)

Proof (following Tag 07NJ):
1. Put `A_{a,b} = A / (J ^ a + I ^ b)` for positive `a,b`. Closedness of `J` and
   `I`-adic completeness identify `A / J` with the inverse limit of `A_{1,b}`:
   injectivity is closedness; for surjectivity adjust successive representatives by
   elements of `J` to make their differences lie in `I ^ b`, then use completeness.
   Reduce `g` to compatible maps into this first row, killing `n ^ r` at `b = 1`.
2. The map `A_{a+1,b+1} → A_{a+1,b} ×_{A_{a,b}} A_{a,b+1}` is onto: if representatives
   differ by `k + l` in the sum of the two defining ideals, subtract `k` from the
   first and add `l` to the second. Its kernel has square zero: modulo
   `J ^ (a+1) + I ^ (b+1)` it lies in the image of `I ^ b`, whose square vanishes.
3. Use `def-weil-pbc-formally-smooth-adic` to lift along the bottom row, then induct
   on `a+b` using the square-zero maps of step 2. A square-zero lift of a map killing
   `n ^ k` kills `n ^ (2*k)`, so each lifting problem satisfies the power condition.
   The two maps defining a pair kill a common power by taking the larger exponent.
4. Since `J ^ (b*t) ≤ I ^ b`, the diagonal `A_{b*t,b}` is `A / I ^ b`. Its compatible
   maps give an algebra map `f : S → A` by `def-weil-pbc-adically-complete-ring`.
5. Reduction to each `A / (J + I ^ b)` agrees with `g`. The injectivity in step 1
   proves `(Ideal.Quotient.mkₐ R J).comp f = g`.
6. Thus `f(n ^ r) ⊆ I + J`, and `f(n ^ (r*t)) ⊆ (I + J) ^ t ⊆ I + J ^ t ⊆ I`:
   each product either has an `I` factor or has all its factors in `J`.
All quotient algebra structures and maps use `def-weil-pbc-algebra-hom-quotient`. -/
theorem FormallySmoothAdic.exists_lift_into_complete
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    (n : Ideal S) (hS : FormallySmoothAdic R S n)
    (I J : Ideal A) [IsAdicComplete I A]
    (t : ℕ) (ht : 1 ≤ t) (hJI : J ^ t ≤ I)
    (hJ : J = ⨅ (m : ℕ) (_ : 1 ≤ m), J ⊔ I ^ m)
    (g : S →ₐ[R] A ⧸ J) (r : ℕ) (hr : 1 ≤ r)
    (hg : ∀ x ∈ n ^ r, g x ∈ I.map (Ideal.Quotient.mk J)) :
    ∃ f : S →ₐ[R] A, (Ideal.Quotient.mkₐ R J).comp f = g ∧
      ∀ x ∈ n ^ (r * t), f x ∈ I := by
  sorry

end Algebra
