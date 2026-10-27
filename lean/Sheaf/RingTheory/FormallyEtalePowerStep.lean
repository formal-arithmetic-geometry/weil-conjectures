/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # One successive infinitesimal inverse for a formally étale map

Source: Stacks Project, Algebra, Tag 0H1D, lemma-formally-etale-lift-infinitesimal
(blueprint: lem-sfb-formally-etale-power-step).

The ring map is the structure map of the algebra. All forward quotient maps and
reductions are Mathlib's canonical constructions. The inverse at level `n` is
specified as a ring homomorphism with both inverse identities, so its algebra
compatibility follows rather than being an extra assumption.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Ideal

/-- Extend the inverse at level `n` uniquely across the next square-zero thickening,
then factor it through the next target ideal power, with both inverse identities
and compatibility with reduction.

Source: Stacks Project, Algebra, Tag 0H1D, lemma-formally-etale-lift-infinitesimal,
the successive dotted arrows and the uniqueness argument
(blueprint: lem-sfb-formally-etale-power-step).

Proof: (1) The equality `I = J.comap (algebraMap A C)` gives preservation of
all ideal powers, hence the canonical quotient maps. Their inverse `g` is
`A`-linear by its left inverse identity on representatives.
(2) The kernel of `A/I^(n+1) → A/I^n` is `I^n/I^(n+1)` and its quotient is
`A/I^n`. It is square zero since `2*n ≥ n+1` for `n ≥ 1`.
(3) Apply the assumed lifting bijection to obtain the unique algebra map `ell`.
(4) If `ell j = [a]` for `j ∈ J`, the lift equality and the inverse identities
give `phi(a) - j ∈ J^n ⊆ J`, so `a ∈ I`. Products of `n+1` such images vanish;
therefore `ell` kills `J^(n+1)`.
(5) Factor `ell` through `C/J^(n+1)`. Its composite with the forward map is the
identity because `ell` is an algebra map.
(6) The other composite, precomposed with the quotient of `C`, and that quotient
itself agree modulo `J^n`. Injectivity of the lifting bijection for the square-zero
ideal `J^n/J^(n+1)` makes them equal, proving the other inverse identity.
(7) Evaluate the defining lift equality on representatives to get compatibility
with reduction. These steps use only the quotient, algebra-map and ideal-power
notions of def-weil-pbc-algebra-hom-quotient; there are no finiteness assumptions. -/
theorem formallyEtale_powerStep
    {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C]
    (I : Ideal A) (J : Ideal C) (hI : I = J.comap (algebraMap A C))
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp (algebraMap A C)))
    (hlift : ∀ (E : Type (max u v)) [CommRing E] [Algebra A E] (N : Ideal E),
      N ^ 2 = ⊥ → Function.Bijective
        (fun h : C →ₐ[A] E ↦ (Ideal.Quotient.mkₐ A N).comp h))
    (n : ℕ) (hn : 1 ≤ n) (g : C ⧸ J ^ n →+* A ⧸ I ^ n)
    (hleft : g.comp (Ideal.quotientMap (J ^ n) (algebraMap A C)
      ((pow_le_pow_left' hI.le n).trans (Ideal.le_comap_pow (algebraMap A C) n))) =
        RingHom.id (A ⧸ I ^ n))
    (hright : (Ideal.quotientMap (J ^ n) (algebraMap A C)
      ((pow_le_pow_left' hI.le n).trans (Ideal.le_comap_pow (algebraMap A C) n))).comp g =
        RingHom.id (C ⧸ J ^ n)) :
    ∃ ell : C →ₐ[A] A ⧸ I ^ (n + 1),
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))).comp
        ell.toRingHom = g.comp (Ideal.Quotient.mk (J ^ n)) ∧
      (∀ ell' : C →ₐ[A] A ⧸ I ^ (n + 1),
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))).comp
          ell'.toRingHom = g.comp (Ideal.Quotient.mk (J ^ n)) → ell' = ell) ∧
      (∀ j : C, j ∈ J → ∃ a : A, a ∈ I ∧ Ideal.Quotient.mk (I ^ (n + 1)) a = ell j) ∧
      (∀ c : C, c ∈ J ^ (n + 1) → ell c = 0) ∧
      ∃ gnext : C ⧸ J ^ (n + 1) →+* A ⧸ I ^ (n + 1),
        gnext.comp (Ideal.Quotient.mk (J ^ (n + 1))) = ell.toRingHom ∧
        gnext.comp (Ideal.quotientMap (J ^ (n + 1)) (algebraMap A C)
          ((pow_le_pow_left' hI.le (n + 1)).trans
            (Ideal.le_comap_pow (algebraMap A C) (n + 1)))) =
              RingHom.id (A ⧸ I ^ (n + 1)) ∧
        (Ideal.quotientMap (J ^ (n + 1)) (algebraMap A C)
          ((pow_le_pow_left' hI.le (n + 1)).trans
            (Ideal.le_comap_pow (algebraMap A C) (n + 1)))).comp gnext =
              RingHom.id (C ⧸ J ^ (n + 1)) ∧
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))).comp gnext =
          g.comp (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))) := by
  sorry

end Ideal
