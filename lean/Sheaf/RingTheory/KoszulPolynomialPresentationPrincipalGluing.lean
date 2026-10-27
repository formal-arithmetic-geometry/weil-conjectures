/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.RingTheory.LocallyKoszulRegularIdeal
public import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Koszul polynomial presentations over a principal cover of the target

Source: Stacks Project, More on Algebra, Tag 07D1, Lemma `lemma-lci-local`
(blueprint: lem-sfb-koszul-polynomial-presentation-principal-gluing).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- Finite polynomial presentations with locally Koszul-regular kernel glue over a
finite principal cover of the target. Source: Stacks Project, More on Algebra,
Tag 07D1 (blueprint: lem-sfb-koszul-polynomial-presentation-principal-gluing).

Proof:
1. Choose the finite polynomial surjection α : P → S supplied by `hfinite`, set
   I = ker α, and lift each g_j to h_j in P. It suffices to prove I locally regular.
2. Adjoin an inverse variable z and map P[z] onto S[1/g_j], sending z to 1/g_j.
   The inverse-variable quotient of lem-weil-pbc-localization-away-polynomial-quotient
   makes this map surjective with kernel J_j = IP[z] + (h_j z - 1): the coefficient
   map P[z] → S[z] has kernel IP[z], and multiples of g_j z - 1 lift.
3. Apply lem-sfb-koszul-polynomial-presentation-independence to the given chart
   presentation and this (n+1)-variable presentation. Thus J_j is locally regular.
4. At a prime q containing I the lifted unit relation gives some h_j outside q.
   The ideal q' = qP[z] + (h_j z - 1) is prime: its quotient is the nonzero domain
   (P/q)[1/h_j], by the inverse-variable quotient. Choose a local regular generating
   sequence for J_j at q'. Apply lem-sfb-koszul-inverse-equation-elimination with
   A = P and h = h_j to get d outside q and Koszul-regular generators for I P_d.
5. These witnesses at every q prove the conclusion. For an empty cover the unit
   relation forces S = 0, so I = P and there is no prime containing I. Zero-variable
   presentations and empty generating sequences are allowed throughout. -/
theorem exists_koszulRegular_polynomial_presentation_of_principal_cover
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hfinite : ∃ (N : ℕ) (φ : MvPolynomial (Fin N) R →ₐ[R] S),
      Function.Surjective φ)
    (t : ℕ) (g : Fin t → S) (hg : Ideal.span (Set.range g) = ⊤)
    (hlocal : ∀ j : Fin t,
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] Localization.Away (g j)),
        Function.Surjective α ∧ (RingHom.ker α.toRingHom).IsLocallyKoszulRegular) :
    ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] S),
      Function.Surjective α ∧ (RingHom.ker α.toRingHom).IsLocallyKoszulRegular := by
  sorry

end Algebra
