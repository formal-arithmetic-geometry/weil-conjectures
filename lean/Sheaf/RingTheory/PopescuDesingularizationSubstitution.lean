/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.RingTheory.StrictlyStandardElement
import Sheaf.LinearAlgebra.Matrix.LeftInverseMinors

/-! # Polynomial substitution in the desingularization construction

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07CR, through the
construction of the polynomials `g` and the two observations on the remaining relations.
-/

@[expose] public section

universe u v w

namespace Algebra

open MvPolynomial

/-- The polynomial part of desingularization, before descending evaluation to a quotient
or proving any smoothness. The variable-index universe lift puts the polynomial quotient
in the universe required by the original algebra.

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07CR, presentation, translation,
scalar left inverse, substitution, and the two observations on the remaining relations.
(blueprint: lem-weil-pbc-popescu-desingularization-substitution).

Proof: choose a strictly standard presentation with `c` selected relations. Translate its
variables by lifts of their images under the section, so their images under `α` are
`π⁴λᵢ` and every relation has constant term in `π⁴R`. Write its linear coefficients as
`rⱼᵢ`. Applying the section to the strictly standard minor identity gives a linear
combination of constant minors equal to `uπ`, where `u = 1 - π³t`. Apply the scalar
left-inverse lemma to obtain `s` with `Σᵢ rⱼᵢsᵢₖ = uπδⱼₖ`. Substitute
`ξᵢ = π²Σₖsᵢₖvₖ + π³wᵢ`. For the first `c` relations, their constant and higher-degree
terms are divisible by `π⁴`, and their linear terms are
`π³(vⱼ + Σᵢrⱼᵢwᵢ)` modulo `π⁴`. Construct the corresponding polynomials `gⱼ` by dividing
these displayed coefficients, obtaining `fⱼ(ξ) = π³gⱼ` and
`gⱼ = vⱼ + Σᵢrⱼᵢwᵢ + πeⱼ`. This is coefficientwise division of explicitly divisible
terms, not cancellation of a possibly zero divisor. All substituted relations lie in
`(π²)`. Substitute into the strictly standard ideal-square relation to get
`πfⱼ(ξ)` in `(g)+(f(ξ))²` for each remaining relation. The chosen lift
`P.σ (algebraMap R A π)` differs from `C π` by an element of the relation ideal, so
replacing it by `C π` changes its product with a relation only by an ideal-square
element. The first `c` relations already lie in `(g)`. The coefficient-ring lift and
the lifted variable indices do not change
any of these identities. This argument does not need annihilator stability or any
Noetherian hypothesis. -/
theorem exists_desingularization_substitution
    (R : Type u) (Λ : Type v) (A : Type w)
    [CommRing R] [CommRing Λ] [CommRing A]
    [Algebra R Λ] [Algebra R A] [FinitePresentation R A]
    (π : R) (α : A →ₐ[R] Λ)
    (hstandard : IsStrictlyStandardElement (R := R) (algebraMap R A π))
    (hρ : ∃ ρ :
      (A ⧸ Ideal.span {(algebraMap R A π) ^ 4}) →ₐ[R]
        (R ⧸ Ideal.span {π ^ 4}),
      ∀ (a : A) (r : R),
        ρ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ r →
        Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (α a) =
          Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (algebraMap R Λ r)) :
    ∃ (n m c : ℕ) (P : Presentation R A (Fin n) (Fin m)) (hc : c ≤ m)
      (s : Fin n → Fin c → R) (lam : Fin n → Λ)
      (r : Fin c → Fin n → R)
      (g e : Fin c → MvPolynomial (ULift.{w} (Fin c ⊕ Fin n)) R),
      let ξ : Fin n → MvPolynomial (ULift.{w} (Fin c ⊕ Fin n)) R := fun i ↦
        C π ^ 2 * ∑ k, C (s i k) *
          X (σ := ULift.{w} (Fin c ⊕ Fin n)) (ULift.up (Sum.inl k)) +
          C π ^ 3 *
            X (σ := ULift.{w} (Fin c ⊕ Fin n)) (ULift.up (Sum.inr i))
      let F := fun j : Fin m ↦ aeval (R := R) ξ (P.relation j)
      (∀ j, g j = (X (σ := ULift.{w} (Fin c ⊕ Fin n)) (ULift.up (Sum.inl j)) :
        MvPolynomial (ULift.{w} (Fin c ⊕ Fin n)) R) +
        ∑ i, C (r j i) *
          X (σ := ULift.{w} (Fin c ⊕ Fin n)) (ULift.up (Sum.inr i)) + C π * e j) ∧
      (∀ j, F (Fin.castLE hc j) = C π ^ 3 * g j) ∧
      (∀ j, F j ∈ Ideal.span {C π ^ 2}) ∧
      (∀ j, C π * F j ∈
        Ideal.span (Set.range g) + (Ideal.span (Set.range F)) ^ 2) ∧
      (∀ i, α (P.val i) = algebraMap R Λ π ^ 4 * lam i) := by
  sorry

end Algebra
