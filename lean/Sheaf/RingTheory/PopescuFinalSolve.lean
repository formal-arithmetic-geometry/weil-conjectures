/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.RingTheory.SingularIdeal

/-!
# Factoring through a smooth algebra when the extended singular ideal is the unit ideal

Source: Stacks Project, Smoothing Ring Maps, Lemma 16.2.8, Tag 07EU (`lemma-final-solve`)
(blueprint: lem-weil-pbc-popescu-final-solve).
-/

universe u v w

namespace Algebra

/-- If the singular ideal of a finitely presented `R`-algebra `A` extends to the unit ideal
in `Λ`, the given map factors through a smooth `R`-algebra.
Source: Stacks Project, Smoothing Ring Maps, Lemma 16.2.8, Tag 07EU
(blueprint: lem-weil-pbc-popescu-final-solve).

Proof: (1) Unit-ideal extension gives finitely many `fᵢ ∈ singularIdeal R A` and `λᵢ ∈ Λ`
with `∑ α(fᵢ) λᵢ = 1` (definition node `def-weil-pbc-singular-ideal`).
(2) Set `B = A[x₁, …, xᵣ]/(∑ fᵢ xᵢ - 1)`. Evaluation `xᵢ ↦ λᵢ` descends to `B → Λ`,
and its composite with `A → B` is `α` by construction.
(3) Each `A_{fᵢ}` is smooth over `R`, by
`lem-weil-pbc-singular-ideal-localization-smooth`.
(4) Each `B_{fᵢ}` is a polynomial algebra in the other variables over `A_{fᵢ}`, by
`lem-weil-pbc-linear-equation-localization-polynomial`; it is smooth over `A_{fᵢ}` by
`lem-weil-pbc-polynomial-ring-smooth` and invariance under algebra isomorphism.
(5) Composition of smooth maps gives smoothness of `B_{fᵢ}` over `R`, by
`lem-weil-pbc-smooth-ring-map-base-change-composition`.
(6) The relation in `B` makes the images of the `fᵢ` generate its unit ideal, so locality
of smoothness gives smoothness of `B` over `R` by
`lem-weil-pbc-smooth-ring-map-local-on-cover`. For an empty family, `Λ` and `B` are zero
rings and the same argument uses the empty cover. The carrier of `B` can be taken in
`Type v`, since this explicit polynomial quotient over `A : Type v` lives there. -/
theorem exists_smooth_factorization_of_singularIdeal_map_eq_top
    {R : Type u} {A : Type v} {Λ : Type w}
    [CommRing R] [CommRing A] [CommRing Λ] [Algebra R A] [Algebra R Λ]
    [FinitePresentation R A] (α : A →ₐ[R] Λ)
    (h : Ideal.map α.toRingHom (singularIdeal R A) = ⊤) :
    ∃ (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      Smooth R B ∧ ∃ (β : A →ₐ[R] B) (γ : B →ₐ[R] Λ), γ.comp β = α := by
  sorry

end Algebra
