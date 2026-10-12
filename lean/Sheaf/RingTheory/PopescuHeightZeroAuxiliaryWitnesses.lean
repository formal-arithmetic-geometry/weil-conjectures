/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.RingTheory.PopescuResolution
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Sheaf.RingTheory.PopescuAuxiliaryAlgebraLocalizations
import Sheaf.RingTheory.SingularIdeal
import Sheaf.RingTheory.SingularIdealLocalizationSmooth

/-!
# Singular elements in the height-zero auxiliary algebra

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FA, auxiliary algebra construction.
(blueprint: lem-weil-pbc-popescu-height-zero-auxiliary-witnesses)
-/

@[expose] public section

universe u v t

open scoped BigOperators

namespace Algebra

/-- The auxiliary algebra transports a singular element of an intermediate algebra and
powers of finitely many singular elements of the original algebra.

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FA, construction and the two
localizations in its proof.
(blueprint: lem-weil-pbc-popescu-height-zero-auxiliary-witnesses)

Proof: Since A is Noetherian and C is finitely presented over R, the map A to C makes
C a finitely presented A-algebra. Choose C = A[x_k]/(f_j), and lift c to a polynomial p.
For the indices i in s, put L = product of the lambda_i. Each lambda_i annihilates
alpha(a_i)^(n_i), so L does too. Construct the actual quotient
B = A[x_k,y_i,z,t_ij]/(f_j - sum_i y_i*t_ij, z*y_i).
Its structure map from A and the evaluation x_k at their images in Lambda, y_i at
alpha(a_i)^(n_i), z at L, and t_ij at zero give beta and delta; the relations vanish.
B is finitely presented over R by the finite polynomial presentation and composition.
Let c' be the class of p. The first auxiliary localization identifies B_z with
C[t_ij,z]_z, respecting c'. Since c belongs to the singular ideal of C, C_c is smooth
over R by the singular-ideal localization theorem. Polynomial extension and localization
are smooth over C_c, so the localization of B at z*c' is smooth over R. Thus z*c'
belongs to the singular ideal of B. Its image is L*gamma(c), which gives b.
For each i, the second auxiliary localization identifies B_(y_i) with a localization
of a polynomial algebra over A. Localizing further at beta(a_i) gives a smooth algebra
over A_(a_i). Since a_i belongs to the singular ideal of A, A_(a_i) is smooth over R.
Composition of these smooth maps and the iterated-localization isomorphism show that
B_(beta(a_i)*y_i) is smooth over R. Thus beta(a_i)*y_i belongs to the singular ideal
of B. Take this element as d_i: its image is alpha(a_i)^(n_i+1).
For s empty the construction is C[z] and only b is required; all products are one.
No witness is chosen as definition data: B is the polynomial quotient just described.
-/
theorem exists_popescu_height_zero_auxiliary_witnesses
    {R : Type u} {A : Type v} {Λ : Type t} {C : Type (max u v)}
    [CommRing R] [CommRing A] [CommRing Λ] [CommRing C]
    [Algebra R A] [Algebra R Λ] [Algebra R C]
    [IsNoetherianRing R] [FinitePresentation R A] [FinitePresentation R C]
    (α : A →ₐ[R] Λ) (β : A →ₐ[R] C) (γ : C →ₐ[R] Λ)
    (hcomp : γ.comp β = α) (s : Finset A)
    (hs : ∀ a ∈ s, a ∈ singularIdeal R A)
    (n : s → ℕ) (ell : s → Λ)
    (hkill : ∀ a : s, ell a * α a.val ^ n a = 0)
    (c : C) (hc : c ∈ singularIdeal R C) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
      ∃ (β' : A →ₐ[R] B) (δ : B →ₐ[R] Λ),
        FinitePresentation R B ∧ δ.comp β' = α ∧
        (∃ b ∈ singularIdeal R B, δ b = (∏ a : s, ell a) * γ c) ∧
        (∀ a : s, ∃ d ∈ singularIdeal R B, δ d = α a.val ^ (n a + 1)) := by
  sorry

end Algebra
