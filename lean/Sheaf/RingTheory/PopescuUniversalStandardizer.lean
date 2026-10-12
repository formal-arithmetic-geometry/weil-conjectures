/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.RingTheory.PopescuResolution
public import Sheaf.RingTheory.StrictlyStandardElement
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.RingTheory.ImprovePresentation
import Sheaf.RingTheory.SingularIdeal
import Sheaf.RingTheory.SingularIdealLocalizationSmooth
import Sheaf.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower
import Sheaf.RingTheory.StrictlyStandardBaseChange

/-!
# The universal standardizer before choosing parameters

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FJ,
items item-generators through item-strictly-standard and item-first-solve.
-/

@[expose] public section

universe u v w
open scoped TensorProduct
namespace Algebra

/-- The universal algebra with relations `x_i^(2N) = sum_j z_ij a_j` has an
improved presentation whose standard powers and singular-ideal inclusion survive
every polynomial base change. This lemma chooses no parameters in the target ring
and no Artinian solution.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FJ,
items item-generators, item-standardizer, item-elkik, item-strictly-standard,
and the justification of item-first-solve.
(blueprint: lem-weil-pbc-popescu-universal-standardizer).

Proof: Since A is finitely presented over the field k, it is Noetherian. Choose
finite generators a_j of its singular ideal. Construct B as the quotient of the
polynomial algebra over A on x_i,z_ij by the displayed d relations; its presentation
P is the quotient presentation. Give B the k[x]-structure sending X_i to x_i.
On each a_j-open, eliminate z_ij to identify the localization with a polynomial
algebra over A localized at a_j, after extending scalars to k[x]. This is smooth.
The relations show that the a_j generate the unit ideal on each x_i-open, so these
opens are smooth too. Apply 07CE to obtain C₀ and its retraction ρ. The improved
differentials are finite free on each x_i-open. Over the Noetherian base k[x], C₀
is finitely presented; 07EZ(e) supplies a common positive c for which every x_i^c
is strictly standard. Define β₀ by A → B → C₀. The retraction gives ρβ₀ = A → B.
For any base change, smoothness on the a_j-opens persists, so the extended singular
ideal of A lies in the singular ideal of the base-changed C₀. Extend along hρ and
take radicals to get the Popescu-ideal inclusion. Strict standardness persists by
07CC. Zero is strictly standard using any finite presentation, c = 0 in the
definition and zero coefficients of the minors: the lift of zero differs from
zero by an element of the relation ideal, so its product with a relation is in
the square of that ideal. All carriers can be the finite polynomial quotients
and the explicit symmetric algebra used by 07CE, in Type(max u v). -/
theorem exists_popescu_universal_standardizer
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] (d N : ℕ) (hN : 0 < N) :
    let S := MvPolynomial (Fin d) k
    ∃ (s : ℕ) (a : Fin s → A), Ideal.span (Set.range a) = singularIdeal k A ∧
      ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra k B)
        (_ : Algebra A B) (_ : IsScalarTower k A B)
        (_ : Algebra S B) (_ : IsScalarTower k S B)
        (P : Presentation A B (Fin d ⊕ (Fin d × Fin s)) (Fin d)),
        (∀ i, P.val (Sum.inl i) = algebraMap S B (MvPolynomial.X i)) ∧
        (∀ i : Fin d, P.relation i =
          ((MvPolynomial.X (Sum.inl i) :
            MvPolynomial (Fin d ⊕ (Fin d × Fin s)) A) ^ (2 * N) -
            ∑ j : Fin s, MvPolynomial.X (Sum.inr (i, j)) * MvPolynomial.C (a j) :
              MvPolynomial (Fin d ⊕ (Fin d × Fin s)) A)) ∧
      ∃ (C₀ : Type (max u v)) (_ : CommRing C₀) (_ : Algebra k C₀)
        (_ : Algebra S C₀) (_ : IsScalarTower k S C₀)
        (_ : FinitePresentation S C₀)
        (β₀ : A →ₐ[k] C₀) (ρ : C₀ →ₐ[S] B) (c : ℕ),
        0 < c ∧ (ρ.restrictScalars k).comp β₀ = IsScalarTower.toAlgHom k A B ∧
        ∀ (R : Type u) [CommRing R] [Algebra k R] [Algebra S R]
          [IsScalarTower k S R] [Algebra R Λ] [IsScalarTower k R Λ]
          [Algebra S Λ] [IsScalarTower S R Λ] [IsScalarTower k S Λ]
          (h : B →ₐ[S] Λ),
          let C := R ⊗[S] C₀
          let γ := AlgHom.liftEquiv S R C₀ Λ (h.comp ρ)
          popescuIdeal ((h.restrictScalars k).comp (IsScalarTower.toAlgHom k A B)) ≤
              popescuIdeal γ ∧
            ∀ x : R, (x = 0 ∨ ∃ i : Fin d,
              x = algebraMap S R (MvPolynomial.X i ^ c)) →
              IsStrictlyStandardElement (R := R) (algebraMap R C x) := by sorry

end Algebra
