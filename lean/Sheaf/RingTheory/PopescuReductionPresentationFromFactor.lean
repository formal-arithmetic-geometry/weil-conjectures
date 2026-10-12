module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Sheaf.RingTheory.PopescuReductionPresentationCore

/-! Lifting a finite polynomial presentation from a reduced standard smooth factor. -/

@[expose] public section

universe u v w

open CategoryTheory

namespace Algebra

/--
The coefficient and variable lifting argument is Tag 07CK, steps 3--4. Choose a finite
polynomial presentation of the reduced standard smooth factor, lift its coefficients and
variable images through the quotient maps, and compare evaluations in the reduced target.
(blueprint: new-lem-popescu-reduction-presentation-from-factor)
-/
theorem exists_popescu_reduction_presentation_of_factor
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (A : Type w) [CommRing A] [Algebra R A]
    (φ : A →ₐ[R] Λ)
    (C : Type (max u v w)) [CommRing C] [Algebra (R ⧸ I) C]
    (hC : IsStandardSmooth (R ⧸ I) C)
    (β : A ⧸ I.map (algebraMap R A) →ₐ[R ⧸ I] C)
    (δ : C →ₐ[R ⧸ I] Λ ⧸ I.map (algebraMap R Λ))
    (hfactor : δ.comp β = reducedAlgHom R Λ I A φ) :
    ∃ (n m : ℕ) (g : Fin m → MvPolynomial (Fin n) A) (lifts : Fin n → Λ),
      (∀ i, MvPolynomial.eval₂ φ.toRingHom lifts (g i) ∈
        I.map (algebraMap R Λ)) ∧
      IsStandardSmooth (R ⧸ I)
        (MvPolynomial (Fin n) (A ⧸ I.map (algebraMap R A)) ⧸
          Ideal.span (Set.range fun i ↦
            MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R A))) (g i))) := by
  sorry

end Algebra
