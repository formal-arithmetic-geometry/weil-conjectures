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
STATEMENT-DISPUTED: The claim is false without a finite-presentation hypothesis on A.
Take R = Λ = C = ℤ, I = 0, and A = ℤ[x₀,x₁,…]. Let φ be the augmentation xⱼ ↦ 0.
Since I = 0, its images in A and Λ are zero; identify all quotients by these ideals
with the original rings. Give C its resulting ℤ/0-algebra structure. Then hC holds
because ℤ is standard smooth over itself. Take β to be the induced augmentation
A/0 → ℤ and δ to be the identity ℤ → ℤ/0 under these identifications. The definition
of reducedAlgHom gives the induced augmentation, so δ.comp β equals it and hfactor holds.

For any proposed finite n, m, relations gᵢ, and integer lifts aₖ, the evaluation condition
is gᵢ(xⱼ = 0, yₖ = aₖ) = 0, since membership in IΛ = 0 means equality to zero.
Thus each gᵢ has zero augmentation when the added variables yₖ are sent to their lifts
(not necessarily when yₖ = 0). Only finitely many xⱼ occur in all coefficients of all gᵢ;
call their index set S. Put B = ℤ[xⱼ : j ∈ S] and D = B[y₀,…,yₙ₋₁]/(g₀,…,gₘ₋₁).
The preceding evaluation descends to a unital map D → ℤ, so D is nonzero. The displayed
quotient in the conclusion is D[xⱼ : j ∉ S], since every relation belongs to B[y].
Infinitely many remaining xⱼ are therefore freely adjoined. Any finite collection of
quotient elements involves only finitely many of these variables. Pick an unused j;
the ℤ-subalgebra they generate omits xⱼ, by uniqueness of polynomial coefficients over
the nonzero ring D. Hence this quotient is not finitely generated, and consequently not
finitely presented, over ℤ. This contradicts IsStandardSmooth.finitePresentation.

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
