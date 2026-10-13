module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.StandardSmooth

/-! Finite-presentation factorization used by the reduced Popescu factor. -/
@[expose] public section
universe u v w
open CategoryTheory
namespace Algebra
/-- Finite-presentation factorization through a standard smooth reduction.
Source: Stacks Project, Tag 07CK, finite-presentation factorization.
The proof applies the filtered-colimit finite-presentation factorization to the
reduced map and retains the standard smooth stage and its factor maps.
(blueprint: new-lem-popescu-reduction-factor-core) -/
theorem exists_standardSmooth_reduction_factorization_core
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R)
    (hΛ : ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ IsStandardSmooth (R ⧸ I) C)
      (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (A : Type w) [CommRing A] [Algebra R A] [FinitePresentation R A]
    (φ : A →ₐ[R] Λ) :
    ∃ (C : Type (max u v w)) (_ : CommRing C) (_ : Algebra R C),
      FinitePresentation R C ∧
      ∃ (ι : A →ₐ[R] C) (φ' : C →ₐ[R] Λ), φ'.comp ι = φ ∧
        IsStandardSmooth (R ⧸ I) (C ⧸ I.map (algebraMap R C)) := by
  sorry
end Algebra
