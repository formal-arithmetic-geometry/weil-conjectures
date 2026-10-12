module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.StandardSmooth

/-! A reduced factorization through one standard smooth algebra. -/

@[expose] public section

universe u v w

open CategoryTheory

namespace Algebra

noncomputable def reducedAlgHom
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (A : Type w) [CommRing A] [Algebra R A]
    (φ : A →ₐ[R] Λ) : A ⧸ I.map (algebraMap R A) →ₐ[R ⧸ I]
      (Λ ⧸ I.map (algebraMap R Λ)) := by
  let hmap : I.map (algebraMap R A) ≤
      (I.map (algebraMap R Λ)).comap φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change φ (algebraMap R A r) ∈ I.map (algebraMap R Λ)
    rw [show φ (algebraMap R A r) = algebraMap R Λ r by simp]
    exact Ideal.mem_map_of_mem (algebraMap R Λ) hr
  let f := Ideal.Quotient.liftₐ (I.map (algebraMap R A))
    (Ideal.Quotient.mkₐ R (I.map (algebraMap R Λ)) |>.comp φ)
    (fun a ha ↦ (Ideal.Quotient.eq_zero_iff_mem).2 (hmap ha))
  exact
    { toRingHom := f.toRingHom
      commutes' := by
        intro r
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        simp [f] }

/--
The construction is the finite-presentation factorization in Tag 07CK. Apply the
finite-presentation factorization criterion to the reduced map and retain the chosen
standard smooth stage and its two factor maps.
(blueprint: new-lem-popescu-reduction-factor)
-/
theorem exists_popescu_reduction_factor
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R)
    (hΛ : ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ IsStandardSmooth (R ⧸ I) C)
      (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (A : Type w) [CommRing A] [Algebra R A] [FinitePresentation R A]
    (φ : A →ₐ[R] Λ) :
    ∃ (C : Type (max u v w)) (_ : CommRing C) (_ : Algebra (R ⧸ I) C),
      IsStandardSmooth (R ⧸ I) C ∧
        ∃ (β : A ⧸ I.map (algebraMap R A) →ₐ[R ⧸ I] C)
          (δ : C →ₐ[R ⧸ I] Λ ⧸ I.map (algebraMap R Λ)),
          δ.comp β = reducedAlgHom R Λ I A φ := by
  sorry

end Algebra
