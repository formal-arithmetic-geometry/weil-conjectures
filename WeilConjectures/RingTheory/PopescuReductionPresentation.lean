/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.StandardSmooth
import WeilConjectures.RingTheory.PopescuReductionPresentationCore
import WeilConjectures.RingTheory.PopescuReductionPresentationFromFactor

/-! # Polynomial data for a standard smooth stage modulo an ideal

If `Λ / IΛ` is a filtered colimit of standard smooth `R/I`-algebras, then a map from a finitely
presented `R`-algebra `A` to `Λ` yields polynomial equations `g` over `A`, with lifts in `Λ` of
the variables at which they evaluate into `IΛ`, such that the reduced equations define a
standard smooth `R/I`-algebra.

## Implementation details

No factor algebra over `R` is constructed here. The lifting claims also hold for empty
presentations, the zero ring and `I = ⊤`.

## References

* [Stacks, Tag 07CK] (the first four steps of the proof)
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Algebra

/-- Polynomial equations over `A` with lifts in `Λ`, evaluating into `IΛ`, whose reductions
modulo `I` present a standard smooth `R/I`-algebra. -/
theorem exists_popescu_reduction_presentation
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R)
    (hΛ : ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ IsStandardSmooth (R ⧸ I) C)
      (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (A : Type w) [CommRing A] [Algebra R A] [FinitePresentation R A]
    (φ : A →ₐ[R] Λ) :
    ∃ (n m : ℕ) (g : Fin m → MvPolynomial (Fin n) A) (lifts : Fin n → Λ),
      (∀ i, MvPolynomial.eval₂ φ.toRingHom lifts (g i) ∈ I.map (algebraMap R Λ)) ∧
      IsStandardSmooth (R ⧸ I)
        (MvPolynomial (Fin n) (A ⧸ I.map (algebraMap R A)) ⧸
          Ideal.span (Set.range fun i ↦
            MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R A))) (g i))) := by
  obtain ⟨C, hCring, hCalg, hC, β, δ, hfactor⟩ :=
    exists_popescu_reduction_factor R Λ I hΛ A φ
  let _ := hCring
  let _ := hCalg
  obtain ⟨n, m, g, lifts, h_eval, hstd⟩ :=
    exists_popescu_reduction_presentation_of_factor R Λ I A φ C hC β δ hfactor
  exact ⟨n, m, g, lifts, h_eval, hstd⟩

end Algebra
