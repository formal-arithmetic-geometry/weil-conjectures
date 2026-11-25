/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.IndStandardSmooth
import WeilConjectures.RingTheory.PopescuStandardReductionFactor
import WeilConjectures.RingTheory.StandardSmoothQuotientLift
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# The presentation construction in Popescu's square-zero lifting lemma

A map from a finitely presented `R`-algebra `A` to `Λ` factors through a finitely presented
`A'`, and `A' / IA'` is identified with `B / IB` for a smooth `R`-algebra `B`, provided that
`Λ / IΛ` is a filtered colimit of smooth algebras.

## Implementation details

`B = R[x, z] / (f, z * D - 1)` lifts a standard smooth presentation of `A' / IA'`, where `D`
is the lifted Jacobian minor. No square-zero hypothesis is used in this construction, only in
the subsequent lifting.

## References

* [Stacks, Tag 07CK]
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Algebra

/-- The presentation construction preceding square-zero lifting in Popescu's lemma. -/
theorem exists_smooth_reduction_factorization
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R)
    (hΛ : ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ Smooth (R ⧸ I) C)
      (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (A : Type w) [CommRing A] [Algebra R A] [FinitePresentation R A]
    (φ : A →ₐ[R] Λ) :
    ∃ (A' : Type (max u v w)) (_ : CommRing A') (_ : Algebra R A'),
      FinitePresentation R A' ∧
      ∃ (ι : A →ₐ[R] A') (φ' : A' →ₐ[R] Λ), φ'.comp ι = φ ∧
      ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra R B),
        Smooth R B ∧
          Nonempty ((B ⧸ I.map (algebraMap R B)) ≃ₐ[R]
            (A' ⧸ I.map (algebraMap R A'))) := by
  have hstd := ind_isStandardSmooth_of_ind_smooth (R ⧸ I)
    (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))) hΛ
  obtain ⟨A', hring, halg, hfp, ι, φ', hcomp, hred⟩ :=
    exists_standardSmooth_reduction_factorization R Λ I hstd A φ
  let := hring
  let := halg
  let := hred
  obtain ⟨B, hBring, hBalg, hBstd, ⟨e⟩⟩ :=
    exists_standardSmooth_quotient_lift R I (A' ⧸ I.map (algebraMap R A'))
  let := hBring
  let := hBalg
  let := hBstd
  exact ⟨A', hring, halg, hfp, ι, φ', hcomp, B, hBring, hBalg,
    inferInstance, ⟨e.restrictScalars R⟩⟩

end Algebra
