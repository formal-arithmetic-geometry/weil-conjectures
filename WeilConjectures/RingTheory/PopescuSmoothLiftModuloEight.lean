/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.RingTheory.PopescuLifting
import WeilConjectures.RingTheory.PopescuSmoothLiftModuloEightAux

/-!
# Lifting the factorization modulo the eighth power

Given a nonzerodivisor `π` of a Noetherian ring `R` such that `Λ / π⁸Λ` is ind-smooth over
`R / π⁸`, a map `A → Λ` from a finitely presented `R`-algebra is lifted modulo `π⁴` to a
finitely presented `R`-algebra `D` with unit singular ideal.

## Implementation details

The algebra `D` from `exists_popescu_smooth_lift_data` is smooth at every prime, so its
singular ideal has empty zero locus and is the unit ideal.

## References

* Stacks Project, Smoothing Ring Maps, proof of Lemma 07F5
-/

@[expose] public section

universe u v
open CategoryTheory
open scoped nonZeroDivisors

/-- A smooth factorization modulo π⁸ lifts to a compatible algebra with unit singular ideal:
if `π` is a nonzerodivisor in `R` and in `Λ` and `Λ / π⁸Λ` is ind-smooth over `R / π⁸`, then
there are a finitely presented `R`-algebra `D` with `singularIdeal R D = ⊤`, an `R`-algebra map
`δ : D → Λ`, and an `R`-algebra map `A / π⁴A → D / π⁴D` compatible with `α` and `δ` modulo
`π⁴`. -/
theorem exists_popescu_smooth_lift_modulo_eight
    (R : Type u) (Λ : Type (max u v)) [CommRing R] [CommRing Λ] [Algebra R Λ]
    [IsNoetherianRing R]
    (A : Type (max u v)) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    (α : A →ₐ[R] Λ) (π : R) (hπ : π ∈ R⁰) (hπΛ : algebraMap R Λ π ∈ Λ⁰)
    (hmod : ObjectProperty.ind.{max u v}
      (fun B : CommAlgCat.{max u v} (R ⧸ Ideal.span {π ^ 8}) ↦
        Algebra.Smooth (R ⧸ Ideal.span {π ^ 8}) B)
      (CommAlgCat.of (R ⧸ Ideal.span {π ^ 8})
        (Λ ⧸ (Ideal.span {π ^ 8}).map (algebraMap R Λ)))) :
    ∃ (D : Type (max u v)) (_ : CommRing D) (_ : Algebra R D)
      (_ : Algebra.FinitePresentation R D) (δ : D →ₐ[R] Λ),
      Algebra.singularIdeal R D = ⊤ ∧
      ∃ φ : (A ⧸ Ideal.span {(algebraMap R A π) ^ 4}) →ₐ[R]
        (D ⧸ Ideal.span {(algebraMap R D π) ^ 4}),
        ∀ (a : A) (d : D),
          φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ d →
          Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (α a) =
          Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (δ d) :=
  set_option linter.style.haveILetI false in by
  obtain ⟨D, _instD, _algD, _fpD, δ, hsmooth, hφ⟩ :=
    exists_popescu_smooth_lift_data R Λ A α π hπ hπΛ hmod
  letI : CommRing D := _instD
  letI : Algebra R D := _algD
  letI : Algebra.FinitePresentation R D := _fpD
  have hz : PrimeSpectrum.zeroLocus (Algebra.singularIdeal R D : Set D) = ∅ := by
    rw [(Algebra.singularIdeal_zeroLocus R D).1]
    ext q
    simp only [Set.mem_empty_iff_false, Set.mem_ofPred_eq, iff_false]
    exact fun h => h (hsmooth q)
  have hsing : Algebra.singularIdeal R D = ⊤ :=
    (PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp hz)
  exact ⟨D, inferInstance, inferInstance, inferInstance, δ, hsing, hφ⟩
