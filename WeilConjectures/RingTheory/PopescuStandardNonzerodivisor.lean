/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Smooth.Basic
public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.StrictlyStandardElement
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import WeilConjectures.RingTheory.PopescuStandardNonzerodivisorAux
import WeilConjectures.RingTheory.ElementaryToStrict
import WeilConjectures.RingTheory.PopescuDelocalizeBase

/-! # A standard nonzerodivisor from the field case of Popescu

If Popescu's theorem holds over fields, then for a regular map `R → Λ` from a nonzero reduced
Noetherian ring, every map from a finitely presented `R`-algebra to `Λ` factors through a
finitely presented algebra in which some nonzerodivisor of `R` is strictly standard.

## Implementation details

The finite polynomial quotient construction of the factor algebra lives in universe `max u v`.

## References

* [Stacks, Tag 07F5] (third and fourth paragraphs of the proof)
-/

@[expose] public section

universe u v
open CategoryTheory
open scoped nonZeroDivisors

/-- The field case produces a strictly standard nonzerodivisor after a finite-presentation
factorization. -/
theorem exists_popescu_standard_nonzerodivisor
    (h : ∀ (k : Type u) (Λ : Type (max u v)) [Field k] [CommRing Λ] [Algebra k Λ]
      [IsNoetherianRing Λ],
      RingHom.IsRegular (algebraMap k Λ) →
        ObjectProperty.ind.{max u v}
          (fun B : CommAlgCat.{max u v} k ↦ Algebra.Smooth k B)
          (CommAlgCat.of k Λ))
    (R : Type u) (Λ : Type (max u v)) [CommRing R] [CommRing Λ] [Algebra R Λ]
    [IsNoetherianRing R] [IsNoetherianRing Λ] [Nontrivial R] [IsReduced R]
    (hreg : RingHom.IsRegular (algebraMap R Λ))
    (A : Type (max u v)) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    (α : A →ₐ[R] Λ) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B)
      (_ : Algebra.FinitePresentation R B) (aB : A →ₐ[R] B) (β : B →ₐ[R] Λ) (π : R),
      β.comp aB = α ∧ π ∈ R⁰ ∧
        Algebra.IsStrictlyStandardElement (R := R) (algebraMap R B π) := by
  obtain ⟨B', _, _, _, β', γ', hfactor⟩ :=
    exists_localized_smooth_factorization h R Λ hreg A α
  obtain ⟨B, _, _, hBfp, aB, β, hcomp, π, hs⟩ :=
    Algebra.exists_factorization_isElementaryStandardElement_of_localized_smooth
      α R⁰ β' γ' (by
        ext x
        exact RingHom.congr_fun hfactor x)
  exact ⟨B, inferInstance, inferInstance, hBfp, aB, β, π.val, hcomp, π.property,
    elementary_standard_is_strict hs⟩
