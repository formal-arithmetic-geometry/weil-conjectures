/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
import WeilConjectures.RingTheory.FilteredColimitOfFactorization
import WeilConjectures.RingTheory.SmoothStandardSmoothRetract
import WeilConjectures.RingTheory.IndSmoothFinitePresentationFactorization

/-!
# Filtered colimits of standard smooth algebras

A filtered colimit of smooth algebras is a filtered colimit of standard smooth algebras.

## Implementation details

Algebras and index categories live in universe `max u v`, so that the category of finitely
presented `R`-algebras with maps to the colimit is small. Every map from a finitely presented
algebra to the colimit factors through a smooth algebra, which is a retract of a standard smooth
algebra; the factorization criterion for filtered colimits then applies.

## References

* [Stacks, Tag 07CI]
* [Stacks, Tag 07CH]
* [Stacks, Tag 07C3]
-/

@[expose] public section

universe u v

open CategoryTheory

namespace Algebra

/-- A filtered colimit of smooth `R`-algebras is a filtered colimit of standard smooth
`R`-algebras (both in the sense of `ObjectProperty.ind`). -/
theorem ind_isStandardSmooth_of_ind_smooth
    (R : Type u) [CommRing R] (Λ : CommAlgCat.{max u v} R)
    (h : ObjectProperty.ind.{max u v} (fun B : CommAlgCat.{max u v} R ↦ Smooth R B) Λ) :
    ObjectProperty.ind.{max u v} (fun C : CommAlgCat.{max u v} R ↦ IsStandardSmooth R C)
      Λ := by
  classical
  let E : Set (CommAlgCat.{max u v} R) := {C | IsStandardSmooth R C}
  have hfp : ∀ C ∈ E, FinitePresentation R C := by
    intro C hC
    have : IsStandardSmooth R C := hC
    infer_instance
  have hfactor : ∀ (A : CommAlgCat.{max u v} R), FinitePresentation R A →
      ∀ (α : A ⟶ Λ), ∃ (C : CommAlgCat.{max u v} R), C ∈ E ∧
        ∃ (β : A ⟶ C) (γ : C ⟶ Λ), β ≫ γ = α := by
    intro A hA α
    have : FinitePresentation R A := hA
    obtain ⟨B, hB, hRB, hsm, β, δ, hδβ⟩ :=
      exists_smooth_factorization_of_ind_smooth α.hom h
    obtain ⟨C, hC, hRC, hstd, ι, ρ, hρι, _⟩ :=
      Smooth.exists_standardSmooth_retract R B
    refine ⟨CommAlgCat.of R C, hstd, CommAlgCat.ofHom (ι.comp β),
      CommAlgCat.ofHom (δ.comp ρ), ?_⟩
    apply CommAlgCat.hom_ext
    change (δ.comp ρ).comp (ι.comp β) = α.hom
    rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc ρ, hρι]
    simpa using hδβ
  obtain ⟨J, hJ, hfiltered, D, ι, hD, ⟨hc⟩⟩ :=
    CommAlgCat.exists_filtered_colimit_of_factorization R Λ E hfp hfactor
  exact ⟨J, hJ, hfiltered, ⟨D, ι, hc⟩, hD⟩

end Algebra
