/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Localization.Away.Basic

import WeilConjectures.AlgebraicGeometry.EtaleAwayOfLocalizedCotangentVanishing
import WeilConjectures.AlgebraicGeometry.SmoothSectionDifferentialBasis
import WeilConjectures.RingTheory.SectionDifferentialBasisQuotient

/-! # Étale neighbourhoods along a smooth algebra section

## References

* [Stacks Project, Tag 07M7](https://stacks.math.columbia.edu/tag/07M7)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A section factors through an algebra that is étale near every prime containing
the section kernel. No global étale localization or quotient equivalence is asserted. -/
theorem exists_etale_neighbourhoods_of_smooth_section
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal A) (σ : B →ₐ[A] A ⧸ J)
    (hB : Smooth (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)) :
    ∃ (C : CommAlgCat.{u} A) (j : B →ₐ[A] C) (τ : C →ₐ[A] A ⧸ J),
      τ.comp j = σ ∧
      ∀ q : PrimeSpectrum C, RingHom.ker τ.toRingHom ≤ q.asIdeal →
        ∃ s : C, s ∉ q.asIdeal ∧
          Etale (Spec.map (CommRingCat.ofHom
            ((algebraMap C (Localization.Away s)).comp (algebraMap A C)))) := by
  classical
  have : Algebra.Smooth A B := by
    exact RingHom.smooth_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hB)
  obtain ⟨A₁, hA₁, D, instAD, instTower, hD, j, τ, hτj, hπ, n, f, hf, hb⟩ :=
    exists_smooth_section_differential_basis A B J σ
  let : Algebra A₁ D := instAD
  let : IsScalarTower A A₁ D := instTower
  let : Algebra.Smooth A₁ D := hD
  let η := τ.toRingHom.comp (algebraMap A₁ D)
  let : Algebra A₁ (A ⧸ J) := η.toAlgebra
  let σ₁ : D →ₐ[A₁] A ⧸ J :=
    { τ.toRingHom with commutes' := fun _ ↦ rfl }
  let a : Ideal D := Ideal.span (Set.range f)
  have ha : a ≤ RingHom.ker τ.toRingHom := by
    apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact hf i
  let C := D ⧸ a
  let τC : C →ₐ[A] A ⧸ J := Ideal.Quotient.liftₐ a τ (fun x hx ↦ ha hx)
  let jC : B →ₐ[A] C := (Ideal.Quotient.mkₐ A a).comp j
  have hτC : τC.toRingHom.comp (Ideal.Quotient.mk a) = σ₁.toRingHom := by
    rfl
  have : Algebra.FinitePresentation A₁ C :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range f))
  refine ⟨CommAlgCat.of A C, jC, τC, ?_, ?_⟩
  · change τC.comp ((Ideal.Quotient.mkₐ A a).comp j) = σ
    rw [← AlgHom.comp_assoc]
    exact hτj
  · intro q hq
    obtain ⟨hH, hΩ⟩ :=
      Algebra.localized_cotangent_vanishes_of_section_differential_basis
        A₁ D (A ⧸ J) σ₁ hπ n f hf hb τC.toRingHom hτC q hq
    obtain ⟨s, hs, hEt⟩ :=
      exists_etale_away_of_localized_cotangent_vanishing (A := A₁) q.asIdeal hH hΩ
    refine ⟨s, hs, ?_⟩
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap A A₁))) := hA₁
    have : Etale (Spec.map
        (CommRingCat.ofHom (algebraMap A₁ (Localization.Away s)))) := hEt
    have hcomp := Etale.etale_comp
      (Spec.map (CommRingCat.ofHom (algebraMap A A₁)))
      (f := Spec.map (CommRingCat.ofHom (algebraMap A₁ (Localization.Away s))))
    convert hcomp using 1
    rw [← Spec.map_comp]
    congr 2
    ext x
    change algebraMap C (Localization.Away s) (algebraMap A C x) =
      algebraMap A₁ (Localization.Away s) (algebraMap A A₁ x)
    rw [← IsScalarTower.algebraMap_apply A C (Localization.Away s),
      ← IsScalarTower.algebraMap_apply A A₁ (Localization.Away s)]


end AlgebraicGeometry
