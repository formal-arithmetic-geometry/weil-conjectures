/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleCondensedCoefficientFamily
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients

/-! # Admissibility bridge for the intrinsic cup

This module states the coefficient-family bridge needed by the native mixed-support cup.
Source: the coefficient convention of the Frobenius unit in blueprint latest;
`part-duality-trace-formula/sec-lefschetz-verdier/sec-frobenius/
sec-purity-duality-and-frobenius/sk-thm-frobenius/_section.md`.
(blueprint: `lem-pod-admissible-to-localizing-coefficient`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

universe u

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedSectionsCupWeilTransport

/-! The finite-primary, integral, finite-extension, and algebraic-closure branches of the
coefficient-family interface are the corresponding branches of the localizing interface. -/

/-- Admissibility in the coefficient-family interface supplies the localizing coefficient
condition required by the intrinsic native cup construction.

The proof splits the four coefficient branches. In the finite branch, the vanishing
of the power of ell implies the corresponding annihilation of every ring element;
the remaining branches are the same disjuncts with their ring-object isomorphisms.
Source: the coefficient convention in
`literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/sec-purity-duality-and-frobenius/
sk-thm-frobenius/_section.md`
(blueprint: `lem-pod-admissible-to-localizing-coefficient`). -/
theorem localizingAdmissibleCoefficientOfAdmissible
    {D : WeilConjectures.FiniteFieldDatum.{u}}
    (C : D.CoefficientDatum)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : CondensedRing.IsAdmissibleCoefficientFor C (Mon.mk Λ)) :
    IsLocalizingAdmissibleCoefficient C.l Λ := by
  rcases hΛ with hA | hInt | hField | hClosure
  · rcases hA with ⟨A, hRing, hFinite, hTop, hDiscrete, hContinuous, ⟨r, _, hr⟩, e⟩
    let := hRing
    let := hTop
    let := hDiscrete
    let := hContinuous
    refine Or.inl ⟨A, hRing, hTop, hDiscrete, hContinuous, hFinite, ⟨r, ?_⟩, e⟩
    intro a
    simp only [nsmul_eq_mul, Nat.cast_pow, hr, zero_mul]
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hInt))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hField)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hClosure))))

end AlgebraicGeometry.ProEtale.CondensedSectionsCupWeilTransport
