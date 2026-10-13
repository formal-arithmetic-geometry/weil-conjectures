/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The localized formal-gluing comparison is a ring equivalence on the
principal chart, compatible with the matching numerator.

Source: Stacks Project, Tags 0BLH and 05ER, localized affine chart comparison.
The proof identifies the matching ring with the formal-gluing `H⁰` module,
applies the localization comparison, and transports its inverse through the
affine section identifications.
(blueprint: new-lem-sbc-punctured-matching-chart-restriction-ring-equiv) -/
theorem puncturedMatching_chart_restriction_ringEquiv
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (f : A) (hf :
      (PrimeSpectrum.basicOpen f : (Spec (.of A)).Opens) ≤ U) :
    let W := (D.modelMap ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f)
    let ρ := ((ΓSpecIso D.matchingRing).inv ≫
      (W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι).appTop).hom
    let ψ := (D.puncturedMap ∣_ W).appTop.hom
    ∃ e : Γ((D.puncturedMap ⁻¹ᵁ W).toScheme, ⊤) ≃+*
      Γ(W.toScheme, ⊤),
      ∀ b : D.matchingRing, e (ψ (ρ b)) = ρ b := by
  sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
