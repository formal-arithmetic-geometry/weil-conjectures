/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
import Sheaf.RingTheory.FormalGlueingH0Localization
import Sheaf.AlgebraicGeometry.Morphisms.PuncturedMatchingChartRestrictionLeftInverse

/-! # Vanishing of a localized matching numerator

Source: Stacks Project, Tags 0BLH and 05ER.
(blueprint: lem-sbc-punctured-matching-chart-kernel-torsion-injectivity)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- A matching-ring numerator whose punctured chart section vanishes has zero
section on the corresponding principal open of the affine candidate.

Source: Stacks Project, Tag 0BLH, proof (construction of the chart algebras),
and Tag 05ER, proof (localized first-projection comparison).

Proof: Since the closed point is absent from D(f), f lies in the maximal ideal.
Choose generators of that ideal and append f. Their principal opens cover U.
Finiteness of q makes their inverse images affine; finiteness of s makes E affine.
The overlap isomorphism supplies the completed chart comparisons, and restriction
supplies the pairwise chart comparisons. These satisfy the cocycle equations.
The sheaf equalizer for this finite cover identifies the underlying A-module of
D.matchingRing with the formal-gluing module H0. The completion map is flat,
so exists_unique_bijective_h0_localization identifies H0 localized at f with
the appended f-chart module. The principal-open section ring of Spec D.matchingRing
is the localization of D.matchingRing at D.baseMap.hom f. Under these identifications,
functoriality of appTop and the Spec-global-sections adjunction identify the
localized first projection with the pullback along D.puncturedMap restricted to W.
Its injectivity sends the assumed zero image of the numerator to zero in that
principal-open section ring. If f is nilpotent (including f = 0), W is empty
and its section ring is the zero ring, so the conclusion holds directly.
This step asserts only vanishing in the chart ring; clearing its denominator
is a separate localization zero-criterion argument.
(blueprint: lem-sbc-punctured-matching-chart-kernel-torsion-injectivity) -/
theorem puncturedMatching_chart_section_injective
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
    ∀ b : D.matchingRing, ψ (ρ b) = 0 → ρ b = 0 := by
  dsimp only
  obtain ⟨g, hg⟩ := puncturedMatching_chart_restriction_leftInverse hU D f hf
  intro b hb
  have h := hg b
  rw [hb, map_zero] at h
  exact h.symm

end AlgebraicGeometry.Scheme.CompletionGluingData
