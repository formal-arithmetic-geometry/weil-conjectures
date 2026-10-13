/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections

/-! # Denominator lifting for punctured matching sections

Source: Stacks Project, Tags 0BLH and 05ER, localized chart comparison.
(blueprint: lem-sbc-punctured-matching-chart-power-lift)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- Every chart section lifts to a matching section after clearing a power of `f`.

Source: Stacks Project, Tag 05ER, the localized chart comparison in its proof,
using 05EP and 05EQ; the geometric charts are those of Tag 0BLH.
Proof: choose generators of the maximal ideal and adjoin f to the family. The
hypothesis hf implies f lies in the maximal ideal (the closed point is not in
D(f)); hence this is still a generating family. The inverse images in Y of the
principal opens are affine since q is finite. The scheme E is affine since s
is finite over an affine. Their section algebras and overlap identifications
from D.overlapIso give formal-gluing data over the flat completion map.
The sheaf equalizer for the finite cover of Y identifies H0 of these data
with the explicit pullback D.matchingRing: the chart coordinates glue to the
Y coordinate, and the remaining equality is exactly equality on the overlap.
The localized chart comparison of 05ER, or h0_chart_power_lift in the module
FormalGlueingH0ChartPowerLift, gives n and a compatible family b whose f-chart
coordinate is f^n times the given section. The f-chart is also the inverse
image of W under D.puncturedMap, by D.puncturedMap_over. The projection to it
is ψ composed with ρ, by functoriality of appTop and the Spec–Γ adjunction.
The action of f is multiplication by ψ(ρ(D.baseMap.hom f)); this gives the
stated equation. This uses only the surjectivity part of the chart comparison.
If f is nilpotent the chart is empty and the zero section lifts with n = 0.
Zero component rings and an empty punctured spectrum cause no exception.
(blueprint: lem-sbc-punctured-matching-chart-power-lift) -/
theorem puncturedMatching_chart_power_lift
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (f : A)
    (hf : (PrimeSpectrum.basicOpen f : (Spec (.of A)).Opens) ≤ U) :
    let W := (D.modelMap ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f)
    let ρ := ((ΓSpecIso D.matchingRing).inv ≫
      (W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι).appTop).hom
    let ψ := (D.puncturedMap ∣_ W).appTop.hom
    ∀ t : Γ((D.puncturedMap ⁻¹ᵁ W).toScheme, ⊤),
      ∃ (n : ℕ) (b : D.matchingRing),
        ψ (ρ b) = ψ (ρ (D.baseMap.hom f)) ^ n * t := by sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
