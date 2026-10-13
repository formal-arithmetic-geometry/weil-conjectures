/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections

/-! # Kernel torsion for the punctured matching projection

Source: Stacks Project, Tags 0BLH and 05ER, localized chart comparison.
(blueprint: lem-sbc-punctured-matching-chart-kernel-torsion)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- A matching section vanishing on the f-chart is killed by a power of f.

Source: Stacks Project, Tag 05ER, the localized chart comparison in its proof,
using 05EP and 05EQ; the geometric charts are those of Tag 0BLH.
Proof: choose a finite generating family of the maximal ideal and include f,
which belongs to the ideal because hf excludes the closed point from D(f).
Use the affine inverse images under q and the affine scheme E to form the
formal-gluing datum given by D.overlapIso. The sheaf equalizer identifies its
H0 with D.matchingRing. Functoriality of appTop and the Spec–Γ adjunction
identify the f-coordinate of b with ψ(ρ b). If it is zero, its completed
coordinate becomes zero after localization at f by the injectivity of the
overlap equivalence, and each other chart coordinate becomes zero after
localization at f by its overlap equation with the f-chart. Each coordinate
is therefore killed by some power of f. There are finitely many coordinates,
so the maximum of their exponents kills the entire compatible family.
Under the equalizer identification scalar multiplication by f is
multiplication by D.baseMap.hom f; the claimed equation follows. Equivalently,
apply the injectivity part of exists_unique_bijective_h0_localization and the
zero criterion for module localization. This argument uses no chart lifting.
For f = 0 the exponent 1 works. For any nilpotent f, an exponent annihilating
f works. The zero ring and empty charts are included.
(blueprint: lem-sbc-punctured-matching-chart-kernel-torsion) -/
theorem puncturedMatching_chart_kernel_torsion
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
    ∀ b : D.matchingRing, ψ (ρ b) = 0 →
      ∃ n : ℕ, D.baseMap.hom f ^ n * b = 0 := by sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
