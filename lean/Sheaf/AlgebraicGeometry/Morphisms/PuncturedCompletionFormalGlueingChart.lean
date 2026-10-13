/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
public import Sheaf.RingTheory.FormalGlueingH0

/-! # Geometric realization of a formal glueing chart

Source: Stacks Project, Tag 0BLH, first two proof paragraphs; Tag 05EL,
the definition of compatible sections.
(blueprint: lem-sbc-punctured-completion-formal-glueing-chart)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The sheaf equalizer identifies matching sections with compatible tuples,
with the selected coordinate equal to restriction to the corresponding chart.

Source: Stacks Project, Tag 0BLH, first two proof paragraphs, and Tag 05EL,
the displayed definition of H0.

Proof: for each generator g j let V j be its principal open in U and let
Y j be its inverse image under q. The generators span the maximal ideal, so
these opens cover U. Finite q makes each Y j affine, and finite s makes E
affine. Take M j to be Gamma(Y j), with its localization-algebra scalar
action, and M' to be Gamma(E). Affine principal-open localization identifies
the localized M' with sections of E over D(g j). The given overlapIso
identifies that scheme with the completed base change of Y j. Its affine
section ring is C tensor Gamma(Y j), giving alpha j. Similarly restriction
to double principal opens gives alpha_overlap. On numerators these maps
are the original section restrictions and scalar extensions; functoriality
of restriction proves the square and cocycle equations. The overlap map is
over Spec C, so alpha commutes with C-scalars. This constructs X.

For a compatible tuple, its chart coordinates glue uniquely to a section
on Y by the sheaf axiom. The prime/chart equations say that this section
and its prime coordinate agree on the overlap: check on the same covering
and use sheaf separatedness. They therefore give a matching pair. Conversely
restrict a matching pair to each Y j and retain its completed coordinate;
these satisfy both compatibility equations. These two operations are inverse
and A-linear, giving b. By puncturedMap_over, the inverse image of W under
puncturedMap is precisely Y i, up to the canonical restriction isomorphism.
Its pullback on sections gives c. The Spec-Gamma adjunction and appTop
functoriality identify c of the i-coordinate with psi(rho(b h)). The same
calculation on a base element a identifies its A-action with multiplication
by psi(rho(baseMap a)), hence c is A-linear for the action stated here.
The construction uses no chart-power-lifting or algebraization theorem.
If a generator is nilpotent its chart module is zero. An empty U has zero
punctured sections and H0 retains just the prime coordinate; zero rings
and redundant generators satisfy the same equalizer equations.
(blueprint: lem-sbc-punctured-completion-formal-glueing-chart) -/
theorem exists_formalGlueingData_matching_chart
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (t : ℕ) (g : Fin t → A)
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal A) (i : Fin t) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let W := (D.modelMap ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (g i))
    let ρ := ((ΓSpecIso D.matchingRing).inv ≫
      (W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι).appTop).hom
    let ψ := (D.puncturedMap ∣_ W).appTop.hom
    letI : Algebra A D.matchingRing := D.baseMap.hom.toAlgebra
    letI : Algebra A Γ((D.puncturedMap ⁻¹ᵁ W).toScheme, ⊤) :=
      ((ψ.comp ρ).comp D.baseMap.hom).toAlgebra
    ∃ (X : FormalGlueing.Data.{u, u, u} φ g)
      (b : FormalGlueing.h0 φ g X ≃ₗ[A] D.matchingRing)
      (c : FormalGlueing.piece (g i) (X.M i) ≃ₗ[A]
        Γ((D.puncturedMap ⁻¹ᵁ W).toScheme, ⊤)),
      ∀ h, ψ (ρ (b h)) = c (h.val.2 i) := by sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
