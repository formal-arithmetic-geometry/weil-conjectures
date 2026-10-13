/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionChartSectionModules

/-!
# Localization of actual chart sections on double intersections

Source: Stacks Project, Tags 0BLH and 05EL.
(blueprint: lem-sbc-punctured-completion-chart-overlap-localizations)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- Localization identifies actual chart sections with sections on double intersections.
Source: Stacks Project, Tag 0BLH, first two proof paragraphs; Tag 05EL, item (1).
(blueprint: lem-sbc-punctured-completion-chart-overlap-localizations)

Proof: put V_i=h^{-1}D(f_i). The ring map defining chartSectionModule sends
an element of A to its structural section on V_i, because the canonical localization
isomorphism commutes with algebraMap. On V_j the section representing f_i has
basic open V_i intersect V_j, by functoriality of basic opens and restriction.
Since V_j is affine, IsAffineOpen.isLocalization_basicOpen identifies the section
ring on that intersection with the localization of Gamma(Y,V_j) at that section.
Restrict scalars to A and apply IsLocalizedModule.restrictScalars_powers and
IsLocalizedModule.linearEquiv to obtain b_ij. On m/1 its value is restriction
of m. More generally b_ij(m/f_i^n) is the restriction of m divided by the
structural section f_i^n on the intersection. Multiplication by a structural
A-section commutes with this division, giving the displayed scalar formula. Identify both
localizations
with the same intersection section ring, swapping the order of the two opens by
inf_comm. Compose the first identification with the inverse of the second to
obtain alpha_overlap. The generator formula follows by cancellation of these
identifications. If either open is empty its sections and the relevant localized
modules are zero, so the same localization universal property applies.
-/
theorem exists_chart_overlap_localizations
    {A : Type u} [CommRing A] {Y : Scheme.{u}} (h : Y ⟶ Spec (.of A))
    (t : ℕ) (f : Fin t → A)
    (hV : ∀ i, IsAffineOpen (h ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))) :
    let M := fun i ↦ chartSectionModule h (f i)
    ∃ (alpha_overlap : ∀ i j,
        FormalGlueing.localize (f j) (FormalGlueing.piece (f i) (M i)) ≃ₗ[A]
          FormalGlueing.localize (f i) (FormalGlueing.piece (f j) (M j)))
      (b : ∀ i j, FormalGlueing.localize (f i) (FormalGlueing.piece (f j) (M j)) ≃+
        Γ(Y, (h ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) ⊓
          (h ⁻¹ᵁ PrimeSpectrum.basicOpen (f j)))),
      (∀ i j m, b i j (alpha_overlap i j (LocalizedModule.mk m 1)) =
        Y.presheaf.map (homOfLE inf_le_left).op m) ∧
      (∀ i j m, b i j (LocalizedModule.mk m 1) =
        Y.presheaf.map (homOfLE inf_le_right).op m) ∧
      (∀ i j (a : A) m, b i j (a • m) =
        ((ΓSpecIso (.of A)).inv ≫ h.appTop ≫
          Y.presheaf.map (homOfLE (le_top :
            (h ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) ⊓
              (h ⁻¹ᵁ PrimeSpectrum.basicOpen (f j)) ≤ ⊤)).op).hom a * b i j m) := by sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
