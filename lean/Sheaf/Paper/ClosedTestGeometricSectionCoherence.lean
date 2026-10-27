/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.ClosedTestLocalizedModelData

/-! # Geometric coherence of localized closed-test sections
Source: Stacks Tags 070I, 0D6E, 0D6G and 09BL
(blueprint: lem-sfb-closed-test-geometric-section-coherence). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ClosedTestLocalizedModelCoherence
open ClosedTestDerivedExchangeModel
-- Use the canonical structures when comparing the existing section-model interfaces.
attribute [-instance] ClosedTestDerivedExchangeModel.condensedMonoidal
  ClosedTestDerivedExchangeModel.proetaleMonoidal ClosedTestDerivedExchangeModel.moduleAbelian
  ClosedTestDerivedExchangeModel.moduleSectionsAdditive
attribute [instance] ClosedTestDerivedExchangeModel.condensedMonoidal
  ClosedTestDerivedExchangeModel.proetaleMonoidal

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
variable (A : Type u) [CommRing A] (𝔞 : Ideal A)
variable {X XZ : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ 𝔞)))
  (w : IsPullback h fZ f (closedMap A 𝔞))

/-- Canonical derived section comparisons commute with weakly etale localization.
Source: Stacks Tags 04IF, 09T5, 0D6E and 0D6G.
Proof: Weakly etale localization identifies the pro-etale sites with slices. Transport
internal modules to section-ring modules using the exact section-preserving equivalence.
Apply the ringed-sheaf-slice derived comparison to each cartesian square. Restriction
has an exact left adjoint and therefore preserves K-injectives; its comparison with
derived direct image is invertible and has the stated representative formula. The mate
counit equation is supplied by that comparison. Transpose it using the triangle
identities to get the displayed unit equation. This proves LocalizationAdjunction.
For the restriction square, compose the ordinary units for the two successive inverse
images and use pullback composition to identify the equal composite scheme maps.
For the localization cube, evaluate both composites on a K-injective representative.
Each is the same fibre-product section map, and the normalized derived direct-image
composition carries that equality to the asserted cube. Exact pullback composition
retains every coefficient constraint. The argument works for arbitrary squares,
so the four specified global arrows and isomorphisms of squares are included.
(blueprint: lem-sfb-closed-test-geometric-section-coherence). -/
theorem closed_test_geometric_section_coherence
    (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :
    GeometricCoherence Λ A 𝔞 f h fZ w V := by
  sorry

end AlgebraicGeometry.ProEtale.ClosedTestLocalizedModelCoherence
