/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.ClosedTestLocalizedModelData

/-! # Normalization of localized closed-test restriction
Source: Stacks Tags 070I, 0D6E, 0D6G and 09BL
(blueprint: lem-sfb-closed-test-localized-restriction-normalization). -/

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

/-- The section-unit model computes the actual localized derived restriction.
Source: Stacks Tags 04IF, 070Y and 0D6G.
Proof: Identify localization at the source and target test objects with the corresponding
slice topoi. The ordinary slice pullback comparison is compatible with the adjunction
counit. Transpose its counit equation and apply the triangle identities to obtain the
unit equation. On each degree of I this equates the evaluated unitAt map with the
restriction unit for the actual closedFibreMap. Apply the universal derived units and
exact pullback factorization. Naturality for j moves Q(j) past the target localization
unit. Its inverse cancels Q(j), leaving precisely the displayed normalized equation.
This uses K-injectivity only for the given representatives, never for h-star I.
(blueprint: lem-sfb-closed-test-localized-restriction-normalization). -/
theorem closed_test_localized_restriction_normalization
    (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ) [I.IsKInjective]
    (J : CochainComplex (Modules Λ XZ) ℤ) [J.IsKInjective]
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] : LocalizedModelEquation Λ A 𝔞 f h fZ w V I J j := by
  sorry

end AlgebraicGeometry.ProEtale.ClosedTestLocalizedModelCoherence
