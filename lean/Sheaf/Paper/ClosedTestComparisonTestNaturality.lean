/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.ClosedTestLocalizedModelData

/-! # Test naturality of closed-test section comparisons
Source: Stacks Tags 070I, 0D6E, 0D6G and 09BL
(blueprint: lem-sfb-closed-test-comparison-test-naturality). -/

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

/-- Presheaf restriction naturality of the five specified section-model comparisons.
Source: Stacks Tags 0D6F and 0D6G.
Proof: The actual adjunction unit and j are sheaf morphisms. Their restriction
naturality, and the naturality of the closed-site inclusion on fibre products, give
the model-arrow square. Naturality of universal derived units and rightDerivedPullback
gives the sourceUnit and targetUnit squares. For the remaining two squares, identify
weakly etale inverse image with restriction to the slice site, retaining
the canonical coefficient pullback comparison. Restriction preserves K-injectives
because its extension-by-zero left adjoint is exact. Compute the two slice section
comparisons on I and J. Each is the degreewise identity between evaluation at the test
and evaluation of its restricted sheaf at the terminal object. A test arrow induces
the ordinary presheaf restriction on both sides. The slice adjunction unit equation
identifies its derived image with sectionsArrow, using its specified pullback
composition factors. Thus the two composites are equal degreewise. The universal
right-derived units descend this equality and give exactly the two displayed squares.
This works for zero complexes, empty tests and identity test maps without extra choices.
(blueprint: lem-sfb-closed-test-comparison-test-naturality). -/
theorem closed_test_comparison_test_naturality
    (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ) [I.IsKInjective]
    (J : CochainComplex (Modules Λ XZ) ℤ) [J.IsKInjective]
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    TestCoherence Λ A 𝔞 f h fZ w V I J j := by
  sorry

end AlgebraicGeometry.ProEtale.ClosedTestLocalizedModelCoherence
