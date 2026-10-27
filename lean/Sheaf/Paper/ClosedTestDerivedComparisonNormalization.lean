/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.ClosedTestLocalizedModelData

/-! # Geometric normalization of the closed-test derived comparisons
Source: Stacks Tags 070I, 0D6E, 0D6G and 09BL
(blueprint: lem-sfb-closed-test-derived-comparison-normalization). -/

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

/-- The model comparisons have the canonical geometric section normalization.
Source: Stacks Tags 09BL, 0D6E and 0D6G.
Proof: Use the three normalized isomorphisms of closed-test K-injective section models.
Their composites give eC and eD with the prescribed inverses. The normalized
K-injective localization comparisons are isomorphisms; cancel the resolution
representative isomorphism on the target to obtain both asserted localizationUnit
isomorphisms. The slice evaluation
comparison gives eV and its hom is the actual evaluationLocalization. Compute the
canonical sectionComparison on the supplied K-injective representative by the
right-derived direct-image composition formula. Its ordinary section formula is the
identity. For the source compose this identity with the actual closed unit and invert
that unit using closed-test unit evaluation. For the target use the literal direct-image
section formula and transport Q(j) through its specified inverse. The universal
right-derived units and exact pullback factors give exactly the two asserted equations;
no geometric restriction map has been assumed invertible.
(blueprint: lem-sfb-closed-test-derived-comparison-normalization). -/
theorem closed_test_derived_comparison_normalization
    [IsAffine X]
    (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A 𝔞).obj V).left, ⊤)]
    (K : DerivedCategory.Plus (Modules Λ X))
    (I : CochainComplex (Modules Λ X) ℤ) [I.IsKInjective]
    (e : DerivedCategory.Q.obj I ≅ K.obj)
    (J : CochainComplex (Modules Λ XZ) ℤ) [J.IsKInjective]
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    IsIso (localizationUnit Λ (sourceTest A 𝔞 f V) I) ∧
    IsIso (localizationUnit Λ (targetTest A 𝔞 fZ V) J) ∧
    NormalizedComparisons Λ A 𝔞 f h fZ V I J j := by
  sorry

end AlgebraicGeometry.ProEtale.ClosedTestLocalizedModelCoherence
