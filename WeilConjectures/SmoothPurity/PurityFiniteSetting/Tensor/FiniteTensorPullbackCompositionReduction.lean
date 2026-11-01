/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorFixedComparisons
import all WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
import WeilConjectures.AlgebraicGeometry.Finite.FiniteIntrinsicPullbackUnitComposition
import all WeilConjectures.AlgebraicGeometry.OpenScalarTensor.ScalarPullbackCompositionCoherence
import all WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicConjugateComparisonTransport
import all WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteDirectCounitFixedRealizationTransport
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting

/-! # Finite coefficient pullback coherence in fixed-scalar coordinates

Source: the finite-reduction proof Step 2, expanded presentation-reduction Step 7;
Stacks Project, sites-cohomology.tex, Tag 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

attribute [local instance 100000] proEtaleRingModules_hasDerivedCategory
attribute [local instance 200000] SheafOfModules.instAbelian
private noncomputable local instance (priority := 200000) finiteTensorFixedStalk (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
    u + 1, u + 2, u + 1} _

section Coordinates
variable {A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category A₀] [Category A₁] [Category A₂]
  [Category B₀] [Category B₁] [Category B₂]
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]

end Coordinates

section Presentation
open CategoryTheory.Limits
attribute [local implicit_reducible] Equivalence.mapDerivedCategory CategoryTheory.Equivalence.mk
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [dC : HasDerivedCategory C] [dD : HasDerivedCategory D]
  [dE : HasDerivedCategory E] [dF : HasDerivedCategory F]

end Presentation

namespace AlgebraicGeometry.Scheme
open CategoryTheory.Limits
open Opposite
open ProEtale.OpenScalarTensor
attribute [local irreducible] sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] MorphismProperty Scheme.ProEt Scheme.instCategoryProEt
  Category.opposite CategoryStruct.opposite Quiver.opposite

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option maxHeartbeats 2000000 in
-- Keep the ordinary adjunction models intact while comparing their sectionwise units.
attribute [local irreducible] Functor.mapDerivedCategory
attribute [local implicit_reducible] sfIntrinsicDerivedEquivalence Equivalence.mapDerivedCategory
  CategoryTheory.Equivalence.mk

end AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

-- Expose the cached ring operations to compare them with the canonical ULift instance.
set_option linter.auxLemma false in
attribute [local implicit_reducible] coefficientCommRing._aux_1 coefficientCommRing._aux_4
  coefficientCommRing._aux_8 coefficientCommRing._aux_13 coefficientCommRing._aux_16
  coefficientCommRing._aux_20 coefficientCommRing._aux_28 coefficientCommRing._aux_30
  coefficientCommRing._aux_32 coefficientCommRing._aux_34 coefficientCommRing._aux_41
  ULift.ring
attribute [local implicit_reducible] Coefficient coefficientCommRing
  sfIntrinsicDerivedEquivalence Equivalence.mapDerivedCategory CategoryTheory.Equivalence.mk
attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence
  finiteReductionRawPullbackModel
attribute [local implicit_reducible] smoothPurityPullback finiteReductionPullback
  finiteTensorPullbackModel finiteTensorReduction sfIntrinsicPullback sfIntrinsicTransport
open CategoryTheory.Limits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

set_option maxHeartbeats 2000000 in
-- Normalize the coefficient alias before comparing the two realization presentations.
attribute [local implicit_reducible] finiteReduction ProEtale.scalarExtensionFunctor
end WeilConjectures.PurityFiniteSetting
