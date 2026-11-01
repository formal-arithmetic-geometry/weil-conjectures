/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.PublishedSystemAmbientCoherence
import WeilConjectures.SixFunctors.TensorComparisonTransport.TensorComparisonTransport
import WeilConjectures.SixFunctors.Published.PublishedSystemTensorIdentification
import WeilConjectures.SixFunctors.Published.PublishedSystemCompositorIdentification

/-! # PublishedSystemTensorComposition
Source: Stacks 0F7B--0F7D, 03EL, 07A4 and 07A7. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.pullbackTensorCalculus HasDerivedCategory.standard
  WeilConjectures.CoefficientClosedStructure.tensor
  WeilConjectures.AmbientPullbackTensor.tensorData
  WeilConjectures.AmbientPullbackTensor.derivedComp
  WeilConjectures.AmbientPullbackTensor.pull
  WeilConjectures.pullbackTensorSystemComparison
  WeilConjectures.pullbackTensorSequenceDerived
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.AmbientProperOpen

attribute [local irreducible] SystemTensorComposition

/-- Composition of the published tensor comparison on actual semilinear systems.
Source: Stacks 0F7B--0F7D, 03EL, 07A4 and 07A7
(blueprint: lem-sf-published-system-tensor-composition).
Proof: Apply ambientPullbackTensorCoherence on the sequence site, with the systemClosed
structures and systemTensorModel models of pullbackTensorCalculus. Both presentations of
ordinary direct image have identical constant section maps; their chosen inverse images
therefore agree. The section certificate identifies c.ordinaryDirect with the inverse of
the ambient push compositor. Conjugation identifies c.ordinaryPull, and the localization
certificate identifies c.pullComp with the inverse of derivedComp. To identify tensor
comparisons, use adjunction-unit injectivity and total-summand pure-tensor extensionality:
the inverse chain map of tensorData is pullbackTensorSequenceCochain, since both send each
unit of a pure tensor to the tensor of its two units. Invert the representative rectangle
and use faithfulness of restriction to K-flat flat-term pairs. Thus tensorData.mu equals
the published system comparison. Substitute these identifications in the final equation
of ambientPullbackTensorCoherence and cancel the invertible compositor. The argument
uses no invertibility of transition maps. At the zero ring or zero complex the
representative equations and uniqueness apply without additional hypotheses. -/
theorem publishedSystemTensorComposition (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∀ (o : WeilConjectures.IntegralSystemRealization.Operations.{u} l E)
      (c : WeilConjectures.IntegralSystemRealization.Compositors.{u} l E o),
      SystemTensorComposition.{u} F l E o c := by
  unfold SystemTensorComposition
  intro o c X Y Z f g M N
  exact @WeilConjectures.TensorComparisonTransport.transfer_tensor_composition
    (WeilConjectures.coefficientSequenceDerived l E Z.obj.left)
    (WeilConjectures.coefficientSequenceDerived l E Y.obj.left)
    (WeilConjectures.coefficientSequenceDerived l E X.obj.left)
    (instCategoryDerivedCategory _) (instCategoryDerivedCategory _)
    (instCategoryDerivedCategory _)
    (WeilConjectures.pullbackTensorCalculus l E Z.obj.left).systemClosed.tensor
    (WeilConjectures.pullbackTensorCalculus l E Y.obj.left).systemClosed.tensor
    (WeilConjectures.pullbackTensorCalculus l E X.obj.left).systemClosed.tensor
    (WeilConjectures.pullbackTensorSequenceDerived l E g.hom.left)
    ((WeilConjectures.publishedSystemAmbientData l E).pull g.hom.left)
    (WeilConjectures.pullbackTensorSequenceDerived l E f.hom.left)
    ((WeilConjectures.publishedSystemAmbientData l E).pull f.hom.left)
    (WeilConjectures.pullbackTensorSequenceDerived l E (f.hom.left ≫ g.hom.left))
    ((WeilConjectures.publishedSystemAmbientData l E).pull (f.hom.left ≫ g.hom.left))
    (WeilConjectures.publishedSystemAmbientPullIso l E g.hom.left)
    (WeilConjectures.publishedSystemAmbientPullIso l E f.hom.left)
    (WeilConjectures.publishedSystemAmbientPullIso l E (f.hom.left ≫ g.hom.left))
    (WeilConjectures.pullbackTensorSystemComparison l E g.hom.left)
    (WeilConjectures.pullbackTensorSystemComparison l E f.hom.left)
    (WeilConjectures.pullbackTensorSystemComparison l E (f.hom.left ≫ g.hom.left))
    ((WeilConjectures.publishedSystemAmbientData l E).tensor g.hom.left)
    ((WeilConjectures.publishedSystemAmbientData l E).tensor f.hom.left)
    ((WeilConjectures.publishedSystemAmbientData l E).tensor (f.hom.left ≫ g.hom.left))
    (c.pullComp f.hom.left g.hom.left)
    ((WeilConjectures.publishedSystemAmbientData l E).comp f.hom.left g.hom.left)
    (WeilConjectures.publishedSystemTensorIdentification l E g.hom.left)
    (WeilConjectures.publishedSystemTensorIdentification l E f.hom.left)
    (WeilConjectures.publishedSystemTensorIdentification l E (f.hom.left ≫ g.hom.left))
    (WeilConjectures.publishedSystemCompositorIdentification l E o c f.hom.left g.hom.left)
    (publishedSystemAmbientCoherence F l hl E f g) M N

end AlgebraicGeometry.ProEtale.AmbientProperOpen
