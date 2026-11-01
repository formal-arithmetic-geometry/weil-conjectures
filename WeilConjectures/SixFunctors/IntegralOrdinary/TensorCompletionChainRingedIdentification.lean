/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionChain
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.GeneratorReduction.RingedTensorChainIdentification

/-! # The ringed chain and the specified ordinary tensor augmentation

Source: Stacks 07A4 and 0941; the two full Roos coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOrdinary
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local implicit_reducible] PurCompactSupport.completed
  integralOperationsGoodLocalization integralOperationsTensorOnGood
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  pullbackTensorCalculus pullbackTensorIntegralTensorModel integralCompletedTensorComparison
  coefficientSequenceLimit

/-- The ringed tensor chain is the specified ordinary tensor completion chain.
Source: Stacks 07A4 and 0941; full-coordinate uniqueness of the strict augmentation.
(blueprint: lem-sf-ringed-tensor-completion-chain-identification).

Proof: the ringed tensor chain has exactly the pure-tensor product coordinates
and the zero shifted coordinate of StrictTensorAugmentation.map. Its existing
uniqueness theorem identifies the two transformations. Evaluate at the pair P,Q.
The component formulas for that map and tensorCompletionChain are both the actual
IntegralAmbient.tensorOperationUnit, so their components are equal. No nonzero or
nonempty assumption is used. -/
theorem ringedTensorChain_eq_tensorCompletionChain (X : Scheme.{u})
    (d : IntegralSystemRealization.RingedModels l E)
    (P Q : CochainComplex (integralTowerModules l E X) ℤ) :
    (d.tensor X).chain.app (P, Q) =
      (ConstructibleTensorModel.tensorCompletionChain l E X).app (P, Q) := by
  rw [GeneratorReduction.ringedTensorChain_eq_strictAugmentation,
    StrictTensorAugmentation.map_app, ConstructibleTensorModel.tensorCompletionChain_app]
  unfold ConstructibleTensorModel.tensorCompletionUnitMap
  rfl

end WeilConjectures.IntegralOrdinary
