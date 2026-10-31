/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionChain
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.OpenFactorCoherence.TensorOperationUnitNormalization
import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentationNormalization

/-! # Identification of strict tensor augmentation chains

The two quotient tensor chains have the same product and shifted coordinates.
Source: Stacks 07A4, 07A6 and 08TC.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOrdinary
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

open IntegralSystemRealization
attribute [local implicit_reducible] PurCompactSupport.completed
attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  proEtaleRingDerivedPullbackFactors proEtaleTensorPullbackTotalIso
  proEtaleCanonicalTensorComparison Functor.mapDerivedCategory IntegralAmbient.tensorOperationUnit

/-- The normalized ringed tensor chain is the constructible presentation's chain.
Source: Stacks 07A4 and 08TC.
(blueprint: lem-sf-integral-tensor-chain-identification).

Proof: the strict augmentation is unique given its product coordinate on homogeneous
pure tensors and its zero shifted coordinate. The ringed model has these coordinates
by its canonical field. The constructible chain is the ordinary tensor operation unit,
whose coordinate normalization gives the same two formulas. Apply uniqueness. -/
theorem ringedTensorChain_eq_constructible (d : RingedModels l E) (W : Scheme.{u}) :
    (d.tensor W).chain = ConstructibleTensorModel.tensorCompletionChain l E W := by
  apply (StrictTensorAugmentation.existsUnique_normalized l E W).unique
  · exact ⟨(d.tensor W).canonical.1.1,
      fun P Q i ↦ (d.tensor W).canonical.1.2 P Q i (i - 1) (by omega)⟩
  · have h := OpenFactorCoherence.tensorOperationUnit_normalized l E W
      (ConstructibleTensorModel.tensorCompletionChain l E W) (fun P Q ↦
        (ConstructibleTensorModel.tensorCompletionChain_app l E W P Q).trans (by
          unfold ConstructibleTensorModel.tensorCompletionUnitMap
          rfl))
    exact ⟨h.1, fun P Q i ↦ h.2 P Q i (i - 1) (by omega)⟩

end WeilConjectures.IntegralOrdinary
