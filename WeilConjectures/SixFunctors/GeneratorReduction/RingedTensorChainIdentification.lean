/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentationConstruction
import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentationNormalization
import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentation

/-! # The canonical ringed tensor chain is the strict quotient augmentation

## References

* [Stacks, Tag 07A4]
* [Stacks, Tag 08TC]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.GeneratorReduction
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  StrictTensorAugmentation.map
attribute [local implicit_reducible] integralOperationsTensorComplexFunctor
  integralOperationsRoos integralOperationsRoosFunctor
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The supplied ringed tensor chain is determined by its two canonical coordinates. -/
theorem ringedTensorChain_eq_strictAugmentation
    (ringed : IntegralSystemRealization.RingedModels l E) (X : Scheme.{u}) :
    (ringed.tensor X).chain = StrictTensorAugmentation.map l E X := by
  apply (StrictTensorAugmentation.existsUnique_normalized l E X).unique
  · constructor
    · intro P Q p q n V x y
      exact (ringed.tensor X).canonical.1.1 P Q p q n V x y
    · intro P Q i
      exact (ringed.tensor X).canonical.1.2 P Q i (i - 1) (by omega)
  · exact StrictTensorAugmentation.coordinates l E X

end WeilConjectures.GeneratorReduction
