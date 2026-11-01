/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenInterchangeReduction.OpenInterchangeReductionData
import WeilConjectures.SixFunctors.GeneratorReduction.StructuralPullPushUnitCompletion
import all WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares

/-! Constructor case for structural word substitution.
Source: current blueprint fix-prop-coherence, structural substitution step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u s i
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.GeneratorReduction

attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory

variable {S : Type s} {W : S → Scheme.{u}} {I : Type i} {location : I → S}

end WeilConjectures.GeneratorReduction

open WeilConjectures.GeneratorReduction

namespace WeilConjectures.OpenInterchangeReduction

end WeilConjectures.OpenInterchangeReduction
