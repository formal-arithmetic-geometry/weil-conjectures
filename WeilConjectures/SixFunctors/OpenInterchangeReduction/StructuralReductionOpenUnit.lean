/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenInterchangeReduction.OpenInterchangeReductionData
import all WeilConjectures.SixFunctors.GeneratorReduction.ShortWordIntegralDomain
import all WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares
import WeilConjectures.SixFunctors.GeneratorReduction.PrimitiveCompletionEffectivity

/-! Constructor case for structural word substitution.
Source: current blueprint fix-prop-coherence, structural substitution step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u s i
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.GeneratorReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S)

end WeilConjectures.GeneratorReduction

namespace WeilConjectures.OpenInterchangeReduction
open GeneratorReduction

set_option maxHeartbeats 800000 in
-- The recursive categorical induction needs a larger heartbeat budget.
end WeilConjectures.OpenInterchangeReduction
