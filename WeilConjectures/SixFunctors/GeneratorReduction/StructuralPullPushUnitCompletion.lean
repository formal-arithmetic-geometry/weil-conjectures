/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.GeneratorReduction.GeneratorReductionData
import WeilConjectures.SixFunctors.GeneratorReduction.PrimitiveCompletionEffectivity
import all WeilConjectures.SixFunctors.GeneratorReduction.ShortWordIntegralDomain

/-! # Completion transport for arbitrary admissible finite words

Source: current blueprint fix-prop-coherence, recursive structural substitution.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u s i
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S)

end WeilConjectures.GeneratorReduction
