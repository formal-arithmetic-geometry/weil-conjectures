/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Open.OpenQuotientKoszulModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitDerivedAdjunctionComparison
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitCanonicalModels

/-! # Total-limit normalization of the ordinary scalar augmentation

Source: Stacks Tags 07A6, 0D6E and 0941
(blueprint: lem-sf-open-dvr-scalar-unit-formula).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard Functor.rightDerivedFunctor

end WeilConjectures
