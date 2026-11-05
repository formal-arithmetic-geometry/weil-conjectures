/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison

/-! # Associativity of a fully faithful integral lift

Source: Stacks Project, Tag 0D6D and the naturality calculation in step 6 of
lem-pod-integral-pullback-composition
(blueprint: lem-pod-integral-system-pullback-lift-associativity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option allowUnsafeReducibility true in
attribute [local irreducible] finiteSystemDerivedPullback finiteSystemDerivedEvaluation
  integralSystemReduction integralSystemReductionEvaluation
  finiteSystemDerivedComposition constructibleIntegralPullback integralDerivedPullback

end WeilConjectures
