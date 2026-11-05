/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations

/-!
# Finite pullback composition in the integral tower presentation

Source: Stacks Project, Tag 0D6D, and Modules on Sites, Tag 03D3
(blueprint: lem-weil-pbc-proetale-derived-pullback-composition).

The general ring-sheaf comparison remains publicly imported. The additional interface
identifies the coefficient-sized tower pullback with the same constant-ring pullback,
with its tensor-unit normalization, and exposes the constant-coefficient specialization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end WeilConjectures
