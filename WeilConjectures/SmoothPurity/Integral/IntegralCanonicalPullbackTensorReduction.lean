/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorIntegralConstruction
public import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison
public import WeilConjectures.SmoothPurity.Integral.IntegralSystemTensorComparisonComposition
public import WeilConjectures.SmoothPurity.Integral.IntegralPullbackTensorCompositionTransport

/-! # Coherent reduction of the canonical integral pullback/tensor comparison

Source: Stacks 07A4 and 0941
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).

The coherent reduction of the canonical integral comparison is the transported system
comparison, conjugated by the whole-system pullback comparison of
`integralPullbackSystemComparison` and by the reduction/tensor comparison built from the
Roos-normalized tensor realization and the coherent counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

end WeilConjectures
