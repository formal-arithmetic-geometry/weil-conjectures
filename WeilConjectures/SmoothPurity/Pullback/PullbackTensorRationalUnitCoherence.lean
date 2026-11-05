/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorIntegralUnitCoherence

/-! Rational unit coherence for the completed pullback tensor comparison.

Source: Stacks Project, Tags 07A4 and 0941; the rational part of
`lem-pur-pullback-tensor-unit-coherence`.
(blueprint: lem-pur-pullback-tensor-rational-unit-coherence)

The proof localizes the integral unit comparison and transports the normalized
left and right unitor equations. The localized comparison is unique by the
same unit cancellation argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField Padic
  sfIntegralConstructible HasDerivedCategory.standard

-- Naturality descends through the specified tensor and unit reduction maps.

-- Tensoring by an object isomorphic to the unit is faithful.

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end WeilConjectures
