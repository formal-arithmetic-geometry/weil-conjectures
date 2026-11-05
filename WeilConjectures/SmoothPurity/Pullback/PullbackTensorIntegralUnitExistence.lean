/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus

/-! Existence of the integral unit comparison.

Source: Stacks Project, Tag 07A4, label lemma-pullback-tensor-product; the
integral coefficient-level unit coherence construction.
(blueprint: lem-pur-pullback-tensor-integral-unit-coherence-existence)

The normalized coherent system unit comparison is lifted through the fully
faithful integral reduction.  Its two system-level unitor equations transport
along the reduction, tensor, pullback, and unit counits to the displayed
integral equations.
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
namespace WeilConjectures

-- Conjugating both inputs of a reduced tensor comparison respects its square.

attribute [local irreducible] Scheme.residueField Padic
  HasDerivedCategory.standard
  pullbackTensorIntegralReductionTensor pullbackTensorIntegralReductionPullback
  pullbackTensorIntegralUnitReduction

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end WeilConjectures
