/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorIntegralCompositionCoherence
import WeilConjectures.SmoothPurity.Canonical.CanonicalRationalPullbackTensorCompositionRightLocalization
import WeilConjectures.SmoothPurity.Canonical.CanonicalRationalPullbackTensorCompositionLeftLocalization

/-! Rational coefficient component of pullback/tensor composition coherence.

Source: Stacks 07A4 and 0941; this is the rational part of
`lem-pur-pullback-tensor-composition-coherence`.
(blueprint: lem-pur-pullback-tensor-composition-coherence)

Localize the normalized integral quotient-tower composition equation. The
object and morphism normalization specifications identify every localized
comparison and compositor with its prescribed rational construction. Bilinearity
of localization identifies the tensor of the two compositor components.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end WeilConjectures
