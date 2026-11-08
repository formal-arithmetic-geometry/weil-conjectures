/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicIntegralTensor

/-! # Shift coherence of the explicit integral comparison

Source: Bhatt--Scholze, Propositions 3.5.1 and 6.8.14(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
variable [IsCommMonObj (abRing l X)] [(sections l X).Additive]
  [PreservesFiniteLimits (sections l X)] [PreservesFiniteColimits (sections l X)]

/-- The explicit inverse-balancing/completion comparison commutes with every integer shift.

Source: Bhatt--Scholze, Propositions 3.5.1 and 6.8.14(2); the shift clause of
`lem-sf-native-integral-tensor-coherence`
(blueprint: new-lem-sf-native-integral-tensor-shift-coherence).

Proof: the ordinary tensor comparison commutes with the degreewise shift of complexes,
and so does its quotient-completion chain map, since both are defined degreewise.
The derived scalar-extension counit is compatible with shifts
(`lem-sbc-derived-scalar-extension-counit-shift`), and a shift structure on a scalar
counit is unique (`lem-pur-scalar-counit-shift-unique`); hence the universal derived
counits lift the two degreewise squares uniquely. The integral transition's shift
structure is defined by the same ordinary tensor normalization, so the composite
inverse-balancing/completion map commutes with the shift by one; compatibility with
the shift by one and the shift coherence isomorphisms give every integer shift. -/
theorem integralTensorComparison_shift (C : CoefficientSystem l X) :
    ∀ {E L : Index l (PadicAlgCl l)} (h : E ≤ L),
      NatTrans.CommShift (integralTensorComparison l X C h) ℤ := by
  sorry

end WeilConjectures.LocallyFiniteAdicRealization
