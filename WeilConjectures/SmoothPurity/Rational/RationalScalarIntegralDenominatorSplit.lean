/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Rational.RationalScalarRestrictionConstructible
public import Mathlib.CategoryTheory.Retract
import WeilConjectures.SmoothPurity.Rational.RationalScalarAmbientTrace

/-! # Ambient finite separable trace retraction

This is the ambient derived-category part of the coefficient-retract argument.
(blueprint: lem-sf-rational-scalar-integral-denominator-split).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The finite separable trace construction gives an ambient retract after
restriction of coefficients.  Constructibility is handled separately.

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15; Stacks Project
Tags 090W and 02FL.
(blueprint: lem-sf-rational-scalar-integral-denominator-split).

Proof: use the trace-dual basis of the finite separable extension F/E.  Restrict
K along the completed coefficient map.  The trace-dual section and multiplication
retraction are defined on the derived representatives and descend through scalar
localization; their composite is the identity by the two dual-basis identities. -/
theorem rationalScalar_ambient_trace_retract
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (K : sfRationalConstructibleCategory l F W) :
    Nonempty (Retract
      (ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l F)
      (C := DerivedCategory (scalarReductionSource l F W))
      (p := Padic.coefficientExtensionUniformizer l F) K.obj.obj)
      (ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l F)
        (C := DerivedCategory (scalarReductionSource l F W))
        (p := Padic.coefficientExtensionUniformizer l F)
        ((sfRationalScalarExtension l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj
          ⟨(rationalScalarDerivedRestriction l E F ι W).obj K.obj.obj,
            rationalScalarDerivedRestriction_constructible l E F ι W K.obj⟩).obj.obj)) := by
  sorry

end WeilConjectures
