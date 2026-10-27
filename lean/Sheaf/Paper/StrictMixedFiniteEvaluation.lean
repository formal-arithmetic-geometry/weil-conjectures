/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.Paper.StrictDirectImageMixedUnitData

/-! # Finite evaluation of coherent strict mixed laws

Source: Stacks Tag 0B56, equation-projection-formula-map.
(blueprint: lem-weil-strict-mixed-finite-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived

universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.StrictDirectImageMixedUnit
open SfStrictDirectImageScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Finite normalization obtained by evaluating an already constructed coherent equation.
Source: Stacks 07A6 and the system evaluation calculus; Step 6 of the strict mixed-unit
calculation (blueprint: lem-weil-strict-mixed-finite-evaluation).

Proof: unpack the coherent witnesses. Apply finite derived evaluation to the system
mixed-unit equation. Expand preservation of composition; use MixedEvaluation at X and Y,
ReductionEvaluation for E and L, and RestrictionEvaluation. Move the natural evaluation
comparisons across reduction of b and across direct image, then cancel the source
reduction-evaluation isomorphism and the target restriction-evaluation isomorphisms.
This gives the finite displayed equality with the prescribed finiteRestriction direction.
For the lift, evaluate the scalar reduction isomorphism and compose it with scalar
extension evaluation and the E and L reduction evaluations. This identifies the finite
L-reduction of completed extension with scalar extension of finite E-reduction. The
transpose_evaluation equation for ScalarSystems identifies the finite mixed unit with
this isomorphism's inverse composed with the level scalar-adjunction unit. Precomposition
with that inverse is a Hom bijection, and the level scalar-adjunction Hom equivalence is
another bijection. Their composite is exactly the asserted finite lift map. No equality
of system morphisms is deduced from their evaluations. -/
theorem strictMixedFiniteEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : IntegralModel l E f) (J : IntegralModel l L f)
    (b : I.image ⋙ sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y ≅
      sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X ⋙ J.image)
    (hc : CoherentLaws l E L ι f I J b) :
    FiniteLaws l E L ι f I J b := by sorry
attribute [instance 20000] WeilConjectures.CompletedCoefficientPushforward.modAbelian
attribute [instance 10000] WeilConjectures.CompletedCoefficientPushforward.hasDerived

end WeilConjectures.StrictDirectImageMixedUnit
