/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.Paper.ProperBaseChangeFourArrows

/-!
# Finite reduction and the pullback square

Source: Stacks Tags 07A4 and 0D6D.
(blueprint: lem-weil-pbc-finite-reduction-pullback-coherence).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance 40000] adicDatumModulesAbelian
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

variable {A : Type (t + 1)} [CommRing A]
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Reduction commutes with the specified comparison of the two pullback composites.
Source: Stacks Tags 07A4 and 0D6D; the coefficient specialization of the comparison
compatibility in Tag 0E48.
(blueprint: lem-weil-pbc-finite-reduction-pullback-coherence).
Proof: on flat-term K-flat representatives, the geometric composition comparisons
are the ordinary pullback composition maps, and reduction comparisons are balanced
tensor reassociation. Both routes take a local tensor to the same pulled-back
section with its quotient scalar. Projection compatibility makes these maps linear
over the finite quotient ring. Equality descends through localization, since all
pullbacks preserve flat-term K-flat complexes. The normalization of each comparison
identifies these localized maps with the displayed comparisons. Transport across
the commutative scheme square and its compatible coefficient identifications gives
the claimed equality. No direct image or base-change invertibility is used. -/
theorem fourCornerReductionPullback_square
    (sq : ChosenCartesianSquare g' f' f g) (d : ProEtaleAdicCoefficientDatum A)
    (n : ℕ) (M : fourCornerDerived Y (adicDatumRing Y d)) :
    (adicDatumReduction X' d n).map ((fourArrowIntegralPullbackComparison sq d).hom.app M) ≫
        (fourCornerReductionPullback g' d n).hom.app ((fourCornerPullback f d).obj M) ≫
          (fourCornerFinitePullback g' d n).map ((fourCornerReductionPullback f d n).hom.app M) =
      (fourCornerReductionPullback f' d n).hom.app ((fourCornerPullback g d).obj M) ≫
        (fourCornerFinitePullback f' d n).map ((fourCornerReductionPullback g d n).hom.app M) ≫
          (fourArrowFinitePullbackComparison sq d n).hom.app
            ((adicDatumReduction Y d n).obj M) := by
  sorry

end AlgebraicGeometry.Scheme
