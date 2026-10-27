/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C6
-/
module

public import Sheaf.Paper.IntegralComparisonCanonicalShifts
public import Sheaf.Paper.IntegralPullbackShiftCoordinates

/-! # Shift compatibility of the normalized pullback realization
Source: Stacks Tags 014E, 0941 and 099N(5).
(blueprint: lem-sf-integral-pullback-realization-shifts). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The representative-normalized pullback realization respects the independently
fixed whole-system shifts.

Source: Stacks Tags 014E, 0941 and 099N(5); the Weil-structures paragraph
of the open-closed triangle proof, expanded in parent node steps 2–7.
(blueprint: lem-sf-integral-pullback-realization-shifts).

Proof: resolve a complex by a flat-term K-flat complex P and take its simultaneous
quotient-system presentation from SY.reductionModel. Shift that presentation
termwise. To identify the reduction shift, first compute the total-limit projection on
an injective replacement and its shift: the degree-j projection is the same
projection in degree j+m. Transpose this equation through the finite scalar
adjunction. Its mate is the finite evaluation comparison of reduction, by
SY.counit_projection; thus that comparison commutes with the adjoint reduction
shift. The universal finite scalar counit identifies its representative shift
with termwise reindexing. Conjugate e[m] by these two localization comparisons
and the reduction shift to present P[m] by C[m]. Define the finite kappa maps
by the termwise shift comparisons. The first presentation equation follows
from the mate equation just proved, and the horizontal one follows by shifting
the old horizontal equation. The
pullback generator x tensor a goes to the same generator in the shifted degree;
thus the normalized presentation map q commutes with shifts and with quotient
transitions. Compute the total-limit comparison on a K-injective replacement of
the restricted tower. The limit-cone insertion is (0,z), so it commutes with the
Roos shift (y,x) to ((-1)^m y,x). The two coordinate equations in hc determine
this same shift on the pullback representative. More explicitly, define q_m
by conjugating q[m] with the exact restriction/pullback termwise shifts. Its
generator equation is the old equation in degree j+m, so M.normalization applies
to this particular q_m after uniqueness on tensor-unit generators. For the Roos
bridge, its equation on injectives follows from rho.computes and the two
coordinates of integralComparisonLimitToRoos: the first is the limit tuple and
the second is zero. Both coordinates agree after the signed shift. Naturality
along an injective replacement gives the bridge equation on the original tower.
Apply M's representative
normalization to P and P[m], and cancel the invertible presentation and Roos
comparison maps. This is the desired square on Q(P), after using hs for the
derived pullback comparison. Naturality along the K-flat resolution and the
essential surjectivity of localization give the square on every derived object. -/
theorem integralComparisonPullbackRealization_commShift
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (ρ : IntegralComparisonRoosModel l E X)
    (M : IntegralComparisonPullbackModel l E f SY ρ)
    (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
    (hc : IntegralCompletedComparison.ShiftCoordinates l E f c)
    (s : (integralDerivedPullback l E f).CommShift ℤ)
    (hs : IntegralCompletedComparison.ShiftDescent l E f c s) :
    letI := s
    letI := integralComparisonReductionShift l E Y SY
    letI := integralComparisonSequencePullbackShift l E f
    letI := integralComparisonLimitShift l E X
    NatTrans.CommShift M.realization.hom ℤ := by
  sorry

end WeilConjectures
