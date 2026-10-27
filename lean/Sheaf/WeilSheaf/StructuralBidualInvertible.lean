/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.WeilSheaf.NativeBidualEvaluationRealization

/-! # Invertibility of the common-stage structural evaluation transpose

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, paragraph 1,
and sk-prop-sf-biduality-general.proof.md, coefficient transports paragraph.
(blueprint: lem-sf-structural-evaluation-bidual-invertible).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.AdicQbarRealization WeilConjectures.NativeExceptionalForgetful
open WeilConjectures.NativeDualRealization WeilConjectures.NativeBidualRealization

namespace WeilConjectures.NativeBidualRealization

/-- The evaluation transpose for the structural exceptional image is invertible at
common algebraically closed coefficients.

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, paragraph 1;
sk-prop-sf-biduality-general.proof.md, coefficient transports paragraph.
(blueprint: lem-sf-structural-evaluation-bidual-invertible).

Proof: apply common-stage Verdier duality on the geometric fiber. Its dualizing
identification identifies its omega with the exceptional image of the coefficient
unit. Compare this exceptional adjunction with the specified system using the
normalized compact-support comparison and uniqueness of right adjoints. The point
unit comparison identifies the coefficient unit with geometricPointOmega. Transport
the tensor-Hom adjunction and its evaluation along this dualizing isomorphism.
The double-dual arrow is the transpose of evaluation after the signed braiding;
therefore the transported arrow is the displayed commonBidual, not an arbitrary
map between the same objects. More explicitly, if tau : H ≅ D is the
comparison normalized by evaluation, transposing the two evaluation squares gives
  delta_M ≫ tau_(H M) ≫ D(tau_M inverse) = bidual_D(M).
Here the last D is contravariant; its input arrow is first made opposite. The
right side and the two comparison factors are invertible, so cancelling those
factors makes delta_M invertible. This includes
the zero object and the empty scheme, and uses no site-perfectness assumption. -/
theorem isIso_commonBidual
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
    (R : Family l D) (X : Space D) (A : Datum D l R X)
    (hp : Permitted D l R X A) (M : C D l X) :
    IsIso (commonBidual D l R X A hp M) := by sorry

end WeilConjectures.NativeBidualRealization
