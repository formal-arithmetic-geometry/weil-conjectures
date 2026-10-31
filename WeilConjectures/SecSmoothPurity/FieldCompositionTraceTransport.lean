/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.CompositionTrace

import WeilConjectures.AlgebraicGeometry.CondensedRationalAdjunction
import WeilConjectures.SixFunctors.ScalarSixCompactSupport
import WeilConjectures.SixFunctors.ScalarSixPullback
import WeilConjectures.SixFunctors.ScalarSixTensorHom
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientDescentTwoColimit
import WeilConjectures.AlgebraicGeometry.CondensedQbarPurityAdjunction

/-! # Passage of normalized trace transitivity to field coefficients

Source: current blueprint sk-prop-sp-composition.proof.md, inversion of ell and
finite-field descent, and parent DAG Steps 6--7.
(blueprint: lem-pur-field-composition-trace-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- Inverting ell and passing to finite subextensions transports the integral
composition equation to field coefficients. The premise is the integral equation
for the fixed normalized family, not an arbitrary choice of integral adjunctions.
Source: current blueprint sk-prop-sp-composition.proof.md, coefficient passage,
and sk-prop-sp-composition, proof Steps 6--7.
(blueprint: lem-pur-field-composition-trace-transport).

Proof in words. Fix a finite field E and choose an integral model K0 of K by the
native rational adjunction theorem, applied to the selected integral adjunction.
Use ScalarCompatible of normalizedFamily to obtain the three scalar counit
identities for the selected finite-field adjunctions themselves. This avoids
identifying a separately rationalized family by a uniqueness assertion whose
premises already contain composition. Apply scalar extension to the integral
composition equation at K0. Scalar-six compact-support composition moves
extension past the normalized support compositor. Scalar-six pullback and its
monoidal tensor comparison move it past the source word. To check the latter
identification, expand pullback composition, Tate-line pullback, ordered powers
and shift reassociation: on root tensors both words send the same root system
and scalar to the same pure tensor; recurse on powers, starting with the scalar
unit at zero. The derived symmetry has the same even shift signs on both sides.
Cancel the comparison isomorphisms and substitute the three scalar counit
identities. This proves the equation on the scalar image of K0; naturality of
both words transports it across the model isomorphism to K. The canonical base
field identification includes the separate rationals presentation.
For the algebraic closure, descend K to a finite-subextension object. The native
qbar adjunction theorem supplies its normalized finite-stage model comparisons;
ScalarCompatible of normalizedFamily supplies the selected closure counit
equations on those models. Extend the rational equation to the
finite-subextension-valued condensed closure
and use the same support and source scalar pasting. Its model-independent counit
formula and scalar cocycles make the result independent of enlarging the finite
field or changing the model. Naturality transports it to K. The root-normalized
pullback coordinates are chosen once per geometric pair, independently of K;
these follow from the normalized root-tower comparison and its scalar square.
Every arbitrary total compactification is retained in this scalar argument. -/
theorem fieldCompositionTraceTransport
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p)
    (hi : ∀ E : PadicAlgCl.FiniteIntermediateField ell,
      NormalizedCompositionTrace ell D hEll (.integral E)) :
    NormalizedCompositionTrace ell D hEll .rationals ∧
    (∀ E : PadicAlgCl.FiniteIntermediateField ell,
      NormalizedCompositionTrace ell D hEll (.rational E)) ∧
    NormalizedCompositionTrace ell D hEll .closure := by
  sorry

end AlgebraicGeometry.ProEtale.PurityTransport
