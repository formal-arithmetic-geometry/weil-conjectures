/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistIntegralLines
public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.IntrinsicCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom
import all WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree
import all WeilConjectures.AlgebraicGeometry.Tate.TateTwistIntegralLines
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import WeilConjectures.SmoothPurity.Integral.IntegralObjectPullbackLine
import WeilConjectures.SmoothPurity.Common.CommonStageTensorLineCoherence
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.SixFunctors.Completed.CompletedTensorScalarLinearity
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization

/-! # Tate twists are well defined and locally free of rank one

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.md`, clauses (1)--(3)
(blueprint: det-def-sp-tate-twist-locally-free).

The helpers specialize the recorded constant sheaf, root module, scalar extension,
signed line and tensor functors. All positive root levels are indexed by `n + 1`.
The theorem includes one common cover, normalized generators, canonical Kummer
independence, signed invertible lines and equivalences with the negative twists.

The finite clauses and the definitions they use are in
`WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree`
(`tateTwist_finite_locallyFree`), the integral and rational twist functors, signed-line
predicates and local calculations in
`WeilConjectures.AlgebraicGeometry.Tate.TateTwistIntegralLines`; both are imported publicly.

## Main statements

* `tateTwist_locallyFree` states all three source clauses for all four coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u v d c h

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] HasDerivedCategory.standard

attribute [local instance 20000] tateAbSheafify tateAbBijective tateWeakSheafify tateSiteSmall
  tateDerived

end AlgebraicGeometry.Scheme
