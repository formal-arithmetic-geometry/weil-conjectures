/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.IntrinsicCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import all WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageScalarComparison
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootLocalModels
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistIntegralLocalModels
import all WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionRestriction
import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorCoherence
import WeilConjectures.SmoothPurity.Integral.IntegralObjectPullbackLine
import WeilConjectures.SmoothPurity.Common.CommonStageTensorLineCoherence
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import all WeilConjectures.SmoothPurity.Finite.FiniteLineTensorConditions
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.SixFunctors.Completed.CompletedTensorScalarLinearity
import all WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import all WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree

/-! # Integral and rational Tate twists: definitions and local calculations

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.md`, clause (3), integral and rational cases
(blueprint: det-def-sp-tate-twist-locally-free).

The integral, rational and algebraically closed twist functors and signed-line predicates,
with the integral and rational local calculations used by `tateTwist_locallyFree`
(`WeilConjectures.AlgebraicGeometry.Tate.TateTwistLocallyFree`). The finite clauses are in
`WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree`.

## Main definitions

* `tateIntegralTwist` and `tateRationalTwist` are the integral and rational twist functors.
* `TateRationalSignedLine` and `TateQbarSignedLine` express the signed-line clauses in the
  recorded integral-representative categories, with the canonical restriction functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u v d c h

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

-- `flatConstantModulesAbelian` (universes `max u v`) leaves a universe metavariable that stalls
-- unification with the `WEqualsLocallyBijective` instance at universe `u + 1` on the slice sites.
attribute [-instance] CategoryTheory.flatConstantModulesAbelian

namespace AlgebraicGeometry.Scheme

/-- Transport invertibility along the actual residue-field homomorphism.
Source: the cover in blueprint clause (3)
(blueprint: det-def-sp-tate-twist-locally-free). -/
@[instance_reducible] def tatePullbackInvertible (ℓ : ℕ) {Y X : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (ℓ : X.residueField x)] :
    ∀ y : Y, Invertible (ℓ : Y.residueField y) :=
  fun y ↦ (map_natCast (f.residueFieldMap y).hom ℓ) ▸
    Invertible.map (f.residueFieldMap y).hom (ℓ : X.residueField (f y))

set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] HasDerivedCategory.standard

attribute [local instance 20000] tateAbSheafify tateAbBijective tateWeakSheafify tateSiteSmall
  tateDerived

end AlgebraicGeometry.Scheme
