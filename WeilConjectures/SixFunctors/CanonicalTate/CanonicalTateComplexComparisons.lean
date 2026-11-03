/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SchemeGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.SixFunctors.Orientation.OrientationIntegralCoefficientTwists
public import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistBaseChange
public import WeilConjectures.SmoothPurity.Supporting.SignedTwistReductionComparison
import WeilConjectures.SixFunctors.Supporting.PositiveRootTensorProduct
import all WeilConjectures.SixFunctors.Orientation.OrientationIntegralCoefficientTwists
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization

/-! # Canonical Tate comparisons: ComplexComparisons

Source: current blueprint, def-pur-tate-datum, canonical root-line comparisons.
This module preserves the original unshifted comparison declarations.
(blueprint: def-pur-canonical-tate-complex-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u v a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures.CanonicalTate
open FrobeniusCoefficientTwists

attribute [local instance 5000] integralTowerHasDerivedCategory scalarReductionTargetDerived

attribute [-instance] PrincipalKoszulStrictReplacement.abSheafify
  PrincipalKoszulStrictReplacement.abLocallyBijective
  PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] IntegralOnSlice.completion
  IntegralOnSlice.completionComparison IntegralOnSlice.completionUnit
  IntegralOnSlice.duality IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso
  HasDerivedCategory.standard completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor SheafOfModules.monoidalCategory IntegralOnSlice.tower
  IntegralOnSlice.augmentation integralOperationsTensorTowerFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- The existing integral line as its degree-zero flat complex.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-complex-comparisons). -/
abbrev integralComplex (X : Scheme.{u}) (r : ℕ) :=
  (CochainComplex.singleFunctor _ 0).obj (positiveLine l E X r)

section IntegralRootTensor
attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
attribute [local semireducible] coefficientTotalTensor
attribute [local implicit_reducible] coefficientTotalTensor

end IntegralRootTensor

/-- The integral degree-zero line is a good flat-term K-flat representative.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-complex-comparisons).
Proof: Locally the line is the coefficient unit, including exponent zero.
It is flat, and its single complex is bounded and K-flat. Every other term is
zero and hence flat. These are the two clauses of integralOperationsGoodComplex. -/
theorem integralGood (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (r : ℕ) :
    integralOperationsGoodComplex l E X (integralComplex l E X r) := by
  obtain ⟨hK, hF, _⟩ :=
    SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization
      (completedIntegralCommRingSheafUnrestricted l E X) (positiveLine l E X r)
      (coefficientTwistLine_exact X
        (R := completedIntegralCommRingSheafUnrestricted l E X)
        (purTwistIntegralModule X l E) (r : ℤ)).2
  exact ⟨hK, hF⟩

end WeilConjectures.CanonicalTate
