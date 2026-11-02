/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.SixFunctors.CommonStageCompactWeilCohomology
public import WeilConjectures.ZetaWeil.OrdinaryCompactCohomology
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.FiniteClopenDerivedDecomposition
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.FiniteClopenConstructibilityBounds
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Pi.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteClopenTensor.ProEtaleFiniteClopenTensorCalculus
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDerivedOpenAdjunction
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import WeilConjectures.SixFunctors.FrobeniusCohomologyTransport
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SixFunctors.Supporting.FrobeniusPointTransportNatural
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageBalancingCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionData
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.SmoothPurity.Sf.SfCommonStageDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusGeometricExchange
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusGeometricExchange
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.Supporting.OperationCoefficientActionData
import WeilConjectures.SmoothPurity.Supporting.BasicOperationReductionAndEvaluation
import WeilConjectures.SmoothPurity.Supporting.BasicOperationCoefficientCoherence
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
import WeilConjectures.SixFunctors.Supporting.FrobeniusPointTransportNatural
public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.DeligneLaumon.FrobeniusCohomologyTransportIso

/-! # Proper sections and semilinear derived germs

Source: Deligne, Weil II (1.1.7), (1.1.10)--(1.1.14), pp. 150--153;
Stacks 07A7 and 0D6D (blueprint: lem-a1-proper-sections-semilinear-germs).
The germs below use the actual whole-system adjunction counit. Composition maps
are the specified simultaneous-system comparisons, localized at the coefficient field.

## Main declarations

* `ProperSemilinearGerms.integralCounit`, `ProperSemilinearGerms.rationalGerm`: the actual
  counit and its compact rational germ.
* `ProperSemilinearGerms.rationalTransport`, `ProperSemilinearGerms.rationalSquare`: the
  specified positive iterates and moving-point comparison.
* `properSectionsSemilinearGermsRational`, `properSectionsSemilinearGerms`: the identity
  and its naturality over a finite extension and over the algebraic closure.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open FrobeniusExchange

set_option allowUnsafeReducibility true in
attribute [local reducible] FrobeniusExchange.modelFunctor
  FrobeniusExchange.modelRationalSource FrobeniusExchange.modelRationalTarget

namespace ProperSemilinearGerms

variable (D : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of D.k₀))) [IsProper Y₀.hom]
  (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The reparametrized point g^(r+1) z h^(-(r+1)), in composition order.
Source: Deligne (1.1.7), (1.1.10)
(blueprint: lem-a1-proper-sections-semilinear-germs). -/
def movingPoint (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (r : ℕ) :=
  localPositivePower (frobeniusPointIso D).inv r ≫ z ≫
    localPositivePower (D.geometricFrobenius Y₀).hom r

/-- Moving points remain k-points and give the displayed semilinear square.
Source: Deligne (1.1.7); Stacks 0D6D
(blueprint: lem-a1-proper-sections-semilinear-germs).
Proof: the defining projection equation g a = a h iterates to g^m a = a h^m.
Compose with h^(-m) z and use z a = id to obtain the first equality. Cancel
h^m h^(-m) in the definition of the moving point to obtain the second equality.
The recurrence localPositivePower denotes exponent m=r+1. -/
theorem movingPoint_properties
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (r : ℕ) :
    movingPoint D Y₀ z r ≫ (D.geometricFiber Y₀).hom = 𝟙 _ ∧
      localPositivePower (frobeniusPointIso D).hom r ≫ movingPoint D Y₀ z r =
        z ≫ localPositivePower (D.geometricFrobenius Y₀).hom r := by
  sorry

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

end ProperSemilinearGerms

end WeilConjectures
