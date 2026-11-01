/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.SixFunctorDatum
public import WeilConjectures.SixFunctors.Supporting.OperationCoefficientActionData
public import WeilConjectures.SmoothPurity.Supporting.BasicOperationReductionAndEvaluation
public import WeilConjectures.SmoothPurity.Supporting.BasicOperationCoefficientCoherence
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.OpenScalarTensor.OpenScalarTensorData
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageBalancingCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionData
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
import all WeilConjectures.AlgebraicGeometry.OpenScalarTensor.OpenScalarTensorData
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import all WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
import all WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionFormulaArrows
import all WeilConjectures.SmoothPurity.ProEtale.ProEtaleOrdinaryTensorPullbackNaturalComparison
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ExactDerivedMonoidalConstruction
import all WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import all WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all WeilConjectures.AlgebraicGeometry.Picard.KFlatRingedToposPullback
import all WeilConjectures.SmoothPurity.ProEtale.ProEtaleTotalTensorPullbackGenerators
import all WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
import all WeilConjectures.Algebra.Homology.StrictScalarHom.StrictScalarHomChain
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorComparisonExtension
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Whiskering
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.Algebra.Homology.BifunctorSingleComparison
import all WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarTensorOrdinary
import all WeilConjectures.CategoryTheory.ScalarHomTensor.ScalarHomTensorComparison
import all WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import all WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import all WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
import all WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarAssociatorConjugate
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageScalarCocycle
import all WeilConjectures.Algebra.Homology.RingedTensorSquare.RingedExchangeTensorCoherence
import WeilConjectures.AlgebraicGeometry.Proper.ProperScalarCounitSquare
import WeilConjectures.AlgebraicGeometry.Open.OpenScalarCounitSquare
import WeilConjectures.AlgebraicGeometry.OpenScalarTensor.ScalarPullbackCompositionCoherence

/-! # Proper and open identities for coefficient reduction

Source: current blueprint main-20261015, sk-prop-sf-pf-reduction, transpose/counit
paragraph; Stacks Tags 0E48, 0GL1 and 0GL6
(blueprint: lem-sf-pf-reduction-proper-open-identities).

The helpers spell out the specified maps in normalized K-flat tensor presentations.
In particular the compact-support map is defined by its scalar adjunct, independently
of the proper/open factorization asserted in the theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open AlgebraicGeometry.ProEtale.OpenScalarTensor
namespace AlgebraicGeometry.ProEtale.PfReductionFactors

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The specified open tensor map includes the canonical pullback compositor.
The supplied projection presentation fixes its inverse by its open-adjunction transpose.
Source: Stacks 0GL1 and blueprint gamma
(blueprint: lem-sf-pf-reduction-proper-open-identities). -/
def openTensor (m : Models.{u}) (A : Type u) [CommRing A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (r : Z ⟶ Y)
    (p : Projection.{u} m A j)
    (K : proEtaleDerivedCategory X A) (L : proEtaleDerivedCategory Y A) :
    (tensor.{u} m A Z).obj
        ((openExtension.{u} (A := A) j).obj K, (constantPullback.{u} (A := A) r).obj L) ≅
      (openExtension.{u} (A := A) j).obj
        ((tensor.{u} m A X).obj (K, (constantPullback.{u} (A := A) (j ≫ r)).obj L)) :=
  p.iso.app (K, (constantPullback.{u} (A := A) r).obj L) ≪≫
    (openExtension.{u} (A := A) j).mapIso
      ((tensor.{u} m A X).mapIso
        ((Iso.refl K).prod ((proEtaleConstantRingPullbackComposition j r A).app L)))

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors DerivedCategory.Q DerivedCategory.Qh

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
end AlgebraicGeometry.ProEtale.PfReductionFactors
