/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FourierAdicArtinSchreier
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.IntrinsicCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCoefficientTwists
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.FourierTransform.AffineSpace
import WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition
import WeilConjectures.AlgebraicGeometry.SmoothPurity.QbarCompactSupportBaseChange
import WeilConjectures.FourierTransform.Properties.Stalk
import WeilConjectures.FourierTransform.ArtinSchreierCohomology
import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDerivedOpenAdjunction
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIdentifiedOpenClosed
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicClosedAmbient
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedClosedKernelAdjoint
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.ExactDerivedAdjunctionUnitShift
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenClosedTriangle
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteLocalConstancyPullback
import WeilConjectures.AlgebraicGeometry.Open.OpenExtensionFiniteTor
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent
import WeilConjectures.CategoryTheory.StageSystem.Functor
import WeilConjectures.DeligneLaumon.FieldWeilShriekShiftData
import WeilConjectures.SmoothPurity.Automorphism.AutomorphismConstructibleStageEquivalence
import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
import Mathlib.CategoryTheory.PathCategory.Basic
import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
import WeilConjectures.WeilSheaf.WeilFourierTransform
import WeilConjectures.FourierTransform.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.FourierTransform.FourierAdicArtinSchreier
import WeilConjectures.DeligneLaumon.CommonStageWeilShriek
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
import WeilConjectures.FourierTransform.ArtinSchreier
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect

/-!
# The convolution of the Fourier kernels

Source: blueprint main-20261015, sec-fourier-transform/sk-prop-convolution-kernel,
lem-fd-convolution-kernel and its proof (blueprint: lem-fd-convolution-kernel).
All objects use the intrinsic adic common-stage coefficient category. The finite index
set labels the standard coordinates, and its cardinality is the rank r, including zero.
The standard basis identifies the dual affine space with the same coordinate scheme.

## Main definitions and statements

- `fourierConvolutionIntegrand`: the two completed pullbacks and their derived tensor.
- `fourierGeometricConvolution`: its unshifted adic compact-support image.
- `fourierDeltaKernel`: the twisted diagonal image, with optional second reflection.
- `fourierKernelConvolutionIso`: the two kernel identities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.AffineSpace
namespace WeilConjectures

/-- The geometric base Spec k of the fixed Fourier setting.
Source: convolution-kernel statement (blueprint: lem-fd-convolution-kernel). -/
abbrev fourierGeometricBase (F : FourierSetting.{u}) := Spec (.of F.field.k)

/-- Standard affine space V, identified with its dual by its standard coordinates.
Source: convolution-kernel statement (blueprint: lem-fd-convolution-kernel). -/
abbrev fourierGeometricSpace (F : FourierSetting.{u}) (n : Type u) :=
  𝔸(n; fourierGeometricBase F)

/-- The structure map of the standard affine space.
Source: convolution-kernel statement (blueprint: lem-fd-convolution-kernel). -/
abbrev fourierGeometricProjection (F : FourierSetting.{u}) (n : Type u) :=
  fourierGeometricSpace F n ↘ fourierGeometricBase F

/-- The product V times V over the geometric base.
Source: convolution-kernel statement (blueprint: lem-fd-convolution-kernel). -/
abbrev fourierGeometricSquare (F : FourierSetting.{u}) (n : Type u) :=
  pullback (fourierGeometricProjection F n) (fourierGeometricProjection F n)

/-- The standard triple product, in the existing kernel-composition convention.
Source: kernel-composition and convolution-kernel proof Step 1
(blueprint: lem-fd-convolution-kernel). -/
abbrev fourierGeometricTriple (F : FourierSetting.{u}) (n : Type u) :=
  pullback
    (pullback.snd (fourierGeometricProjection F n) (fourierGeometricProjection F n))
    (pullback.fst (fourierGeometricProjection F n) (fourierGeometricProjection F n))

/-- The existing projection r13, with no change to the unshifted convolution convention.
Source: kernel-composition (blueprint: lem-fd-convolution-kernel). -/
abbrev fourierGeometricR13 (F : FourierSetting.{u}) (n : Type u) :=
  pullback.tripleProj₁₃ (fourierGeometricProjection F n)
    (fourierGeometricProjection F n) (fourierGeometricProjection F n)

end WeilConjectures
