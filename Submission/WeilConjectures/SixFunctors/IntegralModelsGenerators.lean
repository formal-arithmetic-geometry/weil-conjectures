/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility
public import Submission.WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousLocallyFreePullback
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import Submission.WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax
import Submission.WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import Submission.WeilConjectures.Algebra.Homology.PrincipalConeExactEquivalence
import Submission.WeilConjectures.Algebra.Homology.RingedSiteBoundedDualComponents
import Submission.WeilConjectures.AlgebraicGeometry.CartesianCoefficientTwists
import Submission.WeilConjectures.AlgebraicGeometry.CohomologyTorInterval
import Submission.WeilConjectures.AlgebraicGeometry.ComapUpperStarIsoMate
import Submission.WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit
import Submission.WeilConjectures.AlgebraicGeometry.CondensedClosedSupportAdjunction
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeTensorExact
import Submission.WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
import Submission.WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarScalarBasis
import Submission.WeilConjectures.AlgebraicGeometry.CondensedSubfieldBoundedCopowers
import Submission.WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralTransport
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousEtaleLocalLattices
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationCounit
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralUnderivedPushComparison
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersection
import Submission.WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteConstructibleEncoding
import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import Mathlib.AlgebraicGeometry.Limits
import Submission.WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
import Submission.WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryMonoidal
import Submission.WeilConjectures.AlgebraicGeometry.IntegralResiduePullOrdinaryUnit
import Submission.WeilConjectures.AlgebraicGeometry.LatticeMatrixNeighborhoods
import Submission.WeilConjectures.AlgebraicGeometry.ModuleCupCanonicalHZeroIdentification
import Submission.WeilConjectures.AlgebraicGeometry.NormalizedDVRKFlatTransition
import Submission.WeilConjectures.AlgebraicGeometry.PadicConstantLocalModelTor
import Submission.WeilConjectures.AlgebraicGeometry.PrincipalConeKoszulRoosComparison
import Submission.WeilConjectures.AlgebraicGeometry.PrincipalIdealLocalTestCriterion
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTensorPullbackModels
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
import Submission.WeilConjectures.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
import Submission.WeilConjectures.AlgebraicGeometry.ProjectionFormulaArrows
import Submission.WeilConjectures.AlgebraicGeometry.PullbackFiniteConstantLocalModel
import Submission.WeilConjectures.AlgebraicGeometry.PullbackTensorResolvingComputation
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
import Submission.WeilConjectures.AlgebraicGeometry.SiteDerivedTensorRestriction
import Submission.WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import Submission.WeilConjectures.AlgebraicGeometry.StratifiedTorIntervalDevissage
import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import Submission.WeilConjectures.CategoryTheory.CoefficientPushCopowerCriterion
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import Submission.WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import Submission.WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.RelativeTensorCoequalizer
import Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import Submission.WeilConjectures.CategoryTheory.SiteAlgebraicCompositionUnit
import Submission.WeilConjectures.CategoryTheory.Sites.GeometricInverseImageExact
import Submission.WeilConjectures.CategoryTheory.UnitPowerCompleteness
import Submission.WeilConjectures.ConstructibleSheaf.Devissage
import Submission.WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
import Submission.WeilConjectures.NumberTheory.Padics.IntegersAlgebra
import Submission.WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Submission.WeilConjectures.NumberTheory.Padics.IntegersFinite
import Submission.WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension
import Submission.WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.SheafGluing
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClopenIdempotent

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Integral generators and their finite reductions

(1)--(3) (blueprint: det-lem-integral-models-generators).

The generator classes use the existing canonical scalar extension and locally closed
extension by zero. Finite reductions use the total left derived extension of scalars.
Their etale origin is tested through the existing intrinsic finite-coefficient comparison,
after the explicit restriction to constant scalars.
-/

@[expose] public section

set_option autoImplicit false
-- Preserve shared coefficient terms during proof cleanup.
set_option cleanup.letToHave false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale

universe u

namespace AlgebraicGeometry.ProEtale

/-- Convert a condensed ring sheaf to its existing ring object, then pull back to `X`.
Source: blueprint comparison with completed coefficients, notation `Λ_X`
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedCoefficient (X : Scheme.{u})
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}) :=
  coefficientRing X
    (Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R))

end AlgebraicGeometry.ProEtale

namespace WeilConjectures.SixFunctors

open scoped CategoryTheory.Functor

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

/-- Canonical coefficient specialization used in the integral generator statement.
(1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable instance integralModel_coefficientMonObj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) : MonObj (condensedRingObj Λ X) :=
  Functor.monObjObj (F := upperStarFromPoint X) Λ

/-- The pulled-back continuous quotient ring retains its commutative ring structure.
Source: blueprint integral generators (3), the finite coefficient identification
(blueprint: det-lem-integral-models-generators). -/
noncomputable instance integralModelFiniteCoefficient_isComm (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    IsCommMonObj (completedCoefficient X (Profinite.continuousMapRingSheaf A)).X := by
  exact Functor.isCommMonObj_obj (F := upperStarFromPoint X)

end WeilConjectures.SixFunctors
