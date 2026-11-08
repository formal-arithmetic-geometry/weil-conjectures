/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveTopology
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.Topology.Category.Profinite.Extend
public import Mathlib.Topology.Sheaves.Sheafify
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
public import Submission.WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
public import Submission.WeilConjectures.Algebra.Homology.FlatTruncationTower
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import Submission.WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
public import Submission.WeilConjectures.Algebra.Homology.KFlatTelescopeClosure
public import Submission.WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomology
public import Submission.WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import Submission.WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import Submission.WeilConjectures.Algebra.Homology.TelescopeColimit
public import Submission.WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import Submission.WeilConjectures.Algebra.Homology.TruncationTelescope
public import Submission.WeilConjectures.AlgebraicGeometry.CondensedPullbackTensorComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantRealizationDerivedScalarExtension
public import Submission.WeilConjectures.AlgebraicGeometry.DerivedChangeOfRingsModel
public import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
public import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSubsite
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTensorPullbackModels
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteFreeSliceDerivedHom
public import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import Submission.WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
public import Submission.WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence
public import Submission.WeilConjectures.AlgebraicGeometry.SiteDerivedTensorRestriction
public import Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.ExactDerivedAdjunction
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import Submission.WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
public import Submission.WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import Submission.WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import Submission.WeilConjectures.CategoryTheory.Sites.GeometricInverseImageExact
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
public import Submission.WeilConjectures.SecSmoothPurity.CochainInverseComparison
public import Submission.WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Evaluation coherence for free profinite parameters

Source: Stacks Project, Tags 08J7, 08J9 and 07A7; the generator and scalar
adjunction calculations in the node
(auxiliary; not a blueprint node).

All Hom objects are the recorded closed derived Hom. Gamma is the recorded
ProfiniteFreeSlice.Comparison.gamma. The maps below precede all coherence claims.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FreeParameterEvaluation

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- The recorded internal condensed module category.
Source: HRS Section 3 (auxiliary; not a blueprint node). -/
abbrev PointModules := Profinite.CondensedAction.Modules R

/-- The recorded internal modules on the small pro-etale site.
Source: HRS Section 3 (auxiliary; not a blueprint node). -/
abbrev Modules (X : Scheme.{u}) := ModuleObjectRingedComparison.Internal R.X X

/-- The existing exact point inverse image on modules.
Source: HRS Section 3 (auxiliary; not a blueprint node). -/
abbrev pointPull (X : Scheme.{u}) := ProfiniteFreeSlice.pointModulePullback R.X X

omit [IsCommMonObj R.X] in
/-- The point inverse image on modules is additive and exact.
Source: Stacks 03D2; HRS Section 3 (auxiliary; not a blueprint node). -/
theorem pointPull_exact (X : Scheme.{u}) : (pointPull R X).Additive ∧
    PreservesFiniteLimits (pointPull R X) ∧ PreservesFiniteColimits (pointPull R X) := by
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have : PreservesColimitsOfSize.{0, 0} pointUpperStar.{u} :=
    pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint
    infer_instance
  unfold pointPull ProfiniteFreeSlice.pointModulePullback
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

/-- Additivity of the point inverse image on modules. -/
instance pointPull_additive (X : Scheme.{u}) : (pointPull R X).Additive :=
  (pointPull_exact R X).1

/-- The point inverse image on modules preserves finite limits. -/
instance pointPull_limits (X : Scheme.{u}) : PreservesFiniteLimits (pointPull R X) :=
  (pointPull_exact R X).2.1

/-- The point inverse image on modules preserves finite colimits. -/
instance pointPull_colimits (X : Scheme.{u}) :
    PreservesFiniteColimits (pointPull R X) :=
  (pointPull_exact R X).2.2

/-- The ordinary unbounded point inverse image.
Source: HRS Section 3 (auxiliary; not a blueprint node). -/
abbrev pointPullD (X : Scheme.{u}) := (pointPull R X).mapDerivedCategory

end AlgebraicGeometry.ProEtale.FreeParameterEvaluation
