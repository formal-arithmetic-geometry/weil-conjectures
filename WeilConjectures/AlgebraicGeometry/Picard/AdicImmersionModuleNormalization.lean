/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.SfbCompletionNormalization
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NoetherianStratumDetectionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAbelianClosedCounit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SmoothPurity.ExactCompletedKoszulPullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.InternalHom
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
public import WeilConjectures.ProperBaseChange.RingedKoszulFactorColimit
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import WeilConjectures.ProperBaseChange.RingedKoszulFiniteEvaluation
public import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
public import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
public import WeilConjectures.Algebra.Homology.Monoidal.Dual
public import WeilConjectures.CategoryTheory.Monoidal.Dualizable
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Algebra.Homology.TelescopeColimit
public import WeilConjectures.CategoryTheory.SignedDoubleHomCone.SignedDoubleHomConeSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.ProperBaseChange.RingedCechKoszulDualKFlat
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
public import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
public import WeilConjectures.CategoryTheory.InverseMateEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import all WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all Mathlib.AlgebraicGeometry.Noetherian
import all WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Sites.LocalProperties
import all WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.NoetherianStratumDetectionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.SmoothPurity.ExactCompletedKoszulPullback
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.RingTheory.Localization.Away.Basic
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import all WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import all Mathlib.Algebra.Homology.Double
import all Mathlib.CategoryTheory.Endomorphism
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.Algebra.Homology.Functor
import all WeilConjectures.Algebra.Homology.InternalHom
import all Mathlib.CategoryTheory.Filtered.Final
import all Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
import all WeilConjectures.ProperBaseChange.RingedKoszulFactorColimit
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all Mathlib.CategoryTheory.Monoidal.Closed.Braided
import all Mathlib.CategoryTheory.Limits.Preserves.Opposites
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all WeilConjectures.ProperBaseChange.RingedKoszulFiniteEvaluation
import all WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
import all WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import all WeilConjectures.Algebra.Homology.Monoidal.Dual
import all WeilConjectures.CategoryTheory.Monoidal.Dualizable
import all Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import all WeilConjectures.Algebra.Homology.TelescopeColimit
import all WeilConjectures.CategoryTheory.SignedDoubleHomCone.SignedDoubleHomConeSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import all WeilConjectures.ProperBaseChange.RingedCechKoszulDualKFlat
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Homology.BifunctorShift
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import all WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import all WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all Mathlib.CategoryTheory.Limits.Preserves.Finite
import all Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.CategoryTheory.Sites.RegularEpi
import all Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import all WeilConjectures.CategoryTheory.InverseMateEquivalence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.Mathlib.CategoryTheory.NatIso
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Ring.FilteredColimits
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.AlgebraicGeometry.AffineScheme
import all WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import all WeilConjectures.RingTheory.ProEtale.WContractible
import all Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import all Mathlib.RingTheory.RingHom.FaithfullyFlat
import all WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.CategoryTheory.Site.SiteAlgebraicCompositionUnitSupplement
import all WeilConjectures.CategoryTheory.GeometricMorphism.GeometricInverseImageExactSupplement
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.CategoryTheory.Native.NativeRingedRestrictionSlicesSupplement

/-! # Module-level normalization of immersion and slice restriction

Source: Stacks Tags 00YY, 03D2, 03DJ and 099L.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w c d h vc vd vh

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- Keep coefficient limits folded when comparing module functors.
attribute [local irreducible] CategoryTheory.Limits.limit ConstantCompletion.completed

namespace SfbImmersionNormalization

private abbrev Modules {C : Type c} [Category.{vc} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w}) :=
  SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)

section Scalar

variable {C : Type c} [Category.{vc} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{w}}

end Scalar

section SmallScalar

variable {C : Type w} [SmallCategory C]
  {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{w}}

end SmallScalar

section Presentation

variable {C : Type c} {D : Type d} {H : Type h}
  [Category.{vc} C] [Category.{vd} D] [Category.{vh} H]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D] [EssentiallySmall.{w} H]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {T : GrothendieckTopology H}

end Presentation

end SfbImmersionNormalization

attribute [local instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

end AlgebraicGeometry.Scheme
