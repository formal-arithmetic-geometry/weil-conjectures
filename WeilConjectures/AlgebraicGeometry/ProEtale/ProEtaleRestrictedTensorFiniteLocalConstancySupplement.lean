/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackHomology
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationTensorComplex
import all WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsComparisonSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.LocallyConstantTensor
import all WeilConjectures.AlgebraicGeometry.SiteLocallyConstantFiniteType
import all WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import all Mathlib.RingTheory.Finiteness.Defs
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all Mathlib.CategoryTheory.Sites.Pretopology
import all Mathlib.RingTheory.Noetherian.Defs
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.AlgebraicGeometry.SiteFiniteFreeTruncationModels
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.Algebra.Category.ModuleCat.Free
import all WeilConjectures.AlgebraicGeometry.SiteBoundedTruncationModels
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.SiteBoundedConstantModel
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Sites.Abelian
import all Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import all WeilConjectures.AlgebraicGeometry.SiteBoundedConstantGradedModel
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Category.ModuleCat.Abelian
import all WeilConjectures.AlgebraicGeometry.SiteFiniteConstantExtensionTower
import all WeilConjectures.AlgebraicGeometry.FiniteConstantExtensionTower
import all WeilConjectures.AlgebraicGeometry.SiteFiniteConstantConeStep
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import all WeilConjectures.AlgebraicGeometry.SiteFiniteLocallyConstantWeakSerre
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
import all WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantSerre
import all WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import all WeilConjectures.CategoryTheory.FiniteTypeRestrictionExact
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.FiniteTypeConstantLocalLinear
import all WeilConjectures.CategoryTheory.SiteConstantModuleHomSurjective
import all WeilConjectures.Algebra.Homology.SmoothPurity.ConstantLocalModuleHomSupplement
import all WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Ring.Colimits
import all WeilConjectures.CategoryTheory.Site.SiteConstantModuleUnitSupplement
import all Mathlib.Algebra.Module.FinitePresentation
import all WeilConjectures.CategoryTheory.SiteConstantModuleOverHom
import all WeilConjectures.CategoryTheory.FinitePresentationLocalLift
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Sites.ConstantForget
import all Mathlib.RingTheory.Noetherian.Basic
import all WeilConjectures.CategoryTheory.FiniteTypeExtensionLocalPresentation
import all WeilConjectures.CategoryTheory.ConstantFiniteFreeLocalLift
import all WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.CategoryTheory.Abelian.Exact
import all WeilConjectures.CategoryTheory.ExtensionCokernelPresentation
import all WeilConjectures.Algebra.Homology.SmoothPurity.LocalModuleIsoSupplement
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import all Mathlib.RingTheory.Finiteness.Cardinality
import all WeilConjectures.CategoryTheory.FiniteTypeRestrictionMapExact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.LinearAlgebra.StdBasis
import all WeilConjectures.AlgebraicGeometry.BoundedTopMorphisms
import all Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Mathlib.RingTheory.Finiteness.Basic
import all WeilConjectures.AlgebraicGeometry.SiteFiniteConstantComplexDescent
import all Mathlib.Algebra.Category.ModuleCat.Limits
import all Mathlib.Algebra.Homology.Additive
import all Mathlib.Data.Int.Interval
import all WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import all WeilConjectures.RingTheory.RingPseudoCoherent
import all WeilConjectures.RingTheory.FiniteFreeResolution
import all WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import all Mathlib.Algebra.Homology.Single
import all WeilConjectures.RingTheory.PseudoCoherentIffAllM
import all WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import all WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import all WeilConjectures.CategoryTheory.TruncationTriangle
import all Mathlib.Algebra.Category.ModuleCat.Projective
import all Mathlib.CategoryTheory.Abelian.Projective.Extend
import all WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
import all WeilConjectures.AlgebraicGeometry.SiteTensorLocalModelComparison
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import all Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import all WeilConjectures.Algebra.Homology.SliceTensorNatural
import all WeilConjectures.Algebra.Homology.SliceModuleSheafification
import all Mathlib.Topology.Sheaves.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlatLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import all Mathlib.Algebra.Homology.ShortComplex.Basic
import all Mathlib.CategoryTheory.Subobject.Limits
import all WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import all WeilConjectures.CategoryTheory.RingedSliceExtensionPreservesExact
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import all WeilConjectures.CategoryTheory.RingedSliceExtensionReflectsExact
import all Mathlib.CategoryTheory.Sites.LocallyInjective
import all WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import all Mathlib.RingTheory.TensorProduct.Finite
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.HomologicalComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback

/-!
# Finite local constancy of a restricted derived tensor

Source: Stacks Project, Cohomology on Sites, Tags 094H and 07A4.
(blueprint: lem-pur-proetale-restricted-tensor-finite-local-constancy).
-/

@[expose] public section

universe u
set_option autoImplicit false
-- Honor the sealed tensor constructions despite the package's legacy default.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 256
-- Check each sealed comparison before elaborating its consumers.
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

section Proof

-- Build total tensors directly from countable colimits, avoiding diagram-wide search.

section TensorTransport
universe u₁ u₂ v₁ v₂
open CategoryTheory.MonoidalCategory
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]

end TensorTransport

attribute [local instance] Sheaf.monoidalCategory

section SmallCoefficients
universe s
variable {C : Type s} [Category.{s} C] (J : GrothendieckTopology C)
  (B : Type s) [CommRing B]

attribute [local irreducible] SheafOfModules.monoidalCategory Sheaf.monoidalCategory

attribute [local instance] smallMonoidal

end SmallCoefficients

attribute [-instance] smallConstMonoidal

namespace AlgebraicGeometry.Scheme

attribute [local instance] ProFiniteModels.asSmallDownEquivalence
  ProFiniteModels.asSmallUpEquivalence ProFiniteModels.asSmallDense
  ProFiniteModels.asSmallUpDense

section EncodingTensor
-- Comparing tensor functors needs only the API, never the localization construction.
attribute [local irreducible] SheafOfModules.monoidalCategory Sheaf.monoidalCategory

end EncodingTensor

attribute [local irreducible] encoding siteEncoding

-- Use tensor comparison lemmas without reducing their localized monoidal structures.
attribute [local irreducible] SheafOfModules.monoidalCategory Sheaf.monoidalCategory

attribute [-instance] intrinsicRTMonoidal

attribute [local instance] intrinsicRTMonoidal

end AlgebraicGeometry.Scheme

end Proof
