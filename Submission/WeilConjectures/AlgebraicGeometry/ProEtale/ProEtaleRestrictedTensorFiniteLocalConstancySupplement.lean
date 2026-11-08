/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ProEtaleSheafificationTensorComparison
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import all Submission.WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
import Submission.WeilConjectures.ConstructibleSheaf.Defs
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
import Submission.WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModelsComparison
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Submission.WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Submission.WeilConjectures.AlgebraicGeometry.LocallyConstantTensor
import all Submission.WeilConjectures.AlgebraicGeometry.SiteLocallyConstantFiniteType
import all Submission.WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import all Mathlib.RingTheory.Finiteness.Defs
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all Mathlib.CategoryTheory.Sites.Pretopology
import all Mathlib.RingTheory.Noetherian.Defs
import all Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteFreeTruncationModels
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.Algebra.Category.ModuleCat.Free
import all Submission.WeilConjectures.AlgebraicGeometry.SiteBoundedTruncationModels
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Submission.WeilConjectures.AlgebraicGeometry.SiteBoundedConstantModel
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Sites.Abelian
import all Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import all Submission.WeilConjectures.AlgebraicGeometry.SiteBoundedConstantGradedModel
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Category.ModuleCat.Abelian
import all Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantExtensionTower
import all Submission.WeilConjectures.AlgebraicGeometry.FiniteConstantExtensionTower
import all Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantConeStep
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import all Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteLocallyConstantWeakSerre
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
import all Submission.WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantSerre
import all Submission.WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Submission.WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import all Submission.WeilConjectures.CategoryTheory.FiniteTypeRestrictionExact
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all Submission.WeilConjectures.CategoryTheory.FiniteTypeConstantLocalLinear
import all Submission.WeilConjectures.CategoryTheory.SiteConstantModuleHomSurjective
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subsheaf
import Submission.WeilConjectures.CategoryTheory.LocalModuleHom
import Submission.WeilConjectures.CategoryTheory.LocalModuleIso
import Submission.WeilConjectures.CategoryTheory.ConstantLocalModuleHom
import all Submission.WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Ring.Colimits
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleUnit
import all Mathlib.Algebra.Module.FinitePresentation
import all Submission.WeilConjectures.CategoryTheory.SiteConstantModuleOverHom
import all Submission.WeilConjectures.CategoryTheory.FinitePresentationLocalLift
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Submission.WeilConjectures.CategoryTheory.Sites.ConstantForget
import all Mathlib.RingTheory.Noetherian.Basic
import all Submission.WeilConjectures.CategoryTheory.FiniteTypeExtensionLocalPresentation
import all Submission.WeilConjectures.CategoryTheory.ConstantFiniteFreeLocalLift
import all Submission.WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.CategoryTheory.Abelian.Exact
import all Submission.WeilConjectures.CategoryTheory.ExtensionCokernelPresentation
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import all Mathlib.RingTheory.Finiteness.Cardinality
import all Submission.WeilConjectures.CategoryTheory.FiniteTypeRestrictionMapExact
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.LinearAlgebra.StdBasis
import all Submission.WeilConjectures.AlgebraicGeometry.BoundedTopMorphisms
import all Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Mathlib.RingTheory.Finiteness.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantComplexDescent
import all Mathlib.Algebra.Category.ModuleCat.Limits
import all Mathlib.Algebra.Homology.Additive
import all Mathlib.Data.Int.Interval
import all Submission.WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import all Submission.WeilConjectures.RingTheory.RingPseudoCoherent
import all Submission.WeilConjectures.RingTheory.FiniteFreeResolution
import all Submission.WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import all Mathlib.Algebra.Homology.Single
import all Submission.WeilConjectures.RingTheory.PseudoCoherentIffAllM
import all Submission.WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import all Submission.WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import all Submission.WeilConjectures.CategoryTheory.TruncationTriangle
import all Mathlib.Algebra.Category.ModuleCat.Projective
import all Mathlib.CategoryTheory.Abelian.Projective.Extend
import all Submission.WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
import all Submission.WeilConjectures.AlgebraicGeometry.SiteTensorLocalModelComparison
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import all Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import all Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import all Submission.WeilConjectures.Algebra.Homology.SliceTensorNatural
import all Submission.WeilConjectures.Algebra.Homology.SliceModuleSheafification
import all Mathlib.Topology.Sheaves.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import all Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlatLimits
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import all Mathlib.Algebra.Homology.ShortComplex.Basic
import all Mathlib.CategoryTheory.Subobject.Limits
import all Submission.WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import all Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionPreservesExact
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import all Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionReflectsExact
import all Mathlib.CategoryTheory.Sites.LocallyInjective
import all Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import all Mathlib.RingTheory.TensorProduct.Finite
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.Colimits
import Submission.WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.HomologicalComplex
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import all Submission.WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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
private instance tensorTotal {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasColimitsOfSize.{0, 0} C]
    (P Q : CochainComplex C ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor C) (.up ℤ) :=
  fun _ ↦ @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _
      (inferInstance : HasColimitsOfSize.{0, 0} C) _ _) _

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

private noncomputable abbrev smallR := (sheafCompose J
  (forget₂ CommRingCat.{s} RingCat.{s})).obj
    ((constantSheaf J CommRingCat.{s}).obj (CommRingCat.of B))
private noncomputable abbrev smallScalar :
    (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ (smallR J B).obj := Functor.whiskerRight
  (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
  (forget₂ CommRingCat.{s} RingCat.{s})
private instance smallScalar_injective : Presheaf.IsLocallyInjective J (smallScalar J B) :=
  SheafOfModules.constantCommRingUnit_locallyInjective J B

private instance smallScalar_surjective : Presheaf.IsLocallySurjective J (smallScalar J B) :=
  SheafOfModules.constantCommRingUnit_locallySurjective J B

private noncomputable abbrev smallF := moduleExtension J B (smallR J B) (smallScalar J B)
@[instance_reducible]
private noncomputable instance smallConstMonoidal :
    MonoidalCategory (PresheafOfModules.{s}
      ((Functor.const Cᵒᵖ).obj (RingCat.of B))) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{s}
    (((Functor.const Cᵒᵖ).obj (CommRingCat.of B)) ⋙ forget₂ CommRingCat RingCat)))

attribute [local irreducible] SheafOfModules.monoidalCategory Sheaf.monoidalCategory

private noncomputable abbrev smallMonoidal :=
  @SheafOfModules.monoidalCategory.{s, s, s} C _ J _
    ((constantSheaf J CommRingCat.{s}).obj (CommRingCat.of B)) _ _
    (SheafOfModules.isMonoidal_W
      ((constantSheaf J CommRingCat.{s}).obj (CommRingCat.of B)))

attribute [local instance] smallMonoidal

end SmallCoefficients

attribute [-instance] smallConstMonoidal

namespace AlgebraicGeometry.Scheme

attribute [local instance] ProFiniteModels.asSmallDownEquivalence
  ProFiniteModels.asSmallUpEquivalence ProFiniteModels.asSmallDense
  ProFiniteModels.asSmallUpDense

@[no_expose]
private noncomputable def siteEncoding (X : Scheme.{u}) (A : Type u) [CommRing A] :=
  (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).sheafCongr
    (ProEt.topology X) (proEtaleModelTopology X)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))

private instance intrinsicMonoidalW (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ((ProEt.topology X).W.inverseImage (PresheafOfModules.toPresheaf.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).IsMonoidal :=
  SheafOfModules.isMonoidal_W_separateHomUniverse.{u + 1, u} (R := R)

@[no_expose, instance_reducible]
private noncomputable instance intrinsicRTMonoidal (X : Scheme.{u}) (A : Type u)
    [CommRing A] : MonoidalCategory (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  SheafOfModules.monoidalCategory.{u, u + 1, u + 1} (proEtaleConstantRing X A)

@[no_expose]
private noncomputable def encoding (X : Scheme.{u}) (A : Type u) [CommRing A] :=
  proEtaleModuleRestriction X A ⋙ (siteEncoding X A).functor ⋙
    smallF (proEtaleModelTopology X) (ULift.{u + 1, u} A)

private noncomputable instance encoding_equiv (X : Scheme.{u}) (A : Type u)
    [CommRing A] : (encoding X A).IsEquivalence := by
  let := proEtaleModuleRestriction_isEquivalence X A
  change (proEtaleModuleRestriction X A ⋙ (siteEncoding X A).functor ⋙
    smallF (proEtaleModelTopology X) (ULift.{u + 1, u} A)).IsEquivalence
  let : (smallF (proEtaleModelTopology X) (ULift.{u + 1, u} A)).IsEquivalence := {}
  infer_instance

private noncomputable instance encoding_additive (X : Scheme.{u}) (A : Type u)
    [CommRing A] : (encoding X A).Additive :=
  Functor.additive_of_preserves_binary_products (encoding X A)

section EncodingTensor
-- Comparing tensor functors needs only the API, never the localization construction.
attribute [local irreducible] SheafOfModules.monoidalCategory Sheaf.monoidalCategory

end EncodingTensor

attribute [local irreducible] encoding siteEncoding

-- Use tensor comparison lemmas without reducing their localized monoidal structures.
attribute [local irreducible] SheafOfModules.monoidalCategory Sheaf.monoidalCategory

attribute [-instance] intrinsicRTMonoidal

attribute [local instance] intrinsicRTMonoidal

private instance intrinsicPreadditive (X : Scheme.{u}) (A : Type u) [CommRing A] :
    MonoidalPreadditive (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  SheafOfModules.monoidalPreadditive_kfg.{u + 1, u} (proEtaleConstantRing X A)

private instance intrinsicCountableColimits (X : Scheme.{u}) (A : Type u) [CommRing A] :
    HasColimitsOfSize.{0, 0} (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  inferInstance

end AlgebraicGeometry.Scheme

end Proof
