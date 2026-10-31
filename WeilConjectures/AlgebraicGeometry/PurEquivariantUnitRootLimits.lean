/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtaleRootsOfUnitySheafSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

public import WeilConjectures.AlgebraicGeometry.PurTwistSheavesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.FixedPairCreatedAbelianStructure
public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientModulePullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImageSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.CategoryTheory.FixedPairDerivedForgetComparison
import WeilConjectures.CategoryTheory.StrictRoosDerivedLimitComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorSequence
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement
import WeilConjectures.AlgebraicGeometry.MilnorTower
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.AlgebraicGeometry.RoosCohomologySequence
import WeilConjectures.AlgebraicGeometry.RoosCohomologyMaps
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.AlgebraicGeometry.RoosCohomologyNaturality
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimitSupplement
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
public import WeilConjectures.AlgebraicGeometry.CompletedCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
import WeilConjectures.AlgebraicGeometry.PurIntegralTwistLineInverseImage
import WeilConjectures.AlgebraicGeometry.PurTwistSheafLocallyFree
import WeilConjectures.AlgebraicGeometry.TateTwistLocallyFree
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullbackSupplement
import WeilConjectures.SixFunctors.CompletedCoefficientFreeResolution
import WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.FlatRingedIdealCompleteEquivalenceSupplement
import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.CategoryTheory.RingedExtendedCech
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.CategoryTheory.RingedCompletionUnit
import WeilConjectures.CategoryTheory.RingedDerivedRestriction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestrictionSupplement
import Mathlib.Algebra.Homology.Double
import Mathlib.CategoryTheory.Endomorphism
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.CategoryTheory.Sites.Over
import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import WeilConjectures.CategoryTheory.RingedIdealGenerators
import WeilConjectures.Algebra.Homology.KFlatSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparisonSupplement
import WeilConjectures.CategoryTheory.RingedTowerPushforwardLimitComparison
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotients
import WeilConjectures.AlgebraicGeometry.ConstantCompletionBasic
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsFlatness
import WeilConjectures.AlgebraicGeometry.ConstantModuleSectionProperties
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.AlgebraicGeometry.SectionwiseAdicAlgebraLimit
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.Algebra.Category.CommAlgCat.Basic
import WeilConjectures.RingTheory.LimitFlatModules
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsProjection
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemModulesSupplement
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemProperties
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemFlatAndReduction
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsQuotient
import WeilConjectures.AlgebraicGeometry.ConstantCompletionQuotientKernel
import WeilConjectures.AlgebraicGeometry.ConstantCompletionProjectionKernel
import WeilConjectures.AlgebraicGeometry.AmbRootTowerPullbackCoherence
import WeilConjectures.CategoryTheory.CanonicalRightDerivedAdjunctionShift
public import WeilConjectures.CategoryTheory.RingedConstantTowerPushforwardNormalization
import WeilConjectures.CategoryTheory.Sites.GeometricInverseImageExactSupplement
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.CategoryTheory.Generator.Presheaf

/-! # Equivariant limits of the unit and root towers

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-limit.proof.md, (1)--(3); Stacks Tags 099L, 099M, 099I and 0940
(blueprint: lem-pur-equivariant-unit-root-limits).

Positive exponent n+1 is indexed by n. Equivariance is imposed before derivation.
Presentations retain all finite projections and the actual reduction and power maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u a b a' b' w w' wt wt'
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Endofunctor
namespace AlgebraicGeometry.Scheme.PurUnitRootLimits

/-- The existing module category on the original small pro-etale site.
Source: blueprint limit proof (1) (blueprint: lem-pur-equivariant-unit-root-limits). -/
abbrev Mod (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  SheafOfModules.{u + 1} (purTwistRing T R)

/-- Discrete constant scalars, without replacing them by completed scalars.
Source: blueprint limit proof (3) (blueprint: lem-pur-equivariant-unit-root-limits). -/
abbrev CMod (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] := Mod T (purTwistZlConstant T l)

/-- The existing sectionwise model of inverse image along the automorphism.
Source: blueprint limit proof (1) (blueprint: lem-pur-equivariant-unit-root-limits). -/
abbrev sigmaPull (T : Scheme.{u}) (σ : T ≅ T) (l : ℕ) [Fact l.Prime] :
    CMod T l ⥤ CMod T l :=
  isoSectionwiseModuleInverseImage.{u, u} σ.hom
    (isoSectionwiseConstantMap.{u, u} σ.hom (CommRingCat.of (ULift.{u + 1} ℤ_[l])))

/-- Automorphism inverse image is an autoequivalence.
Source: blueprint limit proof (1) (blueprint: lem-pur-equivariant-unit-root-limits).
Proof: inverse image along σ.inv is inverse; the constant coefficient maps compose
by their constant-section normalization. Use the two site equivalence unit maps. -/
theorem sigmaPull_isEquivalence (T : Scheme.{u}) (σ : T ≅ T) (l : ℕ) [Fact l.Prime] :
    (sigmaPull T σ l).IsEquivalence := by
  let g := σ.hom
  let A := CommRingCat.of (ULift.{u + 1} ℤ_[l])
  let c := isoSectionwiseConstantMap.{u, u} g A
  let F := proEtaleIsoPostcompose g
  let G := proEtaleIsoPostcompose (inv g)
  let e := proEtaleIsoPostcompose_equivalence g
  let E : T.ProEt ≌ T.ProEt :=
    CategoryTheory.Equivalence.mk F G e.2.1.some.symm e.2.2.1.some
  have : E.functor.IsContinuous (ProEt.topology T) (ProEt.topology T) :=
    proEtaleIsoPostcompose_isContinuous g
  have : E.inverse.IsContinuous (ProEt.topology T) (ProEt.topology T) :=
    proEtaleIsoPostcompose_isContinuous (inv g)
  let adj := E.toAdjunction
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
    (ProEt.topology T) (ProEt.topology T)
  let φ := inv c
  let ψ := shAdj.unit.app (purTwistRing T (purTwistZlConstant T l)) ≫
    (G.sheafPushforwardContinuous _ _ _).map c
  have H₁ : Functor.whiskerRight (NatTrans.op E.counit)
      (purTwistRing T (purTwistZlConstant T l)).obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext U : 2
    simp [ψ, φ, shAdj, adj]
  have H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op E.unit)
        (purTwistRing T (purTwistZlConstant T l)).obj =
      𝟙 (purTwistRing T (purTwistZlConstant T l)).obj := by
    have hh : φ ≫ (E.functor.sheafPushforwardContinuous RingCat _ _).map ψ ≫
        shAdj.counit.app (purTwistRing T (purTwistZlConstant T l)) = 𝟙 _ := by
      dsimp only [ψ]
      simp only [Functor.map_comp, Category.assoc]
      erw [shAdj.counit.naturality c]
      have ht := shAdj.left_triangle_components
        (purTwistRing T (purTwistZlConstant T l))
      calc
        _ = φ ≫ ((E.functor.sheafPushforwardContinuous RingCat _ _).map
            (shAdj.unit.app (purTwistRing T (purTwistZlConstant T l))) ≫
            shAdj.counit.app ((E.functor.sheafPushforwardContinuous RingCat _ _).obj
              (purTwistRing T (purTwistZlConstant T l)))) ≫ c := by
          simp only [Category.assoc, Functor.id_map]
          rfl
        _ = φ ≫ 𝟙 _ ≫ c := congrArg (fun h ↦ φ ≫ h ≫ c) ht
        _ = _ := by simp [φ]
    exact congrArg (fun f ↦ f.hom) hh
  exact (SheafOfModules.pushforwardPushforwardEquivalence E φ ψ H₁ H₂).isEquivalence_functor

attribute [instance] sigmaPull_isEquivalence

/-- Fixed pairs in the abelian module category, before localization.
Source: blueprint limit proof (1) (blueprint: lem-pur-equivariant-unit-root-limits). -/
abbrev EqMod (T : Scheme.{u}) (σ : T ≅ T) (l : ℕ) [Fact l.Prime] :=
  IsoAlgebra (sigmaPull T σ l)

/-- Fixed pairs have countable limits, created in the underlying module category.
Source: blueprint limit proof (1) (blueprint: lem-pur-equivariant-unit-root-limits).
Proof: take the ordinary limit of the carrier diagram. The automorphism pullback
preserves it. The limit-cone comparison transports the compatible sigma structures
to an isomorphism on this carrier limit; its projections and universal lifts
intertwine. This is the created-limit construction of fixedPairCreatedAbelianStructure. -/
theorem eqMod_countableLimits (T : Scheme.{u}) (σ : T ≅ T) (l : ℕ) [Fact l.Prime] :
    HasCountableLimits (EqMod T σ l) := by
  have h := IsoAlgebra.fixedPairCreatedAbelianStructure.{u + 2, u + 1, u + 1}
    (sigmaPull T σ l)
  let : CreatesLimitsOfSize.{u + 1, u + 1} (IsoAlgebra.forget (sigmaPull T σ l)) :=
    h.2.2.1.some
  let : HasLimitsOfSize.{u + 1, u + 1} (EqMod T σ l) :=
    hasLimits_of_hasLimits_createsLimits (IsoAlgebra.forget (sigmaPull T σ l))
  infer_instance

attribute [instance] eqMod_countableLimits

/-- The finite unit with its quotient action of discrete constant Z_l.
Source: blueprint limit proof (1) (blueprint: lem-pur-equivariant-unit-root-limits). -/
def unitLevel (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (n : ℕ) : CMod T l :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (purTwistZlReduction T l n))).obj
    (SheafOfModules.unit (purTwistRing T (purTwistFiniteRing T l n)))

/-- The finite root sheaf with its quotient action of discrete constant Z_l.
Source: blueprint limit proof (2) (blueprint: lem-pur-equivariant-unit-root-limits). -/
def rootLevel (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (n : ℕ) : CMod T l :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (purTwistZlReduction T l n))).obj (purTwistRootsModule T l n)

/-- Restriction of the two completed lines to the discrete scalar sheaf.
Source: blueprint limit proof (3) (blueprint: lem-pur-equivariant-unit-root-limits). -/
def res (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] :
    Mod T (purTwistZlCompletion T l) ⥤ CMod T l :=
  SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (purTwistZlCompletionMap T l))

/-- Forget modules to abelian sheaves, using the recorded functor.
Source: blueprint limit proof (1) (blueprint: lem-pur-equivariant-unit-root-limits). -/
abbrev ab (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] :=
  SheafOfModules.toSheaf (purTwistRing T (purTwistZlConstant T l))

/-- The ring-to-abelian-sheaf functor, used to specify all coefficient projections.
Source: blueprint limit proof (1) (blueprint: lem-pur-equivariant-unit-root-limits). -/
abbrev ringAb (T : Scheme.{u}) :=
  sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})

/-- A presentation of the actual equivariant unit and root towers and their limit cones.
Every underlying object, successor map and finite projection is specified. The finite
structure maps are normalized on constant sections and roots; hence their limit structures
are canonical as well. No basis of the root line is chosen.
Source: blueprint limit proof (1)--(2)
(blueprint: lem-pur-equivariant-unit-root-limits). -/
structure Towers (T : Scheme.{u}) (σ : T ≅ T) (l : ℕ) [Fact l.Prime] where
  U : ℕᵒᵖ ⥤ EqMod T σ l
  V : ℕᵒᵖ ⥤ EqMod T σ l
  u : ∀ n : ℕ, (U.obj (op n)).carrier ≅ unitLevel T l n
  v : ∀ n : ℕ, (V.obj (op n)).carrier ≅ rootLevel T l n
  unit_step : ∀ n : ℕ,
    (ab T l).map ((u (n + 1)).inv ≫ (U.map (homOfLE n.le_succ).op).hom.f ≫
      (u n).hom) = (ringAb T).map (purTwistFiniteTransition T l n)
  root_step : ∀ n : ℕ,
    (ab T l).map ((v (n + 1)).inv ≫ (V.map (homOfLE n.le_succ).op).hom.f ≫
      (v n).hom) =
      (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)).map (homOfLE n.le_succ).op
  unit_structure : ∀ n : ℕ,
    (ab T l).map ((sigmaPull T σ l).map (u n).inv ≫ (U.obj (op n)).str.hom ≫
      (u n).hom) =
      (sheafCompose (ProEt.topology T) (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
        (isoSectionwiseConstantMap.{u, u} σ.hom
          (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))))
  root_structure : ∀ (n : ℕ) (W : T.ProEtᵒᵖ)
    (x : ((sigmaPull T σ l).obj (rootLevel T l n)).val.obj W),
    proEtaleRootsOfUnitySections T (l ^ (n + 1)) W
      (((ab T l).map ((sigmaPull T σ l).map (v n).inv ≫
        (V.obj (op n)).str.hom ≫ (v n).hom)).hom.app W x) =
      proEtaleRootsOfUnitySections T (l ^ (n + 1))
        (op ((proEtaleIsoPostcompose σ.hom).obj W.unop)) x
  R : EqMod T σ l
  L : EqMod T σ l
  r : R.carrier ≅ (res T l).obj (SheafOfModules.unit
    (purTwistRing T (purTwistZlCompletion T l)))
  s : L.carrier ≅ (res T l).obj (purTwistZlModule T l)
  p : (Functor.const ℕᵒᵖ).obj R ⟶ U
  q : (Functor.const ℕᵒᵖ).obj L ⟶ V
  unit_projection : ∀ n : ℕ,
    (ab T l).map (r.inv ≫ (p.app (op n)).hom.f ≫ (u n).hom) =
      (ringAb T).map (purTwistZlProjection T l n)
  root_projection : ∀ n : ℕ,
    (ab T l).map (s.inv ≫ (q.app (op n)).hom.f ≫ (v n).hom) =
      limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op n)
  unit_limit : IsLimit (Cone.mk R p)
  root_limit : IsLimit (Cone.mk L q)

/-- The canonical presentations exist for every scheme and automorphism.
Source: blueprint limit proof (1)--(2)
(blueprint: lem-pur-equivariant-unit-root-limits).
Proof: lift the actual quotient and power transitions with their quotient scalar actions.
On constant sections σ acts by identity, and on roots by the unchanged global unit on
postcomposed test schemes. Naturality makes these structure isomorphisms intertwine.
The coefficient and root limit projections define the limit structures uniquely.
The coefficient limit identification is completedCondensedPadicIntegral; the root
limit and action are purTwistZlOne and purTwistZlModule. Forgetting creates limits. -/
theorem towers_nonempty (T : Scheme.{u}) (σ : T ≅ T) (l : ℕ) [Fact l.Prime] :
    Nonempty (Towers T σ l) := by
  sorry

/-- Exact coefficient-sized inverse image, with the existing normalized adjunction.
Source: Stacks Tag 03D2 (blueprint: lem-pur-equivariant-unit-root-limits). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) (l : ℕ) [Fact l.Prime] :
    CMod Y l ⥤ CMod X l :=
  coefficientProEtaleModulePullback.{u, u} f (CommRingCat.of (ULift.{u + 1} ℤ_[l]))

/-- Exactness is the existing geometric inverse-image theorem.
Source: Stacks Tag 03D2 (blueprint: lem-pur-equivariant-unit-root-limits). -/
instance pull_limits {X Y : Scheme.{u}} (f : X ⟶ Y) (l : ℕ) [Fact l.Prime] :
    PreservesFiniteLimits (pull f l) :=
  (coefficientProEtaleModulePullback_exact.{u, u} f
    (CommRingCat.of (ULift.{u + 1} ℤ_[l]))).1

/-- Exactness is the existing geometric inverse-image theorem.
Source: Stacks Tag 03D2 (blueprint: lem-pur-equivariant-unit-root-limits). -/
instance pull_colimits {X Y : Scheme.{u}} (f : X ⟶ Y) (l : ℕ) [Fact l.Prime] :
    PreservesFiniteColimits (pull f l) :=
  (coefficientProEtaleModulePullback_exact.{u, u} f
    (CommRingCat.of (ULift.{u + 1} ℤ_[l]))).2

/-- Additivity of the same exact inverse image.
Source: Stacks Tag 03D2 (blueprint: lem-pur-equivariant-unit-root-limits). -/
instance pull_additive {X Y : Scheme.{u}} (f : X ⟶ Y) (l : ℕ) [Fact l.Prime] :
    (pull f l).Additive := Functor.additive_of_preserves_binary_products _

/-- The unique identification with the sectionwise automorphism inverse image.
The inverse is its canonical generator at the distinguished comma object, so this
specifies the adjunction normalization rather than selecting an abstract isomorphism.
Source: Stacks Tags 03D2 and 00WX
(blueprint: lem-pur-equivariant-unit-root-limits).
Proof: the comma arrow is terminal in the inverse-image colimit. Its generator gives
an inverse to sectionwise evaluation. The constant-section scalar maps identify the
actions, and generators determine every module map uniquely. -/
theorem sigmaComparison_existsUnique (T : Scheme.{u}) (σ : T ≅ T)
    (l : ℕ) [Fact l.Prime] :
    ∃! e : pull σ.hom l ≅ sigmaPull T σ l,
      ∀ (M : CMod T l) (W : T.ProEt)
        (x : M.val.obj (op ((proEtaleIsoPostcompose σ.hom).obj W))),
      (e.inv.app M).val.app (op W) x =
        ((pull σ.hom l).obj M).val.map (proEtaleIsoCommaArrow σ.hom W).op
          (((coefficientProEtaleModuleAdjunction.{u, u} σ.hom
            (CommRingCat.of (ULift.{u + 1} ℤ_[l]))).unit.app M).val.app
              (op ((proEtaleIsoPostcompose σ.hom).obj W)) x) := by
  sorry

/-- The comparison is selected from its unique generator characterization.
Source: Stacks Tag 00WX (blueprint: lem-pur-equivariant-unit-root-limits). -/
def sigmaComparison (T : Scheme.{u}) (σ : T ≅ T) (l : ℕ) [Fact l.Prime] :=
  (sigmaComparison_existsUnique T σ l).exists.choose

/-- The canonical inverse-image commutator, using the recorded adjunction-normalized
composition and the actual equation of equivariant scheme maps.
Source: Stacks Tag 03D8 (blueprint: lem-pur-equivariant-unit-root-limits). -/
def pullCommutator {X Y : Scheme.{u}} (f : X ⟶ Y) (τ : X ≅ X) (σ : Y ≅ Y)
    (h : τ.hom ≫ f = f ≫ σ.hom) (l : ℕ) [Fact l.Prime] :
    pull f l ⋙ sigmaPull X τ l ≅ sigmaPull Y σ l ⋙ pull f l :=
  Functor.isoWhiskerLeft (pull f l) (sigmaComparison X τ l).symm ≪≫
    (coefficientModulePullbackComposition.{u, u} τ.hom f
      (CommRingCat.of (ULift.{u + 1} ℤ_[l]))).symm ≪≫
    eqToIso (congrArg (fun g : X ⟶ Y ↦ pull g l) h) ≪≫
    coefficientModulePullbackComposition.{u, u} f σ.hom
      (CommRingCat.of (ULift.{u + 1} ℤ_[l])) ≪≫
    Functor.isoWhiskerRight (sigmaComparison Y σ l) (pull f l)

/-- Canonical inverse image of semilinear modules, taken before derivation.
Source: blueprint limit proof (1)--(2)
(blueprint: lem-pur-equivariant-unit-root-limits). -/
abbrev eqPull {X Y : Scheme.{u}} (f : X ⟶ Y) (τ : X ≅ X) (σ : Y ≅ Y)
    (h : τ.hom ≫ f = f ≫ σ.hom) (l : ℕ) [Fact l.Prime] :=
  IsoAlgebra.mapOfNatIso (pullCommutator f τ σ h l)

section Categorical
variable {A : Type a} [Category.{b} A] [Abelian A]
  [HasCountableLimits A] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{wt} (ℕᵒᵖ ⥤ A)]

/-- Additivity of inverse limit, from its preserved finite products.
Source: Stacks Tag 0940 (blueprint: lem-pur-equivariant-unit-root-limits). -/
instance lim_additive : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
  Functor.additive_of_preserves_binary_products _

variable [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]

/-- Total right derived inverse limit on the abelian category of strict towers.
Source: Stacks Tag 0940 (blueprint: lem-pur-equivariant-unit-root-limits). -/
abbrev rlim : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A :=
  (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor

/-- The canonical derived constant-tower/inverse-limit adjunction.
Source: Stacks Tag 0940 (blueprint: lem-pur-equivariant-unit-root-limits). -/
def limitAdjunction :
    (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategory ⊣ rlim :=
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
    (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)) ⊣ lim)

/-- The canonical comparison attached to an ordinary cone. Its adjunct is precisely
that cone in degree zero, including every finite projection.
Source: Stacks Tag 0940 (blueprint: lem-pur-equivariant-unit-root-limits). -/
def coneUnit {M : A} {X : ℕᵒᵖ ⥤ A} (p : (Functor.const ℕᵒᵖ).obj M ⟶ X) :
    (DerivedCategory.singleFunctor A 0).obj M ⟶
      rlim.obj ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj X) :=
  (limitAdjunction.homEquiv _ _)
    (((Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).map p)

set_option linter.unusedSectionVars false in
/-- The elementary square defining the actual ell/id reduction transition.
Source: Stacks Tag 0A0E (blueprint: lem-pur-equivariant-unit-root-limits).
Proof: composition is bilinear, and ell times ell^(n+1) is ell^(n+2).
Both composites are multiplication by that same natural number. -/
theorem scalarReduction_square (l : ℕ) (M : A) (n : ℕ) :
    (l • 𝟙 M) ≫ ((l ^ (n + 1)) • 𝟙 M) =
      ((l ^ (n + 2)) • 𝟙 M) ≫ 𝟙 M := by
  simp [smul_smul, pow_succ, Nat.mul_comm]

/-- The source tower in the two-term equivariant free resolution has multiplication
by ell as transition; its target tower is constant. This gives precisely ell/id
transitions in degrees -1 and 0, inside the abelian category before derivation.
Source: Stacks Tags 0A0E and 0941
(blueprint: lem-pur-equivariant-unit-root-limits). -/
def scalarReductionMap (l : ℕ) (M : A) :
    Functor.ofOpSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ l • 𝟙 M) ⟶
      (Functor.const ℕᵒᵖ).obj M :=
  NatTrans.ofOpSequence (fun n ↦ (l ^ (n + 1)) • 𝟙 M)
    (fun n ↦ by
      simpa only [Functor.ofOpSequence_map_homOfLE_succ, Functor.const_obj_map] using
        scalarReduction_square l M n)

/-- The equivariant derived quotient tower is the cone of ell^(n+1) on the strict
source/target towers. Thus both copies of M and every transition retain their
semilinear structure before localization.
Source: Stacks Tags 0A0E and 0941
(blueprint: lem-pur-equivariant-unit-root-limits). -/
def scalarReductions (l : ℕ) (M : A) : DerivedCategory (ℕᵒᵖ ⥤ A) :=
  DerivedCategory.Q.obj (CochainComplex.mappingCone
    ((CochainComplex.singleFunctor (ℕᵒᵖ ⥤ A) 0).map (scalarReductionMap l M)))

/-- The canonical equivariant completion unit: the degree-zero cone inclusion,
transposed through the actual derived constant-tower/limit adjunction.
Source: Stacks Tags 0A0E and 0940
(blueprint: lem-pur-equivariant-unit-root-limits). -/
def scalarCompletionUnit (l : ℕ) (M : A) :
    (DerivedCategory.singleFunctor A 0).obj M ⟶ rlim.obj (scalarReductions l M) :=
  (limitAdjunction.homEquiv _ _)
    (((Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctorIsoCompQ (ℕᵒᵖ ⥤ A) 0).hom.app
        ((Functor.const ℕᵒᵖ).obj M) ≫
      DerivedCategory.Q.map (CochainComplex.mappingCone.inr
        ((CochainComplex.singleFunctor (ℕᵒᵖ ⥤ A) 0).map (scalarReductionMap l M))))

variable {B : Type a'} [Category.{b'} B] [Abelian B] [HasCountableLimits B]
  [HasDerivedCategory.{w'} B] [HasDerivedCategory.{wt'} (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The derived inverse-image/limit comparison is uniquely the adjoint mate of
inverse image applied to the counit, using the canonical constant-tower interchange.
Source: Stacks Tags 0940 and 07A6
(blueprint: lem-pur-equivariant-unit-root-limits).
Proof: the adjunction hom bijection applied to the specified counit composite gives
each component uniquely. Its naturality in both arguments gives naturality of the
components. Conversely equality of their adjuncts gives uniqueness of the transformation. -/
theorem limitComparison_existsUnique :
    ∃! β : rlim ⋙ F.mapDerivedCategory ⟶
        ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory ⋙ rlim,
      ∀ M : DerivedCategory (ℕᵒᵖ ⥤ A),
        (limitAdjunction.homEquiv _ _).symm (β.app M) =
          (ringedConstantTowerPullback F).inv.app (rlim.obj M) ≫
            ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory.map
              (limitAdjunction.counit.app M) := by
  let β := (mateEquiv (limitAdjunction (A := A)) (limitAdjunction (A := B))
    (ringedConstantTowerPullback F).inv).natTrans
  have hβ : ∀ M, (limitAdjunction.homEquiv _ _).symm (β.app M) =
      (ringedConstantTowerPullback F).inv.app (rlim.obj M) ≫
        ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory.map
          (limitAdjunction.counit.app M) := by
    intro M
    exact mateEquiv_counit _ _ _ M
  refine ⟨β, hβ, ?_⟩
  intro γ hγ
  ext M
  apply (limitAdjunction.homEquiv _ _).symm.injective
  exact (hγ M).trans (hβ M).symm

/-- The canonical comparison, chosen by its unique adjunction property.
Source: Stacks Tag 0940 (blueprint: lem-pur-equivariant-unit-root-limits). -/
def limitComparison := (limitComparison_existsUnique F).exists.choose

/-- Apply an exact functor to an ordinary cone using the actual constant-tower identity.
Source: Stacks Tag 0940 (blueprint: lem-pur-equivariant-unit-root-limits). -/
def mapCone {M : A} {X : ℕᵒᵖ ⥤ A} (p : (Functor.const ℕᵒᵖ).obj M ⟶ X) :
    (Functor.const ℕᵒᵖ).obj (F.obj M) ⟶ X ⋙ F :=
  (Functor.compConstIso ℕᵒᵖ F).hom.app M ≫ Functor.whiskerRight p F

private theorem limitComparison_transpose {M : DerivedCategory A}
    {X : DerivedCategory (ℕᵒᵖ ⥤ A)}
    (p : (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategory.obj M ⟶ X) :
    F.mapDerivedCategory.map (limitAdjunction.homEquiv _ _ p) ≫
        (limitComparison F).app X =
      limitAdjunction.homEquiv _ _ ((ringedConstantTowerPullback F).inv.app M ≫
        ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory.map p) := by
  apply (limitAdjunction.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm]
  have hx := (limitComparison_existsUnique F).exists.choose_spec X
  change (limitAdjunction.homEquiv _ _).symm ((limitComparison F).app X) = _ at hx
  simp only [Functor.comp_obj] at hx
  rw [hx, Equiv.symm_apply_apply]
  have hn := (ringedConstantTowerPullback F).inv.naturality_assoc
    ((limitAdjunction.homEquiv _ _) p)
    (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory.map
      (limitAdjunction.counit.app X))
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  rw [← Functor.map_comp]
  congr 1
  exact congrArg (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory.map)
    ((limitAdjunction.homEquiv _ _).symm_apply_apply p)

set_option linter.unusedSectionVars false in
private theorem constantTower_single (M : A) :
    (ringedConstantTowerPullback F).inv.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
        ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory.map
          (((Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategorySingleFunctor 0).hom.app
          ((Functor.const ℕᵒᵖ).obj M) =
      (Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤ B)).mapDerivedCategory.map
          ((F.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        ((Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤ B)).mapDerivedCategorySingleFunctor 0).hom.app
          (F.obj M) ≫
        (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).map
          ((Functor.compConstIso ℕᵒᵖ F).hom.app M) := by
  simp only [ringedConstantTowerPullback, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor]
  rw [← Functor.mapDerivedCategoryNatIso_symm, Iso.symm_symm_eq]
  rw [Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor,
    ← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor F
      (Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤ B)) M]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- Normalization of the derived mate on every ordinary cone. In particular exact
forgetting identifies the equivariant cone units with ordinary projection-induced units.
Source: Stacks Tag 0940 (blueprint: lem-pur-equivariant-unit-root-limits).
Proof: transpose through the target derived adjunction. Naturality of its counit,
the triangle identities, and the defining equation of limitComparison reduce both
sides to the image of p through the exact localization comparison. -/
theorem limitComparison_coneUnit {M : A} {X : ℕᵒᵖ ⥤ A}
    (p : (Functor.const ℕᵒᵖ).obj M ⟶ X) :
    F.mapDerivedCategory.map (coneUnit p) ≫
      (limitComparison F).app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj X) ≫
      rlim.map ((Functor.mapDerivedCategorySingleFunctor
        ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) 0).hom.app X) =
    (F.mapDerivedCategorySingleFunctor 0).hom.app M ≫ coneUnit (mapCone F p) := by
  rw [← Category.assoc]
  change (F.mapDerivedCategory.map (limitAdjunction.homEquiv _ _ _) ≫ _) ≫ _ = _
  rw [limitComparison_transpose, ← Adjunction.homEquiv_naturality_right]
  unfold coneUnit
  apply (limitAdjunction.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_naturality_left_symm]
  erw [Equiv.symm_apply_apply]
  simp only [Functor.map_comp, Category.assoc]
  have hn :=
    (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategorySingleFunctor 0).hom.naturality p
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  have hp : ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).map p =
      Functor.whiskerRight p F := rfl
  rw [hp]
  simpa only [mapCone, Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ k ≫ (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).map
      (Functor.whiskerRight p F)) (constantTower_single F M)

/-- The mate respects the canonical shifts, in addition to being natural on the entire
unbounded derived tower category.
Source: Stacks Tags 07A6 and 0940
(blueprint: lem-pur-equivariant-unit-root-limits).
Proof: the two canonical right-derived adjunctions commute with shifts. The
constant-tower interchange is induced by the termwise identity and also commutes
with shifts. Taking the adjoint mate preserves the resulting shift squares. -/
theorem limitComparison_commShift : NatTrans.CommShift (limitComparison F) ℤ := by
  let β := (mateEquiv (limitAdjunction (A := A)) (limitAdjunction (A := B))
    (ringedConstantTowerPullback F).inv).natTrans
  have heq : limitComparison F = β := by
    apply (limitComparison_existsUnique F).unique
    · exact (limitComparison_existsUnique F).exists.choose_spec
    · intro M
      exact mateEquiv_counit _ _ _ M
  rw [heq]
  let : (limitAdjunction (A := A)).CommShift ℤ :=
    canonicalRightDerivedAdjunctionShift constLimAdj
  let : (limitAdjunction (A := B)).CommShift ℤ :=
    canonicalRightDerivedAdjunctionShift constLimAdj
  have : NatTrans.CommShift (ringedConstantTowerPullback F).inv ℤ := by
    dsimp only [ringedConstantTowerPullback, Iso.trans_inv, Iso.symm_inv]
    infer_instance
  dsimp only [β, mateEquiv, Equiv.coe_fn_mk, TwoSquare.mk, TwoSquare.natTrans]
  infer_instance

end Categorical

private theorem tower_isGrothendieckAbelian
    {A : Type a} [Category.{b} A] [Abelian A] [IsGrothendieckAbelian.{b} A] :
    IsGrothendieckAbelian.{b} (ℕᵒᵖ ⥤ A) := by
  let : HasFilteredColimitsOfSize.{b, b} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{b, b} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact {}

/-- All strict ordinary module towers have K-injective resolutions.
Source: blueprint limit proof (1)
(blueprint: lem-pur-equivariant-unit-root-limits).
Proof: transport to the coefficient-sized small site. Module sheaves are Grothendieck
abelian, as are their countable diagrams by the free-diagram generators. Apply the
Grothendieck K-injective resolution theorem and transport back. -/
theorem moduleTowers_kInjective (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ Mod T R) := by
  let := SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
    (ProEt.topology T) (purTwistRing T R)
  let := tower_isGrothendieckAbelian (A := Mod T R)
  infer_instance

/-- All strict equivariant towers have K-injective resolutions.
Source: blueprint limit proof (1)
(blueprint: lem-pur-equivariant-unit-root-limits).
Proof: the automorphism is an exact autoequivalence. Fixed pairs in the Grothendieck
module category are Grothendieck, using the direct sum of all integer translates
of its generator. Countable diagrams have free-diagram generators. Apply the
Grothendieck K-injective theorem. This is the category of strict towers of fixed pairs,
not fixed pairs in a derived category. -/
theorem eqTowers_kInjective (T : Scheme.{u}) (σ : T ≅ T) (l : ℕ) [Fact l.Prime] :
    Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ EqMod T σ l) := by
  let := SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
    (ProEt.topology T) (purTwistRing T (purTwistZlConstant T l))
  let := IsoAlgebra.isGrothendieckAbelian (sigmaPull T σ l)
  let := tower_isGrothendieckAbelian (A := EqMod T σ l)
  infer_instance

attribute [instance] moduleTowers_kInjective eqTowers_kInjective

/-- The global scalar section ell of the existing unit module.
Source: Stacks Tag 0A0E (blueprint: lem-pur-equivariant-unit-root-limits). -/
def ellSection (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (l : ℕ) :=
  (SheafOfModules.unit (purTwistRing T R)).unitHomEquiv (l • 𝟙 _)

section Completeness
variable (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
  [HasDerivedCategory.{w} (Mod T R)]
  [HasDerivedCategory.{wt} (ℕᵒᵖ ⥤ Mod T R)]

/-- The actual derived quotient tower: tensor the recorded free two-term Koszul
resolution with the sheaf in degree zero, then rearrange as a complex of strict towers.
Source: Stacks Tags 0A0E and 0941
(blueprint: lem-pur-equivariant-unit-root-limits). -/
def reductions (l : ℕ) (M : Mod T R) : DerivedCategory (ℕᵒᵖ ⥤ Mod T R) :=
  DerivedCategory.Q.obj (koszulTowerComplex R
    (koszulTensorTower R ((CochainComplex.singleFunctor (Mod T R) 0).obj M)
      (ellSection T R l)))

/-- The canonical completion unit, adjoint to the recorded strict Koszul augmentation.
Source: Stacks Tags 0A0E and 0940
(blueprint: lem-pur-equivariant-unit-root-limits). -/
def completionUnit (l : ℕ) (M : Mod T R) :
    (DerivedCategory.singleFunctor (Mod T R) 0).obj M ⟶
      rlim.obj (reductions T R l M) :=
  (DerivedCategory.singleFunctorIsoCompQ (Mod T R) 0).hom.app M ≫
    (limitAdjunction.homEquiv _ _)
    (((Functor.const ℕᵒᵖ : Mod T R ⥤ (ℕᵒᵖ ⥤ Mod T R)).mapDerivedCategoryFactors).hom.app
          ((CochainComplex.singleFunctor (Mod T R) 0).obj M) ≫
      DerivedCategory.Q.map (koszulTowerComplexMap R
        (koszulStrictAugmentation R
          ((CochainComplex.singleFunctor (Mod T R) 0).obj M) (ellSection T R l))))

/-- Both equivalent completeness formulations, with their canonical unit and the actual
localization module. The displayed direct colimit of multiplication by ell is R[1/ell]
as an R-module; the internal Hom is the recorded mixed-universe derived sheaf Hom.
Source: Stacks Tags 099L and 0A0E
(blueprint: lem-pur-equivariant-unit-root-limits). -/
def Complete (l : ℕ) (M : Mod T R) : Prop :=
  IsIso (completionUnit T R l M) ∧
    IsZero ((derivedInternalHomMixedUniverses (ProEt.topology T) R).obj
      (op ((DerivedCategory.singleFunctor (Mod T R) 0).obj
        (colimit (Functor.ofSequence
          (X := fun _ : ℕ ↦ SheafOfModules.unit (purTwistRing T R))
          (fun _ ↦ l • 𝟙 _)))),
        (DerivedCategory.singleFunctor (Mod T R) 0).obj M))

end Completeness

section Comparisons
variable (T : Scheme.{u}) (σ : T ≅ T) (l : ℕ) [Fact l.Prime]
  [∀ x : T, Invertible (l : T.residueField x)]
  [HasDerivedCategory.{w} (EqMod T σ l)]
  [HasDerivedCategory.{wt} (ℕᵒᵖ ⥤ EqMod T σ l)]
  [HasDerivedCategory.{w'} (CMod T l)]
  [HasDerivedCategory.{wt'} (ℕᵒᵖ ⥤ CMod T l)]

/-- The two projection-normalized equivariant derived comparison isomorphisms.
The maps are the canonical cone units; their inverses have the orientation displayed
in the node. The same claim is made after exact forgetting.
Source: blueprint limit proof (1)--(2)
(blueprint: lem-pur-equivariant-unit-root-limits).
Proof: quotient and root power transitions are epimorphic, the latter on the
compatible-root cover. Pro-etale countable products are exact, so Milnor and the
projection-normalized strict Roos comparison identify each cone unit as an
isomorphism. Exact conservative forgetting commutes with this total derived limit
by the fixed-pair derived forgetting theorem. It reflects these isomorphisms.
For the two completeness units, the ell-power
free resolutions identify the scalar cone towers with the same actual finite
quotient towers, compatibly with the cone inclusions and all transitions.
This also proves completeness within the ordinary derived equivariant category. -/
theorem equivariant_unit_root_limits (P : Towers T σ l) :
    IsIso (coneUnit P.p) ∧ IsIso (coneUnit P.q) ∧
      IsIso (scalarCompletionUnit l P.R) ∧ IsIso (scalarCompletionUnit l P.L) ∧
      IsIso (limitComparison (IsoAlgebra.forget (sigmaPull T σ l))) := by
  sorry

end Comparisons

/-- The two completed lines are complete over both coefficient sheaves. Each clause
asserts invertibility of the canonical quotient-tower unit and vanishing of internal
RHom from that coefficient sheaf localized at ell.
Source: blueprint limit proof (2)--(3); Stacks Tags 099L, 099M, 099I and 0A0E
(blueprint: lem-pur-equivariant-unit-root-limits).
Proof: multiplication by each ell power on the completed unit is injective and the
free two-term Koszul complex resolves its finite quotient. The epimorphic tower
calculation proves its canonical completeness unit is invertible. On a compatible
primitive-root cover the integral root line is free of rank one, with quotient
map a*zeta to its finite reduction a*zeta_n, commuting with transitions; descent
proves completeness of that line. The flat constant-to-completed coefficient map
identifies all derived reductions, their transitions and units, and their limits,
so restriction preserves these two completeness units. The Noetherian principal
completion theorem identifies these conditions with vanishing of the two respective
localized internal derived Homs. All statements are local and include the empty site. -/
theorem unit_root_complete (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    [∀ x : T, Invertible (l : T.residueField x)]
    [HasDerivedCategory.{w} (Mod T (purTwistZlCompletion T l))]
    [HasDerivedCategory.{wt} (ℕᵒᵖ ⥤ Mod T (purTwistZlCompletion T l))]
    [HasDerivedCategory.{w'} (CMod T l)]
    [HasDerivedCategory.{wt'} (ℕᵒᵖ ⥤ CMod T l)] :
    Complete T (purTwistZlCompletion T l) l
      (SheafOfModules.unit (purTwistRing T (purTwistZlCompletion T l))) ∧
    Complete T (purTwistZlCompletion T l) l (purTwistZlModule T l) ∧
    Complete T (purTwistZlConstant T l) l ((res T l).obj
      (SheafOfModules.unit (purTwistRing T (purTwistZlCompletion T l)))) ∧
    Complete T (purTwistZlConstant T l) l ((res T l).obj (purTwistZlModule T l)) := by
  sorry

section FinitePullback
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (l : ℕ) [Fact l.Prime]

/-- Canonical pullback of each finite unit, fixed by the constant-section adjunct.
Source: Stacks Tags 03D2 and 0H7J
(blueprint: lem-pur-equivariant-unit-root-limits).
Proof: the quotient action is pulled back along the constant ring map. The
constant-section comparison gives the required map and is invertible under inverse
image. Its adjunct is the displayed section map, which determines it uniquely. -/
theorem unitPull_existsUnique (n : ℕ) :
    ∃! c : (pull f l).obj (unitLevel Y l n) ≅ unitLevel X l n,
      (ab Y l).map
        ((coefficientProEtaleModuleAdjunction.{u, u} f
          (CommRingCat.of (ULift.{u + 1} ℤ_[l]))).homEquiv _ _ c.hom) =
        (ringAb Y).map (coefficientProEtaleDirectRingMap.{u, u} f
          (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))) := by
  sorry

/-- The finite unit comparison selected by its unique adjunction normalization.
Source: Stacks Tag 0H7J (blueprint: lem-pur-equivariant-unit-root-limits). -/
def unitPull (n : ℕ) := (unitPull_existsUnique f l n).exists.choose

/-- Canonical finite root pullback, fixed by pullback of roots along the fibre-product
projection. No trivialization of the root sheaf is chosen.
Source: Stacks Tag 03PK (blueprint: lem-pur-equivariant-unit-root-limits).
Proof: the root direct-image map is linear for the quotient constant action. Its
adjunct is the root inverse-image comparison and is invertible because ell is
invertible: roots of unity are then finite etale, and geometric inverse image
preserves these represented sheaves under base change. The module adjunction
and faithful forgetting give uniqueness. -/
theorem rootPull_existsUnique [∀ y : Y, Invertible (l : Y.residueField y)] (n : ℕ) :
    ∃! c : (pull f l).obj (rootLevel Y l n) ≅ rootLevel X l n,
      (ab Y l).map
        ((coefficientProEtaleModuleAdjunction.{u, u} f
          (CommRingCat.of (ULift.{u + 1} ℤ_[l]))).homEquiv _ _ c.hom) =
        proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1)) := by
  sorry

variable [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The finite root comparison selected by its unique adjunction normalization.
Source: Stacks Tag 03PK (blueprint: lem-pur-equivariant-unit-root-limits). -/
def rootPull (n : ℕ) := (rootPull_existsUnique f l n).exists.choose

variable (τ : X ≅ X) (σ : Y ≅ Y) (h : τ.hom ≫ f = f ≫ σ.hom)
  (P : Towers Y σ l) (P' : Towers X τ l)

/-- The finite comparisons lift uniquely to the actual equivariant unit tower.
Source: blueprint limit proof (1)--(2)
(blueprint: lem-pur-equivariant-unit-root-limits).
Proof: adjunction-normalized pullback commutes with quotient reduction and with the
constant-section sigma structures. Conjugating each finite comparison by u and u'
gives compatible equivariant maps. They are isomorphisms and their components are
uniquely specified. -/
theorem unitTowerPull_existsUnique :
    ∃! c : P.U ⋙ eqPull f τ σ h l ≅ P'.U,
      ∀ n : ℕ, (pull f l).map (P.u n).inv ≫ (c.hom.app (op n)).hom.f ≫
        (P'.u n).hom = (unitPull f l n).hom := by
  sorry

/-- The canonical equivariant unit tower pullback, including its actual transitions.
Source: blueprint limit proof (1) (blueprint: lem-pur-equivariant-unit-root-limits). -/
def unitTowerPull := (unitTowerPull_existsUnique f l τ σ h P P').exists.choose

/-- The finite root comparisons lift uniquely to the actual equivariant root tower.
Source: blueprint limit proof (1)--(2)
(blueprint: lem-pur-equivariant-unit-root-limits).
Proof: root pullback commutes with power maps. Its sigma compatibility is the
functoriality of roots for the commuting scheme square, with its pullback-pasting
mate normalization. Conjugate by v and v' and use faithful forgetting for uniqueness. -/
theorem rootTowerPull_existsUnique :
    ∃! c : P.V ⋙ eqPull f τ σ h l ≅ P'.V,
      ∀ n : ℕ, (pull f l).map (P.v n).inv ≫ (c.hom.app (op n)).hom.f ≫
        (P'.v n).hom = (rootPull f l n).hom := by
  sorry

/-- The canonical equivariant root tower pullback, including its actual power maps.
Source: blueprint limit proof (2) (blueprint: lem-pur-equivariant-unit-root-limits). -/
def rootTowerPull := (rootTowerPull_existsUnique f l τ σ h P P').exists.choose

/-- The coefficient pullback map is the unique map with the prescribed finite quotient
projections. It is constructed by the actual target limit-cone universal property.
Source: blueprint limit proof (1) (blueprint: lem-pur-equivariant-unit-root-limits). -/
def coefficientPull : (eqPull f τ σ h l).obj P.R ⟶ P'.R :=
  P'.unit_limit.lift (Cone.mk _
    (mapCone (eqPull f τ σ h l) P.p ≫ (unitTowerPull f l τ σ h P P').hom))

/-- The Tate pullback map is the unique map with the prescribed finite root projections.
It is constructed by the actual target limit-cone universal property.
Source: blueprint limit proof (2) (blueprint: lem-pur-equivariant-unit-root-limits). -/
def tatePull : (eqPull f τ σ h l).obj P.L ⟶ P'.L :=
  P'.root_limit.lift (Cone.mk _
    (mapCone (eqPull f τ σ h l) P.q ≫ (rootTowerPull f l τ σ h P P').hom))

end FinitePullback

section DerivedPullback
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (l : ℕ) [Fact l.Prime]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (τ : X ≅ X) (σ : Y ≅ Y) (h : τ.hom ≫ f = f ≫ σ.hom)
  [HasDerivedCategory.{w} (EqMod Y σ l)]
  [HasDerivedCategory.{wt} (ℕᵒᵖ ⥤ EqMod Y σ l)]
  [HasDerivedCategory.{w'} (EqMod X τ l)]
  [HasDerivedCategory.{wt'} (ℕᵒᵖ ⥤ EqMod X τ l)]
  (P : Towers Y σ l) (P' : Towers X τ l)

/-- Pullback comparison is invertible on precisely the two specified towers. The
endpoint maps are the coefficient and Tate maps defined by all finite projections.
The comparison itself is defined on the entire derived tower category.
Source: blueprint limit proof (1)--(2)
(blueprint: lem-pur-equivariant-unit-root-limits).
Proof: transpose the comparison through the target constant-tower adjunction.
The cone-unit normalization identifies it, on these two sheaf towers, with the
unique map of their ordinary limit cones. The coefficient comparison is invertible
by completed condensed coefficient pullback. The root limit comparison is invertible
by integral Tate-line pullback on the compatible-root cover. Their finite
normalizations give the displayed endpoint maps, and conservative forgetting
reflects invertibility equivariantly. This uses no preservation of arbitrary limits. -/
theorem pullback_unit_root_isIso :
    IsIso (coefficientPull f l τ σ h P P') ∧
    IsIso (tatePull f l τ σ h P P') ∧
    IsIso ((limitComparison (eqPull f τ σ h l)).app
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ EqMod Y σ l) 0).obj P.U)) ∧
    IsIso ((limitComparison (eqPull f τ σ h l)).app
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ EqMod Y σ l) 0).obj P.V)) := by
  sorry

/-- Under the canonical unit-tower and limit identifications, the derived comparison
is exactly the coefficient pullback map.
Source: blueprint limit proof (1) (blueprint: lem-pur-equivariant-unit-root-limits).
Proof: transpose by the target adjunction. The defining mate equation and its
cone-unit normalization reduce the equation to the finite projection equations
of coefficientPull and unitTowerPull. The limit-cone universal property proves it. -/
theorem pullback_unit_normalization :
    (eqPull f τ σ h l).mapDerivedCategory.map (coneUnit P.p) ≫
      (limitComparison (eqPull f τ σ h l)).app
        ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ EqMod Y σ l) 0).obj P.U) ≫
      rlim.map
        (((((Functor.whiskeringRight ℕᵒᵖ (EqMod Y σ l) (EqMod X τ l)).obj
          (eqPull f τ σ h l)).mapDerivedCategorySingleFunctor 0).hom.app P.U) ≫
          (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ EqMod X τ l) 0).map
            (unitTowerPull f l τ σ h P P').hom) =
    ((eqPull f τ σ h l).mapDerivedCategorySingleFunctor 0).hom.app P.R ≫
      (DerivedCategory.singleFunctor (EqMod X τ l) 0).map
        (coefficientPull f l τ σ h P P') ≫ coneUnit P'.p := by
  sorry

/-- Under the canonical root-tower and limit identifications, the derived comparison
is exactly the Tate-line pullback map.
Source: blueprint limit proof (2) (blueprint: lem-pur-equivariant-unit-root-limits).
Proof: the same adjunction calculation as for the unit tower applies to the power
maps. Its two adjuncts have equal finite root projections by tatePull and
rootTowerPull, and the target root cone is limiting. -/
theorem pullback_root_normalization :
    (eqPull f τ σ h l).mapDerivedCategory.map (coneUnit P.q) ≫
      (limitComparison (eqPull f τ σ h l)).app
        ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ EqMod Y σ l) 0).obj P.V) ≫
      rlim.map
        (((((Functor.whiskeringRight ℕᵒᵖ (EqMod Y σ l) (EqMod X τ l)).obj
          (eqPull f τ σ h l)).mapDerivedCategorySingleFunctor 0).hom.app P.V) ≫
          (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ EqMod X τ l) 0).map
            (rootTowerPull f l τ σ h P P').hom) =
    ((eqPull f τ σ h l).mapDerivedCategorySingleFunctor 0).hom.app P.L ≫
      (DerivedCategory.singleFunctor (EqMod X τ l) 0).map
        (tatePull f l τ σ h P P') ≫ coneUnit P'.q := by
  sorry

set_option linter.unusedSectionVars false in
/-- Naturality includes all arrows between any shifted copies of the two tower
objects; it is not restricted to arrows represented by levelwise sheaf maps.
Source: blueprint limit proof (1)--(2)
(blueprint: lem-pur-equivariant-unit-root-limits).
Proof: apply naturality of the canonical mate to the given derived arrow. Its
shift compatibility identifies the endpoint comparisons with the shifts of the
coefficient and Tate comparisons. -/
theorem pullback_naturality (M N : DerivedCategory (ℕᵒᵖ ⥤ EqMod Y σ l))
    (i j : ℤ) (a : M⟦i⟧ ⟶ N⟦j⟧) :
    (eqPull f τ σ h l).mapDerivedCategory.map (rlim.map a) ≫
        (limitComparison (eqPull f τ σ h l)).app (N⟦j⟧) =
      (limitComparison (eqPull f τ σ h l)).app (M⟦i⟧) ≫
        rlim.map (((Functor.whiskeringRight ℕᵒᵖ (EqMod Y σ l) (EqMod X τ l)).obj
          (eqPull f τ σ h l)).mapDerivedCategory.map a) := by
  exact (limitComparison (eqPull f τ σ h l)).naturality a

end DerivedPullback

end AlgebraicGeometry.Scheme.PurUnitRootLimits
