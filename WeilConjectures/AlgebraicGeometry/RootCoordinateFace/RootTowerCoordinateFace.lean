/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
public import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.CompositionAdjunctionNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.AdjunctionSquareExchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
import WeilConjectures.RingTheory.ProEtale.ClosedLiftMap
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.ProEtale.ClosedLiftAdjunction
import WeilConjectures.RingTheory.HenselianOfEtaleSectionLifting
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.ProEtaleCoefficients.ConnectedComponentsProfinite
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentPointMonoidalFactorization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentDerivedSymmetry
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentSectionRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentLisseEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentFinalScalarComparison
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedSquareData
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentOrdinaryPullbackSquare
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedTensorLifts
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedSquareCoherence
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Separation.Profinite
import WeilConjectures.RingTheory.HenselianIntegralIdempotentLifting
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.RingTheory.StrictlyHenselianQuotient
import WeilConjectures.RingTheory.HenselianPairPrimeConnected
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import WeilConjectures.RingTheory.FactorsThroughLocalization
import WeilConjectures.RingTheory.ProEtale.WLocal
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.Small
import WeilConjectures.AlgebraicGeometry.SmoothSectionEtaleLift
import WeilConjectures.RingTheory.HenselizationStageMap
import WeilConjectures.RingTheory.ProEtale.RetractionsStrictlyHenselian
import WeilConjectures.RingTheory.IntegralOverHenselianPair
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebraCore
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebraAffine
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Directed
import Mathlib.Topology.QuasiSeparated
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Algebra.Ring.Subring.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import WeilConjectures.Topology.SheafCokernelLocalImage
import WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Topology.Sheaves.Module
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomFinitePresentationKernel
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Topology.SheafIsomorphismLocalOpenCover
import WeilConjectures.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings
import WeilConjectures.CategoryTheory.Sites.ModuleDirectedColimitUnderlyingSets
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.AlgebraicGeometry.AbelianVariety.CoherentFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Ideal.Quotient.Defs
import WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.InducedCategory
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Topology.GlueSheavesOfModules
import Mathlib.Data.Fintype.EquivFin
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.ModuleFinitePresentationCokernel
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension
import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.ModuleFinitePresentationExtension
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraSheafConstruction
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.RingTheory.SymmetricAlgebraFinitePresentation
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebraColimit
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Ideal.GoingUp
import WeilConjectures.AlgebraicGeometry.Finite.FiniteAffineSectionCover
import WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.Topology.Connected.Separation
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.RingTheory.ProperBaseChange.ProfiniteComponentRingPullback
import Mathlib.RingTheory.TensorProduct.Quotient
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import WeilConjectures.RingTheory.ProEtale.IntegralLocal
import WeilConjectures.Mathlib.RingTheory.Idempotents
import WeilConjectures.RingTheory.WContractibleGeometricCriterion
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import WeilConjectures.RingTheory.HenselianLocalRootLifting
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finset.Order
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.CategoryTheory.ZetaWeil.ContractibleDerivedSectionsTensor
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal
import WeilConjectures.ProperBaseChange.CondensedFieldContinuousRealization
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverConstruction
import WeilConjectures.AlgebraicGeometry.GaloisCategories
import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Connected.Clopen
import WeilConjectures.ProperBaseChange.ProfiniteTestObjectFunctor
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalenceExtension
import Mathlib.GroupTheory.Index
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantCover
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.OpenSubgroups
import WeilConjectures.AlgebraicGeometry.Limits.AffineOverLimitProperties
import WeilConjectures.CategoryTheory.Sites.Torsor
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.PairHenselization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import WeilConjectures.RingTheory.PthRootAlgebraLocal
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.GroupTheory.MonoidLocalization.Away
import WeilConjectures.RingTheory.ParameterRoot.ParameterRootAlgebra
import Mathlib.Order.ULift
import WeilConjectures.RingTheory.FilteredColimitIsDomain
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.FiniteLocalHenselian
import WeilConjectures.RingTheory.RegularSequencePowers
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.KrullDimension.Regular
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import WeilConjectures.ProperBaseChange.MonicTensorPresentation.MonicTensorPresentation
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Coordinate faces of the unpunctured compatible-root tower

Source: blueprint main-20261015, direct-image stability proof, paragraph (3),
agent-extracted coordinate-face input (blueprint: lem-sfb-root-tower-coordinate-face).

The root algebra, coefficient rings, lisse modules and profinite tests are the existing
constructions. The face is the quotient by the selected root coordinates. In particular
it is not the possibly nonreduced cartesian fibre. The comparison is the mate of the
canonical pullback comparison, hence the adjunct of the pulled-back counit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.RootCoordinateFace

variable (p : ℕ) {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
section Coefficients

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Exact coefficient pullback on the ordinary unbounded derived category.
Source: direct-image proof (3), g_J^* (blueprint: lem-sfb-root-tower-coordinate-face). -/
abbrev upper {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (CondensedRing.upperStar Λ f).mapDerivedCategory

/-- The recorded total right derived functor of the full module direct image.
Source: direct-image proof (3), Rq_* (blueprint: lem-sfb-root-tower-coordinate-face). -/
abbrev lower {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  CondensedRing.moduleObjectDerivedPushforward Λ f

/-- The actual exact-pullback/total-direct-image derived adjunction.
Source: direct-image proof (3), defining counit
(blueprint: lem-sfb-root-tower-coordinate-face). -/
def adjunction {X Y : Scheme.{u}} (f : X ⟶ Y) : upper Λ f ⊣ lower Λ f :=
  (CondensedRing.upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction

end Coefficients

section Normalizations

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end Normalizations

end AlgebraicGeometry.ProEtale.RootCoordinateFace
