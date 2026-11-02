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
public import WeilConjectures.AlgebraicGeometry.IntegralLisseClosedBaseChange.IntegralLisseClosedBaseChange
public import WeilConjectures.AlgebraicGeometry.StrictLocalKummerTameModule

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

/-- The ideal of a coordinate face on the base.
Source: direct-image proof (3), U_J (blueprint: lem-sfb-root-tower-coordinate-face). -/
def baseIdeal (J : Finset (Fin r)) : Ideal R :=
  Ideal.span {a | ∃ j ∈ J, a = t j}

/-- The ideal generated by all roots in the selected branches, with no nilpotence bound.
Source: direct-image proof (3), e_J (blueprint: lem-sfb-root-tower-coordinate-face). -/
def rootIdeal (J : Finset (Fin r)) : Ideal (tameRootAlgebra p t) :=
  Ideal.span {a | ∃ (j : Fin r), j ∈ J ∧ ∃ n : TameRootOrder p,
    a = Ideal.Quotient.mk (Ideal.span (tameRootRelations p t)) (MvPolynomial.X (j, n))}

/-- The coordinate-face algebra. Eliminating the selected variables in the presentation
leaves precisely the root algebra on the remaining variables over R/(t_j : j in J).
Source: direct-image proof (3), T_J (blueprint: lem-sfb-root-tower-coordinate-face). -/
abbrev faceRing (J : Finset (Fin r)) := tameRootAlgebra p t ⧸ rootIdeal p t J

/-- The face inclusion sets exactly the selected root coordinates to zero.
Source: direct-image proof (3), e_J (blueprint: lem-sfb-root-tower-coordinate-face). -/
def inclusion (J : Finset (Fin r)) :
    Spec (.of (faceRing p t J)) ⟶ Spec (.of (tameRootAlgebra p t)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (rootIdeal p t J)))

/-- Every selected parameter belongs to the selected-root ideal after scalar extension.
Source: direct-image proof (3), root equations
(blueprint: lem-sfb-root-tower-coordinate-face).
Proof: take the order-one root (1 is prime to p). Its defining equation identifies
the image of t_j with x_(j,1), a generator of the displayed root ideal. The span
universal property gives the asserted containment. This includes J empty. -/
theorem baseIdeal_le (J : Finset (Fin r)) :
    baseIdeal t J ≤ (rootIdeal p t J).comap (algebraMap R (tameRootAlgebra p t)) := by
  apply Ideal.span_le.mpr
  rintro a ⟨j, hj, rfl⟩
  let n : TameRootOrder p := ⟨1, Nat.zero_lt_one, Nat.coprime_one_left p⟩
  have heq : Ideal.Quotient.mk (Ideal.span (tameRootRelations p t))
      (MvPolynomial.X (j, n)) = algebraMap R (tameRootAlgebra p t) (t j) := by
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk (Ideal.span (tameRootRelations p t)) _ -
      Ideal.Quotient.mk (Ideal.span (tameRootRelations p t)) (MvPolynomial.C (t j)) = 0
    rw [← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.subset_span
    exact Or.inl ⟨j, n, by simp [n]⟩
  change algebraMap R (tameRootAlgebra p t) (t j) ∈ rootIdeal p t J
  rw [← heq]
  exact Ideal.subset_span ⟨j, hj, n, rfl⟩

/-- The structural projection of the coordinate face, induced by the actual quotient map.
Source: direct-image proof (3), q_J (blueprint: lem-sfb-root-tower-coordinate-face). -/
def projection (J : Finset (Fin r)) :
    Spec (.of (faceRing p t J)) ⟶ Spec (.of (R ⧸ baseIdeal t J)) :=
  Spec.map (CommRingCat.ofHom
    (Ideal.quotientMap (rootIdeal p t J) (algebraMap R (tameRootAlgebra p t))
      (baseIdeal_le p t J)))

/-- The closed coordinate immersion on the base.
Source: direct-image proof (3), g_J (blueprint: lem-sfb-root-tower-coordinate-face). -/
def baseInclusion (J : Finset (Fin r)) : Spec (.of (R ⧸ baseIdeal t J)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (baseIdeal t J)))

/-- The profinite test scheme, using the recorded functor X[-].
Source: direct-image proof (3), T[P] (blueprint: lem-sfb-root-tower-coordinate-face). -/
abbrev test (X : Scheme.{u}) (P : Profinite.{u}) := (profiniteToProEtOf X).obj P

/-- Functoriality of X[P] in the scheme X, as the actual map of fibre products over Spec Z.
Source: direct-image proof (3), e_(J,P)
(blueprint: lem-sfb-root-tower-coordinate-face). -/
def testMap {X Y : Scheme.{u}} (f : X ⟶ Y) (P : Profinite.{u}) :
    (test X P).left ⟶ (test Y P).left :=
  pullback.lift (pullback.fst _ _) ((test X P).hom ≫ f)
    (specULiftZIsTerminal.hom_ext _ _)

private theorem testMap_snd {X Y : Scheme.{u}} (f : X ⟶ Y) (P : Profinite.{u}) :
    testMap f P ≫ (test Y P).hom = (test X P).hom ≫ f := by
  exact pullback.lift_snd _ _ _

/-- The full test-tower structural projection.
Source: direct-image proof (3), q_P (blueprint: lem-sfb-root-tower-coordinate-face). -/
def towerProjection (P : Profinite.{u}) :
    (test (Spec (.of (tameRootAlgebra p t))) P).left ⟶ Spec (.of R) :=
  (test _ P).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (tameRootAlgebra p t)))

/-- The face-test structural projection.
Source: direct-image proof (3), q_(J,P)
(blueprint: lem-sfb-root-tower-coordinate-face). -/
def faceProjection (J : Finset (Fin r)) (P : Profinite.{u}) :
    (test (Spec (.of (faceRing p t J))) P).left ⟶ Spec (.of (R ⧸ baseIdeal t J)) :=
  (test _ P).hom ≫ projection p t J

/-- The quotient and structural projections form the specified commuting square.
Source: direct-image proof (3), face square
(blueprint: lem-sfb-root-tower-coordinate-face).
Proof: the quotient homomorphism sends the class of a coefficient a to its class
in the root quotient. Spec reverses this equality. The second projection of the
profinite fibre product commutes with testMap by the pullback projection equation. -/
theorem square (J : Finset (Fin r)) (P : Profinite.{u}) :
    testMap (inclusion p t J) P ≫ towerProjection p t P =
      faceProjection p t J P ≫ baseInclusion t J := by
  have h : inclusion p t J ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (tameRootAlgebra p t))) =
      projection p t J ≫ baseInclusion t J := by
    simp only [inclusion, projection, baseInclusion, ← Spec.map_comp]
    congr 1
  dsimp only [towerProjection, faceProjection]
  rw [← Category.assoc, testMap_snd, Category.assoc, h, Category.assoc]

/-- The internal-module category over the specified pulled-back coefficient ring.
Source: direct-image proof (3), Mod(C_(F,X))
(blueprint: lem-sfb-root-tower-coordinate-face). -/
abbrev Modules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

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

/-- Composition of exact pullbacks, induced from the recorded ordinary comparison.
Source: direct-image proof (3), canonical identifications
(blueprint: lem-sfb-root-tower-coordinate-face). -/
def upperComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    upper Λ (f ≫ g) ≅ upper Λ g ⋙ upper Λ f :=
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ f g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The adjunction-normalized composite direct image; no arbitrary isomorphism is chosen.
Source: direct-image proof (3), canonical composition identification
(blueprint: lem-sfb-root-tower-coordinate-face). -/
def lowerComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    lower Λ (f ≫ g) ≅ lower Λ f ⋙ lower Λ g :=
  conjugateIsoEquiv (adjunction Λ (f ≫ g))
    ((adjunction Λ g).comp (adjunction Λ f)) (upperComp Λ f g).symm

/-- The pullback identification for a commuting square, without a cartesianness assumption.
Source: direct-image proof (3), q_J^* g_J^* = e_J^* q^*
(blueprint: lem-sfb-root-tower-coordinate-face). -/
def squareUpper {X' X Y' Y : Scheme.{u}}
    (e : X' ⟶ X) (q' : X' ⟶ Y') (q : X ⟶ Y) (g : Y' ⟶ Y)
    (h : e ≫ q = q' ≫ g) :
    upper Λ g ⋙ upper Λ q' ≅ upper Λ q ⋙ upper Λ e :=
  (upperComp Λ q' g).symm ≪≫
    eqToIso (congrArg (upper Λ) h.symm) ≪≫ upperComp Λ e q

/-- The mate of the actual pullback comparison. Its transpose is e^* of the q-counit.
This formula also defines ordinary cartesian exchange when the square is cartesian.
Source: direct-image proof (3), beta_(J,P)
(blueprint: lem-sfb-root-tower-coordinate-face). -/
def exchange {X' X Y' Y : Scheme.{u}}
    (e : X' ⟶ X) (q' : X' ⟶ Y') (q : X ⟶ Y) (g : Y' ⟶ Y)
    (h : e ≫ q = q' ≫ g) :
    lower Λ q ⋙ upper Λ g ⟶ upper Λ e ⋙ lower Λ q' :=
  (mateEquiv (adjunction Λ q) (adjunction Λ q')
    (TwoSquare.mk _ _ _ _ (squareUpper Λ e q' q g h).hom)).natTrans

end Coefficients

section Normalizations

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end Normalizations

end AlgebraicGeometry.ProEtale.RootCoordinateFace
