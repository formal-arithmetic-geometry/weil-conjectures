/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.AdjunctionSquareExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

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
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
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
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.CategoryTheory.ZetaWeil.ContractibleDerivedSectionsTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Integral direct image and closed base change for lisse continuous coefficients

Source: blueprint main-20261015, direct-image proof paragraph (3), agent-formulated
integral closed-base-change input; Stacks 0EYP is only the discrete-etale analogue.
(blueprint: lem-sfb-integral-lisse-closed-base-change).

All derived categories are ordinary and unbounded. The pullback is exact and is applied
termwise; its adjunction is transported from the recorded total derived adjunction.
Coefficient compatibility uses restriction comparisons in their canonical direction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralLisseClosedBaseChange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing exact module pullback on the ordinary derived category.
Source: sk-def-sfb-module-derived-pushpull, exact pullback identification
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def pull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (CondensedRing.upperStar Λ f).mapDerivedCategory

/-- The recorded K-injective derived adjunction, with exact pullback as its left adjoint.
Source: sk-def-sfb-module-derived-pushpull
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def adj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull Λ f ⊣ CondensedRing.moduleObjectDerivedPushforward Λ f :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).ofNatIsoLeft
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f)

/-- The canonical composition constraint of exact module pullback.
Source: sk-def-sfb-module-derived-pushpull, composition identifications
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def pullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull Λ (f ≫ g) ≅ pull Λ g ⋙ pull Λ f :=
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ f g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The square comparison uses the actual composition identifications and commutativity.
Source: the adjunct formula in the node statement
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def square {X U T Z : Scheme.{u}} {q : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {qZ : T ⟶ Z} (w : CommSq h qZ q s) :
    pull Λ s ⋙ pull Λ qZ ≅ pull Λ q ⋙ pull Λ h :=
  (pullComp Λ qZ s).symm ≪≫
    eqToIso (congrArg (fun f : T ⟶ U ↦ pull Λ f) w.w.symm) ≪≫ pullComp Λ h q

/-- The canonical exchange: the adjunct of the square comparison followed by h* counit.
No geometric property and no exactness of direct image is used in its construction.
Source: the displayed adjunct formula in the node statement
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def exchange {X U T Z : Scheme.{u}} {q : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {qZ : T ⟶ Z} (w : CommSq h qZ q s) :
    CondensedRing.moduleObjectDerivedPushforward Λ q ⋙ pull Λ s ⟶
      pull Λ h ⋙ CondensedRing.moduleObjectDerivedPushforward Λ qZ :=
  Adjunction.squareExchange (adj Λ q) (adj Λ qZ) (pull Λ s) (pull Λ h) (square Λ w)

section Coefficients

variable {Λ}
  {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ'] (c : Λ ⟶ Λ') [IsMonHom c]

end Coefficients

end AlgebraicGeometry.ProEtale.IntegralLisseClosedBaseChange
