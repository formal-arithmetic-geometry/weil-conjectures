/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
public import Submission.WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Submission.WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import Submission.WeilConjectures.CategoryTheory.RingObjects.Ab
public import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import Submission.WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import Submission.WeilConjectures.CategoryTheory.SheafTensor
public import Submission.WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Submission.WeilConjectures.Topology.ContinuousMapCondensedRing
public import Submission.WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Compactness.Compact
public import Submission.WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import Submission.WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Submission.WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Submission.WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Submission.WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
public import Submission.WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import Submission.WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistConstructionsSupplement
import Submission.WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree
import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import Submission.WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import Submission.WeilConjectures.NumberTheory.Padics.IntegersModPow
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistLevels
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Submission.WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Submission.WeilConjectures.CategoryTheory.Monoidal.Conjugate
import Submission.WeilConjectures.ConstructibleSheaf.Pullback
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Mathlib.Topology.NoetherianSpace
import Submission.WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import Submission.WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import Submission.WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.Algebra.Category.Ring.Basic
import Submission.WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Submission.WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import Submission.WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
import Submission.WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Submission.WeilConjectures.CategoryTheory.SiteModuleSliceSheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Submission.WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
import Submission.WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Submission.WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import Submission.WeilConjectures.NumberTheory.Padics.IntegersFinite
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.RingTheory.Localization.Module
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Functor
import Submission.WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.Free
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Submission.WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import Submission.WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedSubfieldBasis
import Submission.WeilConjectures.NumberTheory.Padics.IntegersAlgebra
import Mathlib.RingTheory.Valuation.LocalSubring
public import Submission.WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Cartesian coefficient sheaves

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-prop-sfb-cartesian-coefficients/_section.md`, assertions (1), (2), and the final paragraph
(blueprint: sk-prop-sfb-cartesian-coefficients).

The assertions below use the published coefficient comparison and module pullback.
The inverse-image lift and its comparison with extension of scalars are actual constructions.
The signed lines are the recorded Tate twists, including their sectionwise module encoding.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}}

/-- The normalized integral, rational and algebraic-closure signed comparisons.
Integral maps are fixed by all finite projections through spIntegralComparison;
rational maps by the displayed scalar-extension equation, and Qbar by its finite-field
coprojections. SpInternalCartesian retains precisely alpha_f and the sectionwise
signed coefficient-module comparisons, together with their tensor and dual equations.
Source: blueprint integral, rational, colimit, powers and duals paragraphs
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
structure CartesianAdicComparison (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] where
  rational : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
        (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
          (spRationalTwist.{u} Y ℓ E).X ⟶ (spRationalTwist.{u} X ℓ E).X
  qbar : (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
          (spQbarTwist.{u} Y ℓ).X ⟶ (spQbarTwist.{u} X ℓ).X
  rational_scalar : (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (Mod.extendπ (padicIntegersToPadicSubfield Y ℓ E) (spIntegralTwist.{u} Y ℓ E)) ≫
        rational E =
      Functor.OplaxMonoidal.δ (upperStar AddCommGrpCat.{u + 1} f)
        (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) Y)
        (spIntegralTwist.{u} Y ℓ E).X ≫
      (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) f ⊗ₘ
        spIntegralComparison f ℓ E) ≫
      Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist.{u} X ℓ E))
  qbar_coprojection : (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (colimit.ι (spRationalTwistDiagram Y ℓ) E) ≫ qbar =
        rational E ≫ colimit.ι (spRationalTwistDiagram X ℓ) E)
  integral_rational_cartesian : (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      SpInternalCartesian f (Profinite.padicIntegersRingObj.{u} ℓ E.1)
        (spIntegralTwist.{u} Y ℓ E) (spIntegralTwist.{u} X ℓ E) (spIntegralComparison f ℓ E) ∧
      SpInternalCartesian f (Profinite.continuousMapRingObj.{u} E.1)
        (spRationalTwist.{u} Y ℓ E) (spRationalTwist.{u} X ℓ E) (rational E))
  qbar_cartesian : SpInternalCartesian f (Profinite.padicAlgClRingObj.{u} ℓ)
      (spQbarTwist.{u} Y ℓ) (spQbarTwist.{u} X ℓ) qbar
  integral_inclusion : (∀ (E F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (spIntegralTwistMap Y ℓ h) ≫ spIntegralComparison f ℓ F =
        spIntegralComparison f ℓ E ≫ spIntegralTwistMap X ℓ h)
  rational_inclusion : (∀ (E F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (spRationalTwistMap Y ℓ h) ≫ rational F =
        rational E ≫ spRationalTwistMap X ℓ h)
  root_transition : (∀ (n m : ℕ) (h : n ≤ m),
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
        (Scheme.proEtaleRootsOfUnityTransition Y (ℓ ^ n) (ℓ ^ m)
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ h)) ≫ Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ n) =
      Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ m) ≫
        Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ n) (ℓ ^ m)
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ h))

end AlgebraicGeometry.ProEtale
