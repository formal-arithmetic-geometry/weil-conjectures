/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Submission.WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf

import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
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
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Limits
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
import Submission.WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Submission.WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Submission.WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Sites.Sheaf
import Submission.WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import Submission.WeilConjectures.CategoryTheory.InverseMateEquivalence
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import Submission.WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import Submission.WeilConjectures.Mathlib.CategoryTheory.NatIso
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import Submission.WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Submission.WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import Submission.WeilConjectures.RingTheory.ProEtale.WeaklyEtale
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.SetTheory.Cardinal.Arithmetic
import Submission.WeilConjectures.ProperBaseChange.PrincipalWLocalization.ThmPeIndetaleRefinementPart1Supplement3
import Submission.WeilConjectures.ProperBaseChange.PrincipalWLocalization.ThmPeIndetaleRefinementPart2
import Submission.WeilConjectures.RingTheory.EtaleContraction.ThmPeIndetaleRefinementPart1
import Submission.WeilConjectures.ProperBaseChange.PrincipalWLocalization.Retained.ThmPeIndetaleRefinementPart2Supplement3
import Submission.WeilConjectures.RingTheory.ProEtale.WLocal
import Submission.WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Submission.WeilConjectures.RingTheory.ProEtale.RetractionsStrictlyHenselian
import Submission.WeilConjectures.ProperBaseChange.PrincipalWLocalization.Retained.ThmPeIndetaleRefinementPart3
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Submission.WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import Submission.WeilConjectures.RingTheory.FactorsThroughLocalization
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.RingTheory.Idempotents
import Submission.WeilConjectures.RingTheory.FilteredColimitOfFactorization
import Submission.WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Category.Stonean.Basic
import Submission.WeilConjectures.RingTheory.WContractibleGeometricCriterion
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Submission.WeilConjectures.AlgebraicGeometry.ProperBaseChange.WContractibleAffineEvaluation
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Triple
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteLift
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteFinitePresentationInternalHomColimit
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomOver
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteGlobalPresentationInternalHomColimit
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import Submission.WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Ringed pro-etale open-closed localization

Source: Stacks Project, Tags 09AA, 09BM, 09BN, 09AH, 09AG, 03DI, 03DJ and 0738
(blueprint: lem-weil-pbc-proetale-ringed-open-closed).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The underlying ring sheaf of arbitrary commutative pro-etale coefficients.
Source: Stacks, Modules on Sites, Tag 03D1
(blueprint: lem-weil-pbc-proetale-ringed-open-closed). -/
noncomputable abbrev proEtaleModuleCoefficients {X : Scheme.{u}}
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A

end AlgebraicGeometry.Scheme

namespace SheafOfModules

-- Fix the coefficient universe of the locally bijective criterion; the generic instance
-- leaves a universe metavariable for the essential smallness of the site.
private instance extensionAbWEqualsLocallyBijective {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) : J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  @SheafOfModules.wEqualsLocallyBijective_coefficientUniverse C _ (essentiallySmallSelf.{0} C) J

end SheafOfModules

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
