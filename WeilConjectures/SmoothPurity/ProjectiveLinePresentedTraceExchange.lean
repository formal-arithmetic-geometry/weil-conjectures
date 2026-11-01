/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.SmoothPurity.EtaleFiniteTwistPullbackRest
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.Modules.FieldBaseChange
public import WeilConjectures.SmoothPurity.FiniteP1ChernMapBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
public import WeilConjectures.SmoothPurity.SupportedDerivedUnitForget
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
public import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricFiberFinite
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.SmoothPurity.OrdinaryFiniteTwistTransportUniqueness
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
public import WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityTop
public import WeilConjectures.AlgebraicGeometry.Curve.Estimate
public import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator
public import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.SectionProjectionUnitSupplement
public import Mathlib.Logic.Small.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSupportedDiagonalUnitSupplement
public import WeilConjectures.ConstructibleSheaf.LisseRankOne
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.GroupTheory.Torsion
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.AbTorsionSheaf
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedFac
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
public import WeilConjectures.ProperBaseChange.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.KunnethMapAgrees
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionUnit
public import Mathlib.Tactic.SuppressCompilation
public import WeilConjectures.ConstructibleSheaf.InternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Ring.Int.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DecompositionMapsSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatSingleTensorCompatibilityDataSupplement
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Standard.ProjectiveSpaceStandardCharts
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.SmoothPurity.EtaleFiniteTwistPullbackRest
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SmoothPurity.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar
import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange

/-! # Exchange for the coefficient trace on projective-line presentations -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace
attribute [local instance 20000] Etale.sheafBraidedCategory

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  rightDerivedLowerShriekBaseChangeMap rightDerivedLowerShriekIsoRightDerivedLowerStar

section ProperComparisons

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.leftDerivedFunctor

attribute [local irreducible] rightDerivedLowerShriekOfCompactificationIso


attribute [local irreducible] rightDerivedLowerShriekBaseChangeMap'

end ProperComparisons

section DerivedComparisons

set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2 ordinaryFinitePullback._proof_3
  ordinaryFinitePullback._proof_4 ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8 ordinaryFinitePullback._proof_9
  ordinaryFinitePullback._proof_10 ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13


attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions


private theorem comp_hom
    (A : Type (u + 1)) [CommRing A] {X P Y : Scheme.{u}}
    (e : X ⟶ P) (p : P ⟶ Y) (q : X ⟶ Y) (w : e ≫ p = q) :
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e p ≪≫
      rightDerivedLowerStarCongr (ModuleCat.{u + 1} A) w).hom =
      rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) e p q w.symm := by
  subst q
  simp only [rightDerivedLowerStarCongr_refl, Iso.trans_refl]
  change conjugateEquiv
    ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).comp
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e))
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (e ≫ p))
    (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) e p) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).hom = _
  exact (conjugateEquiv_leftDerivedUpperStarComp_hom (ModuleCat.{u + 1} A)
    e p (e ≫ p) rfl).symm


attribute [local irreducible] ArbitraryBaseFiniteP1Splitting.trace
  ordinaryFiniteShiftedLinePullback

end DerivedComparisons
end AlgebraicGeometry.Etale
