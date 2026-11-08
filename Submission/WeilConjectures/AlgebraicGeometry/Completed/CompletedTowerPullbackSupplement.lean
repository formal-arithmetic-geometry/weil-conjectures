/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import Submission.WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.Completed.CompletedReductionUnit
public import Submission.WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerDerivedLimitFunctor
public import Submission.WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Submission.WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
import Submission.WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
import Submission.WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullbackInterface
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantCoefficientEquivalence
import Submission.WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Adjunction.Additive
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import Submission.WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import Submission.WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
import Submission.WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import Submission.WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Submission.WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenScalarLimitCoherence
import Submission.WeilConjectures.CategoryTheory.NormalizedLimitSquare.NormalizedLimitSquareCoherence
import Submission.WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import Submission.WeilConjectures.CategoryTheory.Strict.StrictRoosShiftLocalization
import Submission.WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import Submission.WeilConjectures.CategoryTheory.StrictRoosComparison
import Submission.WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Submission.WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import Submission.WeilConjectures.CategoryTheory.StrictRoosDerivation
import Submission.WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Submission.WeilConjectures.Algebra.Homology.RoosComplex
import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Submission.WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Submission.WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Submission.WeilConjectures.CategoryTheory.StrictRoosNormalization
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.Basic.Denumerable
import Submission.WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
import Submission.WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
import Submission.WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Submission.WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.StrictReduction.ReductionPullbackDerivedTower
import Submission.WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarMateRestrictionCounitRoute
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
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
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Colimits
import Submission.WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Submission.WeilConjectures.AlgebraicGeometry.ProperBaseChange.NoetherianStratumDetectionSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
import Submission.WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Submission.WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Submission.WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Submission.WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
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
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import Submission.WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all Submission.WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLocalRestriction.ProEtaleLocalDerivedRestrictionComparisonsSupplement
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Submission.WeilConjectures.AlgebraicGeometry.CompletedTowerPullback

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
/-!
# Pullback of strict completed-coefficient towers

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1261;
Stacks Project, Tag 099N (blueprint: def-weil-pbc-completed-pullback).

The structure map into the completed coefficient ring is built from its finite
projections. It is a morphism, with no invertibility assumption. The functor here
precedes derived inverse limit and acts on every strict derived tower.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.Functor

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

/-- Finite constant coefficient inverse image has its canonical isomorphism.
Source: Stacks Tags 09AK and 09AL (blueprint: def-weil-pbc-completed-pullback).
Proof: the constant sheaf inverse image comparison is an isomorphism; the other two
factors are the fixed constant-section coefficient comparisons. Compose these isomorphisms. -/
@[instance]
theorem completedFiniteCoefficientMap_isIso (n : ℕ) :
    IsIso (completedFiniteCoefficientMap g d n) := by
  change IsIso (d.finiteRingIso g n).hom
  infer_instance

/-- Module inverse image followed by extension along the completed structure map.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedModulePullback :
    pbcModules Y (pbcAdicCompletion Y d) ⥤ pbcModules X (pbcAdicCompletion X d) :=
  proEtaleModuleInverseImage g (pbcAdicCompletion Y d) ⋙
    reductionChange X (completedCoefficientMap g d)

/-- Completed module pullback is additive.
Source: Stacks Tag 03EK (blueprint: def-weil-pbc-completed-pullback).
Proof: inverse image of abelian sheaves respects sums of maps, as does the induced
module inverse image. Sheafified scalar extension respects sums on tensor generators.
The composite therefore respects addition. -/
@[instance]
theorem completedModulePullback_additive : (completedModulePullback g d).Additive := by
  dsimp only [completedModulePullback]
  infer_instance

/-- Apply the module pullback to objects and maps at each strict tower level.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedTowerModulePullback :
    pbcTowers Y (pbcAdicCompletion Y d) ⥤ pbcTowers X (pbcAdicCompletion X d) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (completedModulePullback g d)

/-- Levelwise pullback is additive, with equality checked at every level.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: each component is the additive completed module pullback, and equality of
natural transformations is componentwise. -/
@[instance]
theorem completedTowerModulePullback_additive :
    (completedTowerModulePullback g d).Additive := by
  constructor
  intro M N f h
  apply NatTrans.ext
  funext n
  exact (completedModulePullback g d).map_add

private theorem completedCoefficientMap_eq_integralRingIso :
    completedCoefficientMap g d = (d.integralRingIso g).hom := by
  apply limit.hom_ext
  intro n
  change completedCoefficientMap g d ≫ d.projection X n.unop =
    (d.integralRingIso g).hom ≫ d.projection X n.unop
  calc
    _ = completedCoefficientComponent g d n.unop := limit.lift_π _ n
    _ = _ := by
      rw [d.projection_comm]
      rfl

private theorem completedModulePullback_eq_exact :
    completedModulePullback g d =
      proEtaleRingModulePullback g (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso g) := by
  unfold completedModulePullback
  rw [completedCoefficientMap_eq_integralRingIso]
  refine CategoryTheory.Functor.ext (fun M ↦
    (completedAdicChangeData X (d.integralRingIso g).hom).choose_spec.choose
      ((proEtaleModuleInverseImage g (d.completedRing Y)).obj M)) ?_
  intro M N f
  exact (completedAdicChangeData X (d.integralRingIso g).hom).choose_spec.choose_spec.choose
    ((proEtaleModuleInverseImage g (d.completedRing Y)).map f)

private instance completedModulePullback_finiteLimits :
    PreservesFiniteLimits (completedModulePullback g d) := by
  rw [completedModulePullback_eq_exact]
  infer_instance

private instance completedModulePullback_finiteColimits :
    PreservesFiniteColimits (completedModulePullback g d) := by
  rw [completedModulePullback_eq_exact]
  infer_instance

private instance completedTowerModulePullback_finiteLimits :
    PreservesFiniteLimits (completedTowerModulePullback g d) := by
  dsimp only [completedTowerModulePullback]
  exact ⟨fun _ _ _ ↦ inferInstance⟩

private instance completedTowerModulePullback_finiteColimits :
    PreservesFiniteColimits (completedTowerModulePullback g d) := by
  dsimp only [completedTowerModulePullback]
  exact ⟨fun _ _ _ ↦ inferInstance⟩

/-- The universal left-derived property and K-flat representative computation of the
specified pullback pair. Naming this property keeps later choice terms small.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def IsCompletedTowerPullbackPair
    (LF : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
        DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
        (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh) : Prop :=
  LF.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ)) ∧
      (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
      ∀ P : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ,
        (∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
          (R := pbcAdicCompletion Y d)
          (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
            (op n)).mapHomologicalComplex (.up ℤ) |>.obj P)) →
        IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- The universal left derived pair is computed on objectwise K-flat representatives.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: strict diagram K-flat replacements supply a quasi-isomorphism with objectwise
K-flat flat-term source. Pullback preserves quasi-isomorphisms between these by exact
inverse image and K-flat scalar extension. The additive termwise functor preserves
shifts and cones. Apply the resolving-class left-derived theorem; its counit is
invertible on every object of this class. All transitions are pulled back with the
same functor, so the computation remains a strict tower computation. -/
theorem completedTowerPullback_exists :
    ∃ (LF : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
        DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      IsCompletedTowerPullbackPair g d LF ε := by
  let F := completedTowerModulePullback g d
  refine ⟨F.mapDerivedCategory, F.mapDerivedCategoryFactorsh.hom, ?_, ?_, ?_⟩
  · exact Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh
  · exact ⟨inferInstance, inferInstance⟩
  · intro P _
    infer_instance

/-- Canonical total left derived levelwise pullback, with its universal comparison.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedTowerPullback :
    DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcTowers X (pbcAdicCompletion X d)) :=
  (completedTowerPullback_exists g d).choose

/-- The universal counit of strict tower pullback.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedTowerPullbackCounit :
    DerivedCategory.Qh ⋙ completedTowerPullback g d ⟶
      (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  (completedTowerPullback_exists g d).choose_spec.choose

/-- The universal left-derived property and K-flat representative computation of the
specified pullback pair. Naming this property keeps later choice terms small.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def IsCompletedOrdinaryPullbackPair
    (LF : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
        DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
        (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) : Prop :=
  LF.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) ∧
      ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients
          (R := pbcAdicCompletion Y d) P →
        IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- Ordinary derived pullback has the universal pair computed by the one-object
K-flat resolving class. This is ordinary pullback before completion.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: use exact module inverse image followed by the K-flat scalar extension along c_g.
K-flat flat-term resolutions exist on the small site. Scalar extension preserves
quasi-isomorphisms between K-flat complexes. Apply the resolving-class theorem. -/
theorem completedOrdinaryPullback_exists :
    ∃ (LF : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
        DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      IsCompletedOrdinaryPullbackPair g d LF ε := by
  let F := completedModulePullback g d
  refine ⟨F.mapDerivedCategory, F.mapDerivedCategoryFactorsh.hom, ?_, ?_⟩
  · exact Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh
  · intro P _
    infer_instance

/-- Ordinary total left derived completed-coefficient pullback.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedOrdinaryPullback :
    DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcModules X (pbcAdicCompletion X d)) :=
  (completedOrdinaryPullback_exists g d).choose

/-- The fixed ordinary left-derived counit.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedOrdinaryPullbackCounit :
    DerivedCategory.Qh ⋙ completedOrdinaryPullback g d ⟶
      (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  (completedOrdinaryPullback_exists g d).choose_spec.choose

attribute [irreducible] completedTowerPullback completedOrdinaryPullback

open CategoryTheory.Functor

-- Exact-presentation proof utilities from CompletedOpenExchangeTransport.
-- They are private here because that downstream module cannot be imported.
section

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private instance exactTowerFiniteLimits
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteLimits _ _ _ := inferInstance

private instance exactTowerFiniteColimits
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteColimits _ _ _ := inferInstance

private def constantDerivedSquare
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [hC : HasDerivedCategory C] [hD : HasDerivedCategory D]
    [hCt : HasDerivedCategory (ℕᵒᵖ ⥤ C)] [hDt : HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory ⋙ (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D).mapDerivedCategory ≅
      (Functor.const ℕᵒᵖ : C ⥤ ℕᵒᵖ ⥤ C).mapDerivedCategory ⋙
        ((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (Functor.compConstIso ℕᵒᵖ F)

private def transportedSquare
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L L' : C ⥤ D} {T T' : E ⥤ F} (DC : C ⥤ E) (DD : D ⥤ F)
    (e : L ≅ L') (et : T ≅ T') (c : L' ⋙ DD ≅ DC ⋙ T') : L ⋙ DD ≅ DC ⋙ T :=
  isoWhiskerRight e DD ≪≫ c ≪≫ isoWhiskerLeft DC et.symm

attribute [local irreducible] constantDerivedSquare transportedSquare

end

attribute [-instance] exactTowerFiniteLimits exactTowerFiniteColimits

private instance pullbackOrdinaryUniversal :
    (completedOrdinaryPullback g d).IsLeftDerivedFunctor
      (completedOrdinaryPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) := by
  unfold completedOrdinaryPullback completedOrdinaryPullbackCounit
  exact (completedOrdinaryPullback_exists g d).choose_spec.choose_spec.1

private instance pullbackTowerUniversal :
    (completedTowerPullback g d).IsLeftDerivedFunctor
      (completedTowerPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ)) := by
  unfold completedTowerPullback completedTowerPullbackCounit
  exact (completedTowerPullback_exists g d).choose_spec.choose_spec.1

end AlgebraicGeometry.Scheme
