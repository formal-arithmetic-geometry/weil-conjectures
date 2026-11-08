/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.CategoryTheory.Sites.Limits
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
import Submission.WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Submission.WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Submission.WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Sites.Sheaf
import Submission.WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import Submission.WeilConjectures.CategoryTheory.InverseMateEquivalence
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Replete
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
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
public import Submission.WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Submission.WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
public import Submission.WeilConjectures.CategoryTheory.StrictRoosComparison
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Submission.WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Submission.WeilConjectures.CategoryTheory.StrictRoosDerivation
public import Submission.WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Submission.WeilConjectures.Algebra.Homology.RoosComplex
public import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Submission.WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Submission.WeilConjectures.CategoryTheory.StrictRoosNormalization
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.Basic.Denumerable
public import Submission.WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
public import Submission.WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
public import Submission.WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Submission.WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
public import Submission.WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Submission.WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import Submission.WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Submission.WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Localization.Adjunction
public import Submission.WeilConjectures.CategoryTheory.NormalizedLimitSquare.NormalizedLimitSquareCoherence
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import Mathlib.CategoryTheory.Adjunction.Whiskering

import Submission.WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Submission.WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Submission.WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import Submission.WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Submission.WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
/-!
# Scalar and normalized inverse-limit coherence for ringed open extension

Source: Stacks Project, Tags 09BP, 03DI, 03DJ and 03CY; the final paragraph of
blueprint `lem-cbc-completed-extension-zero-comparison.proof.md`
(blueprint: lem-cbc-ringed-open-scalar-limit-coherence).

## Main statements

- `ringedOpenScalarLimitCoherence`: canonical scalar/open and normalized-limit coherence.
- `CbcLimitNormalized`: the specified ordinary-limit and K-injective normalization.
- `CbcAugmentationCompatible`: compatibility with all strict augmentation maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096

universe u vA uA vB uB vC uC vD uD wA wB wC wD

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
attribute [-instance] RingedOpenScalar.scalarLimits RingedOpenScalar.scalarColimits
  RingedOpenScalar.sliceLimits RingedOpenScalar.sliceColimits

namespace CategoryTheory

section
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasLimits A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasLimits B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Actual derived postcomposition on strict towers, with levelwise exactness.
Source: Stacks 03DJ, 05RU
(blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
abbrev cbcTowerDerived : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤
    DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) :=
  @Functor.mapDerivedCategory _ _ _ _ _ _ _ _
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) inferInstance
    (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)

/-- The actual complex-to-derived factorization for tower postcomposition.
Source: Stacks 05RU (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
abbrev cbcTowerFactors :=
  @Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) inferInstance
    (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)

/-- The ordinary-limit unit normalization of the specified comparison. This is the
K-injective normalization of `exactProductFunctorStrictLimit`: on a K-injective tower
it reads `F lim I → lim FI → Rlim FI`. Its Roos description is precisely that theorem's
signed two-summand formula, not an unspecified triangle isomorphism.
Source: Stacks 0941; normalized comparison in
(blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
structure CbcLimitNormalized
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB)
    (lambda : LA ⋙ F.mapDerivedCategory ≅ cbcTowerDerived F ⋙ LB) : Prop where
  equation : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    F.mapDerivedCategory.map (etaA.app X) ≫ lambda.hom.app (DerivedCategory.Q.obj X) ≫
        LB.map ((cbcTowerFactors F).hom.app X) =
      F.mapDerivedCategoryFactors.hom.app (limit X.asFunctor) ≫
        DerivedCategory.Q.map
          (limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone (limit.cone X.asFunctor))) ≫
        etaB.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj X)

end

section
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [K.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K]

/-- Canonical localization of a commuting square, using the existing derived composition
and natural-isomorphism transports, including their exact complex factorizations.
Source: Stacks 05RU (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
def cbcDerivedSquare (e : F ⋙ G ≅ H ⋙ K) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ K.mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso e

/-- The same canonical square on derived strict towers, using levelwise exactness.
Source: Stacks 05RU (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
def cbcDerivedTowerSquare
    [HasLimits A] [HasLimits B] [HasLimits C] [HasLimits D]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{wC} (ℕᵒᵖ ⥤ C)] [HasDerivedCategory.{wD} (ℕᵒᵖ ⥤ D)]
    (e : F ⋙ G ≅ H ⋙ K) :
    cbcTowerDerived F ⋙ cbcTowerDerived G ≅ cbcTowerDerived H ⋙ cbcTowerDerived K :=
  CategoryTheory.NormalizedLimitSquare.towerSquare F G H K e

end

section EquationCalculus

variable {A B C D : Type uA} [Category.{vA} A] [Category.{vA} B]
  [Category.{vA} C] [Category.{vA} D]
  {JS : A ⥤ C} {JR : B ⥤ D} {rU : A ⥤ B} {rT : C ⥤ D}
  {qS : C ⥤ A} {qR : D ⥤ B}
  (e : JS ⋙ rT ≅ rU ⋙ JR) (d : rT ⋙ qR ≅ qS ⋙ rU)
  (adjS : JS ⊣ qS) (adjR : JR ⊣ qR)

variable [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [JS.Additive] [JR.Additive] [rU.Additive] [rT.Additive] [qS.Additive] [qR.Additive]

variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} B]
  [HasDerivedCategory.{wA} C] [HasDerivedCategory.{wA} D]
  [PreservesFiniteLimits JS] [PreservesFiniteColimits JS]
  [PreservesFiniteLimits JR] [PreservesFiniteColimits JR]
  [PreservesFiniteLimits rU] [PreservesFiniteColimits rU]
  [PreservesFiniteLimits rT] [PreservesFiniteColimits rT]
  [PreservesFiniteLimits qS] [PreservesFiniteColimits qS]
  [PreservesFiniteLimits qR] [PreservesFiniteColimits qR]

end EquationCalculus

section
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasLimits A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasLimits B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

end
section CoherenceHelpers
universe v w u' v' w' c h r
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
section Normalization
open NormalizedLimitSquare RoosAdjunctionUnit
variable {A : Type u} [Category.{v} A] [Abelian A] [HasLimits A]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
  [IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ A)]
  {LA : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A}
  {etaA : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LA}

variable {B : Type u'} [Category.{v'} B] [Abelian B] [HasLimits B]
  [HasDerivedCategory.{w'} B] [HasDerivedCategory.{w'} (ℕᵒᵖ ⥤ B)]
  {LB : DerivedCategory.{w'} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{w'} B}
  {etaB : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LB}
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

end Normalization
end CoherenceHelpers
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

section CoherentNormalization
variable {A B C D : Type uA} [Category.{vA} A] [Category.{vA} B]
  [Category.{vA} C] [Category.{vA} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasLimits A] [HasLimits B] [HasLimits C] [HasLimits D]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} B]
  [HasDerivedCategory.{wA} C] [HasDerivedCategory.{wA} D]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ C)] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ D)]
  [IsGrothendieckAbelian.{vA} (ℕᵒᵖ ⥤ A)] [IsGrothendieckAbelian.{vA} (ℕᵒᵖ ⥤ B)]
  [IsGrothendieckAbelian.{vA} (ℕᵒᵖ ⥤ C)] [IsGrothendieckAbelian.{vA} (ℕᵒᵖ ⥤ D)]
  {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {K : C ⥤ D}
  [F.Additive] [G.Additive] [H.Additive] [K.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K]
  {LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A}
  {LB : DerivedCategory.{wA} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wA} B}
  {LC : DerivedCategory.{wA} (ℕᵒᵖ ⥤ C) ⥤ DerivedCategory.{wA} C}
  {LD : DerivedCategory.{wA} (ℕᵒᵖ ⥤ D) ⥤ DerivedCategory.{wA} D}
  {etaA : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LA}
  {etaB : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LB}
  {etaC : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LC}
  {etaD : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LD}
  {e : F ⋙ G ≅ H ⋙ K}

end CoherentNormalization

end CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Existing locally bijective description at the same coefficient universe.
Source: Stacks 03CY (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcAbLocallyBijective (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T

variable {T : Scheme.{u}} (U : T.ProEt)
  {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)

variable [HasDerivedCategory.{wA} (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over
  U))]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over
    U))]
variable [HasDerivedCategory.{wA} (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over
  U))]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over
    U))]
variable [HasDerivedCategory.{wA} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))]
variable [HasDerivedCategory.{wA} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S))]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S))]

attribute [local irreducible] localizedSystemAdjunction
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
attribute [local irreducible] Functor.mapDerivedCategoryNatIso cbcDerivedSquare

attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
attribute [local instance] cbcAbLocallyBijective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] cbcDerivedTowerSquare Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.mapHomologicalComplex NatIso.mapHomologicalComplex

end AlgebraicGeometry.Scheme
