/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.SmoothPurity.IntegralAmbient.NormalizedIntegralPullbackTower
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.Algebra.Homology.RingedPresentationOnSites.RingedPullbackPresentationOnSitesSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.Algebra.Homology.Ringed.RingedPullbackCochainPresentation
import WeilConjectures.SmoothPurity.Normalized.NormalizedIntegralTensorTower
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.Integral.IntegralTensorTransitionCompatibility

/-! # Ambient completion presentations of integral operations

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E, 07A4 and 0941;
sites-modules.tex, Tags 03D7 and 03EL
(blueprint: lem-pur-integral-ambient-operation-models).

All towers and finite operations below are the recorded constructions. The completed
coefficient map is specified by its projections, not by an identification of rings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.all false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a₁ b₁ c₁ d₁
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.IntegralAmbient
open AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive
  SheafOfModules.cochainTensorLocalizationIsMonoidal
  SheafOfModules.cochainTensorLeftPreservesColimits
  SheafOfModules.cochainTensorRightPreservesColimits
attribute [local instance 2000] integralOperationsFiniteHasMap

attribute [local irreducible] constantSheaf

attribute [local irreducible] HasDerivedCategory.standard

set_option maxHeartbeats 60000

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local irreducible] coefficientTotalTensor SheafOfModules.monoidalCategory
  completedIntegralCoefficientSheafUnrestricted unrestrictedIntegralReductionExistence
  SheafOfModules.changeOfRings PresheafOfModules.sheafification

attribute [local irreducible] coefficientMap push pull pullTowerIso tensorTowerIso
  IntegralOnSlice.duality IntegralOnSlice.completion IntegralOnSlice.completionComparison
  IntegralOnSlice.completionUnit IntegralOnSlice.roosUnit

attribute [local semireducible] coefficientTotalTensor

attribute [local irreducible] IntegralOnSlice.tower Functor.mapHomologicalComplex
  DerivedCategory.Q integralOperationsRoos integralOperationsRoosMap

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option maxHeartbeats 200000

/-- Capture the actual data used by the existing tensor model once.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientTensorPresentation (W : Scheme.{t}) :=
  AmbientTensorPresentation.ofComparison
    (IntegralOnSlice.duality l E W none).models.comparison
    (IntegralOnSlice.Good l E W none) (fun _ h ↦ h.1)

set_option warn.classDefReducibility false in
@[irreducible] def ambientCxCategory (W : Scheme.{t}) : Category (ambientCx l E W) :=
  (ambientTensorPresentation l E W).cxCategory

attribute [instance 5000] ambientCxCategory

set_option warn.classDefReducibility false in
/-- Share its recorded category structure throughout the comparisons.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientDCategory (W : Scheme.{t}) : Category (ambientD l E W) :=
  (ambientTensorPresentation l E W).dCategory

attribute [instance 5000] ambientDCategory

/-- The recorded ambient functor is a localization.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
@[instance] theorem ambientQ_isLocalization (W : Scheme.{t}) :
    (ambientQ l E W).IsLocalization (ambientQuasiIso l E W) := by
  with_unfolding_all exact
    @MorphismProperty.HasLocalization.hL _ _ _ (IntegralOnSlice.hasDerived l E W none)

/-- Ordinary pullback in the recorded ambient cochain presentation.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientPullComplex {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientCx l E Y ⥤ ambientCx l E X := by
  with_unfolding_all exact pullComplex l E f

/-- The ordinary total tensor of the recorded slice coefficient presentation.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientTotalTensor (W : Scheme.{t}) :
    ambientCx l E W × ambientCx l E W ⥤ ambientCx l E W :=
  by with_unfolding_all exact (ambientTensorPresentation l E W).totalTensor

/-- The ordinary quotient tower in the captured cochain category.
Source: Stacks 0941 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientQuotientTower (W : Scheme.{t}) :
    ambientCx l E W ⥤ (ℕᵒᵖ ⥤ ambientCx l E W) := by
  with_unfolding_all exact IntegralOnSlice.tower l E W none

/-- The quotient augmentation into this Roos complex.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientRoosUnit (W : Scheme.{t}) (P : ambientCx l E W) :
    P ⟶ (ambientRoosComplex l E W).obj P := by
  with_unfolding_all exact IntegralOnSlice.roosUnit l E W none P

/-- The recorded finite pullback tower in this cochain presentation.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientRecordedPullTower {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientCx l E Y ⥤ (ℕᵒᵖ ⥤ ambientCx l E X) := by
  with_unfolding_all exact integralOperationsPullbackTowerFunctor l E f

/-- The recorded finite tensor tower in this cochain presentation.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientRecordedTensorTower (W : Scheme.{t}) :
    ambientCx l E W × ambientCx l E W ⥤ (ℕᵒᵖ ⥤ ambientCx l E W) := by
  with_unfolding_all exact integralOperationsTensorTowerFunctor l E W

/-- The specified pullback tower comparison, sharing its source category data.
Source: Stacks 03EL (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientPullTowerIso {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientPullComplex l E f ⋙ ambientQuotientTower l E X ≅
      ambientRecordedPullTower l E f := by
  with_unfolding_all exact pullTowerIso l E f

/-- The specified tensor tower comparison, sharing its source category data.
Source: Stacks 03EL (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientTensorTowerIso (W : Scheme.{t}) :
    ambientTotalTensor l E W ⋙ ambientQuotientTower l E W ≅
      ambientRecordedTensorTower l E W := by
  with_unfolding_all exact tensorTowerIso l E W

/-- The recorded derived pullback in this derived category.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientPull {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientD l E Y ⥤ ambientD l E X := by
  with_unfolding_all exact integralDerivedPullback l E f

/-- The recorded completed tensor in this derived category.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientCompletedTensor (W : Scheme.{t}) :
    ambientD l E W × ambientD l E W ⥤ ambientD l E W := by
  with_unfolding_all exact integralCompletedTensor l E W

/-- The recorded pullback comparison on good representatives.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientPullComparison {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientGoodLocalization l E Y ⋙ ambientPull l E f ≅ ambientPullOnGood l E f := by
  with_unfolding_all exact integralDerivedPullbackComparison l E f

/-- The recorded tensor comparison on good representatives.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientTensorComparison (W : Scheme.{t}) :
    (ambientGoodLocalization l E W).prod (ambientGoodLocalization l E W) ⋙
      ambientCompletedTensor l E W ≅ ambientTensorOnGood l E W := by
  with_unfolding_all exact integralCompletedTensorComparison l E W

/-- Completion in the recorded ambient derived category.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientCompletion (W : Scheme.{t}) : ambientD l E W ⥤ ambientD l E W := by
  with_unfolding_all exact IntegralOnSlice.completion l E W none

/-- The recorded completion comparison.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientCompletionComparison (W : Scheme.{t}) :
    ambientGoodLocalization l E W ⋙ ambientCompletion l E W ≅
      ambientCompletionOnGood l E W := by
  with_unfolding_all exact IntegralOnSlice.completionComparison l E W none

/-- The recorded completion unit.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientCompletionUnit (W : Scheme.{t}) :
    𝟭 (ambientD l E W) ⟶ ambientCompletion l E W :=
  by with_unfolding_all exact IntegralOnSlice.completionUnit l E W none

/-- Ordinary derived tensor in the recorded ambient category.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientOrdinaryTensor (W : Scheme.{t}) :
    ambientD l E W × ambientD l E W ⥤ ambientD l E W :=
  by with_unfolding_all exact (ambientTensorPresentation l E W).tensor

/-- The whole ordinary tensor model comparison, with its category data shared once.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientTensorModelComparison (W : Scheme.{t}) :
    ((ambientFlat l E W).ι.prod (ambientFlat l E W).ι) ⋙
      ambientTotalTensor l E W ⋙ ambientQ l E W ≅
        (((ambientFlat l E W).ι ⋙ ambientQ l E W).prod
          ((ambientFlat l E W).ι ⋙ ambientQ l E W)) ⋙ ambientOrdinaryTensor l E W := by
  unfold ambientTotalTensor ambientQ ambientOrdinaryTensor
  with_unfolding_all exact (ambientTensorPresentation l E W).comparison

attribute [local irreducible] integralOperationsLevelPullback
  Scheme.coefficientProEtaleModulePullback unrestrictedIntegralReductionFunctor
  IntegralOnSlice.reduction IntegralOnSlice.reductionWitness

universe a₂ b₂ c₂ d₂ e₂ f₂

/-- Share a constructed value through its proved specification.
Source: the preceding unique construction
(blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def operationDataCopy {A : Type*} (a : A) : A :=
  (operationDataCopy_existsUnique a).exists.choose

/-- The same recorded operations, shared as one specified record.
Source: the preceding constructed package
(blueprint: lem-pur-integral-ambient-operation-models).

The specifying theorem is proved by reflexivity. It determines the entire record by
literal equality to rawAmbientPackage, rather than selecting unspecified operation data. -/
@[irreducible] def ambientPackage := operationDataCopy (rawAmbientPackage l E)

/-- Localization for the shared ambient operation record.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
@[instance] theorem modelQ_isLocalization (W : Scheme.{t}) :
    (modelQ l E W).IsLocalization (ambientQuasiIso l E W) :=
  (ambientPackage l E).qLocalization W

attribute [local irreducible] tensorRepresentative

@[irreducible] private def descendComparison
    {R S A D : Type*} [Category* R] [Category* S] [Category* A] [Category* D]
    (L : R ⥤ S) (hL : ((Functor.whiskeringLeft _ _ D).obj L).FullyFaithful)
    {F G : S ⥤ D} {H : R ⥤ A} {Q V : A ⥤ D} {T : R ⥤ D}
    (C : D ⥤ D) (e : L ⋙ F ≅ H ⋙ Q) (c : Q ⋙ C ≅ V)
    (b : H ⋙ V ≅ T) (g : L ⋙ G ≅ T) : F ⋙ C ≅ G :=
  hL.isoEquiv.symm
    (((Functor.associator L F C).symm ≪≫ Functor.isoWhiskerRight e C ≪≫
      Functor.associator H Q C ≪≫ Functor.isoWhiskerLeft H c ≪≫ b) ≪≫ g.symm)

@[irreducible] private def descendCompletion
    {R S A D : Type*} [Category* R] [Category* S] [Category* A] [Category* D]
    (L : R ⥤ S) (hL : ((Functor.whiskeringLeft _ _ D).obj L).FullyFaithful)
    {F G : S ⥤ D} {H : R ⥤ A} {Q V : A ⥤ D} {T : R ⥤ D}
    (C : D ⥤ D) (η : 𝟭 D ⟶ C)
    (e : L ⋙ F ≅ H ⋙ Q) (c : Q ⋙ C ≅ V) (b : H ⋙ V ≅ T) (g : L ⋙ G ≅ T)
    (u : ∀ P : A, Q.obj P ⟶ V.obj P)
    (hu : ∀ P : A, η.app (Q.obj P) ≫ c.hom.app P = u P) :
    DescendedCompletion L C η e c b g u :=
  (descendCompletion_existsUnique L hL C η e c b g u hu).exists.choose

@[irreducible] private def sourceWhisker (W : Scheme.{t})
    (D : Type a₁) [Category.{b₁} D] :
    (((Functor.whiskeringLeft _ _ D).obj
      (modelGoodLocalization l E W)).FullyFaithful) := by
  let V := (ambientQuasiIso l E W).inverseImage (ambientGood l E W).ι
  have hL : (modelGoodLocalization l E W).IsLocalization V := by
    exact (ambientPackage l E).goodLocalization W
  exact Localization.fullyFaithfulWhiskeringLeft (modelGoodLocalization l E W) V D

@[irreducible] private def sourceProdWhisker (W : Scheme.{t})
    (D : Type a₁) [Category.{b₁} D] :
    (((Functor.whiskeringLeft _ _ D).obj
      ((modelGoodLocalization l E W).prod (modelGoodLocalization l E W))).FullyFaithful) := by
  let V := (ambientQuasiIso l E W).inverseImage (ambientGood l E W).ι
  have hL : (modelGoodLocalization l E W).IsLocalization V := by
    exact (ambientPackage l E).goodLocalization W
  letI := hL
  haveI : V.ContainsIdentities := by
    refine ⟨fun P ↦ ?_⟩
    with_unfolding_all exact (quasiIso_of_isIso
      (𝟙 (show IntegralOnSlice.Cx l E W none from P.obj)))
  exact Localization.fullyFaithfulWhiskeringLeft
    ((modelGoodLocalization l E W).prod (modelGoodLocalization l E W)) (V.prod V) D

@[irreducible] private def derivedPresentation {X Y : Scheme.{t}} (f : X ⟶ Y) :
    DerivedPresentation l E X Y f :=
  let h := modelDerivedData l E f
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2⟩

@[irreducible] private def liftedTensorComparison
    {C D : Type*} [Category* C] [Category* D]
    (K P : ObjectProperty C) (k : ∀ X : P.FullSubcategory, K X.obj)
    (T : C × C ⥤ C) (Q : C ⥤ D) (S : D × D ⥤ D)
    (c : K.ι.prod K.ι ⋙ T ⋙ Q ≅ (K.ι ⋙ Q).prod (K.ι ⋙ Q) ⋙ S)
    (h : ∀ X : P.FullSubcategory × P.FullSubcategory,
      P ((P.ι.prod P.ι ⋙ T).obj X)) :
    (P.ι ⋙ Q).prod (P.ι ⋙ Q) ⋙ S ≅
      P.lift (P.ι.prod P.ι ⋙ T) h ⋙ (P.ι ⋙ Q) :=
  let M := K.lift P.ι k
  NatIso.ofComponents (fun X ↦ (c.app ((M.prod M).obj X)).symm)
    (fun f ↦ c.inv.naturality ((M.prod M).map f))

@[irreducible] private def globalTensorComparison (W : Scheme.{t}) :
    ((modelGoodLocalization l E W).prod
      (modelGoodLocalization l E W)) ⋙ modelOrdinaryTensor l E W ≅
        modelTensorGoodLift l E W ⋙ modelGoodLocalization l E W := by
  let K := ambientFlat l E W
  unfold modelTensorGoodLift modelGoodLocalization
  exact (liftedTensorComparison K (ambientGood l E W)
    (fun P ↦ ambientGoodFlat l E W P.obj P.property) (modelTotalTensor l E W) (modelQ l E W)
    (modelOrdinaryTensor l E W)
    (modelTensorModelComparison l E W)
    (fun P ↦ modelTensorGood l E W P.1.obj P.2.obj P.1.property P.2.property))

@[irreducible] private def liftedTowerRoosComparison
    {A B C T D : Type*} [Category* A] [Category* B] [Category* C]
    [Category* T] [Category* D]
    (P : ObjectProperty C) (H : A ⥤ B) (F : B ⥤ C)
    (h : ∀ X : A, P ((H ⋙ F).obj X))
    (U : C ⥤ T) (V : B ⥤ T) (R : T ⥤ C) (Q : C ⥤ D) (b : F ⋙ U ≅ V) :
    P.lift (H ⋙ F) h ⋙ (P.ι ⋙ (U ⋙ R) ⋙ Q) ≅ H ⋙ (V ⋙ R) ⋙ Q :=
  NatIso.ofComponents (fun X ↦ Q.mapIso (R.mapIso (b.app (H.obj X)))) (by
    intro X Y f
    dsimp [ObjectProperty.lift]
    simp only [← Functor.map_comp]
    have hb := b.hom.naturality (H.map f)
    simp only [Functor.comp_map] at hb
    exact congrArg (fun k ↦ Q.map (R.map k)) hb)

@[irreducible] private def globalTensorRoosComparison (W : Scheme.{t}) :
    modelTensorGoodLift l E W ⋙ modelCompletionOnGood l E W ≅
        modelTensorOnGood l E W :=
  liftedTowerRoosComparison (ambientGood l E W)
    ((ambientGood l E W).ι.prod (ambientGood l E W).ι)
    (modelTotalTensor l E W)
    (fun P ↦ modelTensorGood l E W P.1.obj P.2.obj P.1.property P.2.property)
    (modelQuotientTower l E W) (modelRecordedTensorTower l E W)
    (modelRoos l E W) (modelQ l E W) (modelTensorTowerIso l E W)

@[irreducible] private def globalPullRoosComparison {X Y : Scheme.{t}} (f : X ⟶ Y) :
    modelPullGoodLift l E f ⋙ modelCompletionOnGood l E X ≅
          modelPullOnGood l E f :=
  liftedTowerRoosComparison (ambientGood l E X) (ambientGood l E Y).ι
    (modelPullComplex l E f) (fun P ↦ modelPullGood l E f P.obj P.property)
    (modelQuotientTower l E X) (modelRecordedPullTower l E f)
    (modelRoos l E X) (modelQ l E X) (modelPullTowerIso l E f)

set_option maxHeartbeats 200000

end WeilConjectures.IntegralAmbient
