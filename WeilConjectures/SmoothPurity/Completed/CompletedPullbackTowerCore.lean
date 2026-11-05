/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SmoothPurity.Pur.PurSequenceOrdinaryFactorization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSequenceDirectEvaluation
import all WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackTowerComparison
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitOrdinaryAdjunction
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFixedCalculusModels
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitDerivedAdjunctionComparison

/-! # Coherent reduction and strict pullback tower core

Source: `literature/stacks-project/sites-cohomology.tex`, Lemma 21.18.4
(Tag 07A4, label `lemma-pullback-tensor-product`), together with the integral,
rational, and algebraically closed coefficient conventions
(blueprint: def-pur-completed-pullback-tower-core).

## Main definitions

* `pullbackTensorOrdinaryReduction` and its adjunction fix coherent reduction.
* `pullbackTensorRoosModel` fixes the total-limit/Roos normalization.
* `pullbackTensorPullbackTower` fixes the strict finite-pullback tower comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

section RoosSign
open CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a b w g
variable {B : Type a} [Category.{b} B] [Abelian B] [HasCountableProducts B]

variable [HasLimitsOfShape ℕᵒᵖ B]

variable [HasExactLimitsOfShape (Discrete ℕ) B] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)] [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]

end RoosSign

section CoherentSystems

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Base change preserves the vertical covering condition.
Source: Stacks 0941, 098K (blueprint: def-pur-completed-pullback-tower-core).
Proof: a vertical slice of a pulled-back sieve is the base change of its
vertical slice; pro-etale covers are stable under scheme base change. -/
@[instance] theorem pullbackTensorSequenceBase_continuous {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (pullbackTensorSequenceBase f).IsContinuous
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X)) := by
  exact integralComparisonSequenceBaseChange_continuous f

/-- Module Kan extension followed by sheafification is left adjoint to this direct image.
Source: Stacks 03D2 and 0941 (blueprint: def-pur-completed-pullback-tower-core).
Proof: pass to a small model in coefficient universe u + 1. The free module
presheaf presentation constructs inverse image with extension of scalars;
module sheafification gives its adjunction. Transport back to the stated
sequence sites. The right adjoint and its coefficient map are the displayed ones. -/
@[instance] theorem pullbackTensorSequenceDirect_rightAdjoint {X Y : Scheme.{u}}
    (f : X ⟶ Y) : (pullbackTensorSequenceDirect l E f).IsRightAdjoint := by
  change (integralComparisonSequenceDirectImage l E f).IsRightAdjoint
  exact integralComparisonSequenceDirectImage_isRightAdjoint l E f

/-- Ordinary coherent reduction is left adjoint to the specified ordinary limit.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tower-core).
Proof: send a completed module P to the system of its actual quotients
B_n tensor P. The quotient units form a map P to the limit after scalar
restriction. A system map from these quotients is equivalent, by the ordinary
scalar-extension adjunctions and their compatibility, to a map P to that limit.
This is the required natural Hom bijection. -/
@[instance] theorem pullbackTensorOrdinaryLimit_rightAdjoint (W : Scheme.{u}) :
    (pullbackTensorOrdinaryLimit l E W).IsRightAdjoint := by
  have : IsGrothendieckAbelian.{u + 1} (coefficientSequenceModules l E W) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0} _ _
  have hev (n : ℕ) : PreservesLimitsOfSize.{u + 1, u + 1}
      (coefficientSequenceEvaluation l E W n) := by
    unfold coefficientSequenceEvaluation
    have := SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, u + 1}
      (eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm)
    infer_instance
  have hres (n : ℕ) : (scalarReductionRestriction l E W n).IsRightAdjoint :=
    (scalarReductionExtension_adjunction l E W n).choose.isRightAdjoint
  have : PreservesLimitsOfSize.{u + 1, u + 1}
      (coefficientSequenceRestriction l E W) := by
    apply preservesLimits_of_evaluation
    intro n
    rw [coefficientSequenceRestriction_evaluation]
    have := hev n.unop
    have := hres n.unop
    infer_instance
  have : PreservesLimitsOfSize.{u + 1, u + 1}
      (pullbackTensorOrdinaryLimit l E W) := by
    unfold pullbackTensorOrdinaryLimit
    infer_instance
  exact isRightAdjoint_of_preservesLimits_of_isCoseparating
    (isCoseparator_coseparator (coefficientSequenceModules l E W)) _

attribute [reducible] pullbackTensorUniqueChoice

section TowerComparisonProof
attribute [local irreducible] pullbackTensorReductionEvaluationComplex
  pullbackTensorInverseEvaluationComplex pullbackTensorPullbackTowerLevel
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf

attribute [local implicit_reducible] pullbackTensorOrdinaryModel pullbackTensorOrdinaryLimit
  pullbackTensorConstantLimit
  coefficientConstantTowerLimit coefficientSequenceLimit pullbackTensorOrdinaryReduction
  pullbackTensorOrdinaryAdjunction integralOperationsGoodLocalization
  CategoryTheory.Functor.mapHomologicalComplex HomologicalComplex.asFunctor
  HomologicalComplex.complexOfFunctorsToFunctorToComplex

attribute [local irreducible] pullbackTensorCalculus

attribute [local irreducible] pullbackTensorOrdinaryReduction pullbackTensorOrdinaryAdjunction
  pullbackTensorReductionEvaluation pullbackTensorSequenceDirectEvaluation
  pullbackTensorSequenceInverseEvaluation

attribute [local implicit_reducible] pullbackTensorSequenceBase pullbackTensorSequenceDirect
  pullbackTensorSequenceInverse
  pullbackTensorSequenceAdjunction coefficientSequenceEvaluation integralOperationsLevelPullback
  integralComparisonSequencePullback integralComparisonSequenceDirectImage
  integralComparisonSequenceBaseChange
  unrestrictedIntegralReductionFunctor pullbackTensorRestrictedTower
  integralOperationsPullbackTowerFunctor
  integralOperationsPullbackLevel integralOperationsRestrict
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence

attribute [local irreducible] OrdinaryTowerProof.moduleLevel OrdinaryTowerProof.inverseEvaluation

attribute [local irreducible] OrdinaryTowerProof.comparison

end TowerComparisonProof

attribute [local irreducible] pullbackTensorCalculus pullbackTensorOrdinaryModel

end CoherentSystems

-- Consumers normalize this map by its section equation before comparing adjoints;
-- `pullbackTensorSequenceRing` itself stays semireducible, so their local hints remain valid.
attribute [irreducible] pullbackTensorSequenceRingMap

end WeilConjectures
