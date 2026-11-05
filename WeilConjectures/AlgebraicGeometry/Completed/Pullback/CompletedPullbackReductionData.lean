/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

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

import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.StrictReduction.ReductionPullbackDerivedTower
/-! # Finite reduction of completed pullback

Source: Stacks Project, Tag 099N (5), and blueprint order 1262
(blueprint: lemma-weil-pbc-completed-pullback-reduction).

## Main definitions

- `completedPullbackReductionArrow`: adjunct of the actual limit projection.
- `completedReductionTargetNormalization`: canonical scalar normalization of finite pullback.

## Main statements

- `completedPullback_reduction`: completeness, finite reduction and every coherence clause.

All coefficients remain sheaves on the original small pro-etale sites. Positive
level n is encoded by n-1, so a natural number n denotes the quotient by I^(n+1).
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 128
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] CategoryTheory.Functor.mapHomotopyCategory
attribute [local irreducible] CategoryTheory.Functor.mapHomotopyCategoryFactors
open AlgebraicGeometry.ProEtale
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

attribute [local irreducible] proEtaleModelRingUnit
attribute [-instance] coefficientProEtaleModelBaseChange_isContinuous
  coefficientProEtaleModuleDirectImage_isRightAdjoint

attribute [local irreducible] completedAdicChangeData

set_option synthInstance.maxSize 2048
attribute [local instance] completedTowerModulePullback_additive
attribute [local instance] completedReductionModuleTowerFunctor_additive

attribute [irreducible] completedReductionInverseImageGenerator

attribute [irreducible] completedReductionFiniteTensor

attribute [irreducible] completedReductionFiniteGenerator

attribute [irreducible] completedReductionSectionEquation

attribute [irreducible] HasCompletedReductionOrdinaryComparisonNormalization

section OrdinaryComparison
variable (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)

variable (R' : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S' : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (aR : R ⟶ R') (aS : S ⟶ S')
  (c' : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R' ≅ S')
  (hc : c.hom ≫ aS =
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map aR ≫ c'.hom)

attribute [irreducible] ordinaryIsoCandidate
attribute [local irreducible] exactPullbackIso

attribute [local irreducible] ringTensor

end OrdinaryComparison

attribute [local irreducible] completedReductionCompositeCounitNat

attribute [irreducible] HasCompletedReductionFiniteEvaluationNormalization
attribute [local irreducible] Functor.leftDerivedCounitOnComplex

section DerivedComparisons
attribute [local irreducible] completedReductionComplexCounitNat
  completedReductionTowerComplexNat completedReductionPullbackComplexNat
attribute [local irreducible] cochainRepresentativeWhiskering
attribute [local irreducible] completedReductionModuleTowerFunctor completedReductionTower
attribute [local irreducible] completedTowerModulePullback
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
attribute [local irreducible] Functor.mapDerivedCategoryFactorsh
attribute [local irreducible] completedTowerPullbackCounit

end DerivedComparisons

attribute [irreducible] HasCompletedReductionOrdinaryTransitionNormalization

section OrdinaryTransition
variable (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)

end OrdinaryTransition

attribute [irreducible] HasCompletedReductionTargetTransitionNormalization

attribute [instance] coefficientProEtaleModelBaseChange_isContinuous
  coefficientProEtaleModuleDirectImage_isRightAdjoint

end AlgebraicGeometry.Scheme
