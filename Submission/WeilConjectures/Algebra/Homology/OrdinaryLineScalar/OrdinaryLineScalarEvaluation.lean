/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarData
import all Submission.WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarFlatDescent
import all Submission.WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all Submission.WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import all Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all Submission.WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all Submission.WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all Submission.WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all Submission.WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
import all Submission.WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import all Submission.WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Evaluation compatibility of the scalar and line comparison

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 0G7E and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t a w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
namespace SheafOfModules.OrdinaryLineScalar
attribute [local instance] modulesCategory modulesAbelian monoidalCategory
attribute [local implicit_reducible] monoidalCategory LineUnbounded.tensor
variable {X : Scheme.{t}} [EssentiallySmall.{max a (t + 1)} X.ProEt]
  [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
    HasDerivedCategory.{w} (Modules.{t, a} X R)]
local notation "𝒬[" R "]" => (DerivedCategory.Q (C := Modules X R))
variable {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}

attribute [local irreducible] LineUnbounded.cancellation LineUnbounded.pureTensor
  LineEvaluation.cancellation LineEvaluation.pureTensor

private local instance
    (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)})
    (M : Modules.{t, a} X A) (U : X.ProEtᵒᵖ) :
    SMul ((𝟙_ (Modules.{t, a} X A)).val.obj U) (M.val.obj U) :=
  inferInstanceAs (SMul (A.obj.obj U) (M.val.obj U))

attribute [local irreducible] LineUnbounded.derived LineUnbounded.normalization
  compute signedLinePower scalarTensorPower

end SheafOfModules.OrdinaryLineScalar
