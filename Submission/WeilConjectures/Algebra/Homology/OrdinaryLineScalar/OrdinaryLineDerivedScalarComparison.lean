/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarData
public import Submission.WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarPresentations
public import Submission.WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarLineData
import all Submission.WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarLineData
public import Submission.WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
public import Submission.WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import Submission.WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Submission.WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Submission.WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import Submission.WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Submission.WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
public import Submission.WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Submission.WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarBalancedComparison
import Submission.WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarFlatDescent
import Submission.WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarEvaluation
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
import all Submission.WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Ordinary signed-line tensor and derived scalar extension

Source: Stacks Project, Tags 07A4, 0G7E and 0D6D; blueprint main-20261015,
Tate-twist local freeness, proof (3).
(blueprint: lem-pur-ordinary-line-derived-scalar-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe t a w u v b r ua va
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
-- Prefer the native additive structures over routes through abelian instances.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
namespace SheafOfModules.OrdinaryLineScalar

variable (X : Scheme.{t}) [EssentiallySmall.{max a (t + 1)} X.ProEt]

variable {X}
  [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
    HasDerivedCategory.{w} (Modules.{t, a} X R)]
local notation "𝒬[" R "]" => (DerivedCategory.Q (C := Modules X R))
attribute [local instance] modulesCategory modulesAbelian monoidalCategory
attribute [local implicit_reducible] monoidalCategory
attribute [local irreducible] LineUnbounded.derived LineUnbounded.normalization
  KFlatFixedTensor.representativeIso compute signedLinePower scalarTensorPower
  LineUnbounded.cancellation
  LineUnbounded.pureTensor ScalarHomOrdinary.pure

set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] monoidalCategory scalar

section ScalarTowerProof

private def computation
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    {α : R ⟶ S} (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α) :
    𝒬[R] ⋙ p.derived ⟶ p.ordinary.mapHomologicalComplex (.up ℤ) ⋙ 𝒬[S] :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso (Modules.{t, a} X R)).inv
      p.derived ≫
    Functor.whiskerLeft (HomotopyCategory.quotient (Modules.{t, a} X R) (.up ℤ)) p.counit ≫
    Functor.whiskerLeft (p.ordinary.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso (Modules.{t, a} X S)).hom

attribute [local irreducible] computation

section OrdinaryCore

omit [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
  HasDerivedCategory.{w} (Modules.{t, a} X R)]

end OrdinaryCore

end ScalarTowerProof

set_option backward.isDefEq.respectTransparency.types true

set_option backward.isDefEq.respectTransparency.types false

end SheafOfModules.OrdinaryLineScalar
