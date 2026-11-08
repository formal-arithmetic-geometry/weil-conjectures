/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.SixFunctors.Open.OpenQuotientKoszulModels
import all Submission.WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Equivalence
import Submission.WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import Submission.WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
import Submission.WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Submission.WeilConjectures.CategoryTheory.RingedToposRingData
import Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import Submission.WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import Submission.WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import Submission.WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import Submission.WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The augmented quotient tower under the canonical DVR coefficient comparison

Source: Stacks Tags 0941, 099B and 0A0E; canonical coefficient transport.
(blueprint: lem-sf-open-dvr-limit-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Canonical projection-normalized ordinary and derived limit transport.
Source: Stacks Tags 05RR and 0941
(blueprint: lem-sf-open-dvr-limit-comparison). -/
structure OpenDvrLimitComparison
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)} {T : Scheme.{u}}
    (C : OpenDvrCoefficientModel l E d T) where
  /-- The total-limit comparison is the canonical one under the coefficient equivalence. -/
  rlim : C.towers ⋙ reconstructionRlim T d ≅
    coefficientConstantTowerLimit.{u, u} l E T ⋙ C.derived.functor
  /-- The total-limit comparison extends the ordinary projection-normalized comparison. -/
  limit_model : ∀ I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ℤ,
    ∃ σ : ((reconstructionLimit T d).mapHomologicalComplex (.up ℤ)).obj
          (C.towerComplexes.obj I) ≅
        C.complexes.obj
          (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
            (.up ℤ)).obj I),
      (∀ (i : ℤ) (n : ℕ),
        σ.hom.f i ≫ C.modules.functor.map (limit.π (I.X i) (op n)) =
          limit.π ((C.towerComplexes.obj I).X i) (op n)) ∧
      C.derived.functor.map
          (derivedLimitComplexComparison
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _)
            (coefficientConstantTowerLimit.{u, u} l E T)
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit I) =
        C.modules.functor.mapDerivedCategoryFactors.hom.app
            (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
            (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map σ.inv ≫
          reconstructionRlimComparison T d (C.towerComplexes.obj I) ≫
          (reconstructionRlim T d).map
            (C.ordinaryTowers.mapDerivedCategoryFactors.inv.app I) ≫
          rlim.hom.app (DerivedCategory.Q.obj I)

end WeilConjectures
