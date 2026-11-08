/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
public import Submission.WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalMaps
import Submission.WeilConjectures.AlgebraicGeometry.FiniteP1DiagonalPicard
import Submission.WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitComp
public import Submission.WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
import Submission.WeilConjectures.AlgebraicGeometry.OrdinarySupportedChernNormalization
import Submission.WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalAlphaUnits
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import Submission.WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Submission.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Submission.WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import Submission.WeilConjectures.AlgebraicGeometry.RawModuleScalarComparison.RawModuleScalarDerivedPullbackIso
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison
public import Submission.WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Kummer
public import Submission.WeilConjectures.CategoryTheory.DerivedSingleUnit
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Submission.WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import Submission.WeilConjectures.AlgebraicGeometry.Sites.EtalePicard
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Submission.WeilConjectures.SixFunctors.BaseChange.Square
public import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Submission.WeilConjectures.AlgebraicGeometry.TensorPullback
public import Submission.WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerBoundary
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerScalar
public import Submission.WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Submission.WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Submission.WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Shift
import Mathlib.CategoryTheory.Adjunction.Mates
import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
import Submission.WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import Submission.WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
public import Submission.WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGenerators
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
import Mathlib.Logic.Small.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisons
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
public import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
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
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Submission.WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import Submission.WeilConjectures.Mathlib.CategoryTheory.EssentialImage
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Whiskering
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Derived
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.KFlat
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Vanishing
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.KFlat
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import Submission.WeilConjectures.ConstructibleSheaf.Defs
public import Submission.WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import Submission.WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import Submission.WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import Submission.WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Submission.WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Submission.WeilConjectures.ConstructibleSheaf.Pullback
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Submission.WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import Submission.WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleConstruction
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleLinearCriterion
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Submission.WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import Submission.WeilConjectures.SixFunctors.Finite.Exact
public import Submission.WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystem
public import Submission.WeilConjectures.AlgebraicGeometry.OrdinaryFiniteChernPullback

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The Chern-component formula for the supported diagonal boundary

Canonical constructions: (auxiliary; not a blueprint node).

Source: blueprint lem-amb-p1-diagonal-integrals, standard-chart Cartier calculation;
lem-sp-tower-p1-arbitrary-base-integrals, steps 2 and 6.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

-- Use the same braiding projection as the generic symmetric coefficient API.
attribute [local instance 100000] SymmetricCategory.toBraidedCategory
attribute [local irreducible] genericConstantIso

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000] ordinaryFiniteClass._proof_1 ordinaryFiniteClass._proof_2
  ordinaryFiniteClass._proof_3

attribute [local irreducible] Scheme.finiteEtaleTateLine Scheme.kummerδ₁
  AlgebraicGeometry.ProjectiveSpace
  HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor
  ordinaryFiniteIntegralGenerator ordinaryFiniteRootMap Sheaf.H.map
  Scheme.Pic.toCohomologicalPicardGroup Scheme.Pic.map ordinaryFiniteClassCore
  ordinaryFiniteP1Unit ordinaryFiniteP1ChernPushforward

/-- The ordinary supported Ext group, with its category structures recorded once.
Source: the supported Cartier Kummer class in Stacks 03PL and 0A45.
(auxiliary; not a blueprint node). -/
@[implicit_reducible]
def ordinaryFiniteSupportedExt (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  Ext.{u + 1} ((lowerStar (ModuleCat.{u + 1} A) i).obj
    (ordinaryFiniteConstant A D)) F 2

/-- The existing supported realization, on the named ordinary degree-zero objects.
Source: supportedExactDerivedMap for the exact direct image of a closed immersion.
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteSupportedRealization (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (κ : ordinaryFiniteSupportedExt A i F) :
    (ordinaryFinitePushforward A i).obj (ordinaryFiniteUnit A D) ⟶
      (ordinaryFiniteDegreeZero A T F)⟦(2 : ℤ)⟧ :=
  supportedExactDerivedMap (lowerStar (ModuleCat.{u + 1} A) i)
    (ordinaryFiniteConstant A D) F κ

/-- The supported arrow after forgetting support, on the named ordinary objects.
Source: the supported exact realization and canonical constant unit, Stacks 0A45.
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteSupportedArrow (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (κ : ordinaryFiniteSupportedExt A i F) :
    ordinaryFiniteUnit A T ⟶ (ordinaryFiniteDegreeZero A T F)⟦(2 : ℤ)⟧ :=
  supportedDerivedUnit A i ≫ ordinaryFiniteSupportedRealization A i F κ

attribute [local semireducible] ordinaryFiniteSupportedArrow

/-- Factoring the two mapped supported arrows preserves their original composite.
Source: functoriality of direct image and associativity of composition.
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteSupportedArrow_pushforward (A : Type (u + 1)) [CommRing A]
    {D T U : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] (p : T ⟶ U)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (κ : ordinaryFiniteSupportedExt A i F) :
    (supportedDerivedUnit A p ≫
        (ordinaryFinitePushforward A p).map (supportedDerivedUnit A i)) ≫
          (ordinaryFinitePushforward A p).map (ordinaryFiniteSupportedRealization A i F κ) =
      supportedDerivedUnit A p ≫
        (ordinaryFinitePushforward A p).map (ordinaryFiniteSupportedArrow A i F κ) := by
  exact (Category.assoc (supportedDerivedUnit A p)
    ((ordinaryFinitePushforward A p).map (supportedDerivedUnit A i))
    ((ordinaryFinitePushforward A p).map
      (ordinaryFiniteSupportedRealization A i F κ))).trans
    (congrArg (fun f ↦ supportedDerivedUnit A p ≫ f)
      ((ordinaryFinitePushforward A p).map_comp (supportedDerivedUnit A i)
        (ordinaryFiniteSupportedRealization A i F κ)).symm)

/-- The shifted-twist direct image for one of the product projections.
Source: blueprint finite diagonal check, canonical projection direct image.
(auxiliary; not a blueprint node). -/
@[implicit_reducible]
def ordinaryFiniteP1DiagonalTarget (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) (a : Bool) :
    DerivedCategoryModule A (ProjectiveLine S) :=
  (ordinaryFinitePushforward A
    (X := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) (Y := ProjectiveLine S)
    (projectiveLineDiagonalProjection S a)).obj
      ((ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)

/-- Apply the projected supported class to the canonical constant-object unit.
This is the canonical composite before the trace in the finite diagonal integral.
Source: blueprint finite diagonal check, supported class and composition unit.
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteP1DiagonalSupportedMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) (a : Bool)
    (κ : ordinaryFiniteSupportedExt A (pullback.diagonal (ProjectiveLine S ↘ S))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA)) :
    ordinaryFiniteUnit A (ProjectiveLine S) ⟶ ordinaryFiniteP1DiagonalTarget A N hA S a :=
  projectiveLineDiagonalAlpha A S a ≫
    (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
      (ordinaryFiniteSupportedRealization A (pullback.diagonal (ProjectiveLine S ↘ S))
        (Scheme.finiteEtaleTateLine
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) κ)

/-- The canonical adjunction transport around a commuting composition diagram.
Source: adjunction-unit pasting in the projective-line diagonal calculation.
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteChartTransport (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (e : X ⟶ Y) (p : Y ⟶ Z) (r : X ⟶ Z)
    (hr : e ≫ p = r) (L : DerivedCategoryModule A Y) (L' : DerivedCategoryModule A X)
    (v : (ordinaryFinitePullback A e).obj L ⟶ L') :
    (ordinaryFinitePushforward A p).obj L ⟶ (ordinaryFinitePushforward A r).obj L' :=
  (ordinaryFinitePushforward A p).map ((ordinaryFiniteAdjunction A e).unit.app L) ≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e p).hom.app
      ((ordinaryFinitePullback A e).obj L) ≫
    (rightDerivedLowerStarCongr (ModuleCat.{u + 1} A) hr).hom.app
      ((ordinaryFinitePullback A e).obj L) ≫
    (ordinaryFinitePushforward A r).map v

/-- Direct-image transport from either product projection to the standard P1 projection.
This is the comparison preceding the trace in arbitraryBaseFiniteP1DiagonalTrace.
Source: blueprint lem-amb-p1-diagonal-integrals, identification of each projection.
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteP1DiagonalChartMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    ordinaryFiniteP1DiagonalTarget A N hA S a ⟶
      (ordinaryFinitePushforward A
        (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧) :=
  let e := (projectiveLineDiagonalChart S a).val
  let p := projectiveLineDiagonalProjection S a
  let L := (ordinaryFiniteLine A N hA
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧
  ordinaryFiniteChartTransport A e.hom p
    (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)
    (projectiveLineDiagonalChart S a).property L _
      (ordinaryFiniteShiftedLinePullback A N hA t e.hom
        ((map_natCast
          ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom N) ▸
          hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom)).hom

private theorem base_adjunct_core {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X L : C} {Y M : D} (e : F.obj X ≅ Y) (β : X ⟶ L)
    (v : F.obj L ⟶ M) :
    (adj.unit.app X ≫ G.map e.hom) ≫ G.map (e.inv ≫ F.map β ≫ v) =
      β ≫ adj.unit.app L ≫ G.map v := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← G.map_comp_assoc, Iso.hom_inv_id, G.map_id, Category.id_comp]
  simpa only [Category.assoc] using
    congrArg (fun f => f ≫ G.map v) (adj.unit_naturality β)

private theorem unit_chern_core {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X : C} {Y L : D} (e : F.obj X ⟶ Y) (d : Y ⟶ L) :
    (adj.unit.app X ≫ G.map e) ≫ G.map d = adj.homEquiv X L (e ≫ d) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

private theorem chart_adjunct_core {B C D : Type*} [Category B] [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (R : C ⥤ B) (R' : D ⥤ B) (rc : G ⋙ R ≅ R')
    {X : B} {Y L : C} {Z M : D} (e : F.obj Y ≅ Z)
    (α : X ⟶ R.obj Y) (α' : X ⟶ R'.obj Z)
    (hcomp : α ≫ R.map (adj.unit.app Y ≫ G.map e.hom) ≫ rc.hom.app Z = α')
    (d : Y ⟶ L) (v : F.obj L ⟶ M) :
    α ≫ R.map d ≫ R.map (adj.unit.app L) ≫ rc.hom.app (F.obj L) ≫ R'.map v =
      α' ≫ R'.map (e.inv ≫ F.map d ≫ v) := by
  rw [← hcomp]
  symm
  simp only [Functor.map_comp, Category.assoc]
  rw [← rc.hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← R.map_comp_assoc (G.map e.hom) (G.map e.inv), ← G.map_comp,
    Iso.hom_inv_id, G.map_id, R.map_id, Category.id_comp]
  rw [← rc.hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← R.map_comp_assoc, adj.unit_naturality, R.map_comp]
  simp only [Category.assoc]

private theorem map_sum_components {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    {T : D} {U V : C} (α : T ⟶ F.obj U) (δ b c : U ⟶ V)
    (b' c' : T ⟶ F.obj V) (hsum : δ = b + c)
    (hb : α ≫ F.map b = b') (hc : α ≫ F.map c = c') :
    α ≫ F.map δ = b' + c' := by
  rw [hsum, Functor.map_add, Preadditive.comp_add, hb, hc]

private theorem coefficient_chart_adjunct (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (e : X ⟶ Y) (p : Y ⟶ Z) (r : X ⟶ Z)
    (hr : e ≫ p = r) (L : DerivedCategoryModule A Y) (L' : DerivedCategoryModule A X)
    (d : ordinaryFiniteUnit A Y ⟶ L)
    (v : (ordinaryFinitePullback A e).obj L ⟶ L') :
    supportedDerivedUnit A p ≫ (ordinaryFinitePushforward A p).map d ≫
        ordinaryFiniteChartTransport A e p r hr L L' v =
      supportedDerivedUnit A r ≫ (ordinaryFinitePushforward A r).map
        (ordinaryFiniteArrowPullback A e L L' d v) := by
  unfold ordinaryFiniteChartTransport ordinaryFiniteArrowPullback
  subst r
  rw [rightDerivedLowerStarCongr_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  exact chart_adjunct_core (ordinaryFiniteAdjunction A e)
    (ordinaryFinitePushforward A p) (ordinaryFinitePushforward A (e ≫ p))
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e p)
    (ordinaryFiniteUnitPullback A e) _ _
    (by
      have hc := supportedDerivedUnit_comp A e p
      rw [supportedDerivedUnit_eq A e] at hc
      exact hc) d v

attribute [local semireducible] ordinaryFiniteSupportedRealization
  supportedKummerChern ordinaryFiniteP1KummerClass
  ordinaryFiniteLinePullbackMap ordinaryFiniteP1DiagonalChartMap
  ordinaryFiniteP1Unit ordinaryFiniteP1ChernPushforward ordinaryFiniteP1DiagonalSupportedMap

/-- The diagonal component formula with the base hyperplane Chern arrow specified.
Source: blueprint lem-amb-p1-diagonal-integrals, Chern additivity and adjunct steps.
(blueprint: lem-amb-p1-diagonal-chern-fixed-base)

Proof: the supported Chern equation identifies the unsupported diagonal class with
its divisor line. The chart Picard identity factors this line into the relative
hyperplane and the pullback of the base hyperplane. Chern additivity and pullback
naturality give their sum. The chart adjunction pasting transports the supported
map to its adjunct; unit naturality sends the base summand to its Chern arrow
followed by the twisted unit, while the relative summand is the Chern pushforward.
-/
theorem ordinaryFiniteP1_diagonal_kummer_component_formula_fixed (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (hPP : IsUnit (N : Γ(ProjectiveLine (ProjectiveLine S), ⊤)))
    (hW : IsUnit (N : Γ(pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S), ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine (ProjectiveLine S)) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec A N hA (ProjectiveLine S) hPP c)
    (hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible)
    (κ : ordinaryFiniteSupportedExt A (pullback.diagonal (ProjectiveLine S ↘ S))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA))
    (hκ : SupportedKummerBoundary A N hA (pullback.diagonal (ProjectiveLine S ↘ S))
      hI hW κ) :
    ∀ a : Bool,
            ordinaryFiniteP1DiagonalSupportedMap A N hA S a κ ≫
              ordinaryFiniteP1DiagonalChartMap A N hA t S hS a =
            ordinaryFiniteFirstChern A N hA (ProjectiveLine S) hP
                (Scheme.Pic.ofIsInvertible
                  (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1)) ≫
              ordinaryFiniteP1Unit A N hA t (ProjectiveLine S) hP +
              ordinaryFiniteP1ChernPushforward A N hA (ProjectiveLine S) c := by
  classical
  let P := ProjectiveLine S
  let β : ordinaryFiniteUnit A P ⟶ (ordinaryFiniteLine A N hA P)⟦(2 : ℤ)⟧ :=
    ordinaryFiniteFirstChern A N hA P hP
      (Scheme.Pic.ofIsInvertible (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1))
  intro a
  let Q := ProjectiveLine P
  let W := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)
  let i : P ⟶ W := pullback.diagonal (ProjectiveLine S ↘ S)
  let r : Q ⟶ P := ProjectiveLine P ↘ P
  let d : ordinaryFiniteUnit A W ⟶
      (ordinaryFiniteLine A N hA W)⟦(2 : ℤ)⟧ :=
    ordinaryFiniteSupportedArrow A i (Scheme.finiteEtaleTateLine W N A hA) κ
  let e : Q ⟶ W := (projectiveLineDiagonalChart S a).val.hom
  let δ : ordinaryFiniteUnit A Q ⟶
      (ordinaryFiniteLine A N hA Q)⟦(2 : ℤ)⟧ :=
    ordinaryFiniteLinePullbackMap A N hA t e hW d
  let b : ordinaryFiniteUnit A Q ⟶
      (ordinaryFiniteLine A N hA Q)⟦(2 : ℤ)⟧ :=
    ordinaryFiniteLinePullbackMap A N hA t r hP β
  let := hI.isInvertible_dual_toModules
  have hdeq : d = ordinaryFiniteFirstChern A N hA W hW
      (Scheme.Pic.ofIsInvertible (Scheme.Modules.dual i.ker.toModules)) := by
    exact ordinaryFiniteFirstChern_unique A N hA W hW
      (Scheme.Pic.ofIsInvertible (Scheme.Modules.dual i.ker.toModules)) _
      (ordinary_supported_kummer_chern W N hN A hA hW i hI κ hκ)
  have hδ : δ = ordinaryFiniteFirstChern A N hA Q hPP
      (Scheme.Pic.map e (Scheme.Pic.ofIsInvertible
        (Scheme.Modules.dual i.ker.toModules))) := by
    exact (congrArg
      (ordinaryFiniteLinePullbackMap A N hA t e hW) hdeq).trans
      (ordinaryFiniteFirstChern_pullback A N hA t e hW hPP _)
  have hb : b = ordinaryFiniteFirstChern A N hA Q hPP
      (Scheme.Pic.map r (Scheme.Pic.ofIsInvertible
        (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1))) := by
    exact ordinaryFiniteFirstChern_pullback A N hA t r hP hPP _
  have hceq : c = ordinaryFiniteFirstChern A N hA Q hPP
      (Scheme.Pic.ofIsInvertible (ProjectiveSpace.twist (ULift.{u} (Fin 2)) P 1)) := by
    exact ordinaryFiniteFirstChern_unique A N hA Q hPP _ c hc
  have hsum : δ = b + c := by
    have hp := congrArg (ordinaryFiniteFirstChern A N hA Q hPP)
      (finiteP1_diagonal_picard S hI a)
    have hm := ordinaryFiniteFirstChern_mul A N hA Q hPP
      (Scheme.Pic.ofIsInvertible (ProjectiveSpace.twist (ULift.{u} (Fin 2)) P 1))
      (Scheme.Pic.map r (Scheme.Pic.ofIsInvertible
        (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1)))
    exact hδ.trans (hp.trans (hm.trans ((add_comm _ _).trans
      (congrArg₂ (fun x y : ordinaryFiniteUnit A Q ⟶
        (ordinaryFiniteLine A N hA Q)⟦(2 : ℤ)⟧ ↦ x + y) hb.symm hceq.symm))))
  have hfactor : ordinaryFiniteP1DiagonalSupportedMap A N hA S a κ ≫
      ordinaryFiniteP1DiagonalChartMap A N hA t S hS a =
      supportedDerivedUnit A (projectiveLineDiagonalProjection S a) ≫
        (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map d ≫
          ordinaryFiniteP1DiagonalChartMap A N hA t S hS a := by
    rw [ordinaryFiniteP1DiagonalSupportedMap, projectiveLineDiagonalAlpha_units]
    exact (congrArg (fun f ↦ f ≫ ordinaryFiniteP1DiagonalChartMap A N hA t S hS a)
      (ordinaryFiniteSupportedArrow_pushforward A
        (pullback.diagonal (ProjectiveLine S ↘ S))
        (projectiveLineDiagonalProjection S a) (Scheme.finiteEtaleTateLine W N A hA) κ)).trans
      (Category.assoc (supportedDerivedUnit A (projectiveLineDiagonalProjection S a))
        ((ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map d)
        (ordinaryFiniteP1DiagonalChartMap A N hA t S hS a))
  have hchart : supportedDerivedUnit A (projectiveLineDiagonalProjection S a) ≫
        (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map d ≫
          ordinaryFiniteP1DiagonalChartMap A N hA t S hS a =
      supportedDerivedUnit A r ≫ (ordinaryFinitePushforward A r).map δ := by
    dsimp only [ordinaryFiniteP1DiagonalChartMap, δ, ordinaryFiniteLinePullbackMap]
    exact coefficient_chart_adjunct A e
      (projectiveLineDiagonalProjection S a) r
      (projectiveLineDiagonalChart S a).property _ _ d
      (ordinaryFiniteShiftedLinePullback A N hA t e hW).hom
  exact hfactor.trans (hchart.trans
    (map_sum_components (ordinaryFinitePushforward A r) (supportedDerivedUnit A r)
      δ b c (β ≫ ordinaryFiniteP1Unit A N hA t P hP)
      (ordinaryFiniteP1ChernPushforward A N hA P c) hsum
      (by
        rw [supportedDerivedUnit_eq A r]
        dsimp only [b, ordinaryFiniteLinePullbackMap]
        rw [ordinaryFiniteP1Unit_eq]
        unfold ordinaryFiniteArrowPullback
        exact base_adjunct_core (ordinaryFiniteAdjunction A r)
          (ordinaryFiniteUnitPullback A r) β
          (ordinaryFiniteShiftedLinePullback A N hA t r hP).hom)
      (by
        rw [supportedDerivedUnit_eq A r]
        rw [ordinaryFiniteP1ChernPushforward_eq]
        exact unit_chern_core (ordinaryFiniteAdjunction A r)
          (ordinaryFiniteUnitPullback A r).hom c)))

/-- The supported diagonal boundary has the base and relative hyperplane components.
Source: blueprint lem-amb-p1-diagonal-integrals, standard-chart proof;
lem-sp-tower-p1-arbitrary-base-integrals, steps 2 and 6.
(blueprint: lem-sp-finite-p1-diagonal-kummer-component-formula)

Proof: the diagonal's regular equations on the four product charts are y-x, x-y,
1-xy and xy-1. On the chart indexed by i,j the ideal generator is
(x0*y1-x1*y0)/(xi*yj). Its changes of basis identify the ideal dual with
p1*O(1) tensor p2*O(1), with the diagonal polynomial as its canonical section.
The given supported boundary, composed with the constant unit, is the Chern class
of this dual ideal, by ordinary_supported_kummer and uniqueness of its boundary.
Additivity of the Kummer connecting map on the Picard group gives the sum of the
two pulled-back hyperplane classes. Under the chart for projection a, one is the
relative O(1) class and the other is pulled back from the base P. Module-derived
Hom from the constant free rank-one sheaf is abelian cohomology evaluated at one:
resolve the target by injective module sheaves, forget to section-acyclic abelian
sheaves, and evaluate Hom on the constant generator. This is ordinaryFiniteClass
itself, so the Chern specification identifies the actual relative module-derived
arrow with c. Take beta to be the base O(1) class realized by that same comparison.
Taking adjuncts turns its pullback into beta followed by the twisted unit, and
turns the relative class into the stated Chern pushforward. The adjunction unit
pasting is exactly alpha; the composition and twist comparisons are exactly those
in ordinaryFiniteP1DiagonalChartMap. Thus their sum is the displayed formula.
The argument is over arbitrary rings, including the zero ring, and N=1 gives
the zero-coefficient arrows. No general derived-map detection by stalks is used. -/
theorem ordinaryFiniteP1_diagonal_kummer_component_formula (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (hPP : IsUnit (N : Γ(ProjectiveLine (ProjectiveLine S), ⊤)))
    (hW : IsUnit (N : Γ(pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S), ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine (ProjectiveLine S)) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec A N hA (ProjectiveLine S) hPP c)
    (hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible)
    (κ : ordinaryFiniteSupportedExt A (pullback.diagonal (ProjectiveLine S ↘ S))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA))
    (hκ : SupportedKummerBoundary A N hA (pullback.diagonal (ProjectiveLine S ↘ S))
      hI hW κ) :
    ∀ a : Bool, ∃ β : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
              (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧,
            ordinaryFiniteP1DiagonalSupportedMap A N hA S a κ ≫
              ordinaryFiniteP1DiagonalChartMap A N hA t S hS a =
            β ≫ ordinaryFiniteP1Unit A N hA t (ProjectiveLine S) hP +
              ordinaryFiniteP1ChernPushforward A N hA (ProjectiveLine S) c := by
  intro a
  exact ⟨_, ordinaryFiniteP1_diagonal_kummer_component_formula_fixed N hN A hA
    t S hS hP hPP hW c hc hI κ hκ a⟩

end AlgebraicGeometry.Etale
