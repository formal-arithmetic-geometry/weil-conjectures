/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChartCoordinateDifferenceNeighbourhood
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalBaseChangeCompared
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.PurityDncInvariance
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorBundlePurity
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionPurityCoordinates
public import WeilConjectures.AlgebraicGeometry.Standing.StandingExceptionalComposition
public import WeilConjectures.AlgebraicGeometry.Purity.PurityNormalProjection
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Section.PuritySectionInvariantIntrinsic
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalRegularPureCodimension
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
import all WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.AffineSpace.Subtraction
public import WeilConjectures.AlgebraicGeometry.PurityNormalBundle.PurityNormalBundle
public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import WeilConjectures.RingTheory.AssociatedGradedRing
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationIdentityUnit
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorBundleIntegrationOrientation
import all WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationRankZeroLocal
import WeilConjectures.AlgebraicGeometry.VectorIntegrationChart.VectorIntegrationIdentityAdjunct
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import all WeilConjectures.AlgebraicGeometry.ChartNormalDifferential.ChartNormalDifferential
import all WeilConjectures.AlgebraicGeometry.PurityNormalBundle.PurityNormalBundle
import WeilConjectures.AlgebraicGeometry.SmoothSectionCentredCoordinates.SmoothSectionCentredCoordinates
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.ReesConeNormalization
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.ReesConeNormalizedExistence
public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials

import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionUnitPresentationNormalization
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalEtaleRhoUnitSquare
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalEtaleLocalityUnitChange
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalOrdinaryOrientationRigidity
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import Mathlib.CategoryTheory.Adjunction.Whiskering
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Iso
import all Mathlib.Logic.Small.Defs
import all WeilConjectures.Compactification.Defs
import WeilConjectures.AlgebraicGeometry.Modules.AffineHom
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.Etale.EtaleCoordinateDifferentialBasis

/-! # Normalized diagonal/DNC assemblies on affine coordinate charts

Source: main-20261015, sec-smooth-purity/sk-prop-sp-orientation,
sk-prop-sp-orientation-charts.proof.md, Steps 1--4; projection-purity-agreement.
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

The arrows below retain the canonical comparison-unit and root-line maps.
No frame, scalar, or orientation is supplied by the caller.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.PurityNormalBundle

open Opposite

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem augmentation_inclusion :
    (ConormalGradedAlgebra.presentation i).inclusion 1 ≫
      (commAlgebraSheafModuleFunctor Z.sheaf).map
        (ConormalGradedAlgebra.augmentation i) = 0 := by
  let adj := (Scheme.Modules.exists_tensorPullbackAdjunction i).choose
  apply (adj.homEquiv (ConormalGradedAlgebra.power i 1) _).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext a
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (ConormalGradedAlgebra.augmentation i).right.hom.app (op (i ⁻¹ᵁ U.unop))
    (ConormalGradedAlgebra.homogeneousClass i _ _ 1 U.unop a) = 0
  have h := (ConormalGradedAlgebra.presentation i).augmentation.exists.choose_spec
  simpa only [ConormalGradedAlgebra.augmentation, Nat.one_ne_zero, ↓reduceIte] using
    h 1 U.unop a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem augmentation_comparison :
    ConormalGradedAlgebra.symmetricComparison i ≫ augmentationToBase i =
      VectorBundleZeroSection.augmentationToBase Z (ConormalGradedAlgebra.piece i 1) := by
  apply ExistsUnique.unique (exists_quasiCoherentSymmetricAlgebra_core Z
    (ConormalGradedAlgebra.piece i 1)
    (((VectorBundleZeroSection.antiEquivalence Z).functor.obj
      (op (VectorBundleZeroSection.baseObject Z))).obj) 0)
  · intro U a
    change (augmentationToBase i).right.hom.app (op U)
      ((ConormalGradedAlgebra.symmetricComparison i).right.hom.app (op U)
        ((SymmetricAlgebraSheaf.inclusion _).val.app (op U) a)) = 0
    dsimp only [ConormalGradedAlgebra.symmetricComparison]
    rw [(ConormalGradedAlgebra.presentation i).symmetricComparison.exists.choose_spec]
    have h := congrArg (fun q ↦ q.val.app (op U) a) (augmentation_inclusion i)
    change (((VectorBundleZeroSection.antiEquivalence Z).functor.obj
      (op (VectorBundleZeroSection.baseObject Z))).obj.hom.hom.app (op U))
        ((ConormalGradedAlgebra.augmentation i).right.hom.app (op U)
          (((ConormalGradedAlgebra.presentation i).inclusion 1).val.app (op U) a)) = 0
    change (ConormalGradedAlgebra.augmentation i).right.hom.app (op U)
      (((ConormalGradedAlgebra.presentation i).inclusion 1).val.app (op U) a) = 0 at h
    rw [h, map_zero]
  · exact (exists_quasiCoherentSymmetricAlgebra_core Z
      (ConormalGradedAlgebra.piece i 1)
      (((VectorBundleZeroSection.antiEquivalence Z).functor.obj
        (op (VectorBundleZeroSection.baseObject Z))).obj) 0).exists.choose_spec

end AlgebraicGeometry.PurityNormalBundle

namespace WeilConjectures.PurityFiniteSetting

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [local instance] _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

/-- The ordinary presentation of the specified diagonal orientation. Its defining
comparison equation determines this presentation: comparison is fully faithful on
these bounded-below objects. Source: chart proof, Step 3
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartOrdinaryOrientation (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :
    letI := P.noetherian aY
    letI := Dnc.compactifiable P f aY
    P.diagonalOrdinaryDualizing f ≅ P.diagonalTwistEtale X d :=
  letI := P.noetherian aY
  letI := Dnc.compactifiable P f aY
  ((P.existsUnique_diagonalDualizingObject d f aY).exists.choose_spec).choose

/-- Conversion from the derived tensor unit to the degree-zero coefficient object.
Source: chart proof, source comparison in Step 3
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartDualizingUnit (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    Etale.dualizingComplex P.Coefficient f ≅
      P.diagonalOrdinaryDualizing f :=
  (Etale.rightDerivedUpperShriek P.Coefficient f).mapIso
    (smoothPurityUnitIso P.Coefficient Y).symm

attribute [local irreducible] chartDualizingUnit

/-- Alpha is the inverse smooth base-change mate pulled along the actual diagonal,
followed by its section identity and the coefficient-unit comparison.
Source: chart proof, Step 3; diagonal-dualizing-object proof, Step 1
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartDiagonalAlpha (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV] :
    letI := P.noetherian aV
    letI := Dnc.compactifiable P h aV
    Dnc.sourceSection P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h) ≅
      P.diagonalDualizing h :=
  letI := P.noetherian aV
  letI := P.noetherian (h ≫ aV)
  letI := Dnc.compactifiable P h aV
  letI := (P.comparedDiagonalBaseChange d h (h ≫ aV) aV rfl).2.2.2.1
  Dnc.sourceComparison P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (P.diagonalComparedRestriction h
          (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
            (IsPullback.of_hasPullback h h).flip)) ≪≫ P.chartDualizingUnit h) ≪≫
    (P.diagonalDualizingComparison h).symm

/-- Delta is selected only from the unique, coordinate-normalized DNC comparison.
Its defining equation reads the same family trivialization at t=1 and t=0.
Source: chart proof, Step 3 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartDiagonalDelta (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [IsSeparated (h ≫ aV)]
    [LocallyOfFiniteType aV] [QuasiCompact aV] :=
  (Dnc.existsUnique_dncInvariance P d (pullback.fst h h) (h ≫ aV)
    (pullback.diagonal h) (pullback.diagonal_fst h)).exists.choose

/-- Pulling the specified orientation of a smooth projection to its section,
including the canonical Tate restriction. The vector-purity normalization below
identifies this arrow with zero-section restriction of integration-transposed purity.
Source: chart proof, Step 4 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartSectionOrientation (P : PurityFiniteSetting.{u})
    {N B : Scheme.{u}} (d : ℕ) (q : N ⟶ B)
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]
    [SmoothOfRelativeDimension d q]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (z : B ⟶ N)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := Dnc.compactifiable P q aB
    Etale.sectionInvariant P.Coefficient q z ≅ P.diagonalTwistEtale B d :=
  letI := Dnc.compactifiable P q aB
  (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) z).leftDerivedFunctor.mapIso
      (P.chartDualizingUnit q ≪≫ P.chartOrdinaryOrientation d q aB) ≪≫
    Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t z (P.diagonalExponent_isUnit (q ≫ aB)) d

/-- Beta on the actual associated-graded normal cone and its augmentation section.
The normal projection is the one constructed from the diagonal ideal, including rank zero.
Source: chart proof, Steps 2 and 4
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartDiagonalBeta (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :=
  let s := pullback.diagonal h
  let g := pullback.fst h h
  let hs := pullback.diagonal_fst h
  letI : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g s) :=
    (Scheme.Hom.normalConeData d hs).smoothOfRelativeDimension_proj
  letI := Dnc.normalQuasiCompact d g s hs
  letI := Dnc.normalCompactifiable P d g (h ≫ aV) s hs
  Dnc.normalComparison P d g (h ≫ aV) s hs ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (P.chartSectionOrientation d (Scheme.Hom.normalConeProj g s) (h ≫ aV)
          s.normalConeZeroSection t)

/-- The local assembly uses alpha inverse, then normalized delta, then beta.
Source: chart proof, Steps 3--4
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartDiagonalAssembly (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [IsSeparated (h ≫ aV)]
    [LocallyOfFiniteType aV] [QuasiCompact aV]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :=
  (P.chartDiagonalAlpha d h aV).symm ≪≫ P.chartDiagonalDelta d h aV ≪≫
    P.chartDiagonalBeta d h aV t

/-- The specified diagonal orientation equals its three canonical local factors,
for every finite coefficient stage and every normalized root-line presentation.
Source: chart proof, Steps 1--4 and diagonal-dualizing-object proof, Steps 1--2
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: form the self-product and pull the inverse smooth base-change mate along
its diagonal (lem-pur-diagonal-base-change). The smooth diagonal is regular, and
its associated-graded normal cone is the relative tangent bundle
(lem-pur-diagonal-regular-immersion; def-pur-normal-bundle). Apply the unique
normalized DNC comparison to this closed section (thm-pur-dnc-invariance).
Vector-bundle purity, restricted to the augmentation section, gives beta
(cor-pur-vector-bundle-purity). These are exactly the three factors in the
specified diagonal orientation. Their canonical unit and site comparisons are
the displayed factors, so composing them yields equality of isomorphisms.
The proof works for d=0, empty schemes, and every positive level without a
ramification divisibility hypothesis. -/
theorem diagonal_dnc_chart_normalization (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    P.diagonalDualizingObject d h aV = P.chartDiagonalAssembly d h aV t := by
  sorry

/-- The selected ordinary arrow has the full counit normalization, and realizes
exactly the specified pro-etale arrow. Source: chart proof, Steps 3--4
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: use the witness equation in existsUnique_diagonalDualizingObject. Its
ordinary witness satisfies DiagonalOrientationNormalization. The same witness is
chosen in chartOrdinaryOrientation, so the comparison equation is unchanged. -/
theorem chartOrdinaryOrientation_spec (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :
    letI := P.noetherian aY
    letI := P.noetherian (f ≫ aY)
    letI := Dnc.compactifiable P f aY
    P.DiagonalOrientationNormalization d f aY (P.chartOrdinaryOrientation d f aY) ∧
      P.diagonalDualizingObject d f aY = P.diagonalDualizingComparison f ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
            (P.chartOrdinaryOrientation d f aY) := by
  let := P.noetherian aY
  let := P.noetherian (f ≫ aY)
  let := Dnc.compactifiable P f aY
  exact ((P.existsUnique_diagonalDualizingObject d f aY).exists.choose_spec).choose_spec

section

attribute [local implicit_reducible] diagonalTwistEtale diagonalOrdinaryDualizing

set_option synthInstance.maxSize 2048 in
private theorem chartLocality_comp (P : PurityFiniteSetting.{u})
    {W U X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [QuasiCompact j]
    (k : W ⟶ U) [Etale k] [IsSeparated k] [QuasiCompact k]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    letI := P.noetherian aY
    letI := P.noetherian (f ≫ aY)
    letI := P.noetherian ((j ≫ f) ≫ aY)
    letI := P.noetherian ((k ≫ j ≫ f) ≫ aY)
    letI := Dnc.compactifiable P f aY
    letI := Dnc.compactifiable P (j ≫ f) aY
    letI := Dnc.compactifiable P (k ≫ j ≫ f) aY
    letI := Dnc.compactifiable P ((k ≫ j) ≫ f) aY
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) k j).app
        (P.diagonalOrdinaryDualizing f) ≪≫
      (Etale.ordinaryFinitePullback P.Coefficient k).mapIso (P.diagonalEtaleLocality N j f) ≪≫
      P.diagonalEtaleLocality N k (j ≫ f) =
    P.diagonalEtaleLocality N (k ≫ j) f ≪≫
      P.diagonalDualizingCongr (Category.assoc k j f) := by
  let := P.noetherian aY
  let := P.noetherian (f ≫ aY)
  let := P.noetherian ((j ≫ f) ≫ aY)
  let := P.noetherian ((k ≫ j ≫ f) ≫ aY)
  let := Dnc.compactifiable P f aY
  let := Dnc.compactifiable P (j ≫ f) aY
  let := Dnc.compactifiable P (k ≫ j ≫ f) aY
  let := Dnc.compactifiable P ((k ≫ j) ≫ f) aY
  have hs := locality_comp_field P aY k j f (j ≫ f) (k ≫ j ≫ f) rfl rfl
  have hu := P.diagonalEtaleLocality_unitChange N j f (j ≫ f) rfl
  have hv := P.diagonalEtaleLocality_unitChange N k (j ≫ f) (k ≫ j ≫ f) rfl
  have hw := P.diagonalEtaleLocality_unitChange N (k ≫ j) f (k ≫ j ≫ f)
    (Category.assoc k j f)
  have hS :
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) k j).hom.app
          (Etale.dualizingComplex P.Coefficient f) ≫
        (Etale.ordinaryFinitePullback P.Coefficient k).map
          (Etale.sectionStructuralLocalityIso P.Coefficient j f (j ≫ f) rfl).hom ≫
        (Etale.sectionStructuralLocalityIso P.Coefficient k (j ≫ f)
          (k ≫ j ≫ f) rfl).hom =
        (Etale.sectionStructuralLocalityIso P.Coefficient (k ≫ j) f
          (k ≫ j ≫ f) (Category.assoc k j f)).hom := by
    have hh := congrArg Iso.hom hs
    simp only [Iso.trans_hom, Functor.mapIso_hom] at hh
    change (Etale.ordinaryFinitePullback P.Coefficient k).map
          (Etale.sectionStructuralLocalityIso P.Coefficient j f (j ≫ f) rfl).hom ≫
        (Etale.sectionStructuralLocalityIso P.Coefficient k (j ≫ f)
          (k ≫ j ≫ f) rfl).hom =
      (Etale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} P.Coefficient) k j).inv.app
          (Etale.dualizingComplex P.Coefficient f) ≫
        (Etale.sectionStructuralLocalityIso P.Coefficient (k ≫ j) f
          (k ≫ j ≫ f) (Category.assoc k j f)).hom at hh
    apply (cancel_epi ((Etale.leftDerivedUpperStarComp
      (ModuleCat.{u + 1} P.Coefficient) k j).inv.app
        (Etale.dualizingComplex P.Coefficient f))).1
    simpa only [Iso.inv_hom_id_app_assoc] using hh
  apply Iso.ext
  apply (cancel_epi ((Etale.ordinaryFinitePullback P.Coefficient (k ≫ j)).map
    (OrientationCounit.unitChange P f).hom)).1
  have hn := (Etale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} P.Coefficient) k j).hom.naturality
      (OrientationCounit.unitChange P f).hom
  have hu' := congrArg Iso.hom hu
  have hv' := congrArg Iso.hom hv
  have hw' := congrArg Iso.hom hw
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at hu' hv' hw' ⊢
  simp only [diagonalDualizingCongr, eqToIso_refl, Iso.refl_hom, Category.comp_id]
    at hu' hv'
  dsimp only [Functor.comp_map] at hn
  dsimp only [Etale.ordinaryFinitePullback] at hu' hv' hw' hS ⊢
  rw [reassoc_of% hn]
  rw [← Functor.map_comp_assoc, hu']
  simp only [Functor.map_comp, Category.assoc]
  rw [hv', reassoc_of% hS]
  exact hw'.symm

set_option synthInstance.maxSize 2048 in
/-- Source-etale restriction of the normalized arrow. Open restriction is the
special case of an open immersion; the equation also covers every etale change
of coordinate chart. Source: chart proof, final compatibility paragraph
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: compare the two inverse arrows on etale coordinate opens over Y.
Apply chartOrdinaryOrientation_spec to the original and restricted morphisms.
The coefficient-unit change transports structural locality composition to the
fixed ordinary coefficient object. This composition law and Tate pullback
composition identify the two normalized formulas. Both objects are concentrated
in degree -2d, so the existing derived-map gluing lemma detects their equality.
Cancel the two orientation isomorphisms to obtain the forward-arrow equation. -/
theorem chartOrientation_etale_restriction (P : PurityFiniteSetting.{u})
    {U X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    [SmoothOfRelativeDimension d (j ≫ f)]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := P.noetherian aY
    letI := P.noetherian (f ≫ aY)
    letI := P.noetherian ((j ≫ f) ≫ aY)
    letI := Dnc.compactifiable P f aY
    letI := Dnc.compactifiable P (j ≫ f) aY
    (Etale.ordinaryFinitePullback P.Coefficient j).map
        (P.chartOrdinaryOrientation d f aY).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aY)) d).hom =
      (P.diagonalEtaleLocality N j f).hom ≫
        (P.chartOrdinaryOrientation d (j ≫ f) aY).hom := by
  classical
  let := P.noetherian aY
  let := P.noetherian (f ≫ aY)
  let := P.noetherian ((j ≫ f) ≫ aY)
  let := Dnc.compactifiable P f aY
  let := Dnc.compactifiable P (j ≫ f) aY
  have hN : 0 < P.diagonalExponent := pow_pos P.coefficients.prime.out.pos P.level
  obtain ⟨t₀, D, _⟩ := Etale.exists_ordinaryFiniteP1Adjunction P.diagonalExponent hN
    P.Coefficient P.diagonalExponent_annihilates
  have ht := Etale.ordinaryFiniteTwistTransport_unique P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t₀ t
  subst t₀
  let J := Etale.ordinaryFinitePullback P.Coefficient j
  let T := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aY)) d
  let ef := P.chartOrdinaryOrientation d f aY
  let eg := P.chartOrdinaryOrientation d (j ≫ f) aY
  change J.map ef.hom ≫ T.hom = (P.diagonalEtaleLocality N j f).hom ≫ eg.hom
  suffices hi : J.map ef.inv ≫ (P.diagonalEtaleLocality N j f).hom =
      T.hom ≫ eg.inv by
    change (J.mapIso ef).inv ≫ (P.diagonalEtaleLocality N j f).hom =
      T.hom ≫ eg.inv at hi
    have hh := congrArg (fun q ↦ (J.mapIso ef).hom ≫ q ≫ eg.hom) hi
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
      Category.comp_id] at hh
    simpa only [Functor.mapIso_hom, diagonalTwistEtale] using hh.symm
  obtain ⟨q⟩ := base_normal_form P.diagonalExponent hN P.Coefficient
    P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit (f ≫ aY)) d
  let L := (_root_.DerivedCategory.singleFunctor _ 0).obj
    (Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
      P.diagonalExponent_annihilates (d : ℤ))
  let n : ℤ := -(2 * (d : ℤ))
  have : (L⟦2 * (d : ℤ)⟧).IsLE n :=
    _root_.DerivedCategory.TStructure.t.isLE_shift L 0 (2 * (d : ℤ)) n (by dsimp [n]; omega)
  have : (P.diagonalTwistEtale X d).IsLE n :=
    _root_.DerivedCategory.TStructure.t.isLE_of_iso q.symm n
  have : (J.obj (P.diagonalTwistEtale X d)).IsLE n := by
    have := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).isLE_mapDerivedCategory_obj
      (P.diagonalTwistEtale X d) n
    exact _root_.DerivedCategory.TStructure.t.isLE_of_iso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) j).app _).symm n
  obtain ⟨r⟩ := base_normal_form P.diagonalExponent hN P.Coefficient
    P.diagonalExponent_annihilates U (P.diagonalExponent_isUnit ((j ≫ f) ≫ aY)) d
  let M := (_root_.DerivedCategory.singleFunctor _ 0).obj
    (Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent U
      P.diagonalExponent_annihilates (d : ℤ))
  have : (M⟦2 * (d : ℤ)⟧).IsGE n :=
    _root_.DerivedCategory.TStructure.t.isGE_shift M 0 (2 * (d : ℤ)) n (by dsimp [n]; omega)
  have : (P.diagonalOrdinaryDualizing (j ≫ f)).IsGE n :=
    _root_.DerivedCategory.TStructure.t.isGE_of_iso (r.symm ≪≫ eg.symm) n
  choose V W hV hW _ hx hWV v hv hw using
    fun x : U ↦ Smooth.exists_etale_to_affineSpace (j ≫ f) d x
  apply map_eq_of_cover P.Coefficient W (fun x ↦ ⟨x, hx x⟩) n
  intro x
  have : IsAffine (W x).toScheme := hW x
  have : IsNoetherian (W x).toScheme := isNoetherian_of_locallyOfFiniteType (W x).ι
  have : Etale (v x) := hv x
  have : IsOpenImmersion (AffineSpace.map (ULift.{u} (Fin d)) (V x).ι) :=
    MorphismProperty.of_isPullback
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) (V x).ι).flip
      (inferInstance : IsOpenImmersion (V x).ι)
  let z := v x ≫ AffineSpace.map (ULift.{u} (Fin d)) (V x).ι ≫
    (affineTraceAffineSpaceIso Y d).inv
  have : Etale z := inferInstance
  have : IsSeparated z := inferInstance
  have : LocallyOfFiniteType z := inferInstance
  have : QuasiCompact z := inferInstance
  have hp : (affineTraceAffineSpaceIso Y d).inv ≫ affineTraceProjection Y d =
      AffineSpace (ULift.{u} (Fin d)) Y ↘ Y := by
    apply (cancel_epi (affineTraceAffineSpaceIso Y d).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    exact (AffineSpace.homOfVector_over _ _).symm
  have w : z ≫ affineTraceProjection Y d = (W x).ι ≫ j ≫ f := by
    dsimp only [z]
    simp only [Category.assoc, hp, AffineSpace.map_over]
    rw [← Category.assoc, hw x, Scheme.Hom.resLE_comp_ι]
  let k := (W x).ι
  let := Dnc.compactifiable P (k ≫ j ≫ f) aY
  let := Dnc.compactifiable P ((k ≫ j) ≫ f) aY
  let : HasCompactification (z ≫ affineTraceProjection Y d) :=
    HasCompactification.of_eq w.symm
  have hf := (P.chartOrdinaryOrientation_spec d f aY).1 t D N
    (W x).toScheme (k ≫ j) z (w.trans (Category.assoc k j f).symm)
  have hg := (P.chartOrdinaryOrientation_spec d (j ≫ f) aY).1 t D N
    (W x).toScheme k z w
  have hc := congrArg Iso.hom (P.chartLocality_comp f aY j k N)
  have hT := Etale.vectorIntegrationBaseCoefficientPullback_comp P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t k j (k ≫ j) rfl
    (P.diagonalExponent_isUnit (f ≫ aY))
    (P.diagonalExponent_isUnit ((j ≫ f) ≫ aY)) d
  have hn := (Etale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} P.Coefficient) k j).hom.naturality ef.inv
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at hc
  dsimp only [Functor.comp_map] at hn
  apply (cancel_epi ((Etale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} P.Coefficient) k j).hom.app (P.diagonalTwistEtale X d))).1
  apply (cancel_mono (P.diagonalEtaleLocality N k (j ≫ f)).hom).1
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [J, T, ef, eg, Etale.ordinaryFinitePullback] at hn hf hg hc hT ⊢
  rw [← reassoc_of% hn, hc, reassoc_of% hf, hg]
  have hcongr :
      (P.diagonalDualizingCongr (w.trans (Category.assoc k j f).symm)).hom ≫
        (P.diagonalDualizingCongr (Category.assoc k j f)).hom =
      (P.diagonalDualizingCongr w).hom := by
    simp only [diagonalDualizingCongr, eqToIso.hom, eqToHom_trans]
  rw [hcongr, ← hT]
  simp only [Category.assoc, k, diagonalTwistEtale]

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Smooth base change on ordinary dualizing objects, retaining the actual
inverse-compact-support mate and the degree-zero coefficient-unit comparisons.
Source: chart proof, Step 3 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartOrdinaryBaseChange (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (b : Y' ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X)
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback a f' f b) :
    letI := Dnc.compactifiable P f aY
    (Etale.ordinaryFinitePullback P.Coefficient a).obj
      (P.diagonalOrdinaryDualizing f) ≅ P.diagonalOrdinaryDualizing f' :=
  letI := Dnc.compactifiable P f aY
  letI := Dnc.invertibleExponent P (f ≫ aY)
  letI := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
    P.Coefficient f d sq
  letI := (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient sq).2
    (NatIso.isIso_app_of_isIso
      (Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq) (𝟙_ _))
  (Etale.ordinaryFinitePullback P.Coefficient a).mapIso (P.chartDualizingUnit f).symm ≪≫
    asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient sq) ≪≫
      P.chartDualizingUnit f'

/-- Target-open restriction of the orientation; combined with source restriction
this is the arbitrary pair of affine opens U and V in the node.
Source: chart proof, final restriction paragraph
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: base change the diagonal square and its inverse smooth base-change mate.
The normalized DNC arrow is unchanged by its base-change characterization.
Vector integration and the pure-root Tate restriction commute with this base
change. Therefore the three factors pull back to the three new factors.
Apply the defining assembly equality locally and glue on affine opens. -/
theorem chartOrientation_open_baseChange (P : PurityFiniteSetting.{u})
    {X Y X' V : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (v : V ⟶ Y) [IsOpenImmersion v] [QuasiCompact v]
    (h : X' ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (j : X' ⟶ X) (sq : IsPullback j h f v)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := Dnc.compactifiable P f aY
    letI := Dnc.compactifiable P h (v ≫ aY)
    (Etale.ordinaryFinitePullback P.Coefficient j).map
        (P.chartOrdinaryOrientation d f aY).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aY)) d).hom =
      (P.chartOrdinaryBaseChange d f aY v h j sq).hom ≫
        (P.chartOrdinaryOrientation d h (v ≫ aY)).hom := by
  sorry

/-- The actual diagonal normal cone is the symmetric total space of the diagonal
conormal module, including the empty regular sequence when d=0. Thus it is the
relative tangent bundle, rather than a separately chosen rank-d bundle.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: apply centred smooth-section coordinates to the first projection and its
diagonal. The coordinate ideal is a regular sequence of length d, including
length zero. Its degree-one classes give the conormal frame and its homogeneous
monomials identify Sym(I/I^2) with the associated graded algebra. Relative Spec
of this canonical comparison, composed with the homogeneous-normalized Rees
comparison, identifies the actual normal cone and preserves augmentation. -/
theorem chartDiagonalNormalBundle {U V : Scheme.{u}} [IsNoetherian U]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [SmoothOfRelativeDimension d h]
    [QuasiCompact h] :
    (ConormalGradedAlgebra.piece (pullback.diagonal h) 1).IsFiniteLocallyFreeOfRank d ∧
      IsIso (ConormalGradedAlgebra.symmetricComparison (pullback.diagonal h)) := by
  have := SmoothOfRelativeDimension.smooth d h
  have H := SmoothSectionCentredCoordinates.exists_centred_coordinates d
    (pullback.fst h h) (pullback.diagonal h) (pullback.diagonal_fst h)
  exact H.2.2

/-- Pullback of the compared coefficient unit, with the canonical monoidal map.
Source: chart proof, Step 4 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartUnitPullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (P.smoothPurityPullback f).obj
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit P.Coefficient Y)) ≅
      𝟙_ (_root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) :=
  let unitPullback (A : Type (u + 1)) [CommRing A] [Finite A]
      {S T : Scheme.{u}} (g : S ⟶ T) :
      (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit A T)) ≅
        𝟙_ (_root_.DerivedCategory
          (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))) :=
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.mapIso
        (projectionUnitRaw A T) ≪≫
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) g).symm.app _ ≪≫
      ProEtale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g
  unitPullback P.Coefficient f

attribute [local irreducible] chartUnitPullback projectionUnitRaw
attribute [local irreducible] Sheaf.monoidalCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

set_option backward.isDefEq.respectTransparency false in

/-- The finite transported exceptional inverse image of the coefficient unit, in the
standing pro-etale exceptional coordinates: the uniqueness of right adjoints of the
etale compact-support pushforward, transported by comparison pullback.
Source: blueprint finite exceptional inverse image
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartDiagonalDualizingStanding (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    P.diagonalDualizing f ≅
      (ProEtale.rightDerivedUpperShriek P.Coefficient f).obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
            (Etale.ordinaryFiniteUnit P.Coefficient Y)) :=
  letI : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient)
      (HasCompactification.compactification f)).IsLeftAdjoint :=
    (Etale.rightDerivedUpperShriekOfCompactificationAdjunction P.Coefficient
      (HasCompactification.compactification f)).isLeftAdjoint
  (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
      (((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} P.Coefficient)
          (HasCompactification.compactification f))).rightAdjointUniq
        (Etale.rightDerivedUpperShriekOfCompactificationAdjunction P.Coefficient
          (HasCompactification.compactification f))).app _)

set_option synthInstance.maxSize 2048 in
attribute [local semireducible] chartUnitPullback Sheaf.monoidalCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory in
/-- Ordered affine space is smooth of its coordinate dimension.
Source: chart proof, Step 1 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: transport projection_smooth through the coordinate-preserving isomorphism
between the two ordered affine towers. It is the identity at zero; at a
successor both towers adjoin the same final polynomial variable. -/
theorem chartTraceProjection_smooth (B : Scheme.{u}) (r : ℕ) :
    SmoothOfRelativeDimension r (affineTraceProjection B r) := by
  induction r with
  | zero =>
      change SmoothOfRelativeDimension 0 (𝟙 B)
      infer_instance
  | succ r ih =>
      have : SmoothOfRelativeDimension 1
          (AffineSpace PUnit.{u + 1} (affineTraceTower B r) ↘ affineTraceTower B r) := by
        simpa only [Nat.card_unique] using
          (AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (affineTraceTower B r))
      have := smoothOfRelativeDimension_comp
        (AffineSpace PUnit.{u + 1} (affineTraceTower B r) ↘ affineTraceTower B r)
        (affineTraceProjection B r) (n := 1) (m := r)
      simpa only [affineTraceTower, affineTraceProjection, Nat.add_comm] using this

set_option backward.isDefEq.respectTransparency false in
private theorem chartProjectionOrientation_inv (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (r : ℕ)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :
    let := P.noetherian aB
    let := chartTraceProjection_smooth B r
    (P.chartOrdinaryOrientation r (affineTraceProjection B r) aB).inv =
      P.diagonalAffineMate t D B (P.diagonalExponent_isUnit aB) r := by
  let := P.noetherian aB
  let := affineTraceNoetherian B r
  let := chartTraceProjection_smooth B r
  let := Dnc.compactifiable P (affineTraceProjection B r) aB
  let N := Etale.canonicalEtaleCompactSupportNormalization P.Coefficient
  have hn := (P.chartOrdinaryOrientation_spec r (affineTraceProjection B r) aB).1
    t D N (affineTraceTower B r) (𝟙 _) (𝟙 _) rfl
  simp only [diagonalDualizingCongr, eqToIso_refl, Iso.refl_hom,
    Category.comp_id, Iso.hom_inv_id_assoc] at hn
  have he := (cancel_mono
    (P.diagonalEtaleLocality N (𝟙 _) (affineTraceProjection B r)).hom).mp hn
  let e := Etale.leftDerivedUpperStarId
    (ModuleCat.{u + 1} P.Coefficient) (affineTraceTower B r)
  let : (Etale.ordinaryFinitePullback P.Coefficient
      (𝟙 (affineTraceTower B r))).Faithful := Functor.Faithful.of_iso e.symm
  exact Functor.map_injective _ he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] VectorBundleZeroSection.antiEquivalence

/-- Relative Spec of the canonical symmetric comparison, followed by the normalized
Rees comparison, from the actual cone to its conormal vector bundle. Its homogeneous
normalization fixes every ideal class, so it contains no arbitrary bundle automorphism.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartNormalModelRaw {U V : Scheme.{u}} [IsNoetherian U]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [SmoothOfRelativeDimension d h]
    [QuasiCompact h] :
    letI := (chartDiagonalNormalBundle d h).1
    (pullback.diagonal h).ker.normalCone ≅ VectorBundleZeroSection.scheme U d
      (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) :=
  letI := (chartDiagonalNormalBundle d h).1
  let e : VectorBundleZeroSection.algebraObject U d
        (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) ≅
      PurityNormalBundle.algebraObject (pullback.diagonal h) :=
    ObjectProperty.isoMk _ (@asIso _ _ _ _
      (ConormalGradedAlgebra.symmetricComparison (pullback.diagonal h))
      (chartDiagonalNormalBundle d h).2)
  let eOver := (ObjectProperty.ι (fun Y : Over U ↦ IsAffineHom Y.hom)).mapIso
    (((VectorBundleZeroSection.antiEquivalence U).inverse.mapIso e).unop)
  (Etale.FiniteSmoothPurity.reesConeComparison_exists (pullback.diagonal h)).choose ≪≫
    (Over.forget U).mapIso eOver

attribute [local irreducible] chartNormalModelRaw

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The conormal vector-bundle model exists for the actual diagonal normal cone,
with its actual projection and zero section. This makes the preceding universal
presentation equation nonvacuous also in rank zero.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: take the inverse of chartNormalModelRaw. Its specified value gives uniqueness.
chartDiagonalNormalBundle gives finite local freeness and invertibility
of the canonical symmetric comparison. Apply the relative Spec anti-equivalence
and compose with the homogeneous-normalized Rees comparison. Both algebra maps
preserve constants and augmentation, so projection and zero commute. Their
coordinate formulas identify this with the differential normal-bundle map. -/
theorem chartNormal_model_exists {U V : Scheme.{u}} [IsNoetherian U]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [SmoothOfRelativeDimension d h]
    [QuasiCompact h] :
    letI := (chartDiagonalNormalBundle d h).1
    ∃! e : VectorBundleZeroSection.scheme U d
        (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) ≅
          (pullback.diagonal h).ker.normalCone,
      e = (chartNormalModelRaw d h).symm ∧
      e.hom ≫ Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h) =
        VectorBundleZeroSection.π U d (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) ∧
      VectorBundleZeroSection.zero U d (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) ≫
        e.hom = (pullback.diagonal h).normalConeZeroSection := by
  let := (chartDiagonalNormalBundle d h).1
  let := (chartDiagonalNormalBundle d h).2
  let δ := pullback.diagonal h
  let E := VectorBundleZeroSection.antiEquivalence U
  let A := VectorBundleZeroSection.algebraObject U d (ConormalGradedAlgebra.piece δ 1)
  let B := PurityNormalBundle.algebraObject δ
  let e : A ≅ B := ObjectProperty.isoMk _
    (asIso (ConormalGradedAlgebra.symmetricComparison δ))
  let eOver := (ObjectProperty.ι (fun Y : Over U ↦ IsAffineHom Y.hom)).mapIso
    ((E.inverse.mapIso e).unop)
  let j := (Over.forget U).mapIso eOver
  have hjp : j.hom ≫ VectorBundleZeroSection.π U d
      (ConormalGradedAlgebra.piece δ 1) = PurityNormalBundle.projection δ :=
    Over.w eOver.hom
  have ha : E.inverse.map e.inv ≫
      E.functor.preimage ((E.counitIso.app A).hom ≫
        ObjectProperty.homMk (VectorBundleZeroSection.augmentationToBase U
          (ConormalGradedAlgebra.piece δ 1))) =
      E.functor.preimage ((E.counitIso.app B).hom ≫
        ObjectProperty.homMk (PurityNormalBundle.augmentationToBase δ)) := by
    apply E.functor.map_injective
    simp only [Functor.map_comp, Functor.map_preimage]
    have hn := E.counitIso.hom.naturality e.inv
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    refine ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun q ↦ q ≫ _) hn).trans (Category.assoc _ _ _))).trans ?_
    apply congrArg (fun q ↦ (E.counitIso.app B).hom ≫ q)
    apply ObjectProperty.hom_ext
    change inv (ConormalGradedAlgebra.symmetricComparison δ) ≫
      VectorBundleZeroSection.augmentationToBase U (ConormalGradedAlgebra.piece δ 1) = _
    rw [← PurityNormalBundle.augmentation_comparison δ, IsIso.inv_hom_id_assoc]
    all_goals rfl
  have hjz : VectorBundleZeroSection.zero U d
      (ConormalGradedAlgebra.piece δ 1) ≫ j.inv = PurityNormalBundle.zeroSection δ :=
    congrArg (fun q ↦ q.unop.hom.left) ha
  have hR := (Etale.FiniteSmoothPurity.reesConeComparison_exists δ).choose_spec
  have hp : (chartNormalModelRaw d h).hom ≫
      VectorBundleZeroSection.π U d (ConormalGradedAlgebra.piece δ 1) =
      Scheme.Hom.normalConeProj (pullback.fst h h) δ := by
    unfold chartNormalModelRaw
    change (Etale.FiniteSmoothPurity.reesConeComparison_exists δ).choose.hom ≫
      j.hom ≫ _ = _
    rw [hjp, hR.1]
    exact Scheme.Hom.purityNormalProjection_eq δ (pullback.fst h h)
      (pullback.diagonal_fst h)
  have hz : δ.normalConeZeroSection ≫ (chartNormalModelRaw d h).hom =
      VectorBundleZeroSection.zero U d (ConormalGradedAlgebra.piece δ 1) := by
    unfold chartNormalModelRaw
    change δ.normalConeZeroSection ≫
      (Etale.FiniteSmoothPurity.reesConeComparison_exists δ).choose.hom ≫ j.hom = _
    rw [← Category.assoc, hR.2.1, ← hjz, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  refine ⟨(chartNormalModelRaw d h).symm, ⟨rfl, ?_, ?_⟩, fun _ he ↦ he.1⟩
  · change (chartNormalModelRaw d h).inv ≫ _ = _
    exact (Iso.inv_comp_eq _).mpr hp.symm
  · change _ ≫ (chartNormalModelRaw d h).inv = _
    exact (Iso.comp_inv_eq _).mpr hz.symm




/-- The affine counit mate is invertible at every finite coefficient stage.
Source: chart proof, Step 4; projection-purity-agreement
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: chartGamma_counit_normalization identifies the realization of this mate
with the existing ordered comparison at the unit. Projection-purity-agreement
identifies that map with inverse smooth orientation. Finite site comparison
reflects isomorphisms on the bounded-below etale objects, giving the assertion. -/
theorem chartAffineMate_isIso (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (r : ℕ)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :
    letI := P.noetherian aB
    IsIso (P.diagonalAffineMate t D B (P.diagonalExponent_isUnit aB) r) := by
  let := P.noetherian aB
  let := chartTraceProjection_smooth B r
  rw [← chartProjectionOrientation_inv P B aB r t D]
  infer_instance

/-- Gamma in the ordinary-etale coefficient presentation, with its actual
ordered-counit hom. Source: chart proof, Step 4
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartAffineGamma (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (r : ℕ)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :=
  letI := P.noetherian aB
  letI := P.chartAffineMate_isIso B aB r t D
  asIso (P.diagonalAffineMate t D B (P.diagonalExponent_isUnit aB) r)

/-- Epsilon is the exceptional-composition mate followed by etale identification,
in its normalized ordinary presentation. The normalized locality iso is defined
by transposing the actual compact-support compositor and sum-extension counit.
Source: chart proof, Step 4 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartEpsilon (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (u : U ⟶ affineTraceTower V d) [Etale u] [IsSeparated u]
    [LocallyOfFiniteType u] [QuasiCompact u]
    (w : u ≫ affineTraceProjection V d = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  letI := P.noetherian aV
  letI := P.noetherian (h ≫ aV)
  letI := affineTraceNoetherian V d
  letI := Dnc.compactifiable P h aV
  letI : HasCompactification (u ≫ affineTraceProjection V d) :=
    HasCompactification.of_eq w.symm
  (P.diagonalDualizingCongr w).symm ≪≫
    (P.diagonalEtaleLocality N u (affineTraceProjection V d)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
/-- The etale exceptional identification on any specified bounded-below etale
presentation. It is the unique counit-preserving adjunction comparison of the
normalized sum-extension comparison, transported through the comparison unit.
Source: chart proof, Step 4 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartEtaleIdentification (P : PurityFiniteSetting.{u})
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (u : U ⟶ X) [Etale u] [IsSeparated u] [HasCompactification u]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (K : Etale.DerivedCategoryModule P.Coefficient X)
    (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    (ProEtale.rightDerivedUpperShriek P.Coefficient u).obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj K) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) u).leftDerivedFunctor.obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj K) :=
  let A := ModuleCat.{u + 1} P.Coefficient
  letI := ProEtale.isIso_derivedComparisonAdjunction_unit_app A X K hK
  let ρ := (N.adjunction u (HasCompactification.compactification u)
    (Etale.rightDerivedUpperShriek P.Coefficient u)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient u)).exists.choose
  (ProEtale.comparisonUpperStar A U).mapDerivedCategory.mapIso
      ((Etale.rightDerivedUpperShriek P.Coefficient u).mapIso
        (asIso ((ProEtale.derivedComparisonAdjunction A X).unit.app K)).symm ≪≫
        ρ.app K ≪≫ (Etale.leftDerivedUpperStarIsoMapDerivedCategory A u).symm.app K) ≪≫
    (Dnc.pullComparison P u K).symm

attribute [local irreducible] affineTraceTower affineTraceProjection

attribute [local semireducible] affineTraceTower affineTraceProjection

section

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  ConormalGradedAlgebra.representative
  Scheme.Hom.relativeDifferentials Scheme.Hom.relativeDifferentialsDerivation
  ConormalGradedAlgebra.piece

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-one identification defining N_Delta = T_(U/V). Its normalization
is [y(a)-x(a)] -> da, so its symmetric relative Spec is the canonical tangent
identification used in the normal model, with the same sign as chart differences.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: on the affine tensor-product ring the diagonal ideal is the kernel of
multiplication. The universal derivation sends a to the class of 1 tensor a
minus a tensor 1. Its universal property identifies I/I^2 with the relative
Kahler module; these classes generate and their relations are additivity and
the Leibniz rule. Sheafify this affine identification. Under the canonical
associated-graded comparison the representative of the same difference has
exactly this class. This gives the stated iso and normalization; generation by
the differentials gives uniqueness. Taking symmetric algebras and relative Spec
identifies the cone with Spec Sym(Omega), preserving projection and augmentation.
The empty affine scheme and the empty rank-zero list cause no exception. -/
theorem chartDiagonalConormal_differentials {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (h : U ⟶ V) [IsSeparated h] :
    ∃! e : ConormalGradedAlgebra.piece (pullback.diagonal h) 1 ≅ h.relativeDifferentials,
      ∀ a : Γ(U, ⊤),
        ∃ b : (ConormalGradedAlgebra.power (pullback.diagonal h) 1).val.obj
            (Opposite.op ⊤),
          (ConormalGradedAlgebra.powerInclusion (pullback.diagonal h) 1).val.app
              (Opposite.op ⊤) b =
            (pullback.snd h h).appTop a - (pullback.fst h h).appTop a ∧
          e.hom.val.app (Opposite.op ((pullback.diagonal h) ⁻¹ᵁ ⊤))
              (ConormalGradedAlgebra.representative (pullback.diagonal h) 1 ⊤ b) =
            h.relativeDifferentials.val.map (homOfLE le_top).op
              (h.relativeDifferentialsDerivation.d (X := Opposite.op ⊤) a) := by
  obtain ⟨ω, hω⟩ := ChartNormalDifferential.differenceIdentification h
  refine ⟨ω.symm, ?_, ?_⟩
  · intro a
    let δ := pullback.diagonal h
    let φ := SheafOfModules.unitToPushforwardObjUnit δ.toRingCatSheafHom
    let c := (pullback.snd h h).appTop a - (pullback.fst h h).appTop a
    have hc : (SheafOfModules.evaluation (pullback h h).ringCatSheaf
        (Opposite.op ⊤)).map φ c = 0 := by
      change δ.appTop c = 0
      dsimp only [c]
      rw [map_sub]
      apply sub_eq_zero.mpr
      have he : (pullback.snd h h).appTop ≫ δ.appTop =
          (pullback.fst h h).appTop ≫ δ.appTop := by
        rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
        simp only [δ, pullback.diagonal_snd, pullback.diagonal_fst]
      exact ConcreteCategory.congr_hom he a
    have hc' : c ∈ Set.range ((SheafOfModules.evaluation (pullback h h).ringCatSheaf
        (Opposite.op ⊤)).map (kernel.ι φ)) := by
      rw [Scheme.Modules.range_map_kernelι]
      exact hc
    obtain ⟨c', hc'⟩ := hc'
    obtain ⟨k, hk⟩ := ChartNormalDifferential.idealKernelIso δ
    let b := k.inv.app ⊤ c'
    have hki : k.inv ≫ δ.ker.toModulesι = kernel.ι φ := by
      rw [← hk, Iso.inv_hom_id_assoc]
    have hb : (ConormalGradedAlgebra.powerInclusion δ 1).val.app
        (Opposite.op ⊤) b = c :=
      (congrArg (fun q ↦ q.app ⊤ c') hki).trans hc'
    have hb' : (ConormalGradedAlgebra.powerInclusion (pullback.diagonal h) 1).val.app
        (Opposite.op ⊤) b =
        (pullback.snd h h).appLE ⊤ ⊤ le_top a -
          (pullback.fst h h).appLE ⊤ ⊤ le_top a := by
      simpa only [Scheme.Hom.appLE, Scheme.Hom.appTop, Scheme.Hom.preimage_top,
        homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id] using hb
    refine ⟨b, ?_, ?_⟩
    · simpa only [Scheme.Hom.appLE, Scheme.Hom.appTop, Scheme.Modules.Hom.app,
        Scheme.Hom.preimage_top, homOfLE_refl,
        op_id, CategoryTheory.Functor.map_id, Category.comp_id] using hb'
    · have hn := hω ⊤ ⊤ le_top le_top le_top a b hb'
      simp only [Scheme.Hom.preimage_top, homOfLE_refl, op_id,
        PresheafOfModules.map_id, ModuleCat.restrictScalarsId'_inv_app,
        ModuleCat.restrictScalarsId'App_inv_apply] at hn ⊢
      change ω.inv.val.app (Opposite.op ⊤) _ = h.relativeDifferentialsDerivation.d a
      rw [← hn]
      exact ConcreteCategory.congr_hom
        (congrArg (fun f ↦ f.val.app (Opposite.op ⊤)) ω.hom_inv_id) _
  · intro e he
    apply Iso.ext
    apply (cancel_epi ω.hom).mp
    apply (h.relativeDifferentialsHomEquiv _).injective
    apply Scheme.Modules.derivation_ext_of_isAffine
    intro a
    obtain ⟨b, hb, he⟩ := he a
    have hb' : (ConormalGradedAlgebra.powerInclusion (pullback.diagonal h) 1).val.app
        (Opposite.op ⊤) b =
        (pullback.snd h h).appLE ⊤ ⊤ le_top a -
          (pullback.fst h h).appLE ⊤ ⊤ le_top a := by
      simpa only [Scheme.Hom.appLE, Scheme.Hom.appTop, Scheme.Modules.Hom.app,
        Scheme.Hom.preimage_top, homOfLE_refl,
        op_id, CategoryTheory.Functor.map_id, Category.comp_id] using hb
    have hn := hω ⊤ ⊤ le_top le_top le_top a b hb'
    simp only [Scheme.Hom.preimage_top, homOfLE_refl, op_id,
      PresheafOfModules.map_id, ModuleCat.restrictScalarsId'_inv_app,
        ModuleCat.restrictScalarsId'App_inv_apply] at hn he
    change e.hom.val.app (Opposite.op ⊤)
        (ω.hom.val.app (Opposite.op ⊤) (h.relativeDifferentialsDerivation.d a)) =
      ω.inv.val.app (Opposite.op ⊤)
        (ω.hom.val.app (Opposite.op ⊤) (h.relativeDifferentialsDerivation.d a))
    rw [hn]
    exact he.trans (by
      rw [← hn]
      exact (ConcreteCategory.congr_hom
        (congrArg (fun f ↦ f.val.app (Opposite.op ⊤)) ω.hom_inv_id) _).symm)



end

section

attribute [local irreducible] Etale.rightDerivedLowerShriek
  Etale.rightDerivedUpperShriek Etale.rightDerivedUpperShriekAdjunction
  Etale.affineLinearCompactComparison Functor.mapDerivedCategory

attribute [local implicit_reducible] affineTraceTower affineTraceProjection
  diagonalTwistEtale diagonalOrdinaryDualizing diagonalExponent
  Etale.affineLinearBaseCoefficient

end

attribute [local irreducible] chartOrdinaryOrientation
  Etale.ordinaryFiniteUnitPullback Etale.leftDerivedUpperStarId Etale.affineLinearPullbackId

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordered differential frame induced by an etale coordinate chart. Combined
with chartDiagonalConormal_differentials and the canonical symmetric comparison,
its relative Spec is N_h = O_U^d with the specified normal-coordinate basis.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: the etale transitivity sequence identifies Omega_U/V with pullback of
the differentials of affine d-space. The latter is free on the ordered dx_i.
The universal derivation commutes with pullback, giving exactly this generator
formula. The free-sheaf universal property makes the normalized map unique;
etale-local invertibility makes it an isomorphism. At d=0 both differential
modules are zero and the unique map is their identity. -/
theorem chartCoordinateDifferentialFrame {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
    [Etale u] (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    ∃! e : SheafOfModules.free (R := U.ringCatSheaf) (ULift.{u} (Fin d)) ≅
        h.relativeDifferentials,
      ∀ i : ULift.{u} (Fin d),
        e.hom.val.app (Opposite.op ⊤)
            ((SheafOfModules.ιFree (R := U.ringCatSheaf) i).val.app (Opposite.op ⊤)
              (1 : U.ringCatSheaf.obj.obj (Opposite.op ⊤))) =
          h.relativeDifferentialsDerivation.d (X := Opposite.op ⊤)
            (u.appTop (AffineSpace.coord V i)) := by
  classical
  have : SmoothOfRelativeDimension d
      (AffineSpace (ULift.{u} (Fin d)) V ↘ V) := by
    simpa only [Nat.card_ulift, Nat.card_fin] using
      (AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) V)
  have : SmoothOfRelativeDimension d h := by
    rw [← w]
    simpa only [Nat.zero_add] using
      (smoothOfRelativeDimension_comp (n := 0) (m := d) u
        (AffineSpace (ULift.{u} (Fin d)) V ↘ V))
  have : h.relativeDifferentials.IsFiniteLocallyFreeOfRank d :=
    h.isFiniteLocallyFreeOfRank_relativeDifferentials d
  have : h.relativeDifferentials.IsLocallyFree :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree h.relativeDifferentials d
  obtain ⟨e, he⟩ :=
    AlgebraicGeometry.DiagonalDifferenceReesFrame.coordinate_differential_frame d h u w
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply SheafOfModules.free_hom_ext
  intro i
  apply Scheme.Modules.hom_ext_of_isAffine
  intro x
  change e'.hom.val.app (Opposite.op ⊤)
      ((SheafOfModules.ιFree i).val.app (Opposite.op ⊤) x) =
    e.hom.val.app (Opposite.op ⊤)
      ((SheafOfModules.ιFree i).val.app (Opposite.op ⊤) x)
  change U.ringCatSheaf.obj.obj (Opposite.op ⊤) at x
  have hx : x = x • (1 : U.ringCatSheaf.obj.obj (Opposite.op ⊤)) := by simp
  rw [hx]
  simp only [map_smul]
  exact congrArg (fun y ↦ x • y) ((he' i).trans (he i).symm)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The conormal model with its value fixed by relative Spec and homogeneous Rees
coordinates. The equality in chartNormal_model_exists determines the selected object.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartNormalModel {U V : Scheme.{u}} [IsNoetherian U]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [SmoothOfRelativeDimension d h]
    [QuasiCompact h] :
    letI := (chartDiagonalNormalBundle d h).1
    VectorBundleZeroSection.scheme U d
      (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) ≅
        (pullback.diagonal h).ker.normalCone :=
  (chartNormal_model_exists d h).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordered conormal frame: dx_i is carried back along [y(a)-x(a)] -> da.
Both isomorphisms are uniquely determined by their displayed generator formulas.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartConormalFrame {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h]
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale u]
    (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    SheafOfModules.free (R := U.ringCatSheaf) (ULift.{u} (Fin d)) ≅
      ConormalGradedAlgebra.piece (pullback.diagonal h) 1 :=
  (chartCoordinateDifferentialFrame d h u w).exists.choose ≪≫
    (chartDiagonalConormal_differentials h).exists.choose.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Degree-one functions on Spec Sym(I/I²) in the ordered conormal frame.
This is homOfVector of the symmetric-algebra generators, not a chosen scheme iso.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartConormalCoordinateMap {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    [IsNoetherian U] (d : ℕ) (h : U ⟶ V) [IsSeparated h]
    [SmoothOfRelativeDimension d h] [QuasiCompact h]
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale u]
    (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    letI := (chartDiagonalNormalBundle d h).1
    VectorBundleZeroSection.scheme U d
      (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) ⟶
        AffineSpace (ULift.{u} (Fin d)) U :=
  letI := (chartDiagonalNormalBundle d h).1
  AffineSpace.homOfVector
    (VectorBundleZeroSection.π U d (ConormalGradedAlgebra.piece (pullback.diagonal h) 1))
    fun i ↦ (VectorBundleZeroSection.algebraIso U d
      (ConormalGradedAlgebra.piece (pullback.diagonal h) 1)).hom.right.hom.app (Opposite.op ⊤)
        ((SymmetricAlgebraSheaf.inclusion
          (ConormalGradedAlgebra.piece (pullback.diagonal h) 1)).val.app (Opposite.op ⊤)
            ((chartConormalFrame d h u w).hom.val.app (Opposite.op ⊤)
              ((SheafOfModules.ιFree (R := U.ringCatSheaf) i).val.app (Opposite.op ⊤)
                (1 : U.ringCatSheaf.obj.obj (Opposite.op ⊤)))))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual normal-cone coordinates: the canonical conormal model followed by the
ordered differential frame. In particular no arbitrary zero-preserving bundle map occurs.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartNormalCoordinateMap {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    [IsNoetherian U] (d : ℕ) (h : U ⟶ V) [IsSeparated h]
    [SmoothOfRelativeDimension d h] [QuasiCompact h]
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale u]
    (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    (pullback.diagonal h).ker.normalCone ⟶ AffineSpace (ULift.{u} (Fin d)) U :=
  (chartNormalModel d h).inv ≫ chartConormalCoordinateMap d h u w

attribute [local irreducible] chartNormalModel chartConormalFrame

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem framedVectorCoordinates {S : Scheme.{u}} [IsAffine S] [IsNoetherian S]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (e : SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin d)) ≅ F) :
    let c := AffineSpace.homOfVector (VectorBundleZeroSection.π S d F) fun i ↦
      (VectorBundleZeroSection.algebraIso S d F).hom.right.hom.app (Opposite.op ⊤)
        ((SymmetricAlgebraSheaf.inclusion F).val.app (Opposite.op ⊤)
          (e.hom.val.app (Opposite.op ⊤)
            ((SheafOfModules.ιFree (R := S.ringCatSheaf) i).val.app (Opposite.op ⊤)
              (1 : Γ(S, ⊤)))))
    IsIso c ∧ VectorBundleZeroSection.zero S d F ≫ c =
      AffineSpace.zeroSection (ULift.{u} (Fin d)) S := by
  classical
  let I := ULift.{u} (Fin d)
  let R : Type u := Γ(S, ⊤)
  let X := VectorBundleZeroSection.scheme S d F
  let π := VectorBundleZeroSection.π S d F
  let A : S.affineOpens := ⟨⊤, isAffineOpen_top S⟩
  let b := (Pi.basisFun R I).map
    (SheafOfModules.sectionsLinearEquivOfIsoFree e.symm (Opposite.op ⊤)).symm
  have hb (i : I) : b i = e.hom.val.app (Opposite.op ⊤)
      ((SheafOfModules.ιFree (R := S.ringCatSheaf) i).val.app (Opposite.op ⊤)
        (1 : Γ(S, ⊤))) := by
    simp only [b, Module.Basis.map_apply, Pi.basisFun_apply]
    change e.hom.val.app (Opposite.op ⊤)
      (∑ j : I, (SheafOfModules.ιFree (R := S.ringCatSheaf) j).val.app
        (Opposite.op ⊤) ((Pi.single i 1 : I → R) j)) = _
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  let φ := CommRingCat.ofHom (SymmetricAlgebra.equivMvPolynomial b).symm.toRingHom
  let m := X.topIso.inv ≫ VectorBundleZeroSection.affineChart S d F A ≫
    Spec.map φ ≫ (AffineSpace.SpecIso I (.of R)).inv ≫ AffineSpace.map I A.2.fromSpec
  have hc : CommRingCat.ofHom (MvPolynomial.C : R →+* _) ≫ φ =
      CommRingCat.ofHom (algebraMap R (SymmetricAlgebraSheaf.sections F (Opposite.op ⊤))) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (SymmetricAlgebra.equivMvPolynomial b).symm.commutes
  have hm : m = AffineSpace.homOfVector π (fun i ↦
      (VectorBundleZeroSection.algebraIso S d F).hom.right.hom.app (Opposite.op ⊤)
        ((SymmetricAlgebraSheaf.inclusion F).val.app (Opposite.op ⊤)
          (e.hom.val.app (Opposite.op ⊤)
            ((SheafOfModules.ιFree (R := S.ringCatSheaf) i).val.app
              (Opposite.op ⊤) (1 : Γ(S, ⊤)))))) := by
    apply AffineSpace.hom_ext
    · dsimp only [m]
      simp only [Category.assoc, AffineSpace.map_over, AffineSpace.SpecIso_inv_over_assoc,
        ← Spec.map_comp_assoc]
      rw [hc]
      dsimp only [I]
      rw [AffineSpace.homOfVector_over]
      change X.topIso.inv ≫ VectorBundleZeroSection.affineChart S d F A ≫
        Spec.map (CommRingCat.ofHom (algebraMap R
          (SymmetricAlgebraSheaf.sections F (Opposite.op ⊤)))) ≫ A.2.fromSpec = π
      have hh := congrArg (fun q ↦ X.topIso.inv ≫ q ≫ (⊤ : S.Opens).ι)
        (VectorBundleZeroSection.affineChart_spec S d F A).2.1
      simpa only [A, Scheme.Hom.preimage_top, Category.assoc,
        IsAffineOpen.isoSpec_inv_ι, morphismRestrict_ι,
        Scheme.toIso_inv_ι_assoc] using hh
    · intro i
      dsimp only [m]
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.map_appTop_coord]
      rw [AffineSpace.SpecIso_inv_appTop_coord]
      have hn := CategoryTheory.congr_fun (Scheme.ΓSpecIso_inv_naturality φ)
        (MvPolynomial.X i)
      change (Scheme.ΓSpecIso (.of (SymmetricAlgebraSheaf.sections F
          (Opposite.op ⊤)))).inv ((SymmetricAlgebra.equivMvPolynomial b).symm
            (MvPolynomial.X i)) = (Spec.map φ).appTop
              ((Scheme.ΓSpecIso (.of (MvPolynomial I R))).inv (MvPolynomial.X i)) at hn
      rw [← hn, SymmetricAlgebra.equivMvPolynomial_symm_X]
      have hh := VectorBundleZeroSection.affineChart_appTop S d F A
        (SymmetricAlgebra.ι R _ (b i))
      change (VectorBundleZeroSection.affineChart S d F A).appTop
        ((Scheme.ΓSpecIso (.of (SymmetricAlgebraSheaf.sections F (Opposite.op ⊤)))).inv
          (SymmetricAlgebra.ι R _ (b i))) = _ at hh
      refine (congrArg (fun x ↦ X.topIso.inv.appTop x) hh).trans ?_
      rw [hb]
      change X.topIso.inv.appTop ((⊤ : X.Opens).topIso.inv _) = _
      rw [AffineSpace.homOfVector_appTop_coord]
      have ht : (⊤ : X.Opens).topIso.inv ≫ X.topIso.inv.appTop = 𝟙 _ := by
        have hi : (⊤ : X.Opens).ι.appTop = (⊤ : X.Opens).topIso.inv := by
          simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
          congr 1
        rw [← hi, ← Scheme.Hom.comp_appTop, Scheme.toIso_inv_ι]
        rfl
      exact ConcreteCategory.congr_hom ht _
  let : IsIso (VectorBundleZeroSection.affineChart S d F A) :=
    (VectorBundleZeroSection.affineChart_spec S d F A).1
  let : IsIso φ := (RingEquiv.toCommRingCatIso
    (SymmetricAlgebra.equivMvPolynomial b).symm.toRingEquiv).isIso_hom
  let : IsIso A.2.fromSpec := by
    change IsIso (isAffineOpen_top S).fromSpec
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  constructor
  · rw [← hm]
    infer_instance
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, AffineSpace.homOfVector_over,
      (VectorBundleZeroSection.zero_spec S d F).1, AffineSpace.zeroSection_over]
  · intro i
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.homOfVector_appTop_coord, AffineSpace.zeroSection_appTop_coord]
    have hz := VectorBundleZeroSection.zero_pullback S d F (⊤ : S.Opens)
    have hz' := ConcreteCategory.congr_hom hz
      ((SymmetricAlgebraSheaf.inclusion F).val.app (Opposite.op ⊤)
        (e.hom.val.app (Opposite.op ⊤)
          ((SheafOfModules.ιFree (R := S.ringCatSheaf) i).val.app (Opposite.op ⊤)
            (1 : Γ(S, ⊤)))))
    have h0 := (VectorBundleZeroSection.augmentation_spec S F).1 ⊤
      (e.hom.val.app (Opposite.op ⊤)
        ((SheafOfModules.ιFree (R := S.ringCatSheaf) i).val.app (Opposite.op ⊤)
          (1 : Γ(S, ⊤))))
    have hh := hz'.trans h0
    simp only [Scheme.Hom.appLE, Scheme.Hom.preimage_top,
      homOfLE_refl, op_id, S.presheaf.map_id, Category.comp_id,
      CommRingCat.comp_apply] at hh
    exact hh


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem chartConormalCoordinates_spec {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    [IsNoetherian U] (d : ℕ) (h : U ⟶ V) [IsSeparated h]
    [SmoothOfRelativeDimension d h] [QuasiCompact h]
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale u]
    (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    let := (chartDiagonalNormalBundle d h).1
    IsIso (chartConormalCoordinateMap d h u w) ∧
      VectorBundleZeroSection.zero U d (ConormalGradedAlgebra.piece
        (pullback.diagonal h) 1) ≫ chartConormalCoordinateMap d h u w =
        AffineSpace.zeroSection (ULift.{u} (Fin d)) U := by
  let := (chartDiagonalNormalBundle d h).1
  exact framedVectorCoordinates d (ConormalGradedAlgebra.piece
    (pullback.diagonal h) 1) (chartConormalFrame d h u w)

attribute [local irreducible] chartConormalCoordinateMap chartNormalCoordinateMap

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The constructed coordinates identify projection and zero, including the empty frame.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: chartNormal_model_exists identifies the selected model with the relative Spec of
Sym(I/I²) -> gr(I), normalized by a -> a/t on Rees charts. The conormal-differential iso
and chartCoordinateDifferentialFrame give the ordered degree-one generators. On each
frame Sym is the polynomial algebra, so homOfVector is invertible. The degree-zero
structure map gives the projection equality, and augmentation kills every generator,
giving the zero equality. For d=0 this is the empty polynomial algebra and identity. -/
theorem chartNormalCoordinateMap_spec {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    [IsNoetherian U] (d : ℕ) (h : U ⟶ V) [IsSeparated h]
    [SmoothOfRelativeDimension d h] [QuasiCompact h]
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale u]
    (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    IsIso (chartNormalCoordinateMap d h u w) ∧
    chartNormalCoordinateMap d h u w ≫ (AffineSpace (ULift.{u} (Fin d)) U ↘ U) =
      Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h) ∧
    (pullback.diagonal h).normalConeZeroSection ≫ chartNormalCoordinateMap d h u w =
      AffineSpace.zeroSection (ULift.{u} (Fin d)) U := by
  let := (chartDiagonalNormalBundle d h).1
  have hc := chartConormalCoordinates_spec d h u w
  let : IsIso (chartConormalCoordinateMap d h u w) := hc.1
  have hm := (chartNormal_model_exists d h).exists.choose_spec
  have hmdef : chartNormalModel d h = (chartNormal_model_exists d h).exists.choose := by
    unfold chartNormalModel
    rfl
  rw [← hmdef] at hm
  have hp : (chartNormalModel d h).inv ≫
      VectorBundleZeroSection.π U d (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) =
      Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h) :=
    (Iso.inv_comp_eq _).mpr hm.2.1.symm
  have hz : (pullback.diagonal h).normalConeZeroSection ≫ (chartNormalModel d h).inv =
      VectorBundleZeroSection.zero U d (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) :=
    (Iso.comp_inv_eq _).mpr hm.2.2.symm
  have hi : IsIso (chartNormalCoordinateMap d h u w) := by
    unfold chartNormalCoordinateMap
    infer_instance
  constructor
  · exact hi
  constructor
  · unfold chartNormalCoordinateMap
    rw [Category.assoc]
    change (chartNormalModel d h).inv ≫
      (chartConormalCoordinateMap d h u w ≫
        (AffineSpace (ULift.{u} (Fin d)) U ↘ U)) = _
    have ho : chartConormalCoordinateMap d h u w ≫
        (AffineSpace (ULift.{u} (Fin d)) U ↘ U) =
        VectorBundleZeroSection.π U d
          (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) :=
      by
        unfold chartConormalCoordinateMap
        exact AffineSpace.homOfVector_over _ _
    rw [ho]
    exact hp
  · unfold chartNormalCoordinateMap
    change _ ≫ (chartNormalModel d h).inv ≫ chartConormalCoordinateMap d h u w = _
    rw [← Category.assoc, hz]
    exact hc.2

/-- Canonical restriction of a section invariant through an etale map over its base.
The map is the normalized exceptional-adjunction mate pulled back to the section,
with the two pullback-composition constraints explicitly included.
Source: chart proof, Step 3 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartSectionEtaleRestriction (P : PurityFiniteSetting.{u})
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    {W X B : Scheme.{u}} [IsNoetherian W] [IsNoetherian X] [IsNoetherian B]
    (e : W ⟶ X) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (f : X ⟶ B) (q : W ⟶ B) [HasCompactification f] [HasCompactification q]
    (w : e ≫ f = q) (s : B ⟶ X) (s' : B ⟶ W) (hs : s' ≫ e = s) :
    Etale.sectionInvariant P.Coefficient f s ≅ Etale.sectionInvariant P.Coefficient q s' :=
  letI : HasCompactification (e ≫ f) := HasCompactification.of_eq w.symm
  (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) s' e s hs.symm).app _ ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) s').leftDerivedFunctor.mapIso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} P.Coefficient) e).app _ ≪≫
        (Etale.tensorMateEtalePrecompLocalityIso P.Coefficient N e f).app (𝟙_ _) ≪≫
        eqToIso (by cases w; rfl))

/-- The standard zero-section invariant, before site comparison. Compactifiability
is derived from the finite-type base, not supplied as additional data.
Source: chart proof, Step 3 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartStandardSection (P : PurityFiniteSetting.{u}) (B : Scheme.{u}) (d : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :=
  letI := Dnc.compactifiable P (AffineSpace (ULift.{u} (Fin d)) B ↘ B) aB
  Etale.sectionInvariant P.Coefficient (AffineSpace (ULift.{u} (Fin d)) B ↘ B)
    (AffineSpace.zeroSection (ULift.{u} (Fin d)) B)

/-- Coordinate differences preserve the first projection, including after restriction.
Source: chart proof, Step 1 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: chartCoordinateDifferences is homOfVector with base map the first projection.
Its projection composite is therefore that base map by homOfVector_over. Precompose
with the open inclusion and reassociate. The argument does not require d positive. -/
theorem chartCoordinateDifferences_over {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) (O : (pullback h h).Opens) :
    (O.ι ≫ chartCoordinateDifferences d h u) ≫
        (AffineSpace (ULift.{u} (Fin d)) U ↘ U) = O.ι ≫ pullback.fst h h := by
  simp only [Category.assoc, chartCoordinateDifferences, AffineSpace.homOfVector_over]

/-- Source coordinates on the actual diagonal section invariant. First restrict to
O, then use the normalized etale restriction along its coordinate-difference map.
The Cartesian zero square fixes the section comparison, and no purity arrow is used.
Source: chart proof, Steps 1 and 3
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartSourceCoordinateComparison (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [hh : IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
    (O : (pullback h h).Opens) (s : U ⟶ O.toScheme)
    (hs : s ≫ O.ι = pullback.diagonal h)
    (hc : Etale (O.ι ≫ chartCoordinateDifferences d h u))
    (sq : IsPullback s (𝟙 U) (O.ι ≫ chartCoordinateDifferences d h u)
      (AffineSpace.zeroSection (ULift.{u} (Fin d)) U))
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    Dnc.sourceSection P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h) ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.obj
          (P.chartStandardSection U d (h ≫ aV)) :=
  letI := P.noetherian aV
  letI := P.noetherian (h ≫ aV)
  letI := P.noetherian (pullback.fst h h ≫ (h ≫ aV))
  letI := P.noetherian ((O.ι ≫ pullback.fst h h) ≫ (h ≫ aV))
  letI := Dnc.compactifiable P (pullback.fst h h) (h ≫ aV)
  letI := Dnc.compactifiable P (O.ι ≫ pullback.fst h h) (h ≫ aV)
  letI := Dnc.compactifiable P (AffineSpace (ULift.{u} (Fin d)) U ↘ U) (h ≫ aV)
  letI := P.noetherian ((AffineSpace (ULift.{u} (Fin d)) U ↘ U) ≫ (h ≫ aV))
  letI := hc
  letI : IsSeparated ((O.ι ≫ chartCoordinateDifferences d h u) ≫
      (AffineSpace (ULift.{u} (Fin d)) U ↘ U)) :=
    (chartCoordinateDifferences_over d h u O).symm ▸
      MorphismProperty.comp_mem _ O.ι (pullback.fst h h)
        (IsSeparated.isSeparated_of_mono O.ι)
        (IsSeparated.isStableUnderBaseChange.of_isPullback
          (IsPullback.of_hasPullback h h).flip hh)
  letI := IsSeparated.of_comp (O.ι ≫ chartCoordinateDifferences d h u)
    (AffineSpace (ULift.{u} (Fin d)) U ↘ U)
  Dnc.sourceComparison P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (P.chartSectionEtaleRestriction N O.ι (pullback.fst h h)
            (O.ι ≫ pullback.fst h h) rfl (pullback.diagonal h) s hs ≪≫
          (P.chartSectionEtaleRestriction N (O.ι ≫ chartCoordinateDifferences d h u)
            (AffineSpace (ULift.{u} (Fin d)) U ↘ U) (O.ι ≫ pullback.fst h h)
            (chartCoordinateDifferences_over d h u O)
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) U) s
            (sq.w.trans (Category.id_comp _))).symm)

/-- Normal coordinates on the actual normal-section invariant, using the conormal
model and the ordered differential frame, followed by normalized etale locality.
Source: chart proof, Steps 2 and 3
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartNormalCoordinateComparison (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale u]
    (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    Dnc.normalSection P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h)
        (pullback.diagonal_fst h) ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.obj
          (P.chartStandardSection U d (h ≫ aV)) :=
  letI := P.noetherian (h ≫ aV)
  letI : SmoothOfRelativeDimension d
      (Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h)) :=
    (Scheme.Hom.normalConeData d (pullback.diagonal_fst h)).smoothOfRelativeDimension_proj
  letI := Dnc.normalQuasiCompact d (pullback.fst h h)
    (pullback.diagonal h) (pullback.diagonal_fst h)
  letI := Dnc.normalCompactifiable P d (pullback.fst h h) (h ≫ aV)
    (pullback.diagonal h) (pullback.diagonal_fst h)
  letI := P.noetherian
    (Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h) ≫ (h ≫ aV))
  letI := Dnc.compactifiable P (AffineSpace (ULift.{u} (Fin d)) U ↘ U) (h ≫ aV)
  letI := P.noetherian ((AffineSpace (ULift.{u} (Fin d)) U ↘ U) ≫ (h ≫ aV))
  letI := (chartNormalCoordinateMap_spec d h u w).1
  Dnc.normalComparison P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h)
      (pullback.diagonal_fst h) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (P.chartSectionEtaleRestriction N (chartNormalCoordinateMap d h u w)
          (AffineSpace (ULift.{u} (Fin d)) U ↘ U)
          (Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h))
          (chartNormalCoordinateMap_spec d h u w).2.1
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) U)
          (pullback.diagonal h).normalConeZeroSection
          (chartNormalCoordinateMap_spec d h u w).2.2).symm

attribute [local irreducible] chartSourceCoordinateComparison chartNormalCoordinateComparison

end WeilConjectures.PurityFiniteSetting
