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
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] VectorBundleZeroSection.antiEquivalence

attribute [local irreducible] chartNormalModelRaw

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] chartNormalModel chartConormalFrame

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] chartConormalCoordinateMap chartNormalCoordinateMap

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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

attribute [local irreducible] chartSourceCoordinateComparison chartNormalCoordinateComparison

end WeilConjectures.PurityFiniteSetting
