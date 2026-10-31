/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteOrdinaryCoordinateArrow
public import WeilConjectures.AlgebraicGeometry.FiniteP1KummerCoordinates
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteChernPullback
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
public import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystemSupplement
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
public import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
public import WeilConjectures.CategoryTheory.DerivedSingleUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.FiniteP1LocalCoordinateComparison
import WeilConjectures.AlgebraicGeometry.FiniteP1RealizedCoordinatePullback

/-! # Pullback of arbitrary ordinary arrows in the finite coordinates

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-p1-ordinary-coordinate-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
set_option linter.auxLemma false in
-- Reuse the sheafification and localization witnesses stored in the endpoint maps.
attribute [local instance 100000] finiteKummerUnitCoordinate._proof_4
  finiteKummerUnitCoordinate._proof_5 finiteKummerUnitCoordinate._proof_9
  finiteKummerUnitCoordinate._proof_10
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
open SpTowerClasses
attribute [local instance 100000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 100001] finiteOrdinaryDerived finiteOrdinaryExt
  finiteOrdinaryIntrinsicDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [local instance 100000] Etale.ordinaryFiniteDerivedCategoryInstance
attribute [local implicit_reducible] Etale.ordinaryFiniteDerivedCategoryInstance
  Etale.ordinaryFiniteSingleFunctor Etale.ordinaryFiniteDegreeZero
attribute [local irreducible] Functor.mapDerivedCategory SpTowerP1.nuSingle
  HasDerivedCategory.ofIsGrothendieckAbelian HomologicalComplex.quasiIso
  Etale.projectiveLineTraceTransport
  geoP1PullComparison
  Etale.ordinaryFiniteUnitPullback Etale.ordinaryFiniteShiftedLinePullback

/-- Pullback and site comparison send the projective-line endpoint coordinates to
the local coordinates of the ordinary pulled arrow. This is functorial for every
arrow, before specifying its cohomology class.
Source: diagonal-tower trace (1), exact site comparison and inverse image
(blueprint: lem-sfb-finite-p1-ordinary-coordinate-pullback).

Proof: expand the two endpoint coordinates. Naturality of the site-comparison
pullback square conjugates the pullback of the comparison image to the comparison
image of ordinary pullback. The constant coordinate is its source comparison;
uniqueness of normalized Tate transport identifies its target comparison with
ordinaryFiniteShiftedLinePullback. Apply the realization functor and compose with
the inverse source single comparison and the shifted target single comparison.
All cancellation is by isomorphisms, so zero coefficients and empty schemes are
included. -/
theorem finiteP1_ordinary_coordinate_pullback (n : ℕ)
    [Finite (SpTowerShriek.R l E n)] {X S : Scheme.{u}}
    (e : X ≅ ProjectiveLine S) (hS : IsUnit (l : Γ(S, ⊤)))
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX)
    (a : Etale.ordinaryFiniteUnit (FiniteRing l E n) (ProjectiveLine S) ⟶
      (Etale.ordinaryFiniteLine (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext _ _ (coefficient_annihilates l E n)) (ProjectiveLine S))⟦(2 : ℤ)⟧) :
    HEq
      ((finiteKummerUnitCoordinate l E n e c).hom ≫
        (finiteOverRealization l E n e).map
          ((geoP1Comparison (FiniteRing l E n) (ProjectiveLine S)).map a) ≫
        (finiteKummerLineCoordinate l E n e hS c).inv)
      (finiteOrdinaryCoordinateArrow l E n X c
        (Etale.ordinaryFiniteLinePullbackMap (FiniteRing l E n) (l ^ (n + 1))
          (ULift.ext _ _ (coefficient_annihilates l E n))
          (Etale.projectiveLineTraceTransport (l ^ (n + 1))
            (pow_pos (Fact.out : l.Prime).pos _) (FiniteRing l E n)
            (ULift.ext _ _ (coefficient_annihilates l E n))) e.hom
          (finiteP1_unitOnPullback (l ^ (n + 1)) (ProjectiveLine S ↘ S)
            (by simpa only [Nat.cast_pow] using hS.pow (n + 1))) a)) := by
  exact (heq_of_eq (finiteP1_realized_coordinate_pullback l E n e hS c a)).trans
    (finiteP1LocalCoordinateImage_ordinary l E n X c
      (Etale.ordinaryFiniteLinePullbackMap (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext _ _ (coefficient_annihilates l E n))
        (Etale.projectiveLineTraceTransport (l ^ (n + 1))
          (pow_pos (Fact.out : l.Prime).pos _) (FiniteRing l E n)
          (ULift.ext _ _ (coefficient_annihilates l E n))) e.hom
        (finiteP1_unitOnPullback (l ^ (n + 1)) (ProjectiveLine S ↘ S)
          (by simpa only [Nat.cast_pow] using hS.pow (n + 1))) a))

end AlgebraicGeometry.ProEtale.DiagonalTrace
