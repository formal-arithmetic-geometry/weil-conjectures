/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.SmoothPurity.EtaleFiniteTwistPullbackRest
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
import all WeilConjectures.SmoothPurity.SupportedDerivedUnitForget

/-! # Base change of the projective-line Chern map

This is the geometric Chern-square part of the adjunct base-change argument.
(blueprint: lem-sp-finite-p1-chern-map-base-change)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local implicit_reducible] ordinaryFiniteSingleFunctor

set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13

-- Reuse the proposition instances already stored in the ordinary derived category.
-- Elaborate every helper interface with these same canonical localization arguments.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private theorem rootMap_pullback (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (upperStar AddCommGrpCat.{u + 1} f).map (ordinaryFiniteRootMap A N hA Y) ≫
        (moduleAbelianUpperStarComparison A f).app _ ≫
        (moduleAbelianForget A X).map (t.line f hY).hom =
      (t.roots f hY).hom ≫ ordinaryFiniteRootMap A N hA X := by
  apply (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right]
  dsimp only [moduleAbelianUpperStarComparison]
  erw [Equiv.apply_symm_apply]
  ext W z
  exact (t.line_normalization f hY W 1 z)

private theorem forget_lowerStar_map (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)} (a : F ⟶ G) :
    (moduleAbelianForget A Y).map ((lowerStar (ModuleCat.{u + 1} A) f).map a) =
      (lowerStar AddCommGrpCat.{u + 1} f).map ((moduleAbelianForget A X).map a) := by
  rfl

private theorem integralGenerator_pullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar AddCommGrpCat.{u + 1} f).map (ordinaryFiniteIntegralGenerator A Y) ≫
        (moduleAbelianUpperStarComparison A f).app _ ≫
        (moduleAbelianForget A X).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app
            (ModuleCat.of A A)).hom =
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom ≫
        ordinaryFiniteIntegralGenerator A X := by
  apply (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right]
  dsimp only [moduleAbelianUpperStarComparison]
  erw [Equiv.apply_symm_apply]
  have h := coefficient_unit A f
  simpa only [supportedConstantUnit, supportedIntegralUnit, supportedIntegralGenerator,
    Adjunction.homEquiv_unit, Functor.map_comp, forget_lowerStar_map, Category.assoc,
    RawModuleScalarComparison.forget] using h

attribute [local irreducible] ordinaryFiniteRootMap Sheaf.H.map cohomologyMap

attribute [local irreducible] ordinaryFiniteUnitPullback
  ordinaryFiniteShiftedLinePullback ordinaryFiniteIntegralGenerator
  Scheme.finiteEtaleTateLine
  ordinaryFiniteSinglePullbackIso ordinaryFiniteSingleExactPullbackIso
  ordinaryFiniteExtHomEquiv ordinaryFiniteKummerClass

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace

-- The original interface retains hN; this naturality proof works without positivity.
set_option linter.unusedVariables false in
end AlgebraicGeometry.Etale
