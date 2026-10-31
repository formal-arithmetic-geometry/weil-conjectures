/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.SmoothPurity.EtaleFiniteTwistPullbackRest
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat

/-! # Base change of the ordinary constant-object unit

The equation holds for every commutative square; exchange need not be invertible.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, the substitution of
canonical pullback counits (blueprint: lem-sf-ordinary-finite-constant-base-change).
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace
  upperStar lowerStar DerivedCategory.singleFunctors
  ordinaryFiniteUnitPullback singleFunctorCompLeftDerivedUpperStarIso
  leftDerivedUpperStarComp derivedUpperStarLowerStarAdjunction derivedSquareUpperStarIso

private theorem unit_pullback_comp (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g fg hfg).hom.app
        (ordinaryFiniteUnit A Z) ≫
      (ordinaryFinitePullback A f).map (ordinaryFiniteUnitPullback A g).hom ≫
        (ordinaryFiniteUnitPullback A f).hom =
      (ordinaryFiniteUnitPullback A fg).hom := by
  exact ordinaryFiniteUnitPullback_comp A f g fg hfg

private theorem unit_pullback_square (A : Type (u + 1)) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {w : Y' ⟶ Y}
    (sq : CommSq v f' f w) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app
        (ordinaryFiniteUnit A Y) ≫
      (ordinaryFinitePullback A v).map (ordinaryFiniteUnitPullback A f).hom ≫
        (ordinaryFiniteUnitPullback A v).hom =
      (ordinaryFinitePullback A f').map (ordinaryFiniteUnitPullback A w).hom ≫
        (ordinaryFiniteUnitPullback A f').hom := by
  apply (cancel_epi
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f' w (v ≫ f) sq.w).hom.app
      (ordinaryFiniteUnit A Y))).mp
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [unit_pullback_comp, unit_pullback_comp]

end AlgebraicGeometry.Etale
