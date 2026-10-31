/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.CategoryTheory.DerivedSingleUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import all Mathlib.Logic.Small.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisons
/-!
# Canonical single-complex pullback comparisons

The constant and shifted coefficient comparisons are constructed for a general
coefficient category before specializing them to modules. This caches their
structural instances and avoids comparing separate expanded derived constructions.
Source: blueprint thm-amb-p1-adjunction.proof.md.
(blueprint: lem-z8-etale-single-pullback-comparisons).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
/-- The shifted single-object comparison, formed before fixing the coefficient category. -/
def shiftedSinglePullbackIso (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Sheaf Y.smallEtaleTopology B) (J' : Sheaf X.smallEtaleTopology B)
    (e : (upperStar B f).obj J ≅ J') (n : ℤ) :
    (upperStar B f).leftDerivedFunctor.obj
        (((DerivedCategory.singleFunctor _ 0).obj J)⟦n⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj J')⟦n⟧ :=
  letI := commShiftLeftDerivedUpperStar B f
  (((upperStar B f).leftDerivedFunctor.commShiftIso n).app _) ≪≫
    (shiftFunctor _ n).mapIso
      ((singleFunctorCompLeftDerivedUpperStarIso B f).app J ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso e)

end AlgebraicGeometry.Etale
