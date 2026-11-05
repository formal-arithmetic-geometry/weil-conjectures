/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.AlgebraicGeometry.Derived.DerivedExchangeModuleTermwiseSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenPastingSupplement
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Unbounded proper/open BaseChange

Source: Stacks Project, Tags 0F7F.
-/

@[expose] public section

universe u v w vT wT

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] Functor.mapHomologicalComplex

attribute [local irreducible] upperStar lowerStar squareUpperStarIso
  openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit Functor.rightDerivedFunctorUnitQ
  Functor.rightDerivedFunctorObjQIso
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryCompIso

section Normalization

variable {C₀ C₁ C₂ C₃ : Type v}
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    [Abelian.HasKInjectiveResolutions C₀] [Abelian.HasKInjectiveResolutions C₁]
    (R : C₀ ⥤ C₂) (P : C₁ ⥤ C₃) (K : C₀ ⥤ C₁) (E : C₂ ⥤ C₃)
    [R.Additive] [P.Additive] [K.Additive] [E.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]

end Normalization

section ExactComparison

variable {X Y Y' Z : Type v} [Category.{w} X] [Category.{w} Y]
  [Category.{w} Y'] [Category.{w} Z]
    [Abelian X] [Abelian Y] [Abelian Y'] [Abelian Z]
  [HasDerivedCategory X] [HasDerivedCategory Y]
  [HasDerivedCategory Y'] [HasDerivedCategory Z]
  (F : X ⥤ Y) (J : Y ⥤ Z) (F' : X ⥤ Y') (J' : Y' ⥤ Z)
  [F.Additive] [J.Additive] [F'.Additive] [J'.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
  (t : F ⋙ J ≅ F' ⋙ J')

end ExactComparison

section Cube

variable {B C B' C' B₀ C₀ B₀' C₀' : Type v}
  [Category.{w} B] [Category.{w} C] [Category.{w} B'] [Category.{w} C']
  [Category.{w} B₀] [Category.{w} C₀] [Category.{w} B₀'] [Category.{w} C₀']
    [Abelian B] [Abelian C] [Abelian B'] [Abelian C']
  [Abelian B₀] [Abelian C₀] [Abelian B₀'] [Abelian C₀']
  [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory B'] [HasDerivedCategory C']
  [HasDerivedCategory B₀] [HasDerivedCategory C₀]
  [HasDerivedCategory B₀'] [HasDerivedCategory C₀']
  [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions B']
  [Abelian.HasKInjectiveResolutions B₀] [Abelian.HasKInjectiveResolutions B₀']
  (G : B ⥤ C) (H : B' ⥤ C') (G₀ : B₀ ⥤ C₀) (H₀ : B₀' ⥤ C₀')
  (P : B ⥤ B') (Q : C ⥤ C') (P₀ : B₀ ⥤ B₀') (Q₀ : C₀ ⥤ C₀')
  (U : B ⥤ B₀) (V : C ⥤ C₀) (U' : B' ⥤ B₀') (V' : C' ⥤ C₀')
  [G.Additive] [H.Additive] [G₀.Additive] [H₀.Additive]
  [P.Additive] [Q.Additive] [P₀.Additive] [Q₀.Additive]
  [U.Additive] [V.Additive] [U'.Additive] [V'.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [PreservesFiniteLimits P₀] [PreservesFiniteColimits P₀]
  [PreservesFiniteLimits Q₀] [PreservesFiniteColimits Q₀]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
  [PreservesFiniteLimits V'] [PreservesFiniteColimits V']

end Cube

end AlgebraicGeometry.Etale
