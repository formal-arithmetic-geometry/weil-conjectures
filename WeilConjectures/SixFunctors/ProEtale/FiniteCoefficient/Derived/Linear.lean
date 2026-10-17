/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!
# Linearity of the pro-étale pullback and pushforward

For a `Λ`-linear Grothendieck abelian category `A` and a morphism of schemes `g`, the
pushforward `g_*` and the pullback `g^*` on pro-étale sheaves with values in `A` are `Λ`-linear,
and so are the derived functors `Rg_*` and `Lg^*`. This is the pro-étale counterpart of
`AlgebraicGeometry.Etale.linear_rightDerivedLowerStar` and
`AlgebraicGeometry.Etale.linear_leftDerivedUpperStar`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (Λ : Type*) [Ring Λ] [Linear Λ A] {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The pushforward `g_*` on pro-étale sheaves with values in a `Λ`-linear category is
`Λ`-linear: it acts on morphisms by whiskering. -/
instance linear_lowerStar : (g)_*[A].Linear Λ where

/-- The pullback `g^*` on pro-étale sheaves with values in a `Λ`-linear category is `Λ`-linear,
being left adjoint to the `Λ`-linear pushforward. -/
instance linear_upperStar : (g)^*[A].Linear Λ :=
  (upperStarLowerStarAdjunction A g).left_adjoint_linear

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived pullback `Lg^*` on pro-étale sheaves is `Λ`-linear: it is isomorphic to the
functor `D(g^*)` induced by the `Λ`-linear exact functor `g^*`. -/
instance linear_leftDerivedUpperStar : (L((g)^*[A])).Linear Λ :=
  Functor.linear_of_iso Λ ((g)^*[A]).leftDerivedFunctorIsoMapDerivedCategory.symm

/-- The derived pushforward `Rg_*` on pro-étale sheaves is `Λ`-linear, being right adjoint to the
`Λ`-linear `Lg^*`. -/
instance linear_rightDerivedLowerStar : (R((g)_*[A])).Linear Λ :=
  (derivedUpperStarLowerStarAdjunction A g).right_adjoint_linear

end AlgebraicGeometry.ProEtale
