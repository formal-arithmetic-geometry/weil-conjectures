/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!

# Concrete coefficient categories have small site coefficients

A category `A` with `Hom`-types in `Type (u + 1)`, concrete over `Type (u + 1)` with a
forgetful functor that preserves limits and filtered colimits of size `u + 1` and reflects
isomorphisms, has small site coefficients (`CategoryTheory.SmallSiteCoefficients`): for a
site with objects in `Type (u + 1)` and `Hom`-types in `Type u`, the covering sieves of an
object form a category of size `u + 1`, so Mathlib's plus-construction
(`Mathlib/CategoryTheory/Sites/LeftExact.lean`) produces a left exact sheafification.

In particular the intended coefficient categories `ModuleCat.{u + 1} Λ` and `Ab.{u + 1}`
have small site coefficients, and they are Grothendieck abelian of size `u + 1` (Mathlib),
so the sheaf categories on the small sites of `P`-schemes over `Scheme.{u}` with these
coefficients are Grothendieck abelian by
`CategoryTheory.GrothendieckTopology.isGrothendieckAbelian_sheaf_smallGrothendieckTopology`.

-/

@[expose] public section

universe u' u

namespace CategoryTheory

open Limits

/-- A category concrete over `Type (u + 1)` whose forgetful functor preserves limits and
filtered colimits of size `u + 1` and reflects isomorphisms has small site coefficients:
Mathlib's plus-construction provides a left exact sheafification on every site with
objects in `Type (u + 1)` and `Hom`-types in `Type u`. -/
instance (priority := low) SmallSiteCoefficients.of_concreteCategory (A : Type u')
    [Category.{u + 1} A] {FA : A → A → Type*} {CA : A → Type (u + 1)}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
    [HasLimitsOfSize.{u + 1, u + 1} A] [HasColimitsOfSize.{u + 1, u + 1} A]
    [PreservesLimitsOfSize.{u + 1, u + 1} (forget A)] [(forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (forget A)] :
    SmallSiteCoefficients A where
  hasSheafify _ := inferInstance

variable (Λ : Type (u + 1)) [Ring Λ] (X : AlgebraicGeometry.Scheme.{u})

example : SmallSiteCoefficients (ModuleCat.{u + 1} Λ) := inferInstance

example : SmallSiteCoefficients Ab.{u + 1} := inferInstance

example : IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  inferInstance

example : IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1}) := inferInstance

end CategoryTheory
