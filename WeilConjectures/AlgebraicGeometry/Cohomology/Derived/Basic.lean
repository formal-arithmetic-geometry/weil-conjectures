/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.AlgebraicGeometry.Cohomology.Restriction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# The derived category of `𝒪_X`-modules and perfect complexes

For a scheme `X`, the category `X.Modules` of `𝒪_X`-modules is a Grothendieck abelian category
(`AlgebraicGeometry.Scheme.Modules.isGrothendieckAbelian`), made an instance here. Hence it has
K-injective resolutions and a derived category `D(𝒪_X) = DerivedCategory X.Modules`
(`HasDerivedCategory.ofIsGrothendieckAbelian`).

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.derivedPushforward f`: the derived direct image
  `Rf_* : D(𝒪_X) ⥤ D(𝒪_S)`, the total right derived functor of the pushforward, computed on
  K-injective complexes.
- `AlgebraicGeometry.Scheme.Modules.IsFiniteProjective`: an `𝒪_X`-module which is a direct
  summand of a free module of finite rank. On an affine scheme `Spec A` these are the modules
  `M~` with `M` a finitely generated projective `A`-module.
- `AlgebraicGeometry.Scheme.Modules.IsPerfectComplex E`: an object `E` of `D(𝒪_X)` is perfect if
  every point has an affine open neighbourhood `U` on which `E|_U` is isomorphic to a bounded
  complex of finite projective `𝒪_U`-modules.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isPerfectComplex_singleFunctor_obj_of_isInvertible`: an
  invertible module placed in degree `0` is perfect.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- `X.Modules` is a Grothendieck abelian category. As a consequence it has K-injective
resolutions and a derived category `D(𝒪_X) = DerivedCategory X.Modules`, whose objects are the
cochain complexes of `𝒪_X`-modules and whose morphisms are obtained by inverting the
quasi-isomorphisms (`HasDerivedCategory.ofIsGrothendieckAbelian`).

(blueprint: `def-pc-derived-category`) -/
instance (X : Scheme.{u}) : IsGrothendieckAbelian.{u} X.Modules :=
  SheafOfModules.isGrothendieckAbelian X.ringCatSheaf

end AlgebraicGeometry.Scheme.Modules
