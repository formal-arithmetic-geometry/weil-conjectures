/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# Constructible sheaves are compact in `Loc(Dᵇc)`, given the ind-constructible heart

Let `R` be a commutative ring object of sheaves on `X_proét`. Write `IndCons(X, R)` for the
filtered colimits of constructible sheaves of `R`-modules (blueprint `sk-prop-ind-heart`,
`CategoryTheory.ObjectProperty.ind` of `IsConstructibleModuleObject R`), and `Dic(X, R)` for the
complexes with cohomology sheaves in `IndCons(X, R)` (blueprint `sk-cor-ambient-ind-derived`).

We isolate the inputs of blueprints `sk-thm-constructible-compactness` and
`det-prop-int-compactness-compact` on the coefficient ring:

* `AlgebraicGeometry.ProEtale.IsIndConstructibleHeart R` (blueprint `sk-prop-ind-heart` (2),
  `det-prop-int-compactness-compact` (1)): `IndCons(X, R)` is closed in the category of
  `R`-modules under kernels, cokernels, extensions and direct sums;
* `AlgebraicGeometry.ProEtale.HasIndConstructibleExtBound R` (blueprint `sk-cor-ind-heart-ii`):
  for a constructible sheaf `C` there is `d` with `Ext^q(C, B) = 0` for `q > d` and all `B` in
  `IndCons(X, R)`, and `Ext^q(C, -)` commutes with direct sums of objects of `IndCons(X, R)`;
* exactness of countable products of `R`-modules (blueprint `sk-prop-pe-products`), which makes
  `D(X_proét, R)` left complete.

Given these, `Dic(X, R)` is a localizing subcategory containing `Loc(Dᵇc(X, R))`
(`AlgebraicGeometry.ProEtale.localizingClosure_boundedConstructible_le`), and every
constructible sheaf placed in degree `0` is compact in `Loc(Dᵇc(X, R))`
(`AlgebraicGeometry.ProEtale.isCompactObj_singleFunctor_of_isIndConstructibleHeart`): this is the
abstract finite-window argument `DerivedCategory.compactFor_of_homologyProperty`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory ZeroObject

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

/-- The category of `R`-modules has direct sums. -/
instance hasColimitsOfShape_discrete_mod (J : Type (u + 1)) :
    HasColimitsOfShape (Discrete J) (Mod (Sheaf (Scheme.ProEt.topology X) A) R) :=
  have : HasColimitsOfSize.{u + 1, u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) A) R) :=
    IsGrothendieckAbelian.hasColimits _
  HasColimitsOfSize.has_colimits_of_shape _

/-- The derived category `D(X_proét, R)` has direct sums. -/
instance hasColimitsOfShape_discrete_derivedCategory_mod (J : Type (u + 1)) :
    HasColimitsOfShape (Discrete J)
      (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)) :=
  DerivedCategory.hasColimitsOfShape_discrete J

end AlgebraicGeometry.ProEtale
