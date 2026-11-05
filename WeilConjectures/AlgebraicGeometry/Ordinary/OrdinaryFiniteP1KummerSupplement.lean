/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarComparison.RawModuleScalarDerivedPullbackIso
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Kummer

/-!
# Canonical arrows for the ordinary finite projective-line calculation

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/thm-amb-p1-decomposition.md and
thm-amb-p1-adjunction.md; Stacks Project, Tags 03PL and 03FD
(blueprint: def-asd-ordinary-finite-p1-kummer-class).

## Main definitions

* `ordinaryFiniteRootMap`: scalar extension of roots of unity.
* `ordinaryFiniteClass`: realization of a module-derived class in abelian cohomology.
* `ordinaryFiniteP1KummerClass`: the scalar Kummer class of the specified `O(1)`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor ChangeOfRings

namespace AlgebraicGeometry.Etale

-- Reuse the proposition instances already stored in the ordinary derived category.
-- This keeps the canonical localization data identical before taking object maps.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] ModuleCat.extendScalars
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors
  Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor

attribute [local instance 100000] ordinaryFiniteDerivedCategoryInstance

set_option backward.isDefEq.respectTransparency false in
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor

attribute [local irreducible] ordinaryFiniteExtHomEquiv

attribute [local irreducible]
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
  Scheme.finiteEtaleTwistScalar

attribute [local irreducible] ordinaryFiniteRootMap Sheaf.H.map

end AlgebraicGeometry.Etale
