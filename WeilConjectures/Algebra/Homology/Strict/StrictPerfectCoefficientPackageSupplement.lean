/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

import Mathlib.Algebra.Category.ModuleCat.Products
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackage

/-!
# Strict-perfect coefficient packages

Source: the Weil conjectures blueprint, proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).

## Main definitions

- `SheafOfModules.StrictPerfectCoefficientPackage`: the chosen degreewise splittings.
- `SheafOfModules.StrictPerfectCoefficientRepresentation`: a bounded localized model.
- `SheafOfModules.IsLocallyStrictPerfectComplex` and `SheafOfModules.IsPerfectOnRingedSite`:
  local perfectness of complexes and perfectness of derived objects.
- `ModuleCat.StrictPerfectCoefficientPackage`: the global ring-module version.
- `ModuleCat.StrictPerfectCoefficientPackage.constant`: its associated constant sheaf package.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

end SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

attribute [instance] CategoryTheory.module_overFunctor_preservesZero

end SheafOfModules

namespace ModuleCat

variable {Λ : Type u} [CommRing Λ]

end ModuleCat

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (Λ : Type u) [CommRing Λ]

attribute [instance] strictPerfectConstantPresheaf_additive

attribute [instance] strictPerfectConstantSheaf_additive

end SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (Λ : Type u) [CommRing Λ]

attribute [instance] strictPerfectConstantFiniteFreeComparison_isIso

end SheafOfModules

namespace ModuleCat

variable {Λ : Type u} [CommRing Λ]

end ModuleCat
