/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Enough injectives for sheaves of modules on a scheme

Source: Stacks Project, Injectives, Lemma 01DI
(blueprint: lem-weil-pbc-scheme-modules-enough-injectives).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Every sheaf of modules on a scheme embeds into an injective sheaf of modules.

Source: Stacks Project, Injectives, Lemma 01DI
(blueprint: lem-weil-pbc-scheme-modules-enough-injectives).

Proof:
The opens of `X` form a small site. Apply the proved upstream theorem
`SheafOfModules.isGrothendieckAbelian` to the structure sheaf `X.ringCatSheaf`.
This makes `X.Modules` a Grothendieck abelian category, with the same universe as
its underlying site. Mathlib's Grothendieck-category enough-injectives instance
then gives the required injective presentations. This uses no hypothesis on `X`
beyond being a scheme, and also applies when its underlying space is empty. -/
theorem enoughInjectives (X : Scheme.{u}) : EnoughInjectives X.Modules := by
  have : IsGrothendieckAbelian.{u} X.Modules :=
    SheafOfModules.isGrothendieckAbelian X.ringCatSheaf
  infer_instance

end AlgebraicGeometry.Scheme.Modules
