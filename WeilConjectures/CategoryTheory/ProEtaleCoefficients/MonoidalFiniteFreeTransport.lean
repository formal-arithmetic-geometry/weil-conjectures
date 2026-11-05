/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian

/-!
# Additive monoidal transport of a finite free internal module

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md, third sentence.
(blueprint: lem-sfb-monoidal-finite-free-transport)

The biproducts are taken in the existing category of internal modules. Their actions
are componentwise, as constructed in `CategoryTheory.ModuleObjects.Abelian`.
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ v₁ v₂

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

-- Mathlib exposes this finite-to-binary conversion as a theorem, not an instance.
attribute [local instance] CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts

namespace CategoryTheory.Functor

end CategoryTheory.Functor
