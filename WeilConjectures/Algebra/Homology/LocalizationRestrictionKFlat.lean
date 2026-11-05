/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import WeilConjectures.Algebra.Homology.MixedTensorRestrictionComparison
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Flat.Localization

/-! # K-flatness after restricting a localized base

Source: Stacks Project, Tags 06Y6 and 00CS.
(blueprint: lem-pc-localization-restriction-kflat).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

end ModuleCat
