/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate

/-! # Reflection and unit equations under localization

Source: Stacks Tag 099M, localization step; Mathlib's fully faithful precomposition API.
(blueprint: lem-weil-pbc-koszul-localization-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory

