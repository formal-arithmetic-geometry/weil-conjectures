/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.FiniteLocalizationFreeStep
import WeilConjectures.RingTheory.StabilizedFiniteFreeTower

/-! # Finite-free models at finitely many localizations

Source: Stacks Project, Tag 08EE, descending construction in the proof of
lemma-lift-pseudo-coherent (blueprint: lem-sc-finite-localization-free-model).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace DerivedCategory

end DerivedCategory
