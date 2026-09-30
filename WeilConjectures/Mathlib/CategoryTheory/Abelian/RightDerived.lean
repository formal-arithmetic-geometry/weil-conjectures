/-
Copyright (c) 2026 The Weil Conjectures Project Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Additivity of right derived functors

The right derived functors `F.rightDerived n` of an additive functor `F` are additive. This
follows from the additivity of `injectiveResolutions C`.
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D] (F : C ⥤ D) [F.Additive]

instance : F.rightDerivedToHomotopyCategory.Additive :=
  inferInstanceAs (injectiveResolutions C ⋙ F.mapHomotopyCategory _).Additive

/-- The right derived functors of an additive functor are additive. -/
instance (n : ℕ) : (F.rightDerived n).Additive :=
  inferInstanceAs
    (F.rightDerivedToHomotopyCategory ⋙ HomotopyCategory.homologyFunctor D _ n).Additive

end CategoryTheory.Functor
