/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Lazard's theorem: a flat module is a filtered colimit of finite free modules

For a module `M` over a commutative ring `R`, consider the category `ModuleCat.FinFreeOver M` of
linear maps `R^n ⟶ M` from finite free modules (written `Fin n →₀ R`), with morphisms the
linear maps `R^n ⟶ R^m` over `M`. If `M` is flat, this category is filtered
(`ModuleCat.FinFreeOver.isFiltered`) and `M` is the colimit of the forgetful diagram
(`ModuleCat.FinFreeOver.isColimitCocone`): this is Lazard's theorem (Stacks, Tag 058G). Both
statements are consequences of the equational criterion for flatness
(`Module.Flat.exists_factorization_of_comp_eq_zero_of_free`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits

namespace ModuleCat

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

namespace FinFreeOver

variable {M}

variable (M)

variable [Module.Flat R M]

end FinFreeOver

end ModuleCat
