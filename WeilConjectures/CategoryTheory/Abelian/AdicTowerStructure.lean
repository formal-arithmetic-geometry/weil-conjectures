/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# `ℓ`-adic towers in abelian categories

An `ℓ`-adic tower in an abelian category `C` (`CategoryTheory.AdicTowerStructure`) is a tower
`(Gₙ)` together with maps `ιₙₘ : Gₙ ⟶ Gₙ₊ₘ` such that `0 ⟶ Gₙ ⟶ Gₙ₊ₘ ⟶ Gₘ ⟶ 0` (the second map
being the transition map) is short exact, and such that the transition map `Gₙ₊ₘ ⟶ Gₙ` followed
by `ιₙₘ` is multiplication by `ℓᵐ`.

Such a structure exists (`CategoryTheory.AdicTowerStructure.ofIsColimit`) on a tower `(Gₙ)` with
`ℓⁿ Gₙ = 0` whose transition maps `G_k ⟶ Gₙ` are cokernels of `ℓⁿ : G_k ⟶ G_k` (that is,
`G_k ⊗ ℤ/ℓⁿ ≅ Gₙ`) and which is flat (`G_{n+m} --ℓⁿ--> G_{n+m} --ℓᵐ--> G_{n+m}` is exact): for
instance a tower of flat sheaves of `ℤ/ℓⁿ`-modules `Fₙ` with `Fₙ₊₁ ⊗ ℤ/ℓⁿ ≅ Fₙ`. Then `ιₙₘ` is
induced by multiplication by `ℓᵐ`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type*} [Category C] [Abelian C]

namespace AdicTowerStructure

variable {G : ℕᵒᵖ ⥤ C} {ℓ : ℕ}

end AdicTowerStructure

end CategoryTheory
