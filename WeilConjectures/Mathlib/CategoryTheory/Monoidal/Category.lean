/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Tensor powers of an object of a monoidal category

For an object `X` of a monoidal category `C` and `n : ℕ`, this file defines the `n`-th tensor
power `X ^⊗ n`, by recursion on `n` from `X ^⊗ 0 = 𝟙_ C` and `X ^⊗ (n + 1) = X ^⊗ n ⊗ X`, and
gives the isomorphisms making `n ↦ X ^⊗ n` a monoid homomorphism up to coherent isomorphism.

## Main definitions

- `CategoryTheory.MonoidalCategory.tensorPow`, with notation `X ^⊗ n`: the `n`-th tensor power.

## Main results

- `CategoryTheory.MonoidalCategory.tensorPowOneIso`: `X ^⊗ 1 ≅ X`.
- `CategoryTheory.MonoidalCategory.tensorPowAddIso`: `X ^⊗ (m + n) ≅ X ^⊗ m ⊗ X ^⊗ n`.
- `CategoryTheory.MonoidalCategory.tensorPowIso`: isomorphic objects have isomorphic tensor
  powers.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The `n`-th tensor power `X ^⊗ n = X ⊗ ⋯ ⊗ X` of an object of a monoidal category, with the
convention that the empty tensor power is the tensor unit. -/
def tensorPow (X : C) : ℕ → C
  | 0 => 𝟙_ C
  | n + 1 => tensorPow X n ⊗ X

@[inherit_doc] scoped infixr:80 " ^⊗ " => tensorPow

variable (X Y : C)

@[simp]
lemma tensorPow_zero : X ^⊗ 0 = 𝟙_ C := rfl

@[simp]
lemma tensorPow_succ (n : ℕ) : X ^⊗ (n + 1) = X ^⊗ n ⊗ X := rfl

/-- The first tensor power of `X` is `X`. -/
def tensorPowOneIso : X ^⊗ 1 ≅ X := λ_ X

variable {X Y}

/-- Isomorphic objects have isomorphic tensor powers. -/
def tensorPowIso (e : X ≅ Y) : ∀ n : ℕ, X ^⊗ n ≅ Y ^⊗ n
  | 0 => Iso.refl _
  | n + 1 => tensorIso (tensorPowIso e n) e

variable (X)

/-- Tensor powers turn addition of exponents into the tensor product. -/
def tensorPowAddIso : ∀ m n : ℕ, X ^⊗ (m + n) ≅ X ^⊗ m ⊗ X ^⊗ n
  | m, 0 => (ρ_ (X ^⊗ m)).symm
  | m, n + 1 => tensorIso (tensorPowAddIso m n) (Iso.refl X) ≪≫ α_ _ _ _

end CategoryTheory.MonoidalCategory
