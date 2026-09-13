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
the comparison isomorphisms `X ^⊗ 1 ≅ X`, `X ^⊗ (m + n) ≅ X ^⊗ m ⊗ X ^⊗ n` and
`X ^⊗ (m * n) ≅ (X ^⊗ m) ^⊗ n`.

## Main definitions

- `CategoryTheory.MonoidalCategory.tensorPow`, with notation `X ^⊗ n`: the `n`-th tensor power.

## Main results

- `CategoryTheory.MonoidalCategory.tensorPowOneIso`: `X ^⊗ 1 ≅ X`.
- `CategoryTheory.MonoidalCategory.tensorPowAddIso`: `X ^⊗ (m + n) ≅ X ^⊗ m ⊗ X ^⊗ n`.
- `CategoryTheory.MonoidalCategory.tensorPowMulIso`: `X ^⊗ (m * n) ≅ (X ^⊗ m) ^⊗ n`.
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

-- The precedence is that of `^`, of which this is the monoidal analogue.
@[inherit_doc] scoped infixr:75 " ^⊗ " => tensorPow

variable (X : C)

@[simp]
lemma tensorPow_zero : X ^⊗ 0 = 𝟙_ C := rfl

@[simp]
lemma tensorPow_succ (n : ℕ) : X ^⊗ (n + 1) = X ^⊗ n ⊗ X := rfl

/-- The first tensor power of `X` is `X`. -/
def tensorPowOneIso : X ^⊗ 1 ≅ X := λ_ X

/-- Tensor powers turn addition of exponents into the tensor product. -/
def tensorPowAddIso : ∀ m n : ℕ, X ^⊗ (m + n) ≅ X ^⊗ m ⊗ X ^⊗ n
  | m, 0 => (ρ_ (X ^⊗ m)).symm
  | m, n + 1 => tensorIso (tensorPowAddIso m n) (Iso.refl X) ≪≫ α_ _ _ _

/-- Tensor powers turn multiplication of exponents into iteration. -/
def tensorPowMulIso : ∀ m n : ℕ, X ^⊗ (m * n) ≅ (X ^⊗ m) ^⊗ n
  | _, 0 => Iso.refl _
  | m, n + 1 => tensorPowAddIso X (m * n) m ≪≫ tensorIso (tensorPowMulIso m n) (Iso.refl _)

variable {X}

/-- Isomorphic objects have isomorphic tensor powers. -/
def tensorPowIso {Y : C} (e : X ≅ Y) : ∀ n : ℕ, X ^⊗ n ≅ Y ^⊗ n
  | 0 => Iso.refl _
  | n + 1 => tensorIso (tensorPowIso e n) e

@[simp]
lemma tensorPowIso_zero {Y : C} (e : X ≅ Y) : tensorPowIso e 0 = Iso.refl _ := rfl

@[simp]
lemma tensorPowIso_succ {Y : C} (e : X ≅ Y) (n : ℕ) :
    tensorPowIso e (n + 1) = tensorIso (tensorPowIso e n) e :=
  rfl

@[simp]
lemma tensorPowIso_refl : ∀ n : ℕ, tensorPowIso (Iso.refl X) n = Iso.refl _
  | 0 => rfl
  | n + 1 => by
    rw [tensorPowIso_succ, tensorPowIso_refl n]
    ext
    simp

end CategoryTheory.MonoidalCategory
