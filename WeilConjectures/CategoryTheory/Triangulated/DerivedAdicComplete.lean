/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# Derived adic completeness

Let `C` be a preadditive category, `K : C` an object with a countable product
`P = ∏_{i : ℕ} K`, and `n : ℤ`. Let `s : P ⟶ P` be the shift with `s ≫ π_i = π_{i+1}`.
By Milnor's description of derived limits, the derived limit of the tower
`⋯ --n--> K --n--> K` is the fibre of `𝟙 - n • s : P ⟶ P`. Hence `K` is *derived
`n`-adically complete* (i.e. `R lim (⋯ --n--> K --n--> K) = 0`, see Stacks 091N, 091Q) if and
only if `𝟙 - n • s` is an isomorphism. We take this as a purely categorical definition.

## Main definitions

- `CategoryTheory.adicTowerShift`: the shift `s : ∏ᵢ K ⟶ ∏ᵢ K`.
- `CategoryTheory.IsDerivedAdicComplete`: `K` is derived `n`-adically complete if
  `𝟙 - n • adicTowerShift K` is an isomorphism.
- `CategoryTheory.isDerivedAdicComplete`: the corresponding `ObjectProperty`.
- `CategoryTheory.powerTriangleOneSubZSMulAdicTowerShift`: `𝟙 - n • adicTowerShift` as an
  endomorphism of the countable power `CategoryTheory.powerTriangle T` of a triangle.

## Main statements

- `CategoryTheory.IsDerivedAdicComplete.isZero_of_isIso_zsmul_id`: derived Nakayama: if `K` is
  derived `n`-adically complete and `n` acts invertibly on `K`, then `K` is zero.
- `CategoryTheory.IsDerivedAdicComplete.map`: preservation by additive functors preserving the
  relevant countable product.
- `CategoryTheory.IsDerivedAdicComplete.of_distTriang₁₂` (and variants): two out of three for
  distinguished triangles in a pretriangulated category.
- `CategoryTheory.IsDerivedAdicComplete.shift`: stability under shifts.

-/

@[expose] public section

namespace CategoryTheory

open Limits Category Preadditive

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section Shift

variable (K : C) [HasProduct (fun _ : ℕ ↦ K)]

end Shift

section Preadditive

variable [Preadditive C]

namespace IsDerivedAdicComplete

end IsDerivedAdicComplete

end Preadditive

section Pretriangulated

open Pretriangulated

variable [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [HasCountableProducts C]

variable [HasZeroObject C] [Pretriangulated C]

namespace IsDerivedAdicComplete

end IsDerivedAdicComplete

end Pretriangulated

end CategoryTheory
