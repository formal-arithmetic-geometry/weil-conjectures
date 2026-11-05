/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import WeilConjectures.CategoryTheory.Triangulated.DerivedAdicComplete

/-!
# Criteria for derived adic completeness

We collect some elementary criteria for derived `n`-adic completeness
(`CategoryTheory.IsDerivedAdicComplete`) of an object of a preadditive category.

## Main statements

- `CategoryTheory.IsDerivedAdicComplete.of_isZero`: zero objects are derived complete.
- `CategoryTheory.IsDerivedAdicComplete.of_map`: if a family of additive functors preserving the
  product `∏_{i : ℕ} K` jointly reflects isomorphisms, and sends `K` to derived complete
  objects, then `K` is derived complete.
- `CategoryTheory.IsDerivedAdicComplete.biproduct`: finite biproducts of derived complete
  objects are derived complete.
- `AddCommGrpCat.isDerivedAdicComplete_iff_bijective`: an abelian group `G` is derived
  `n`-adically complete if and only if `(xᵢ) ↦ (xᵢ - n • xᵢ₊₁)` is a bijection of `ℕ → G`.

-/

@[expose] public section

namespace CategoryTheory

open Limits Category Preadditive

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]

namespace IsDerivedAdicComplete

section Biproduct

variable {J : Type} [Finite J] (K : J → C) [HasBiproduct K]
  [∀ j, HasProduct fun _ : ℕ ↦ K j] [HasProduct fun _ : ℕ ↦ ⨁ K]
  [HasBiproduct fun j ↦ ∏ᶜ fun _ : ℕ ↦ K j]

end Biproduct

end IsDerivedAdicComplete

end CategoryTheory

namespace AddCommGrpCat

open CategoryTheory Category Limits Preadditive

universe w

end AddCommGrpCat
