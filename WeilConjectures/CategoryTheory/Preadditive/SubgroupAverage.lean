/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Preadditive.TraceSplitting
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card

/-!
# Averaging over subgroups in a preadditive category

Let `V` be an object of a preadditive category with an action `ρ : G → End V` of a finite group
(`ρ a ≫ ρ b = ρ (b * a)`, `ρ 1 = 𝟙`) such that `|G|` is invertible on `V`. For a subgroup `H`,
the *average* `avg_H = |H|⁻¹ ∑_{a ∈ H} ρ a` (`CategoryTheory.subgroupAvg`, written as
`[G : H] |G|⁻¹ ∑_{a ∈ H} ρ a` so that only `|G|` needs to be invertible) is the projector onto
the `H`-invariants:

* a morphism to (resp. from) `V` invariant under `H` is fixed by `avg_H`
  (`CategoryTheory.comp_subgroupAvg_of_forall`, `CategoryTheory.subgroupAvg_comp_of_forall`);
* `avg_⊥ = 𝟙`, `avg_⊤ = |G|⁻¹ ∑_a ρ a`;
* `avg_A ≫ avg_B = avg_(A ⊔ B)` for `B` normal (`CategoryTheory.subgroupAvg_comp_subgroupAvg`);
* if `(i, n) ↦ c i * n` is a bijection `I × H ≃ G`, then `avg_H ≫ ∑_i ρ (c i) = |I| • avg_⊤`
  (`CategoryTheory.subgroupAvg_comp_sum`).
-/

@[expose] public section

open CategoryTheory Category Limits Preadditive

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] {G : Type*} [Group G] [Fintype G]

variable {V : C} (ρ : G → (V ⟶ V))

variable {ρ} (hρ : ∀ a b, ρ a ≫ ρ b = ρ (b * a))
include hρ

variable [IsIso (Nat.card G • 𝟙 V)]

end CategoryTheory
