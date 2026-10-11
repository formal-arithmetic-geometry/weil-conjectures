/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.RingTheory.Flat.Basic

/-!
# Filtered colimits of flat modules

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 05UT
(blueprint: lem-weil-pbc-filtered-colimit-flat-modules).
-/

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A filtered colimit of flat modules over a commutative ring is flat.
Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 05UT.
(blueprint: lem-weil-pbc-filtered-colimit-flat-modules)

Proof:
1. By `def-weil-pbc-flat-ring-map`, it suffices to show that tensoring an injective
   linear map `u : N₁ →ₗ[R] N₂` with `colimit F` is injective. Tensor symmetry identifies
   this with injectivity of `1 ⊗ u`; each stage map `fᵢ = 1 ⊗ u` is injective by
   flatness of `F.obj i`.
2. By `lem-weil-pbc-tensor-commutes-with-colimits`, the tensors of `colimit F` with
   `N₁` and `N₂`, with coprojections `pᵢ = μᵢ ⊗ 1` and `qᵢ = μᵢ ⊗ 1`
   (`μᵢ = colimit.ι F i`), are colimits of the stage tensors
   (`def-weil-pbc-category-colimit`). The `fᵢ` commute with the transition maps, and
   `f = 1 ⊗ u` satisfies `f ∘ pᵢ = qᵢ ∘ fᵢ`, as checked on pure tensors.
3. If `f x = 0`, `lem-weil-pbc-filtered-colimit-modules-elementwise` represents
   `x = pᵢ y`. Since `qᵢ (fᵢ y) = 0`, the same lemma gives a transition `a : i → k`
   at which `fᵢ y` becomes zero. Naturality and injectivity of `fₖ` imply that `y`
   becomes zero at `k`, so `x = 0`. Thus `f` is injective and `colimit F` is flat. -/
theorem filteredColimit_flat
    {R : Type u} [CommRing R]
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ ModuleCat.{v} R) [HasColimit F]
    (hflat : ∀ i : I, Module.Flat R (F.obj i)) :
    Module.Flat R (colimit F : ModuleCat.{v} R) := by
  sorry

end ModuleCat
