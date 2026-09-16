/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# The free module on a type is spanned by the tautological family

`ModuleCat.free R` sends a type `I` to the free `R`-module on `I`, whose tautological family of
elements is `ModuleCat.freeMk`. This file records that this family spans the free module.
-/

@[expose] public section

universe u

namespace ModuleCat

/-- **The free module on a type is spanned by its tautological family**: the elements
`ModuleCat.freeMk i` span `(ModuleCat.free R).obj I`. -/
theorem span_range_freeMk (R : Type u) [Ring R] (I : Type u) :
    Submodule.span R (Set.range (freeMk (R := R) (X := I))) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun f ↦ ?_
  induction f using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add f g hf hg => exact Submodule.add_mem _ hf hg
  | single a b =>
      rw [show (Finsupp.single a b : I →₀ R) = b • freeMk a from
        (Finsupp.smul_single_one a b).symm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end ModuleCat
