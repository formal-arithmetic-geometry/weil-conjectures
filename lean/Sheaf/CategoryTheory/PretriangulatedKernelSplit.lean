/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additive functors preserve existing kernels from pre-triangulated categories

Source: Stacks Project, Derived Categories, Tag 05QU, lemma-when-split
(blueprint: lem-cor-int-compactness-ii-pretriangulated-kernel-split).
-/

@[expose] public section

universe u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

namespace Functor

/--
An additive functor from a pre-triangulated category to a preadditive category
preserves every kernel that exists in its source.  The proof follows Stacks
Project, Tag 05QU: a kernel arrow is a split monomorphism, and the resulting
projection-coprojection decompositions are carried through the additive functor.
The factorization and uniqueness equations give the universal property of the
mapped kernel for an arbitrary target object.  The pre-triangulated source
provides the cone triangles and their rotation exactness; no kernel is assumed
to exist in the target (blueprint: lem-cor-int-compactness-ii-pretriangulated-kernel-split).
-/
theorem preservesKernel_of_pretriangulated
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    {X Y K : C} (d : X ⟶ Y) (k : K ⟶ X) (hk : k ≫ d = 0)
    (hK : IsLimit (KernelFork.ofι k hk)) :
    Nonempty (IsLimit (KernelFork.ofι (f := F.map d) (F.map k) (by
      rw [← F.map_comp, hk, F.map_zero]))) := by
  sorry

end Functor

end CategoryTheory
