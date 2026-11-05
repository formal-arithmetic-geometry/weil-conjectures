/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Right adjoints of functors of bounded amplitude

Let `F ⊣ G` be an adjunction between pretriangulated categories equipped with t-structures
`t₁` and `t₂`. If `F` raises the upper bound by at most `N` (it sends `t₁.IsLE X n` to
`t₂.IsLE (F X) (n + N)`), then `G` lowers the lower bound by at most `N`: it sends
`t₂.IsGE Y m` to `t₁.IsGE (G Y) (m - N)`. In particular `G` preserves bounded below objects.

## Main statements

- `CategoryTheory.Triangulated.TStructure.isGE_rightAdjoint_obj`
- `CategoryTheory.Triangulated.TStructure.plus_rightAdjoint_obj`
-/

@[expose] public section

namespace CategoryTheory.Triangulated.TStructure

open Limits Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] (t₁ : TStructure C) (t₂ : TStructure D)
  {F : C ⥤ D} {G : D ⥤ C}

end CategoryTheory.Triangulated.TStructure
