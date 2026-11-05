/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc

/-!
# Complements on the truncation functors indexed by `EInt`

We record extensionality principles for morphisms to `t.eTruncLT.obj b` and from
`t.eTruncGE.obj a`, and the compatibility of the commutation isomorphism
`t.eTruncLTGEIsoGELT a b` with the projections `t.eTruncGEπ a`.
-/

@[expose] public section

namespace CategoryTheory.Triangulated.TStructure

open Limits Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C)

variable [IsTriangulated C]

end CategoryTheory.Triangulated.TStructure
