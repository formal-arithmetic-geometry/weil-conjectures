/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Additive functors and the single functors to cochain complexes

The isomorphisms `F(A[a]) ≅ F(A)[a]` (`HomologicalComplex.singleMapHomologicalComplex`) are
compatible with the shifts of the single functors.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.Additive]

end CategoryTheory.Functor
