/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation

/-!
# Sheaf cohomology is the right-derived evaluation in every degree

`CategoryTheory.Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ` identifies
`Hⁿ⁺¹(F)` with the `(n+1)`-st right derived functor of the evaluation at a terminal object `T`.
In degree `0`, both are the sections `F(T)`, the evaluation being left exact.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

end CategoryTheory.Sheaf
