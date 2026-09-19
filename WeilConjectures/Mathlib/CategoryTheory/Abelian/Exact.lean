/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# The short exact sequence attached to a monomorphism

A monomorphism `u : G ⟶ H` in an abelian category sits in the short exact sequence
`0 ⟶ G ⟶ H ⟶ coker u ⟶ 0`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **A monomorphism sits in a short exact sequence with its cokernel**:

```text
  0 ⟶ G ⟶ H ⟶ coker u ⟶ 0
```
-/
lemma shortExact_mk_cokernelπ {G H : C} (u : G ⟶ H) [Mono u] :
    (ShortComplex.mk u (cokernel.π u) (by simp)).ShortExact where
  exact := exact_cokernel u

end CategoryTheory.ShortComplex
