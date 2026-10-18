/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Sheaf.RingTheory.ReducednessTensorAlgEquiv

/-!
# Reducedness after tensoring with a chosen algebraic closure

Source: Stacks Project, Fields, Tag 09GV (algebraic closures are isomorphic over the
base field), with tensor-product transport of reducedness.
(blueprint: lem-trf-reducedness-tensor-chosen-algebraic-closure).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- Reducedness of a tensor product with an arbitrary chosen algebraic closure is
independent of the choice of closure, and agrees with Mathlib's canonical closure.

Source: Stacks Project, Fields, Tag 09GV, with tensor-product transport of reducedness.
(blueprint: lem-trf-reducedness-tensor-chosen-algebraic-closure).

Proof:
1. By `lem-pc-algebraic-closure-exists-unique` (Stacks Tag 09GV), the chosen closure
   and `AlgebraicClosure k` are isomorphic as field extensions of `k`; choose the
   resulting `k`-algebra equivalence.
2. Apply `lem-trf-reducedness-tensor-alg-equiv` to this equivalence and the identity
   on `A`. The induced tensor-product ring equivalence transports nilpotent elements
   in both directions, so reducedness is equivalent.
-/
theorem isReduced_tensorProduct_chosen_algebraicClosure_iff
    (k : Type u) (A : Type v) (Ω : Type w)
    [Field k] [CommRing A] [Algebra k A]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] :
    IsReduced (A ⊗[k] Ω) ↔
      IsReduced (A ⊗[k] (AlgebraicClosure k)) := by
  sorry

end Algebra
