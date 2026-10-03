/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-!
# Tensor products of reduced algebras over a perfect field

Over a perfect field every reduced algebra is geometrically reduced, so the tensor product of two
reduced algebras is reduced: a product of reduced varieties is reduced.

## Main results

- `isReduced_tensorProduct_of_perfectField`

## Blueprint

- `sk-i-geometry`: products of reduced varieties over a perfect field are reduced.
-/

@[expose] public section

open TensorProduct

/-- Over a perfect field `k`, the tensor product of two reduced `k`-algebras is reduced.
(blueprint: `sk-i-geometry`) -/
theorem isReduced_tensorProduct_of_perfectField (k A B : Type*) [Field k] [PerfectField k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [IsReduced A] [IsReduced B] :
    IsReduced (A ⊗[k] B) := by
  sorry
