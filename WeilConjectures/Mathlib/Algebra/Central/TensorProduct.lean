/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Central.TensorProduct
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Base change of central simple algebras

Let `A` be a central simple algebra over a field `K` and `F` a field extension of `K`. Then
`F ⊗[K] A` is a central simple algebra over `F`.

## Main statements

- `Algebra.IsCentral.baseChange`: `F ⊗[K] A` is central over `F`.
- `IsSimpleRing.tensorProduct_of_isCentral`: `F ⊗[K] A` is simple.

## Implementation notes

Both proofs write an element of `F ⊗[K] A` in coordinates `∑ fⱼ ⊗ aⱼ` with respect to a
`K`-basis `(fⱼ)` of `F`, and use that commutators with `1 ⊗ a` act coordinatewise.
-/

@[expose] public section

open TensorProduct

variable (K F A : Type*) [Field K] [Field F] [Algebra K F] [Ring A] [Algebra K A]

/-- The base change `F ⊗[K] A` of a central `K`-algebra `A` to a field extension `F` is
central over `F`. -/
instance Algebra.IsCentral.baseChange [Algebra.IsCentral K A] :
    Algebra.IsCentral F (F ⊗[K] A) :=
  sorry

/-- The base change `F ⊗[K] A` of a central simple `K`-algebra `A` to a field extension `F`
is simple. -/
instance IsSimpleRing.tensorProduct_of_isCentral [Algebra.IsCentral K A] [IsSimpleRing A] :
    IsSimpleRing (F ⊗[K] A) :=
  sorry
