/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Frobenius-closed bases from a Frobenius-compatible filtration

Let `k` be a perfect field of characteristic `p` and `E` a `k`-algebra which is a field. Suppose
`F : ℕ → Submodule k E` is an exhaustive increasing filtration with `F 0 = k`, such that
`f ∈ F n → f ^ p ∈ F (p * n)` and `f ^ p ∈ F n → f ∈ F (n / p)`. Then `E` has a
*Frobenius-closed* `k`-basis: a family `w : ι → E` such that `1` together with the
`w i ^ p ^ r` form a `k`-basis of `E`.

This is the linear-algebra part of Kuhlmann, *Additive polynomials and their role in the
model theory of valued fields*, Theorem 10 / Lemma 26.
-/

@[expose] public section

universe v

open Submodule

namespace FrobeniusClosedBasis

section LinearAlgebra

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

end LinearAlgebra

section Frobenius

variable {k E : Type*} [Field k] [Field E] [Algebra k E] {p : ℕ} [Fact p.Prime] [CharP E p]

end Frobenius

section Construction

variable {k : Type*} {E : Type v} [Field k] [Field E] [Algebra k E]

end Construction

section Main

variable {k : Type*} {E : Type v} [Field k] [Field E] [Algebra k E]

end Main

end FrobeniusClosedBasis
