/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

/-!
# Möbius components of a multiplicative family of idempotents

Let `α` be a lattice with a bottom element in which all intervals are finite, `R` a (not
necessarily commutative) ring and `π : α → R` a family with `π x * π y = π (x ⊓ y)` (for instance
the projectors onto the invariants of a family of normal subgroups). The *Möbius components*
`e k = ∑_{m ≤ k} μ(m, k) • π m` (`IncidenceAlgebra.moebiusComponent`) decompose the `π`:

* `∑_{k ≤ j} e k = π j` (`IncidenceAlgebra.sum_Iic_moebiusComponent`, by Möbius inversion);
* `e k * π m = e k` if `k ≤ m` and `0` otherwise (`IncidenceAlgebra.moebiusComponent_mul`), and
  similarly `π m * e k` (`IncidenceAlgebra.mul_moebiusComponent`);
* `e ⊥ = π ⊥` (`IncidenceAlgebra.moebiusComponent_bot`).

In particular the `e k` are orthogonal idempotents.
-/

@[expose] public section

open Finset

namespace IncidenceAlgebra

variable {α R : Type*} [Lattice α] [OrderBot α] [LocallyFiniteOrder α] [DecidableEq α] [Ring R]

variable {π : α → R}

variable [DecidableLE α]

end IncidenceAlgebra
