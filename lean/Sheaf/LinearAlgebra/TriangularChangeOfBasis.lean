/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Triangular changes of basis with unit diagonal

Source: Stacks Project, Algebra, Lemma Tag 00MT (`lemma-add-trivial-complex`),
proof, the two changes of basis (blueprint: lem-weil-pbc-triangular-change-of-basis).
-/

@[expose] public section

universe u v

namespace Module.Basis

/-- A triangular coordinate matrix with unit diagonal gives a new basis.
Source: Stacks Project, Algebra, Tag 00MT, proof, the two changes of basis
(blueprint: lem-weil-pbc-triangular-change-of-basis).

Proof: The given basis identifies the module with the finite coordinate module, and the
coordinate map sending its standard vectors to `v` has coefficients `t`. For `m = 0` the
empty family is already a basis. In the upper triangular case, solve for the old basis
vectors starting at the last index and descending: each diagonal unit permits solving for
that vector after all later vectors have been obtained. For independence, inspect a relation
in its first coordinate, then proceed upwards; each diagonal unit forces the corresponding
coefficient to vanish. In the lower triangular case, solve for the old basis vectors from
the first index upwards, and inspect relations from the last coordinate downwards. In both
cases `v` spans and is linearly independent, hence determines a basis. All four steps use
`def-weil-pbc-free-module`, represented by Mathlib's `Module.Free` and `Module.Basis`. -/
theorem exists_basis_of_triangular_unit_diagonal
    {R : Type u} [CommRing R] {F : Type v} [AddCommGroup F] [Module R F]
    {m : ℕ} (b : Module.Basis (Fin m) R F) (v : Fin m → F)
    (t : Fin m → Fin m → R)
    (hcoords : ∀ k, v k = ∑ l : Fin m, t k l • b l)
    (htriangular : (∀ k l, l < k → t k l = 0) ∨ (∀ k l, k < l → t k l = 0))
    (hdiag : ∀ k, IsUnit (t k k)) :
    ∃ c : Module.Basis (Fin m) R F, ∀ k, c k = v k := by
  sorry

end Module.Basis
