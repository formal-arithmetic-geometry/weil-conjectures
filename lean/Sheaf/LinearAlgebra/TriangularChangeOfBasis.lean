/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block

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

Proof: In the given basis the coordinate matrix of `v` is the transpose of `t`.
Transposition exchanges upper and lower triangularity. In either case its determinant
is the product of the diagonal entries, hence a unit. Mathlib's determinant criterion
then gives linear independence and spanning, from which `Module.Basis.mk` constructs
the basis. This includes `m = 0`, where the empty product is one, and works over any
commutative ring. The basis notion is `def-weil-pbc-free-module`. -/
theorem exists_basis_of_triangular_unit_diagonal
    {R : Type u} [CommRing R] {F : Type v} [AddCommGroup F] [Module R F]
    {m : ℕ} (b : Module.Basis (Fin m) R F) (v : Fin m → F)
    (t : Fin m → Fin m → R)
    (hcoords : ∀ k, v k = ∑ l : Fin m, t k l • b l)
    (htriangular : (∀ k l, l < k → t k l = 0) ∨ (∀ k l, k < l → t k l = 0))
    (hdiag : ∀ k, IsUnit (t k k)) :
    ∃ c : Module.Basis (Fin m) R F, ∀ k, c k = v k := by
  classical
  have hmat : b.toMatrix v = Matrix.transpose t := by
    ext i k
    rw [Module.Basis.toMatrix_apply]
    rw [show v k = ∑ l : Fin m, t k l • b l from hcoords k]
    simp only [map_sum, map_smul, Module.Basis.repr_self]
    simp [Finsupp.single_apply]
  have hdet : IsUnit (b.det v) := by
    rw [Module.Basis.det_apply, hmat]
    rcases htriangular with hu | hl
    · rw [Matrix.det_of_isLowerTriangular _]
      · simp only [Matrix.transpose_apply]
        rw [IsUnit.prod_univ_iff]
        exact hdiag
      · intro i j hij
        exact hu j i hij
    · rw [Matrix.det_of_isUpperTriangular]
      · simp only [Matrix.transpose_apply]
        rw [IsUnit.prod_univ_iff]
        exact hdiag
      · intro i j hij
        exact hl j i hij
  obtain ⟨hli, hspan⟩ := (b.is_basis_iff_det).2 hdet
  exact ⟨Module.Basis.mk hli hspan.ge, fun k =>
    Module.Basis.mk_apply hli hspan.ge k⟩

end Module.Basis
