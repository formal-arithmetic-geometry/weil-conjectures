/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.Algebra.DirectSum.Module

/-!
# The grading of the symmetric algebra

Source: Stacks Project, Algebra, Section 00DM, tensor algebra
(blueprint: lem-weil-pbc-symmetric-algebra-graded).
-/

universe u v

namespace SymmetricAlgebra

/-- Source: Stacks Project, Algebra, Section 00DM
(blueprint: lem-weil-pbc-symmetric-algebra-graded).
The kernel of the tensor-to-symmetric quotient is the commutator ideal `J`.
Tensor degree `n` is the `n`th power of the range of `TensorAlgebra.ι`;
symmetric degree `n` is its image under `algHom`.

Proof (the node's seven steps):
1. Use `TensorAlgebra.gradedAlgebra` (lem-weil-pbc-tensor-algebra-graded) to decompose
   tensors uniquely into finitely many homogeneous terms.
2. Write each element of `J` as a finite sum of `a * (ι x * ι y - ι y * ι x) * b`.
   Decompose `a` and `b` and expand. Each resulting term lies in `J` and has
   degree `p + 2 + q`, by multiplicativity of the tensor grading.
3. Collect equal degrees. Uniqueness in the tensor grading shows that each component
   belongs to `J`; hence `J` is the internal direct sum of its intersections with the grades.
4. The quotient map sends pure tensors to products of `SymmetricAlgebra.ι`
   (lem-weil-pbc-symmetric-algebra-universal-property). These span the image of each grade;
   degrees zero and one are respectively `R • 1` and the range of `ι`.
5. Lift a symmetric-algebra element to the tensor algebra and project its finite decomposition.
6. Lift the differences of two finite homogeneous decompositions to tensors of the same
   degrees. Their sum lies in `J`; Step 3 puts every component in `J`, so all differences vanish.
7. Lift two homogeneous symmetric elements. Their tensor product lies in degree `n + m`;
   applying the quotient map gives the multiplicative inclusion. -/
theorem graded_by_tensor_images (R : Type u) (M : Type v)
    [CommRing R] [AddCommGroup M] [Module R M] :
    DirectSum.IsInternal (fun n : ℕ =>
      ((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ n).comap
        (LinearMap.ker (algHom R M).toLinearMap).subtype) ∧
    (∀ n : ℕ,
      ((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ n).map
          (algHom R M).toLinearMap =
        Submodule.span R
          {s | ∃ x : Fin n → M, s = (List.ofFn (fun i => ι R M (x i))).prod}) ∧
    (((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ 0).map
        (algHom R M).toLinearMap = Submodule.span R {1}) ∧
    (((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ 1).map
        (algHom R M).toLinearMap = (ι R M).range) ∧
    DirectSum.IsInternal (fun n : ℕ =>
      ((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ n).map
        (algHom R M).toLinearMap) ∧
    (∀ n m : ℕ,
      (((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ n).map
          (algHom R M).toLinearMap) *
        (((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ m).map
          (algHom R M).toLinearMap) ≤
        ((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ (n + m)).map
          (algHom R M).toLinearMap) := by
  sorry

end SymmetricAlgebra
