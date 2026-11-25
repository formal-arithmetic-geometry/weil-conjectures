/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.LinearAlgebra.TensorAlgebra.Grading

/-!
# The grading of the symmetric algebra

The images in `Sym(M)` of the tensor-power grades `(range ι)^n` of the tensor algebra form an
internal grading of the symmetric algebra, and the kernel of `TensorAlgebra R M → Sym(M)` is
graded by its intersections with these grades.

## References

* [Stacks Project, Section 00DM](https://stacks.math.columbia.edu/tag/00DM)
-/

@[expose] public section

universe u v

namespace SymmetricAlgebra

open scoped DirectSum Pointwise

/-- The image in `Sym(M)` of the `n`-th tensor-power grade is spanned by the products of `n`
elements `ι x`. -/
theorem graded_span_pure_tensors (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] :
    ∀ n : ℕ,
      ((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ n).map
          (algHom R M).toLinearMap =
        Submodule.span R
          {s | ∃ x : Fin n → M, s = (List.ofFn (fun i => ι R M (x i))).prod} := by
  classical
  intro n
  rw [Submodule.map_pow, ← LinearMap.range_comp]
  change (ι R M).range ^ n = _
  rw [Submodule.pow_eq_span_pow_set]
  congr 1
  ext s
  rw [Set.mem_pow_iff_prod]
  constructor
  · rintro ⟨f, hf, rfl⟩
    choose x hx using hf
    exact ⟨x, by simp [List.prod_ofFn, hx]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨fun i => ι R M (x i), fun i => ⟨x i, rfl⟩, by simp [List.prod_ofFn]⟩

/-- The degree-zero image in `Sym(M)` is spanned by `1`. -/
theorem graded_degree_zero (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] :
    ((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ 0).map
        (algHom R M).toLinearMap = Submodule.span R {1} := by
  rw [pow_zero, Submodule.map_one, Submodule.one_eq_span]

/-- The degree-one image in `Sym(M)` is the range of `ι`. -/
theorem graded_degree_one (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] :
    ((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ 1).map
        (algHom R M).toLinearMap = (ι R M).range := by
  rw [pow_one, ← LinearMap.range_comp]
  rfl

/-- The images in `Sym(M)` of the tensor-power grades form an internal direct sum. -/
theorem graded_image_internal (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] :
    DirectSum.IsInternal (fun n : ℕ =>
      ((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ n).map
        (algHom R M).toLinearMap) := by
  classical
  simp only [Submodule.map_pow, ← LinearMap.range_comp]
  change DirectSum.IsInternal (fun n : ℕ => (ι R M).range ^ n)
  let D : ℕ → Submodule R (SymmetricAlgebra R M) := fun n => (ι R M).range ^ n
  let j : M →ₗ[R] ⨁ n : ℕ, D n :=
    DirectSum.lof R ℕ (fun n => D n) 1 ∘ₗ
      (ι R M).codRestrict _ (fun m => by
        simpa only [D, pow_one] using LinearMap.mem_range_self (ι R M) m)
  have hj (m : M) : j m = DirectSum.of (fun n => D n) 1
      ⟨ι R M m, by simpa only [D, pow_one] using
        LinearMap.mem_range_self (ι R M) m⟩ := rfl
  let g := lift j
  have hg (n : ℕ) (x : D n) : g x = DirectSum.of (fun n => D n) n x := by
    obtain ⟨x, hx⟩ := x
    dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
    change x ∈ (ι R M).range ^ n at hx
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      rw [AlgHom.commutes, DirectSum.algebraMap_apply]
      rfl
    | add x y i hx hy ihx ihy =>
      rw [map_add, ihx, ihy, ← map_add]
      rfl
    | mem_mul m hm i x hx ih =>
      obtain ⟨m, rfl⟩ := hm
      rw [map_mul, ih]
      change lift j (ι R M m) * _ = _
      rw [lift_ι_apply, hj, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)
  have hleft : (DirectSum.coeAlgHom D).comp g = AlgHom.id R (SymmetricAlgebra R M) := by
    ext m
    change DirectSum.coeAlgHom D (lift j (ι R M m)) = ι R M m
    rw [lift_ι_apply, hj, DirectSum.coeAlgHom_of]
  let h : GradedAlgebra D := GradedAlgebra.ofAlgHom D g hleft hg
  exact DirectSum.Decomposition.isInternal D

/-- The kernel of `TensorAlgebra R M → Sym(M)` is the internal direct sum of its intersections
with the tensor-power grades. -/
theorem graded_kernel_internal (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] :
    DirectSum.IsInternal (fun n : ℕ =>
      ((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ n).comap
        (LinearMap.ker (algHom R M).toLinearMap).subtype) := by
  classical
  let T : ℕ → Submodule R (TensorAlgebra R M) :=
    fun n => (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ n
  let f := (algHom R M).toLinearMap
  let J := LinearMap.ker f
  let K : ℕ → Submodule R J := fun n => (T n).comap J.subtype
  have hT : DirectSum.IsInternal T := DirectSum.Decomposition.isInternal T
  have hS := (graded_image_internal R M).submodule_iSupIndep
  change DirectSum.IsInternal K
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s v hv hsum n hn
    apply Subtype.ext
    exact (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero T).mp
      hT.submodule_iSupIndep s (fun n => (v n : TensorAlgebra R M)) hv
      (by simpa using congrArg Subtype.val hsum) n hn
  · apply top_unique
    intro x _
    let d := DirectSum.decompose T (x : TensorAlgebra R M)
    have hd : ∑ n ∈ d.support, (d n : TensorAlgebra R M) = x :=
      DirectSum.sum_support_decompose T (x : TensorAlgebra R M)
    have hf : ∑ n ∈ d.support, f (d n) = 0 := by
      rw [← map_sum, hd]
      exact x.property
    have hz (n : ℕ) : f (d n) = 0 := by
      by_cases hn : n ∈ d.support
      · exact (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hS
          d.support (fun n => f (d n))
          (fun n _ => Submodule.mem_map_of_mem (d n).property) hf n hn
      · have hn : d n = 0 := by simpa using hn
        rw [hn]
        exact map_zero f
    let v : ℕ → J := fun n => ⟨d n, hz n⟩
    have hx : ∑ n ∈ d.support, v n = x := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using hd
    rw [← hx]
    exact Submodule.sum_mem _ (fun n _ =>
      (le_iSup K n) (show v n ∈ K n from (d n).property))

/-- The product of the degree-`n` and degree-`m` images in `Sym(M)` lies in the degree-`(n + m)`
image. -/
theorem graded_image_mul (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] :
    ∀ n m : ℕ,
      (((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ n).map
          (algHom R M).toLinearMap) *
        (((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ m).map
          (algHom R M).toLinearMap) ≤
        ((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ (n + m)).map
          (algHom R M).toLinearMap := by
  intro n m
  rw [← Submodule.map_mul, ← pow_add]

/-- The symmetric algebra is graded by the images of the tensor-power grades: the kernel of
`TensorAlgebra R M → Sym(M)` is graded, each image is spanned by products of `n` elements `ι x`,
the images in degrees zero and one are `R • 1` and `range ι`, and the images form an internal
direct sum compatible with multiplication. -/
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
  exact ⟨graded_kernel_internal R M, graded_span_pure_tensors R M,
    graded_degree_zero R M, graded_degree_one R M,
    graded_image_internal R M, graded_image_mul R M⟩

end SymmetricAlgebra
