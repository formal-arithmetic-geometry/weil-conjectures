# graded component declarations

## Reason

The stage-3 proof decomposes the original conjunction into six named component theorems so the
conjunction can be assembled explicitly. The existing theorem signature is unchanged; the six
public theorem signatures below are additions, each strictly one conjunct of that theorem.
All six component proofs are complete, including kernel internality from the tensor decomposition
and independence of the image grades. The assembled grading theorem has no remaining obligation.

## Old

```lean
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
```

## New

The six added signatures, verbatim in the `SymmetricAlgebra` namespace (universes `u v`):

```lean
theorem graded_kernel_internal (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] :
    DirectSum.IsInternal (fun n : ℕ =>
      ((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ n).comap
        (LinearMap.ker (algHom R M).toLinearMap).subtype)

theorem graded_span_pure_tensors (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] :
    ∀ n : ℕ,
      ((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ n).map
          (algHom R M).toLinearMap =
        Submodule.span R
          {s | ∃ x : Fin n → M, s = (List.ofFn (fun i => ι R M (x i))).prod}

theorem graded_degree_zero (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] :
    ((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ 0).map
        (algHom R M).toLinearMap = Submodule.span R {1}

theorem graded_degree_one (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] :
    ((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ 1).map
        (algHom R M).toLinearMap = (ι R M).range

theorem graded_image_internal (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] :
    DirectSum.IsInternal (fun n : ℕ =>
      ((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ n).map
        (algHom R M).toLinearMap)

theorem graded_image_mul (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] :
    ∀ n m : ℕ,
      (((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ n).map
          (algHom R M).toLinearMap) *
        (((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ m).map
          (algHom R M).toLinearMap) ≤
        ((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ (n + m)).map
          (algHom R M).toLinearMap
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.LinearAlgebra.SymmetricAlgebra.Graded | Y2 | New public component declarations are available. |
| Sheaf.LinearAlgebra.SymmetricAlgebra.DegreeExact | unclaimed | direct importer using graded_by_tensor_images; compiled against the delivered module |

## Status

landed 20261013T022436-L-3223745 2026-10-13 (merge of deliver/Y2/Sheaf.LinearAlgebra.SymmetricAlgebra.Graded)
