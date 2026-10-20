# MvPolynomial.graded_kernel_finite

## Reason

The assigned retirement in coord/retire-items.tsv identifies a duplicate of the
upstream graded-kernel theorem. The Sheaf version requires three extra hypotheses
that its proof never uses: scalar compatibility on the target, finite homogeneous
generation of the target, and surjectivity. The upstream theorem proves precisely
the same conjunction without those hypotheses, by the same two-step argument.
Retire the duplicate and use the adopted theorem directly.

## Old

In Sheaf.RingTheory.GradedKernelFinite:

```lean
theorem graded_kernel_finite {k : Type u} [Field k]
    {F : Type v} [AddCommGroup F] [Module (MvPolynomial (Fin 2) k) F]
    {M : Type w} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    (ℱ : ℤ → AddSubgroup F) (hF : DirectSum.IsInternal ℱ)
    (ℳ : ℤ → AddSubgroup M) (_hM : DirectSum.IsInternal ℳ)
    (_hsmulF : ∀ (n : ℕ) (j : ℤ) (f : MvPolynomial (Fin 2) k) (x : F),
      f ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℱ j → f • x ∈ ℱ ((n : ℤ) + j))
    (_hsmulM : ∀ (n : ℕ) (j : ℤ) (f : MvPolynomial (Fin 2) k) (x : M),
      f ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℳ j → f • x ∈ ℳ ((n : ℤ) + j))
    (_hfiniteF : ∃ s : Set F, s.Finite ∧ (∀ x ∈ s, SetLike.IsHomogeneousElem ℱ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = ⊤)
    (_hfiniteM : ∃ s : Set M, s.Finite ∧ (∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = ⊤)
    (q : F →ₗ[MvPolynomial (Fin 2) k] M) (_hq : Function.Surjective q)
    (_hgraded : ∀ (j : ℤ) (x : F), x ∈ ℱ j → q x ∈ ℳ j) :
    @Submodule.IsHomogeneous ℤ (AddSubgroup F) (MvPolynomial (Fin 2) k) F
      _ _ _ q.ker ℱ _ _ _ hF.chooseDecomposition ∧
    ∃ s : Set F, s.Finite ∧ (∀ x ∈ s, SetLike.IsHomogeneousElem ℱ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = q.ker
```

## New

No declaration remains in the retired Sheaf module. Use the existing declaration
in WeilConjectures.RingTheory.GradedKernelFinite:

```lean
theorem graded_kernel_finite {k : Type u} [Field k]
    {F : Type v} [AddCommGroup F] [Module (MvPolynomial (Fin 2) k) F]
    {M : Type w} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    (ℱ : ℤ → AddSubgroup F) (hF : DirectSum.IsInternal ℱ)
    (ℳ : ℤ → AddSubgroup M) (hM : DirectSum.IsInternal ℳ)
    (hsmulF : ∀ (n : ℕ) (j : ℤ) (f : MvPolynomial (Fin 2) k) (x : F),
      f ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℱ j → f • x ∈ ℱ ((n : ℤ) + j))
    (hfiniteF : ∃ s : Set F, s.Finite ∧ (∀ x ∈ s, SetLike.IsHomogeneousElem ℱ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = ⊤)
    (q : F →ₗ[MvPolynomial (Fin 2) k] M)
    (hgraded : ∀ (j : ℤ) (x : F), x ∈ ℱ j → q x ∈ ℳ j) :
    @Submodule.IsHomogeneous ℤ (AddSubgroup F) (MvPolynomial (Fin 2) k) F
      _ _ _ q.ker ℱ _ _ _ hF.chooseDecomposition ∧
    ∃ s : Set F, s.Finite ∧ (∀ x ∈ s, SetLike.IsHomogeneousElem ℱ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = q.ker
```

The DAG node's Lean attachment now names that existing upstream theorem. Its
mathematical statement, proof steps, dependencies and unit route stay identical.
No source-library file is changed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.GradedKernelInternal | unclaimed | Redirect the private proof import and remove the three obsolete arguments at its one application. Keep every declaration signature and visibility unchanged. |
| Sheaf.RingTheory.GradedNakayamaFree | already retired on the current base | No file or import remains to adapt. |

tools/downstream.py reports exactly one downstream module and one external
declaration user: Sheaf.RingTheory.GradedKernelInternal. The direct source search
agrees. tools/import_direction.py confirms that the upstream import introduces
no cycle. The upstream GradedKernelInternal and GradedNakayamaFree already
import the upstream theorem and require no adaptation. The consumer's hsmulM and
hq hypotheses remain in its unchanged signature and are explicitly acknowledged
in its proof to avoid unused-variable warnings. Its target-finiteness instance
also remains unchanged. The upstream conclusion agrees literally with the old
conclusion; hence the consumer's statement and downstream meanings do not change.

## Status

landed 20261020T135417-L-1820494 2026-10-20 (merge of deliver/N2/Sheaf.RingTheory.GradedKernelFinite)
