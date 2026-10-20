# MvPolynomial.exists_finite_homogeneous_generators

## Reason

Retirement item in coord/retire-items.tsv, authorized by the human's 2026-10-20
hand-off. The Sheaf module duplicates the complete proved upstream theorem.
The only signature difference is naming an unused existential proof binder.

## Old

From Sheaf.RingTheory.FiniteHomogeneousGenerators:

```lean
theorem exists_finite_homogeneous_generators {k : Type u} [Field k]
    {M : Type v} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    [Module.Finite (MvPolynomial (Fin 2) k) M]
    (ℳ : ℤ → AddSubgroup M) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : M),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℳ j →
        s • x ∈ ℳ ((n : ℤ) + j)) :
    ∃ (r : ℕ) (d : Fin r → ℤ) (m : Fin r → M)
      (hm : ∀ i, m i ∈ ℳ (d i))
      (f : (Fin r →₀ MvPolynomial (Fin 2) k) →ₗ[MvPolynomial (Fin 2) k] M),
      Function.Surjective f ∧
      (∀ i, f (Finsupp.single i 1) = m i) ∧
      (∀ (i : Fin r) (n : ℕ) (s : MvPolynomial (Fin 2) k),
        s ∈ homogeneousSubmodule (Fin 2) k n →
          f (s • Finsupp.single i 1) ∈ ℳ ((n : ℤ) + d i))
```

## New

Use the existing declaration in WeilConjectures.RingTheory.FiniteHomogeneousGenerators:

```lean
theorem exists_finite_homogeneous_generators {k : Type u} [Field k]
    {M : Type v} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    [Module.Finite (MvPolynomial (Fin 2) k) M]
    (ℳ : ℤ → AddSubgroup M) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : M),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℳ j →
        s • x ∈ ℳ ((n : ℤ) + j)) :
    ∃ (r : ℕ) (d : Fin r → ℤ) (m : Fin r → M)
      (_ : ∀ i, m i ∈ ℳ (d i))
      (f : (Fin r →₀ MvPolynomial (Fin 2) k) →ₗ[MvPolynomial (Fin 2) k] M),
      Function.Surjective f ∧
      (∀ i, f (Finsupp.single i 1) = m i) ∧
      (∀ (i : Fin r) (n : ℕ) (s : MvPolynomial (Fin 2) k),
        s ∈ homogeneousSubmodule (Fin 2) k n →
          f (s • Finsupp.single i 1) ∈ ℳ ((n : ℤ) + d i))
```

Withdraw the duplicate Sheaf module. The upstream module is unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.FiniteHomogeneousGenerators | K2 | Withdraw duplicate module. |
| Sheaf.RingTheory.GradedKernelInternal | unclaimed | Replace its private proof import by the upstream twin; all declarations and proof bodies remain identical. |

The current downstream scan finds only GradedKernelInternal, both directly and
transitively. The retirement table's FiniteGradedModuleLowerBound and GradedFreeCover
consumers have already been retired; their upstream modules already import the twin.
No target statement or definition changes. The existing DAG node is attached to the
equivalent upstream theorem, preserving its statement and proof steps.

The returned packet fe0bdad7fe predated the concurrent GradedKernelFinite
retirement in be63bcda32a. This repair takes GradedKernelInternal as currently
landed, including its upstream GradedKernelFinite import and corresponding proof
call, and changes only the finite-generator import. Thus the concurrent proof
adaptation is preserved verbatim. The refreshed consumer compiled on the server
through lcompile.py (exit 0, 2.8 seconds).

## Status

landed 20261020T153010-L-2862177 2026-10-20 (merge of deliver/K2/Sheaf.RingTheory.FiniteHomogeneousGenerators)
