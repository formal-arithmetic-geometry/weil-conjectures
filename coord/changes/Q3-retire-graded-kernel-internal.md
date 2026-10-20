# MvPolynomial.graded_kernel_internal_finite

## Reason

The assigned retirement row in coord/retire-items.tsv lists this Sheaf module as a
proved upstream duplicate. The live Sheaf module now has zero holes. Its theorem
has exactly the upstream conclusion but two additional, unused hypotheses:
target scalar compatibility hsmulM and surjectivity hq. Its proof already applies
the same upstream finite-generator and finite-kernel results. Retire this duplicate
and attach its node to the complete adopted theorem. No upstream file is modified.

## Old

From Sheaf.RingTheory.GradedKernelInternal:

```lean
theorem graded_kernel_internal_finite {k : Type u} [Field k]
    {F : Type v} [AddCommGroup F] [Module (MvPolynomial (Fin 2) k) F]
    {M : Type w} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    [Module.Finite (MvPolynomial (Fin 2) k) F]
    [Module.Finite (MvPolynomial (Fin 2) k) M]
    (ℱ : ℤ → AddSubgroup F) (hF : DirectSum.IsInternal ℱ)
    (ℳ : ℤ → AddSubgroup M) (hM : DirectSum.IsInternal ℳ)
    (hsmulF : ∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : F),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℱ j → s • x ∈ ℱ ((n : ℤ) + j))
    (hsmulM : ∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : M),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℳ j → s • x ∈ ℳ ((n : ℤ) + j))
    (q : F →ₗ[MvPolynomial (Fin 2) k] M) (hq : Function.Surjective q)
    (hgraded : ∀ (j : ℤ) (x : F), x ∈ ℱ j → q x ∈ ℳ j) :
    DirectSum.IsInternal (fun j ↦ (ℱ j).comap q.ker.subtype.toAddMonoidHom) ∧
    Module.Finite (MvPolynomial (Fin 2) k) q.ker ∧
    ∃ s : Set q.ker, s.Finite ∧
      (∀ x ∈ s, SetLike.IsHomogeneousElem
        (fun j ↦ (ℱ j).comap q.ker.subtype.toAddMonoidHom) x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = ⊤
```

## New

Use the existing declaration in WeilConjectures.RingTheory.GradedKernelInternal:

```lean
theorem graded_kernel_internal_finite {k : Type u} [Field k]
    {F : Type v} [AddCommGroup F] [Module (MvPolynomial (Fin 2) k) F]
    {M : Type w} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    [Module.Finite (MvPolynomial (Fin 2) k) F]
    [Module.Finite (MvPolynomial (Fin 2) k) M]
    (ℱ : ℤ → AddSubgroup F) (hF : DirectSum.IsInternal ℱ)
    (ℳ : ℤ → AddSubgroup M) (hM : DirectSum.IsInternal ℳ)
    (hsmulF : ∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : F),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℱ j → s • x ∈ ℱ ((n : ℤ) + j))
    (q : F →ₗ[MvPolynomial (Fin 2) k] M)
    (hgraded : ∀ (j : ℤ) (x : F), x ∈ ℱ j → q x ∈ ℳ j) :
    DirectSum.IsInternal (fun j ↦ (ℱ j).comap q.ker.subtype.toAddMonoidHom) ∧
    Module.Finite (MvPolynomial (Fin 2) k) q.ker ∧
    ∃ s : Set q.ker, s.Finite ∧
      (∀ x ∈ s, SetLike.IsHomogeneousElem
        (fun j ↦ (ℱ j).comap q.ker.subtype.toAddMonoidHom) x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = ⊤
```

Withdraw the Sheaf module; its declaration and private helper are duplicates.
The old signature follows by applying the upstream theorem to
`ℱ hF ℳ hM hsmulF q hgraded`, ignoring hsmulM and hq. All universes,
instances, inherited grading expressions, finiteness and spanning conclusions
are identical. No target statement or definition changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.GradedKernelInternal | Q3 | Withdraw the duplicate. |
| Sheaf.RingTheory.GradedSyzygy | already retired | No source or importer remains to adapt. |
| WeilConjectures.RingTheory.GradedSyzygy | unmodified | Already imports and applies the upstream theorem twice; no adaptation. |

The downstream.py scan finds zero downstream modules and only the duplicate's own
declaration as a user. A direct search of lean/Sheaf, lean/WeilConjectures and
quarantine finds no import of the withdrawn module. The DAG parent
lem-sc-p1-graded-syzygy still cites lem-sc-p1-graded-kernel-internal in steps 2 and 3:
this is preserved, now resolved by the upstream Lean attachment. No node is deleted
and no mathematical dependency or unit route is bypassed. The unit record
sk-thm-picard-duality has no realized entry requiring the duplicate module.

Validation: lcompile.py accepts the scratch theorem with the full old signature
and direct upstream application (exit 0, 1.1 seconds). Its axiom set and the
upstream theorem's axiom set are exactly propext, Classical.choice and Quot.sound.
The unchanged upstream GradedSyzygy consumer compiles (exit 0, 2.7 seconds).

## Status

landed 20261020T160259-L-3350377 2026-10-20 (merge of deliver/Q3/Sheaf.RingTheory.GradedKernelInternal)
