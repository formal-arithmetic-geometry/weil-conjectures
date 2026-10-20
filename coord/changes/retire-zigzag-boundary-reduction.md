# HomologicalComplex₂.zigzag_boundary_reduction

## Reason

The Sheaf module is an unused duplicate of the already proved adopted source-library
`HomologicalComplex₂.zigzagBoundary_reduction`. The canonical theorem has exactly the same
hypotheses and conclusion, including the unused row-exactness assumption. Withdraw the duplicate
under brief step 8d and attach its existing DAG node to the canonical theorem. No source-library
file or declaration changes. No definition or target statement changes.

## Old

Module `Sheaf.Algebra.Homology.ZigzagBoundaryReduction`:

```lean
theorem zigzag_boundary_reduction
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (hrow : ∀ (p q : ℕ), 0 < p →
      (ShortComplex.mk ((A.d (p + 1) p).f q) ((A.d p (p - 1)).f q)
        (by rw [← HomologicalComplex.comp_f, A.d_comp_d,
          HomologicalComplex.zero_f])).Exact)
    (n : ℕ) (a : zigzagTotal A n) (ha : a ∈ zigzagCycles A n)
    (hboundary : ∃ y : (A.opcycles 0).X (n + 1),
      (A.opcycles 0).d (n + 1) n y = (A.pOpcycles 0).f n
        (DirectSum.component R (ZigzagIndex n)
          (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2) ⟨(0, n), by simp⟩ a)) :
    ∃ b : zigzagTotal A (n + 1),
      a - zigzagBoundary A n b ∈ zigzagCycles A n ∧
      DirectSum.component R (ZigzagIndex n)
        (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2)
        ⟨(0, n), by simp⟩ (a - zigzagBoundary A n b) = 0
```

## New

The Sheaf module is withdrawn with no declarations. The existing canonical theorem is in
`WeilConjectures.Algebra.Homology.ZigzagBoundaryReduction`:

```lean
theorem zigzagBoundary_reduction
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (hrow : ∀ (p q : ℕ), 0 < p →
      (ShortComplex.mk ((A.d (p + 1) p).f q) ((A.d p (p - 1)).f q)
        (by rw [← HomologicalComplex.comp_f, A.d_comp_d,
          HomologicalComplex.zero_f])).Exact)
    (n : ℕ) (a : zigzagTotal A n) (ha : a ∈ zigzagCycles A n)
    (hboundary : ∃ y : (A.opcycles 0).X (n + 1),
      (A.opcycles 0).d (n + 1) n y = (A.pOpcycles 0).f n
        (DirectSum.component R (ZigzagIndex n)
          (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2) ⟨(0, n), by simp⟩ a)) :
    ∃ b : zigzagTotal A (n + 1),
      a - zigzagBoundary A n b ∈ zigzagCycles A n ∧
      DirectSum.component R (ZigzagIndex n)
        (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2)
        ⟨(0, n), by simp⟩ (a - zigzagBoundary A n b) = 0
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.ZigzagBoundaryReduction | R3 | Withdraw unused duplicate. |

`tools/downstream.py Sheaf.Algebra.Homology.ZigzagBoundaryReduction --uses
zigzag_boundary_reduction` reports zero downstream modules and only the declaration itself
as a use of the old name. Repository-wide searches over `lean/Sheaf` and `lean/WeilConjectures` found no import of the
Sheaf module and no use of `zigzag_boundary_reduction` outside its declaration. Existing users
of the canonical theorem, including `WeilConjectures.Algebra.Homology.ZigzagTrivialIfRowBoundary`,
already import the source-library module and need no changes. The sole DAG attachment is
`new-zigzag-boundary-reduction`, redirected in this packet. The deferred retirement note in
`coord/changes/retire-sheaf-twins-kept-20261020.tsv` has no remaining consumer obstruction.

## Status

landed 20261020T132036-L-1405855 2026-10-20 (merge of deliver/R3/Sheaf.Algebra.Homology.ZigzagBoundaryReduction)
