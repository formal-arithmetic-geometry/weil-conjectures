# ordinaryTensorIso

## Reason

The proof of `canonicalComplexTensorComparison` must unfold the chosen ordinary
tensor witness once to identify it with the witness supplied by
`internal_section_tensor_comparison`. Marking the definition locally irreducible
prevents unrelated elaboration from unfolding it while preserving the existing
definition and public signature.

## Old

```lean
def ordinaryTensorIso (M N : Internal Λ X) :
    (equivalence Λ X).functor.obj (M ⊗ N) ≅
      ((sectionTensor Λ X).obj ((equivalence Λ X).functor.obj M)).obj
        ((equivalence Λ X).functor.obj N) :=
  (internal_section_tensor_comparison (Scheme.ProEt.topology X)
    (condensedRingObj Λ X)).2.choose M N
```

## New

```lean
def ordinaryTensorIso (M N : Internal Λ X) :
    (equivalence Λ X).functor.obj (M ⊗ N) ≅
      ((sectionTensor Λ X).obj ((equivalence Λ X).functor.obj M)).obj
        ((equivalence Λ X).functor.obj N) :=
  (internal_section_tensor_comparison (Scheme.ProEt.topology X)
    (condensedRingObj Λ X)).2.choose M N

attribute [local irreducible] ordinaryTensorIso
```

## Users

`tools/downstream.py Sheaf.Paper.InternalSectionTotalComparison --uses ordinaryTensorIso`
finds only the defining module using this name. The attribute is local to the module;
downstream signatures, definitions and reducibility are unchanged. No target statement
or definition used by a target changes, so no target statement review is reopened.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.InternalSectionTotalComparison` | W8 | The proof unfolds the definition explicitly with `delta`. |

## Status

landed 20261019T034343-L-424586 2026-10-19 (merge of deliver/W8/Sheaf.Paper.InternalSectionTotalComparison)
