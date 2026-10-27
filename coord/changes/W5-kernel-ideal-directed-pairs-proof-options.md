# AlgebraicGeometry.Scheme.CommAlgebraSheaf.kernelIdeal_directed_pairs

## Reason

The completed proof needs Lean to unfold the underlying algebra module while elaborating
its sectionwise linear maps. Declaration-scoped transparency options permit this. A
second scoped option silences unused-binder warnings for the original statement's
quasi-coherence hypothesis and proof-irrelevant preorder witnesses. Preflight classifies
these new commands as an interface change and requests this record.

## Old

No local option preceded the declaration:

```lean
theorem kernelIdeal_directed_pairs
```

Its complete signature is preserved verbatim in the delivered module and in the node's
unchanged `lean.statement` field. The old body was `by sorry`.

## New

```lean
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
```

These options precede the unchanged theorem and apply to that declaration alone.
The transparency option is also scoped separately to each new private helper.
There is no file-wide option, new public declaration, public import change, or changed
definition. The body is a complete proof from existing declarations. Statement meaning
and consumer-visible interfaces are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.KernelIdealDirectedPairs | W5 | Proof elaboration and lint only |

`tools/downstream.py Sheaf.AlgebraicGeometry.KernelIdealDirectedPairs --uses
kernelIdeal_directed_pairs` reports zero downstream modules and the item itself as
the only textual use. The unfinished DAG parents remain needed and unchanged.
No existing statement or definition changes, so no consumer adaptation is required.

## Status

landed 20261023T132222-L-2236838 2026-10-23 (merge of deliver/W5/Sheaf.AlgebraicGeometry.KernelIdealDirectedPairs)
