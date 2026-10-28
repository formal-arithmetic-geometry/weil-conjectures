## What changed

Proved `WeilConjectures.IntegralHom.twoTermFreeHomTensor_coordinate_unique` in
`Sheaf.Algebra.Homology.TwoTermFreeHomTensorCoordinateMap`. The proof applies the total tensor
coproduct and Hom-complex product universal properties, then equates the two signed formulas.
All existing declaration signatures and the definition of `IsSignedHomTensor` are preserved.
The uniqueness node now records this extensionality argument.

Added the completely proved general helper `WeilConjectures.IntegralHom.tensorHomEvaluation_ext`
in `Sheaf.Algebra.Homology.TensorHomEvaluationExt`. Its proved private helper shows that
identity-slice evaluation detects presheaf maps into internal Hom. The sheafification adjunction
then reduces equality of maps from a sheaf tensor to evaluation on presheaf pure tensors.
The helper abstracts over the sheafification instances. Profiling identified expensive
conversion checks around the monoidal tensor comparison: abstracting those instances and
avoiding unfolding reduced the combined file from 93 to 77 seconds. The remaining proved
helper is therefore in its own module so that each file meets the per-file compile limit.
No shared definition or attribute changes.

Validation: `lcompile.py --all` compiled the helper in 33.1 seconds and the item in 50.3 seconds,
with no errors or warnings.

The item adds proof-only imports of `WeilConjectures.Algebra.Homology.HomComplexComponents`
and the new helper module. Expanded the existing existence proof in words and corrected its
blueprint tags to the actual existing coordinate-existence node.

## Proved and sorry left

Original holes: 2. Holes closed: 1. Holes added: 0. Holes remaining: 1.

- Proved `WeilConjectures.IntegralHom.twoTermFreeHomTensor_coordinate_unique`
  (node `lem-sf-two-term-free-hom-tensor-coordinate-uniqueness`).
- Remaining: `WeilConjectures.IntegralHom.twoTermFreeHomTensor_coordinate_exists`
  (node `lem-sf-two-term-free-hom-tensor-coordinate-existence`). Its original statement is
  retained with one named `sorry`; no part of this obligation is split off again.
- Added and proved `WeilConjectures.IntegralHom.tensorHomEvaluation_ext`
  (node `lem-sf-tensor-hom-evaluation-ext`). Its private helper is also completely proved.

This is a partial proof delivery. Moving a proved helper into another file adds no unfinished
statement and does not decompose the existence obligation.

## No longer needed

No imports, modules or nodes are pruned from the item as a whole. For uniqueness, the
finite-support decomposition, the two identifications with the unit, and the construction
of an isomorphism are unnecessary. The unchanged theorem retains these hypotheses for callers.
Existence still requires the finite-free calculation, so its dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The uniqueness node's old proof repeated the existence construction. Uniqueness follows
instead from universal properties and the two evaluation formulas, even for arbitrary Q.
The proof uses pure tensors before sheafification and all identity slices; it never assumes
that a sheaf-tensor section is a sum of global pure tensors. Naturality provides every further
slice component. No target or intermediate statement is changed.

The old coordinate-existence docstring tags referred to a nonexistent node with an extra
`components` segment; they now point to `lem-sf-two-term-free-hom-tensor-coordinate-existence`.

## New nodes

`lem-sf-tensor-hom-evaluation-ext` records the completely proved tensor-to-Hom evaluation
criterion in `Sheaf.Algebra.Homology.TensorHomEvaluationExt`. This is the universal-property
step on one tensor summand and one Hom-product factor. It is independent of complex degrees,
signs, finite support and the main existence theorem. Zero modules, the zero coefficient ring
and an empty site are covered by the same universal-property proof. No new hole is added. The local elaboration setup is documented in
`coord/changes/two-term-hom-tensor-coordinate-local-elaboration.md`; no consumer adaptation is
needed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Algebra.Homology.TensorHomEvaluationExt": "ef808581d7ca350231faaccc3db250db7c3f2448", "Sheaf.Algebra.Homology.TwoTermFreeHomTensorCoordinateMap": "8444b51954b1dbd24be661de854f496253e05a2b"}, "results": {"Sheaf.Algebra.Homology.TwoTermFreeHomTensorComponents": {"hash": "22fd0dad2b2b496a9244bac3c6b8126cf794caa5", "status": "OK"}}, "seconds": 23, "time": "2026-10-28T12:22:22+0800", "transitive": 0, "version": 1}
```

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
