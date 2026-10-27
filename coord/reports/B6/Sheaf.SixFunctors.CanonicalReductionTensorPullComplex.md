## What changed

Added `Sheaf.SixFunctors.CanonicalReductionTensorPullComplexComponent`, whose public
component theorem isolates the degree-`n` ordinary strict-system tensor identity.
The assigned module now imports that theorem and proves its original whole-complex
statement by `HomologicalComplex.Hom.ext` and the component theorem. The original
statement and all binders are unchanged.

## Proved and sorry left

Closed the original body proof of
`WeilConjectures.IntegralSystemRealization.canonicalReductionTensorPullComplex`.
Its proof is a genuine homological-complex extensionality argument from the
component statement.

Added one sorry, strictly simpler than the original target:
`WeilConjectures.IntegralSystemRealization.canonicalReductionTensorPullComplex_component`
(node `lem-sf-canonical-reduction-tensor-pull-complex-component`). It is the
same equality after taking one cochain degree and records the finite pure-tensor
calculation that remains to be proved. No definition contains a sorry.

## No longer needed

No existing import or dependency module is removed. The parent proof no longer
needs to unfold or reason about the strict-system maps directly; those calculations
are isolated in the component node. The parent node's direct proof dependency is
therefore replaced by the component node, while the component retains the ordinary
bridge, strict reduction, sequence comparison, and scalar tensor dependencies needed
for its planned calculation.

## Where the brief, the DAG or earlier work was wrong

The supplied node described a degreewise finite-component and pure-tensor argument,
but the module had no declaration representing that intermediate step. A direct
whole-complex proof would duplicate the homological-complex assembly. The new node
makes the missing degreewise calculation explicit and the assigned theorem reduces
to it by the standard extensionality lemma. No target statement or definition was
changed.

## New nodes

`lem-sf-canonical-reduction-tensor-pull-complex-component` is realized by
`Sheaf.SixFunctors.CanonicalReductionTensorPullComplexComponent`. It states equality
of the two displayed strict-system maps after taking any degree `n`; its source is
the first paragraph of `lem-fix-operation-reduction.proof.md` (Stacks 07A4, 07A6,
0941). Its proof is left as one named sorry for the finite pure-tensor calculation,
with the direct bridge, strict reduction, sequence comparison, and scalar tensor
nodes recorded as dependencies.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CanonicalReductionTensorPullComplex": "c333c8d0c27659891aca8c73a693987384ea6257", "Sheaf.SixFunctors.CanonicalReductionTensorPullComplexComponent": "c77a9802c6ff3ddf2eb4eef7af6225b678f9ec7a"}, "results": {}, "time": "2026-10-28T06:25:47+0800", "transitive": 0, "version": 1}
```

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
