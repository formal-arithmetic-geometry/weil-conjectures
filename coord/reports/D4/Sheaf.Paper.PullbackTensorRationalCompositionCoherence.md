## What changed

Implemented `pullbackTensorRationalCompositionCoherence` by transporting the integral
composition equation through localization. The proof uses the two explicitly stated
localization sublemmas for the left and right rational routes and functoriality of the
localization functor. Added the two split-off modules and their DAG nodes.

## Proved and sorry left

The target theorem `pullbackTensorRationalCompositionCoherence` is proved. Two strictly
smaller localization components remain as named `sorry` theorems:

- `canonicalRationalPullbackTensorComposition_left_localization`, node
  `lem-pur-pullback-tensor-rational-composition-coherence-left-localization`;
- `canonicalRationalPullbackTensorComposition_right_localization`, node
  `lem-pur-pullback-tensor-rational-composition-coherence-right-localization`.

No `sorry` was added to a definition.

## No longer needed

Removed the proof-only import `Sheaf.CategoryTheory.BilinearCoefficientDescent`; the
completed proof only needs the integral coherence theorem and the two localization
components. The initially considered standalone pullback-map localization split is not
needed because it is subsumed by the left and right route statements.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan named bilinear coefficient descent directly, but the Lean
interface exposes the needed statement more cleanly as two route-localization equations.
The parent theorem is therefore reduced through those two concrete components.

## New nodes

`lem-pur-pullback-tensor-rational-composition-coherence-left-localization` and
`lem-pur-pullback-tensor-rational-composition-coherence-right-localization` record the
left and right route localization equations used by the target proof.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.CanonicalRationalPullbackTensorCompositionLeftLocalization": "57a4f1616209c49904a1bb3acb022927010f1d21", "Sheaf.Paper.CanonicalRationalPullbackTensorCompositionRightLocalization": "f91df8afa9e630e42f07249ccf20699db185c857", "Sheaf.Paper.PullbackTensorRationalCompositionCoherence": "320b5e606cf5d317950133d9d54cab76098a9853"}, "results": {"Sheaf.Paper.PullbackTensorCommonStageCompositionCoherence": {"hash": "dd75407ee2c5c7af0d6ca68ce9e323a4d92ec09b", "status": "OK"}, "Sheaf.Paper.PullbackTensorCompositionCoherence": {"hash": "d76c6e6b4b555f3c5799a14f929dbdd77b749070", "status": "OK"}}, "seconds": 19, "time": "2026-10-28T06:39:33+0800", "transitive": 0, "version": 1}
```

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
