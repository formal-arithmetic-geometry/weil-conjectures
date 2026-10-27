## What changed

Marked `finiteIntrinsicProjectionCompatibility` as `STATEMENT-DISPUTED` in the sandbox.
No proof was added because the quantified family `e` has no compatibility condition across
morphisms of `SixFunctorSpace`.

## Proved and sorry left

No holes were closed. The existing `sorry` in
`finiteIntrinsicProjectionCompatibility` remains, at node
`new-sf-finite-intrinsic-projection-compatibility`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The theorem quantifies over an arbitrary family of objectwise tensor isomorphisms. Its
conclusion compares `e X` and `e Y` along an arbitrary `f : X ⟶ Y`, but the hypotheses
provide no naturality square relating those two isomorphisms. Twisting `e Y` by a natural
automorphism changes the right-hand side while leaving the left-hand side data at `X`
unchanged. The node needs an explicit cross-space naturality/compatibility hypothesis or
a canonical coherent family.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteIntrinsicProjectionCompatibility": "50a2b60e6642755c44fc8734bca6d52fcab333d4"}, "results": {}, "time": "2026-10-28T04:13:54+0800", "transitive": 0, "version": 1}
```

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
