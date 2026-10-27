## What changed

Marked `WeilConjectures.completedPullbackTensor_evaluation_cube_model` as
`STATEMENT-DISPUTED`.  Its binder `ν` ranges over an arbitrary natural
isomorphism, while the hypotheses only normalize the canonical finite tensor
comparison.  The conclusion depends on `ν`, so the supplied assumptions do not
suffice to determine the asserted equality.

## Proved and sorry left

No holes were closed.  The existing hole in
`completedPullbackTensor_evaluation_cube_model` remains, because the statement
is underdetermined as written.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The DAG statement says “with an arbitrary finite tensor comparison ν”, but the
right hand side changes with `ν` and no normalization condition on `ν` is
assumed.  The parent currently supplies the canonical
`finitePullbackTensorConstructionIso`; the theorem should either fix `ν` to
that comparison or add the componentwise normalization hypothesis identifying
`ν` with it.  As written, quantifying over arbitrary `ν` would force all such
isomorphisms to have equal components, which is not a consequence of the
listed assumptions.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CompletedPullbackTensorEvaluationCube": "5bea46e70c7c60f91238c0a4e55791c40eae92c8"}, "results": {}, "time": "2026-10-27T23:24:09+0800", "transitive": 0, "version": 1}
```

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
