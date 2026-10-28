## What changed

Updated `Sheaf.SixFunctors.OpenScalarAdjunctionCounit` so
`coefficient_factored_aux` combines two applications of the new one-coefficient package
statement `coefficient_factored_single`. The original conjunction hole is therefore reduced
to a strictly smaller one-coefficient theorem with the same geometric hypotheses and no
second coefficient ring or coefficient map.

## Proved and sorry left

`coefficient_factored_aux` is closed by a real conjunction proof from
`coefficient_factored_single` at `E,m` and `L,n`. One sorry remains in
`coefficient_factored_single`, whose node is
`lem-coef-open-scalar-adjunction-counit-factored-single`.

## No longer needed

No imports, declarations, or previously declared proof dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

No error was found. The existing factored-aux node has been updated to record the
one-coefficient reduction used by the Lean proof.

## New nodes

`lem-coef-open-scalar-adjunction-counit-factored-single` records the strictly smaller
one-coefficient package theorem and its proof plan. Its node file is included in the
sandbox delivery.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenScalarAdjunctionCounit": "dc2ab31677e7ef7b1feb870f60a91e3d5e88cd6a"}, "results": {}, "time": "2026-10-28T07:53:52+0800", "transitive": 0, "version": 1}
```

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
