## What changed

Split the scalar transition proof into a normalized core transition and its completed tensor square, then assembled the original theorem from those two named statements. The target module now compiles with no inline `sorry`; the two strict substeps retain the unfinished mathematical obligations as named theorem statements.

## Proved and sorry left

Closed the original theorem `WeilConjectures.podReindexingTensorCoefficientTransition` by assembling the core and tensor clauses. Added the named theorem holes `WeilConjectures.podReindexingTensorCoefficientTransition_core` and `WeilConjectures.podReindexingTensorCoefficientTransition_tensor` (one `sorry` each).

## No longer needed

None. The original module's import remains necessary for the transition structure and its Laws definition; the two new modules use only the declarations required by their split statements.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the normalized pure, reduction, limit, and completed tensor squares into one theorem, while the available declarations expose them as separate construction stages. The proof was therefore split into the core three squares and the tensor square so that the target can be assembled without an inline proof hole.

## New nodes

- `lem-pod-reindexing-tensor-coefficient-transition-core`
- `lem-pod-reindexing-tensor-coefficient-transition-tensor`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingTensorCoefficientTransition": "9bf9dc2f5757ae32029131de124af21585a47dfd", "Sheaf.Paper.PodReindexingTensorCoefficientTransitionCore": "76da0c7e824467bfced3911ffb710ac507235537", "Sheaf.Paper.PodReindexingTensorCoefficientTransitionTensor": "099b9a2b414017559f2dbd2b5374c15fc79f40d4"}, "results": {}, "time": "2026-10-28T07:11:08+0800", "transitive": 0, "version": 1}
```

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
