## What changed

Proved `normalized_reindexing_tensor_integral` by reducing it to the
representative tensor square with the inverse target realization tensorator
postcomposed, then cancelling that isomorphism with `cancel_mono`. Added the
single lower-level module `Sheaf.Paper.AdicReindexingTensorIntegralCancelled`
and its DAG node for the fixed-field representative calculation.

## Proved and sorry left

- Closed `WeilConjectures.AdicQbarRealization.normalized_reindexing_tensor_integral`.
- Added one strictly lower-level split-off sorry:
  `WeilConjectures.AdicQbarRealization.normalized_reindexing_tensor_integral_cancelled`.

## No longer needed

No planned proof dependency was removed. The target keeps its public
`AdicRealizationFamilyData` import; the proof-only import is the new cancelled
representative module.

## Where the brief, the DAG or earlier work was wrong

The target's proof plan describes the final cancellation but had no Lean
statement for the representative square before cancellation. The new node
records that intermediate equation explicitly, while the target proof performs
the actual categorical cancellation.

## New nodes

- `lem-sf-adic-reindexing-tensor-integral-cancelled`, implemented by
  `Sheaf.Paper.AdicReindexingTensorIntegralCancelled`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicReindexingTensorIntegral": "5a526b1b502c78c399d3f393f04b2c647e58a2ca", "Sheaf.Paper.AdicReindexingTensorIntegralCancelled": "f55a1d56b89b73567ecb5d69e137f5d2b332bc13"}, "results": {"Sheaf.Paper.AdicReindexingTensorCompatibility": {"hash": "3fc3054fe0f10bb8ef1b4e3e0e8a52cf2f9b19c7", "status": "OK"}}, "seconds": 26, "time": "2026-10-28T08:22:09+0800", "transitive": 0, "version": 1}
```

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
