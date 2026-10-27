## What changed

Rewrote the completed `commonProjectionPullbackTensorCompatibility` proof to pass its
finite-stage representative formula explicitly to
`projectionTensorComparisonCompatible_of_representative_formula`. The theorem statement,
imports, and all declarations remain unchanged.

## Proved and sorry left

The upper declaration `commonProjectionPullbackTensorCompatibility` is proved. The
existing lower declaration `projectionTensorComparisonCompatible_of_representative_formula`
remains one `sorry`, unchanged; it is the representative normalization bridge recorded by
node `lem-sf-common-projection-pullback-tensor-representative-bridge`.

## No longer needed

None. The existing representative bridge and all imports remain needed by the proof.

## Where the brief, the DAG or earlier work was wrong

None identified.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CommonProjectionPullbackTensorCompatibility": "b503f852e2e2b1ab0a066af8b12e79a6469fd238"}, "results": {}, "time": "2026-10-28T05:18:47+0800", "transitive": 0, "version": 1}
```

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
