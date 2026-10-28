## What changed

Refactored the proved homogeneous extraction into the private helper
`finiteBoundaryEquality_comp`, which converts the heterogeneous endpoint witnesses
into the displayed composition equality. The endpoint transport theorem remains the
single unresolved calculation.

## Proved and sorry left

`scalarFiniteBoundary_composition` is proved from
`scalarFiniteBoundary_boundaryEquality` using the new helper. One `sorry` remains in
`scalarFiniteBoundary_boundaryEquality`; it is the scalar adjunction, exact finite
evaluation, and endpoint uniqueness calculation recorded by
`lem-sfb-scalar-finite-boundary-composition-endpoints`.

## No longer needed

None. The existing import and proof dependencies remain necessary for the endpoint
calculation.

## Where the brief, the DAG or earlier work was wrong

No statement or dependency correction was found. Direct simplification and the
available generic evaluation declarations do not prove the endpoint calculation;
the existing endpoint split is retained rather than duplicating it under another
name.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ScalarFiniteBoundaryComposition": "717c22cd138a942fdfae5e585eed44cac8c75636"}, "results": {"Sheaf.Paper.TowerScalarFiniteBoundary": {"hash": "aca96c6ab8d0c649810512019228408581265645", "status": "OK"}}, "seconds": 123, "time": "2026-10-28T08:03:02+0800", "transitive": 0, "version": 1}
```

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
