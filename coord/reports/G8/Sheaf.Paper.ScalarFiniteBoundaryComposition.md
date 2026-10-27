## What changed

Added the named endpoint-witness reduction `scalarFiniteBoundary_boundaryEquality` in
`ScalarFiniteBoundaryComposition.lean`. The original composition theorem now extracts
ordinary equality from its `finiteBoundaryEquality` witnesses using `eq_of_heq`.
The item node records the new proof dependency, and a node was added for the split
endpoint-witness statement.

## Proved and sorry left

The original `scalarFiniteBoundary_composition` theorem is proved from the endpoint
witnesses. One sorry remains in `scalarFiniteBoundary_boundaryEquality`; it is the
endpoint transport and exact finite-evaluation calculation recorded by node
`lem-sfb-scalar-finite-boundary-composition-endpoints`.

## No longer needed

None. All imports and stated dependencies remain on the route used by the endpoint
calculation.

## Where the brief, the DAG or earlier work was wrong

The original DAG treated the endpoint transports and the homogeneous equality as one
Lean step. The library's `finiteBoundaryEquality` explicitly records heterogeneous
endpoint witnesses, so the endpoint-witness proposition is a separate intermediate
statement needed before extracting the displayed equality.

## New nodes

`lem-sfb-scalar-finite-boundary-composition-endpoints` records the finiteBoundaryEquality
endpoint calculation and is attached to the new named theorem in the item module.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ScalarFiniteBoundaryComposition": "f19e080e5eed79dd50907100b6efafab9fa33a94"}, "results": {"Sheaf.Paper.TowerScalarFiniteBoundary": {"hash": "aca96c6ab8d0c649810512019228408581265645", "status": "OK"}}, "seconds": 121, "time": "2026-10-28T05:26:43+0800", "transitive": 0, "version": 1}
```

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
