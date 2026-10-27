## What changed

The core theorem now assembles `TransportCoreData` from three explicitly separated
subproblems.  `ExceptionalRingTransportCoreReconstruction` packages the shift proofs
and endpoint reconstructions, while `ExceptionalRingTransportCorePostData` packages the
transported functors, adjunctions, evaluation comparisons, and integral-left comparison.
The core file chooses the coherent integral operations and realizations using
`integralCompactificationSystemRealization` and assembles the record.

## Proved and sorry left

Closed the original hole `exists_exceptional_transport_core_data` by a real record
assembly.  Added two strictly smaller named subproblem holes:
`exists_exceptional_transport_reconstructions` in
`ExceptionalRingTransportCoreReconstruction.lean` (node
`new-lem-sf-exceptional-ring-transport-reconstructions`) and
`exists_exceptional_transport_post_data` in `ExceptionalRingTransportCorePostData.lean`
(node `new-lem-sf-exceptional-ring-transport-post-data`).

## No longer needed

The original core proof plan's direct dependencies
`lem-sf-exceptional-system-transport` and
`lem-pur-normalized-reconstruction-adjunction-calculus` are no longer imported directly
by the core module; they remain dependencies of the split post-data and reconstruction
subproblems.  The prior unsplit core proof route is replaced by the two named subproblems.

## Where the brief, the DAG or earlier work was wrong

The original node treated the full transport record as one indivisible construction,
although its reconstruction/shift choices and its remaining functor/comparison fields
are independent strictly smaller packages.  The DAG and module have been updated to
record this decomposition.

## New nodes

`new-lem-sf-exceptional-ring-transport-reconstructions` records the reconstruction and
shift package.  `new-lem-sf-exceptional-ring-transport-post-data` records the remaining
transported functor and comparison package.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalRingTransportCoreData": "1b08da23874f674af9875d03fd176d0d9ca38d25", "Sheaf.Paper.ExceptionalRingTransportCorePostData": "d78432a93e47aea56c7aa7771f6c3dacc7356eb7", "Sheaf.Paper.ExceptionalRingTransportCoreReconstruction": "97117b29062089e316f192d7e9687762f18e2ced"}, "results": {"Sheaf.Paper.ExceptionalRingTransportCoreLaws": {"hash": "ea2ac12046cedb8db17e8e767a47c877e21110a1", "status": "OK"}}, "seconds": 19, "time": "2026-10-28T05:38:18+0800", "transitive": 0, "version": 1}
```

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
