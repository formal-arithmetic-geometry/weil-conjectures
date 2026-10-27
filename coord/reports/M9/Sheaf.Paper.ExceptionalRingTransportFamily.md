## What changed

Proved `exists_exceptional_ring_transport_family` by applying two strictly smaller named construction interfaces: `exists_exceptional_ring_operations` supplies finite and integral operation/left-realization families, and `exists_exceptional_transport_for_operations` packages their normalized transport data. Added the corresponding two Sheaf modules and DAG nodes.

## Proved and sorry left

The item theorem `exists_exceptional_ring_transport_family` is proved. Two strictly simpler split-off declarations remain sorry: `exists_exceptional_ring_operations` in node `lem-sf-exceptional-ring-operations-existence`, and `exists_exceptional_transport_for_operations` in node `lem-sf-exceptional-ring-transport-core`.

## No longer needed

The attempted `ExceptionalRingStageAssembly` route was removed because its import graph passes through `RingCanonicalScalarInvertibility`, creating a cycle back to this item. The proof uses only the two split-off interfaces and the existing integral scalar data module.

## Where the brief, the DAG or earlier work was wrong

The prior direct route through `ExceptionalRingStageAssembly` is cyclic in the current source graph: `ExceptionalRingStageAssembly → ExceptionalRingScalarMates → RingCanonicalScalarInvertibility → ExceptionalRingTransportFamily`. The acyclic decomposition separates operation-family construction from transport packaging.

## New nodes

`lem-sf-exceptional-ring-operations-existence` records the strictly smaller operation and left-realization family construction.

`lem-sf-exceptional-ring-transport-core` records the strictly smaller normalized transport packaging from supplied operation and left-realization families.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalRingOperationsExistence": "112d99338de58cbb647fba5a8c32490772d4cf78", "Sheaf.Paper.ExceptionalRingTransportCore": "ed9fc7758aa9cc288ba28e9d6ed3fe66e0a9a88c", "Sheaf.Paper.ExceptionalRingTransportFamily": "5960d42c061d3c3d87bda0f357d5137c36100426"}, "results": {}, "time": "2026-10-28T01:04:46+0800", "transitive": 0, "version": 1}
```

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
