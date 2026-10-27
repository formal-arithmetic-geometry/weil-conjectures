## What changed

Proved `exists_exceptional_transport_for_operations` by assembling two strictly
smaller interfaces. `ExceptionalRingTransportCoreData` supplies the object,
functor, adjunction, reconstruction, evaluation-isomorphism, and integral-left
realization fields. `ExceptionalRingTransportCoreLaws` supplies the support,
adjunction, evaluation, and proper/open normalization laws. The core module
imports both proof-only interfaces and packages their witnesses into
`ExceptionalIntegralScalar.Transported`.

## Proved and sorry left

The original hole in `exists_exceptional_transport_for_operations` is closed by
real Lean assembly. Two strictly simpler split-off declarations remain sorry:

- `exists_exceptional_transport_core_data` in node
  `lem-sf-exceptional-ring-transport-core-data`;
- `exists_exceptional_transport_core_laws` in node
  `lem-sf-exceptional-ring-transport-core-laws`.

No sorry occurs inside a definition or private declaration.

## No longer needed

The core proof no longer imports the three original construction interfaces
directly; they remain transitive dependencies of the two split-off interfaces.
No additional declared node is pruned.

## Where the brief, the DAG or earlier work was wrong

The prior core node treated the entire `Transported` record as one construction
obligation even though its data fields and compatibility laws are independently
assembled by the two stages of the stated proof. The delivered proof makes that
separation explicit while preserving the unit route and the exact target
statement.

## New nodes

`lem-sf-exceptional-ring-transport-core-data` records existence of the strict
transport data fields. `lem-sf-exceptional-ring-transport-core-laws` records
existence of the compatibility and normalization laws for those data fields.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalRingTransportCore": "87222536a47dc08a48ed436e6a8378b42f61ec3c", "Sheaf.Paper.ExceptionalRingTransportCoreData": "0594ce4c32d960081d992cae1f47df4460c80fab", "Sheaf.Paper.ExceptionalRingTransportCoreLaws": "ea2ac12046cedb8db17e8e767a47c877e21110a1"}, "results": {}, "time": "2026-10-28T03:43:00+0800", "transitive": 0, "version": 1}
```

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
