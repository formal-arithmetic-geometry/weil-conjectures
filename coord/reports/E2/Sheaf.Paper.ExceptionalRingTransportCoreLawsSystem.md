## What changed

The system-law theorem now assembles three strictly smaller law statements: the
support identity, the adjunction comparison, and the paired reduction comparisons.
The three new theorem modules are imported proof-only by
`ExceptionalRingTransportCoreLawsSystem`; its public statement and structure are
unchanged. Each isolated theorem records the corresponding strict-system
transport calculation and remains available for independent proof work.

## Proved and sorry left

The hole in `exists_exceptional_transport_core_system_laws` is closed by a real
constructor proof from the three isolated law theorems. Three strictly smaller
holes are added:

- `exists_exceptional_transport_core_system_support_law` in
  `ExceptionalRingTransportCoreLawsSystemSupport.lean`;
- `exists_exceptional_transport_core_system_adjunction_law` in
  `ExceptionalRingTransportCoreLawsSystemAdjunction.lean`;
- `exists_exceptional_transport_core_system_reduction_laws` in
  `ExceptionalRingTransportCoreLawsSystemReduction.lean`.

No `sorry` occurs in a definition.

## No longer needed

The original single proof step in the system-law node is replaced by the three
isolated steps. No existing import or unit-level route is pruned; the public
`ExceptionalRingTransportCoreData` import remains required by all theorem
signatures.

## Where the brief, the DAG or earlier work was wrong

`TransportCoreData` contains arbitrary object, functor, and comparison fields,
without compatibility equations. Therefore the four equations in the system-law
package cannot be derived directly from that record. The original one-step DAG
proof plan has been refined into three independent strict-system transport
calculations, with the paired endpoint reductions kept together because they use
the same reconstruction-counit argument.

## New nodes

- `lem-sf-exceptional-ring-transport-core-system-support-law`, stated by
  `exists_exceptional_transport_core_system_support_law`.
- `lem-sf-exceptional-ring-transport-core-system-adjunction-law`, stated by
  `exists_exceptional_transport_core_system_adjunction_law`.
- `lem-sf-exceptional-ring-transport-core-system-reduction-laws`, stated by
  `exists_exceptional_transport_core_system_reduction_laws`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalRingTransportCoreLawsSystem": "4165610bc155c7566a70f987503df48599e484ad", "Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemAdjunction": "770c08c984cbcd9718cfc33d3d30564b319efa15", "Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemReduction": "5ff474c8ac27f502c85c04dbb33f531c193d0546", "Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupport": "9d306bdd90ed0d93d725f36f40984d20361f5644"}, "results": {}, "time": "2026-10-28T08:00:58+0800", "transitive": 0, "version": 1}
```

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
