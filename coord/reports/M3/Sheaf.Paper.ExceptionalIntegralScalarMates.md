## What changed

The module now proves `exceptionalIntegralScalarMates_data` by composing two
strictly smaller named construction statements: existence of the `Mates` record
and existence of its complete finite-level `ReductionMates` family.  The two
construction statements remain explicit `sorry` obligations with their own DAG
nodes.  A module option suppresses the pre-existing unused existential-binder
linter warning; it changes no declaration interface.  No imports or existing
declarations were changed.

## Proved and sorry left

The hole in `exceptionalIntegralScalarMates_data` is closed.  The following
holes remain or were split off:

- `exceptionalIntegralScalarMates_data_mates` (node
  `lem-sf-exceptional-integral-scalar-mates-data-mates`): `sorry`.
- `exceptionalIntegralScalarMates_data_reduction` (node
  `lem-sf-exceptional-integral-scalar-mates-data-reduction`): `sorry`.
- `exceptionalIntegralScalarMates_system` remains `sorry` (node
  `lem-sf-exceptional-integral-scalar-mates-system`).

No definitions contain `sorry`; the existing core and final theorem proofs are
unchanged.

## No longer needed

None.  The data proof uses only the two new construction nodes; all imports of
the module remain required by its declarations.

## Where the brief, the DAG or earlier work was wrong

The module's data theorem was left as a large construction hole even though its
conclusion is a direct assembly of two independent existential records.  The
DAG did not expose those two strictly smaller construction obligations, so they
are recorded as the two new nodes below.  The statement itself is unchanged.

## New nodes

`lem-sf-exceptional-integral-scalar-mates-data-mates` records existence of the
fixed `Mates` record.  `lem-sf-exceptional-integral-scalar-mates-data-reduction`
records existence of the reduction family after that record is chosen.  Both
use the Zheng Lemma 5.22/Proposition 5.26 construction and are stated strictly
below the original existential conclusion.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 3 INFRA, 1 OK.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalIntegralScalarMates": "9c3eaaa837f4321931db860719389846bc6551d8"}, "results": {"Sheaf.Paper.ExceptionalRingOperationsExistence": {"hash": "12b6f37c3f38af79a030a433dc2ffb6b444cf31b", "status": "INFRA"}, "Sheaf.Paper.ExceptionalRingTransportCore": {"hash": "87222536a47dc08a48ed436e6a8378b42f61ec3c", "status": "INFRA"}, "Sheaf.Paper.ExceptionalRingTransportCoreData": {"hash": "0594ce4c32d960081d992cae1f47df4460c80fab", "status": "INFRA"}, "Sheaf.Paper.ExceptionalRingTransportFamily": {"hash": "5960d42c061d3c3d87bda0f357d5137c36100426", "status": "OK"}}, "seconds": 83, "time": "2026-10-28T05:33:51+0800", "transitive": 0, "version": 1}
```

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
