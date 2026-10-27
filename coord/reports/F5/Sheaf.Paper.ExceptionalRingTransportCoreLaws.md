## What changed

Added three proof-dependency modules that isolate the system, finite-evaluation, and
proper/open normalization subsets of `TransportCoreLaws`. The assigned module imports
those subsets and assembles their fields into `TransportCoreLaws` without changing its
statement or structure. All four modules compile with `lcompile.py --all`.

## Proved and sorry left

The assigned theorem
`WeilConjectures.ExceptionalIntegralScalar.exists_exceptional_transport_core_laws`
is reduced to three strictly smaller law-package theorems and its constructor proof is
complete. The three split-off theorem proofs remain `sorry`:

- `exists_exceptional_transport_core_system_laws`
  (`lem-sf-exceptional-ring-transport-core-system-laws`);
- `exists_exceptional_transport_core_evaluation_laws`
  (`lem-sf-exceptional-ring-transport-core-evaluation-laws`);
- `exists_exceptional_transport_core_normalization_laws`
  (`lem-sf-exceptional-ring-transport-core-normalization-laws`).

Thus one target hole is closed by decomposition and three strictly smaller holes are
added. No sorry occurs inside a definition.

## No longer needed

The assigned module's proof does not directly import or use the four original planned
proof-dependency modules; the split theorem statements document their intended source,
while the assembly uses only the three new law-package modules. No adopted source module
or unit-level route is removed. The public `ExceptionalRingTransportCoreData` import is
retained because the statements of all four structures use `TransportCoreData`.

## Where the brief, the DAG or earlier work was wrong

The original target asks for compatibility equations about an arbitrary
`TransportCoreData` witness, while that data structure contains no compatibility fields.
A direct proof therefore cannot derive the equations from `d` alone. The DAG's single
large proof step was refined into three independent strict substeps corresponding to the
system, evaluation, and proper/open normalization calculations.

## New nodes

- `lem-sf-exceptional-ring-transport-core-system-laws`, stated in
  `lean/Sheaf/Paper/ExceptionalRingTransportCoreLawsSystem.lean`.
- `lem-sf-exceptional-ring-transport-core-evaluation-laws`, stated in
  `lean/Sheaf/Paper/ExceptionalRingTransportCoreLawsEvaluation.lean`.
- `lem-sf-exceptional-ring-transport-core-normalization-laws`, stated in
  `lean/Sheaf/Paper/ExceptionalRingTransportCoreLawsNormalization.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalRingTransportCoreLaws": "b259262fe74d3b4e12841ffc4857a6dfbe5aca00", "Sheaf.Paper.ExceptionalRingTransportCoreLawsEvaluation": "688978287140d29fc2b84bc4d8cf83da4cdfb745", "Sheaf.Paper.ExceptionalRingTransportCoreLawsNormalization": "18f4fa729bdf94a7e25050c5aa1c3faf3c07153f", "Sheaf.Paper.ExceptionalRingTransportCoreLawsSystem": "ae598adbdaad495c7e3728a9b1dff9b22a4193b2"}, "results": {}, "time": "2026-10-28T05:16:20+0800", "transitive": 0, "version": 1}
```

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
