## What changed

Restored the module from the rework cluster's quarantined copy and split it verbatim,
because the restored file exceeded the 60-second per-file gate (68 s wall, 57 s CPU when
the reviewer compiled the published original). Reviewer FIX: the split runs so that the
item module keeps the theorem its node records, and the new module carries the record of
the scalar-projection node. The new public core module
`Sheaf.Paper.EtaleCoefficientSystemAdjointCore` contains the exceptional-adjoint and
exceptional-transport records, the integer-ring and coefficient-change definitions, the
existing sorry `strictEtaleScalarTransportProjection`, and the identity/composition
coherence proofs. The item module publicly imports the core and keeps the Brown assembly,
the target adjoint `etaleCoefficientSystemAdjoint`, the scalar-level modules, the
transport assembly and the scalar/cofinal transport theorems. Both files compile within
the gate (core 31 s, item 21-27 s). The local linter pass is disabled. No signature or
proof body changed. Node `lem-pur-etale-scalar-transport-projection` now records the core
module; node `lem-pur-etale-coefficient-system-adjoint` is unchanged.

## Proved and sorry left

No additional theorem was proved. One existing named sorry remains:
`AlgebraicGeometry.strictEtaleScalarTransportProjection` in
`Sheaf.Paper.EtaleCoefficientSystemAdjointCore`, recorded by node
`lem-pur-etale-scalar-transport-projection`.

## No longer needed

None. No import, DAG dependency, or module was pruned.

## Where the brief, the DAG or earlier work was wrong

The returned delivery was rejected because its module had been removed from the
published tree after the delivery base and moved to quarantine. The current branch has
since restored that quarantined blob. The original restored file exceeded the per-file
compile limit under the current build load; the split keeps both compilation units below
the limit while preserving the public import surface. The earlier reviewer fix (13fe)
left the new module recorded by no node and was refused at landing (rule b); here the
scalar-projection node records the core, where its theorem is.

## Related modules compiled before delivery

15 related module(s) compiled against this delivery by deliver3.py: 14 OK, 1 PRE.

```json
{"capped": false, "direct": 15, "left_out": 0, "own": {"Sheaf.Paper.EtaleCoefficientSystemAdjoint": "7f5e2823b0240871e66125c38d59b59298020ff3", "Sheaf.Paper.EtaleCoefficientSystemAdjointCore": "bf41042b694a3262bb953f9ebe010ba611935d87"}, "results": {"Sheaf.Paper.AdicActualSystemsNormalized": {"hash": "783673e328f02ca183eac67d1d96307a533f61c6", "status": "OK"}, "Sheaf.Paper.ClopenExceptionalScalarDescent": {"hash": "6f93085f7a982f8809424c4b14233af4b04c4278", "status": "OK"}, "Sheaf.Paper.ClopenStrictSystemComparison": {"hash": "50408338f1fcc348b9f99f0f18f7f6cdac3965dd", "status": "OK"}, "Sheaf.Paper.ClopenStrictSystemSupport": {"hash": "89e02439ec595fece4240210d61911112fd648ef", "status": "OK"}, "Sheaf.Paper.EtaleCoefficientProperCoproducts": {"hash": "9d256ce4b442e2cfdc89624945d375a7b108124c", "status": "OK"}, "Sheaf.Paper.EtaleTowerBrownAdjunction": {"hash": "e7e64582d1bdae39565d47fad96f46a46349af35", "status": "OK"}, "Sheaf.Paper.ExceptionalSystemInterfaces": {"hash": "1467bc211d2d611062301238771231b80b3d1813", "status": "OK"}, "Sheaf.Paper.FiniteClopenExceptionalRestriction": {"hash": "0bd8b9f935d5b81f8fa4b71217589919c25bff9b", "status": "OK"}, "Sheaf.Paper.FiniteCoefficientAdjointData": {"hash": "3aa546c7145d338eb44ab0baa9bae449a0b5fe58", "status": "OK"}, "Sheaf.Paper.FiniteExceptionalSiteNormalization": {"hash": "45a4008948aeb8b277eac484c15db3a7a001323f", "status": "OK"}, "Sheaf.Paper.FreeInsertionCompactSupportCoherence": {"hash": "36a41fe45c552892408c347a3f3bbefc9cca27bc", "status": "OK"}, "Sheaf.Paper.IntegralExceptionalInverseImage": {"hash": "64c7331a57e3878805911bfd2f624e53cce16e9f", "status": "PRE"}, "Sheaf.Paper.PurityWitnessedOpenChartTransport": {"hash": "1b0f68983b11bc7c54a1cc79c20c543349628e9c", "status": "OK"}, "Sheaf.Paper.StrictEtaleExceptionalAdjointInterfaces": {"hash": "cf85a1ccb7dc9a8fe2e5758f6b60b114086d3469", "status": "OK"}, "Sheaf.Paper.TensorHomExchange": {"hash": "220d046d5b668a7f1aaab68abea931d9b7b3f9b2", "status": "OK"}}, "seconds": 194, "time": "2026-10-28T03:15:20+0800", "transitive": 0, "version": 1}
```

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
