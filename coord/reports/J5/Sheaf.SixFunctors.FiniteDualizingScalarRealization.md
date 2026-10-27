## What changed

Replaced the sorry in `WeilConjectures.finiteDualizing_scalar_realization` by the complete mate transport proof. The proof establishes invertibility by composing the comparison-site and intrinsic restriction mates, then proves the identity and composition equations by adjunction naturality and endpoint conjugation.

Added the two strictly lower canonical restriction coherence statements used by the proof:
`finiteDualizingRealizationRestriction_unit` and `finiteDualizingRealizationRestriction_comp`.
Their statements and DAG nodes are included with their documented proofs still to be supplied by follow-up workers.


## Proved and sorry left

Proved and closed:

- `WeilConjectures.finiteDualizing_scalar_realization`.

New lower-level sorries, each with a DAG node:

- `WeilConjectures.finiteDualizingRealizationRestriction_unit` (`lem-coef-dualizing-realization-restriction-unit`).
- `WeilConjectures.finiteDualizingRealizationRestriction_comp` (`lem-coef-dualizing-realization-restriction-comp`).

No definition contains `sorry`, and no axiom or unsafe declaration was added.

## No longer needed

The target proof uses the finite dualizing data, normalized DVR tower, witness compatibility, and the two new restriction coherence nodes. The declared site-mates dependency is not needed for this arbitrary-family proof and is not imported. No existing public declaration was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The current source snapshot restored the target with its original sorry while the previous complete proof had been dropped during the red-build rework. The target's direct proof requires the two restriction-square coherence facts; they are strictly below the target and are recorded as separate nodes.

## Forced adaptations

None. The delivered edit of `Sheaf.Paper.IntegralProperReductionBound` (held by B2) was withdrawn by the reviewer: the published module compiles unchanged against this delivery (lcompile 23.8 s, exit 0, 2026-10-28), so the adaptation was not forced. The module is landed as published and change record `J5-integral-proper-reduction-instance-cache` is withdrawn.

## New nodes

`lem-coef-dualizing-realization-restriction-unit` states identity coherence of the section-normalized realization restriction square.

`lem-coef-dualizing-realization-restriction-comp` states successive-restriction pasting coherence for the same square.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralProperReductionBound": "b058d2f367608e35a54d0eb099c686a7e4de4d5d", "Sheaf.SixFunctors.FiniteDualizingRealizationRestrictionComp": "cba8a7a51d7d509786f4ed9b40553471e6d89a41", "Sheaf.SixFunctors.FiniteDualizingRealizationRestrictionUnit": "4348f248da64a67bbf865d400668513535d47f07", "Sheaf.SixFunctors.FiniteDualizingScalarRealization": "08374770589942deed8468aff467c0b2c3d5f9bc"}, "results": {"Sheaf.SixFunctors.FiniteDualizing": {"hash": "cf1d04c0140d20e7b2f193288b7c1ecb21a5346c", "status": "OK"}}, "seconds": 189, "time": "2026-10-28T01:12:36+0800", "transitive": 0, "version": 1}
```

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
