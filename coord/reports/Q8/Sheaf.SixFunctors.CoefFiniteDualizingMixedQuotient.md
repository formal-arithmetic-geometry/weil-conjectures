## What changed

Restored the quarantined finite dualizing mixed quotient module and added an
explicit public import of `Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels`.
The explicit import makes the model API a direct dependency of this module,
which is required while the scalar-reduction re-export is being repaired in the
current build. The theorem statement and its documented proof plan are
unchanged.

The module compiles cleanly with the existing `finiteU_quotient_transition`
proof obligation still present. The current global build failure is in the
imported scalar-reduction/model chain, recorded by the assigned rework row.

## Proved and sorry left

This is a zero-hole rework repair at the source/interface level: no existing
sorry was closed and no new sorry was added. The item still contains the one
assigned sorry in
`WeilConjectures.IntegralFiniteExtension.finiteU_quotient_transition`
(node `lem-sf-finite-dualizing-mixed-quotient`). It remains a named theorem
with its source and complete proof plan in its docstring. No definition contains
a sorry.

## No longer needed

None. Both the scalar-reduction exchange module and the finite extension model
module remain required by the theorem statement and proof plan. No DAG node or
module is pruned.

## Where the brief, the DAG or earlier work was wrong

The item was quarantined by the 2026-10-27 global build after its scalar
reduction import failed through the unfinished model chain. The source itself
is the previously split theorem and has no local declaration mismatch. An
explicit model import records the direct interface dependency so this module
remains stable when the scalar module's import closure is repaired. Completing
the theorem remains a separate mathematical obligation from the dependency
repair.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient": "a28c9d36cb6b2ea927c8286190715cd613d53b35"}, "results": {"Sheaf.SixFunctors.CoefIntegralFiniteDualizingCoherence": {"hash": "33e6258868e735e99734a98c2ddda6fb4b2830e1", "status": "OK"}}, "seconds": 75, "time": "2026-10-28T01:01:45+0800", "transitive": 0, "version": 1}
```

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
