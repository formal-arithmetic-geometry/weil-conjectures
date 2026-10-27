## What changed

Restored `Sheaf.Paper.ClopenSystemRealizationData` from its quarantine copy and added a
local priority-10000 registration of `AlgebraicGeometry.strictEtaleSystemDerived` and
`AlgebraicGeometry.strictEtaleLevelDerived`. This keeps the strict-system derived
categories used by the module aligned with the instances carried by its fields after the
new `Scheme.ProjectionRestriction.derived` instance was introduced. No declarations or
statements changed, and no imports were changed.

## Proved and sorry left

The module contains no `sorry` declarations. The assigned zero-hole rework is repaired;
no new statements or holes were added.

## No longer needed

None. The module's imports and all DAG dependencies remain needed for its public
structures and definitions.

## Where the brief, the DAG or earlier work was wrong

The earlier build assumed that the strict-level `HasDerivedCategory` instances would be
selected automatically. The newer `Scheme.ProjectionRestriction.derived` instance can
instead be selected, producing a non-definitional type mismatch in the existing fields.
A local priority-10000 registration is required; the DAG statement itself is unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ClopenSystemRealizationData": "c0784f8f9871b0f80784ed4e07ca4d60da9b3406"}, "results": {"Sheaf.Paper.ClopenCanonicalRestrictionEvaluation": {"hash": "4bbad6be2a2963f186131adc37f4341c0d3f5c3b", "status": "OK"}}, "seconds": 52, "time": "2026-10-28T07:29:16+0800", "transitive": 0, "version": 1}
```

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
