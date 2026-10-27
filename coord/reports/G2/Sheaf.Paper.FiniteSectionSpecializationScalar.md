## What changed

Proved `AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSectionSpecialization_scalar`
from a canonical normalized finite-section scalar transport statement and the existing
uniqueness theorem for normalized finite families. Added the split-off theorem
`finiteSectionSpecialization_scalar_canonical`, whose proof is the remaining geometric
construction from the scalar base-change, shifted-line, and compositor ingredients.

## Proved and sorry left

Closed the item theorem's one `sorry`. One `sorry` remains in
`finiteSectionSpecialization_scalar_canonical`; it is a strictly smaller construction
statement, with its own node and source proof plan.

## No longer needed

The parent proof no longer directly needs the separate low-level coefficient, local
comparison, derived pullback, shifted-line, full-faithfulness, or compositor nodes;
they are dependencies of the canonical split-off statement. No imports were removed.

## Where the brief, the DAG or earlier work was wrong

The previous module failed the global build because its public import
`Sheaf.SecSmoothPurity.DncCoefficientTransportData` was unavailable in the intermediate
quarantine snapshot. The current restored source is available and compiles. The original
proof plan was too high-level to elaborate directly, so the canonical normalized-family
construction was split off as a named intermediate theorem.

## New nodes

- `new-lem-sp-finite-section-specialization-scalar-canonical`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteSectionSpecializationScalar": "f54d04e74af0c83b9ce4797e47de58e7edc01123", "Sheaf.Paper.FiniteSectionSpecializationScalarCanonical": "c9238521cb9b06d65c8196389d38ffcf71f5eb3a"}, "results": {}, "time": "2026-10-28T00:52:50+0800", "transitive": 0, "version": 1}
```

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
