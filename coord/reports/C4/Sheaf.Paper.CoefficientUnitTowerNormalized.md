## What changed

Restored `Sheaf.Paper.CoefficientUnitTowerNormalized` from the exact quarantine path
in its current rework row. Repaired the module-local transparency setting that
blocked the application of the inverse realization to the actual coefficient unit.
`spCoefficientCommRings` must unfold to identify its evaluated quotient sheaves with
`SpTowerShriek.B`, so it is no longer marked locally irreducible. The constant-sheaf, p-adic field
and coefficient-integer definitions are kept locally irreducible instead. This
reduces the profiled compile from 60.4 to 47.4 seconds; profiling options have been
removed from the delivered source. The final source compiled without warnings
in 41.8 seconds.

The theorem, every archived helper, every import, and the recorded mathematical
argument are retained. The proof computes ordinary unit reductions using the
section-preserving coordinates, proves the evaluated degree-zero complex K-flat,
and applies the scalar model's representative comparison. The DAG node
`lem-sp-coefficient-unit-tower-normalized`, its attachment, and all dependencies
still describe this proof and require no changes. No source-library file changes.

The unchanged archived direct importer `Sheaf.Paper.FiniteOrientationReduction`
compiled against the repaired item in 46.2 seconds. Its temporary sandbox source
was removed after validation, and is not included in the delivery. The compile
service supplied the current unpublished `CoefficientTowerShriekInterfaces` in
its private overlay.

Change record: `coord/changes/C4-coefficient-unit-local-transparency.md`.

## Proved and sorry left

This is an assigned zero-hole build repair, not a new mathematical proof.
`AlgebraicGeometry.ProEtale.SpFiniteOrientation.coefficient_unit_tower_normalized`
remains completely proved. Its archived source contained zero sorries; the restored
module contains zero sorries. Holes closed: none (0 of 0). Holes added: none.
No statements were split off.

## No longer needed

None. No imports, modules, declarations, or DAG dependencies are pruned. In
particular the quarantined consumer still needs the coefficient-unit normalization
and is not withdrawn. The unit and chapter routes are preserved.

## Where the brief, the DAG or earlier work was wrong

The snapshot's old build-error file mentions a bad import of
`CoefficientTowerShriekInterfaces`, but the current rework row names the later
application type mismatch at line 239 of the archive. Both were checked against
current coordination records over SSH. The assigned defect is caused by the local
irreducibility of the coefficient diagram, not a hole in its normalization argument.
The restored module was first checked successfully against the current interface
provided by the compile service's unpublished dependency overlay (53.1 seconds).
No target statement, binder, definition data, or mathematical hypothesis changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CoefficientUnitTowerNormalized": "f7c0266f07c8e0614858a49e5b83c21295c5e567"}, "results": {}, "time": "2026-10-28T02:57:58+0800", "transitive": 0, "version": 1}
```

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
