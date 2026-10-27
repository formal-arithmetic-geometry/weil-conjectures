## What changed

Proved `scalarModelRoosZeroLift_uniqueness` by combining the strict first-coordinate
extensionality theorem with the zero shifted-coordinate equations and the mapping-cocone
identity. Added the split module
`Sheaf.TraceFormula.ScalarModelRoosZeroLiftNestedCoordinateExtensionality` for the
nested tensor-balancing and sheafification step, and imported it proof-only.

## Proved and sorry left

Closed the original sorry in `scalarModelRoosZeroLift_uniqueness`.
Added one named sorry, `scalarModelRoosZeroLift_nestedCoordinate_extensionality`, in
node `lem-trf-scalar-model-roos-zero-lift-nested-coordinate-extensionality`; it is the
strict unshifted-coordinate generator-extensionality substep.

## No longer needed

The original proof-dependency declaration
`def-trf-integral-comparison-realization-models` is retained for the split theorem's
statement and construction. No planned dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The existing realization module keeps its tensor-generator extensionality helper
private, so the nested generator step cannot be completed from the public interface
available to this module. The lower-level split records precisely that missing step;
the remainder of the uniqueness proof is fully formalized here.

## New nodes

`lem-trf-scalar-model-roos-zero-lift-nested-coordinate-extensionality` records the
strict first-coordinate equality from nested scalar tensor generators. Its Lean module
is `Sheaf.TraceFormula.ScalarModelRoosZeroLiftNestedCoordinateExtensionality`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.TraceFormula.ScalarModelRoosZeroLiftNestedCoordinateExtensionality": "140749d5d47ab86cdb3ffa7608eca6912ab34aa7", "Sheaf.TraceFormula.ScalarModelRoosZeroLiftUniqueness": "b1a0b7601e311688676ecc488a5c201538f54323"}, "results": {"Sheaf.TraceFormula.ScalarModelRoosZeroLift": {"hash": "868796b16c44d583d854e88f3bcd43c2a0b6e4b6", "status": "OK"}}, "seconds": 131, "time": "2026-10-28T04:22:30+0800", "transitive": 0, "version": 1}
```

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
