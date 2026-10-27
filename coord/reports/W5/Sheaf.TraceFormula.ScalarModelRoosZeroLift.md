## What changed

Added a categorical assembly proof for `scalarModelRoosZeroLift`, splitting the documented argument into normalized lift existence and zero-shifted Roos-coordinate uniqueness modules. The top theorem composes the existence factorization with the uniqueness equality and uses associativity.

## Proved and sorry left

The target theorem `scalarModelRoosZeroLift` is proved. The split-off declarations `scalarModelRoosZeroLift_existence` and `scalarModelRoosZeroLift_uniqueness` retain one `sorry` each for their model-specific constructions.

## No longer needed

None. The original realization-model import remains required by the split statements.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the realization construction, coordinate transport, and localized uniqueness into one theorem. The proof was split into two strictly smaller statements matching its numbered proof steps; the target statement and interfaces are unchanged.

## New nodes

- `lem-trf-scalar-model-roos-zero-lift-existence`
- `lem-trf-scalar-model-roos-zero-lift-uniqueness`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.TraceFormula.ScalarModelRoosZeroLift": "868796b16c44d583d854e88f3bcd43c2a0b6e4b6", "Sheaf.TraceFormula.ScalarModelRoosZeroLiftExistence": "16f65d845f267ab346a73e9b03845e1372507671", "Sheaf.TraceFormula.ScalarModelRoosZeroLiftUniqueness": "1075f057cc9927a037b083c167322f1cf3873a6d"}, "results": {}, "time": "2026-10-28T00:54:14+0800", "transitive": 0, "version": 1}
```

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
