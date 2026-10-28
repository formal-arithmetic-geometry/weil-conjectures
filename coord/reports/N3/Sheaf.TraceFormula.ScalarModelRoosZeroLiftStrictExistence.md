## What changed

Proved `scalarModelRoosZeroLift_strict_exists` by strictifying the input Roos map and applying
`scalarModelRoosZeroLift_core`. Added the split-off module
`Sheaf.TraceFormula.ScalarModelRoosZeroLiftStrictification` for the strictification step, and
updated the item's DAG proof route to record both dependencies.

## Proved and sorry left

The item's `scalarModelRoosZeroLift_strict_exists` is proved. One strictly simpler theorem is
split off with `sorry`: `scalarModelRoosZeroLift_strictify` in
`Sheaf.TraceFormula.ScalarModelRoosZeroLiftStrictification` (node
`lem-trf-scalar-model-roos-zero-lift-strictification`).

## No longer needed

No imports or declared dependencies were removed. The proof uses the core construction and the
new strictification theorem; no other route dependencies are needed.

## Where the brief, the DAG or earlier work was wrong

The original one-step DAG route omitted the strictification premise needed to apply the core
construction to an arbitrary Roos map. The premise is isolated as a genuine lower-level theorem.

## New nodes

`lem-trf-scalar-model-roos-zero-lift-strictification` records the construction of a zero-shift
representative preserving unshifted quotient coordinates. Its Lean declaration is in
`lean/Sheaf/TraceFormula/ScalarModelRoosZeroLiftStrictification.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.TraceFormula.ScalarModelRoosZeroLiftStrictExistence": "5e5c41b8bfa4c4ca53ea1e097bc0c4a9ea8c8ead", "Sheaf.TraceFormula.ScalarModelRoosZeroLiftStrictification": "ec894abb5924e2a20e1cdde5f20cc103206d528d"}, "results": {}, "time": "2026-10-28T10:54:28+0800", "transitive": 0, "version": 1}
```

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
