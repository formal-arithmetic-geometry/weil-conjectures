## What changed

Closed `WeilConjectures.scalarModelRoosZeroLift_factorization`'s existence
interface by composing two explicit lower interfaces: the strict scalar Roos
lift construction and the normalized factorization step.  The assigned module
imports those two new statement modules and has no remaining `sorry`.

## Proved and sorry left

The assigned declaration `scalarModelRoosZeroLift_factorization_exists` is
proved.  Two strictly smaller construction steps remain as named statements:

- `scalarModelRoosZeroLift_strict_exists` in
  `ScalarModelRoosZeroLiftStrictExistence.lean` (node
  `lem-trf-scalar-model-roos-zero-lift-strict-existence`), whose proof supplies
the zero-shift lift and coordinate predicate for arbitrary `f`.
- `scalarModelRoosZeroLift_factorization_from_coordinates` in
  `ScalarModelRoosZeroLiftFactorizationFromCoordinates.lean` (node
  `lem-trf-scalar-model-roos-zero-lift-factorization-from-coordinates`), whose
  proof supplies the displayed normalization equality from the zero-shift and
  coordinate hypotheses.

These are decomposition sorries, each strictly weaker than the assigned
existence-and-factorization statement, and each has its source and proof plan
in its docstring and DAG node.

## No longer needed

None.  The assigned proof uses the core definitions and both new lower
interfaces.

## Where the brief, the DAG or earlier work was wrong

The prior split treated the full existence-and-factorization conclusion as a
single interface while the available core declaration only isolates strict
lift construction.  The proof plan therefore needs separate strict-construction
and normalized-factorization steps; the item now combines those steps without
changing its statement.

## New nodes

`lem-trf-scalar-model-roos-zero-lift-strict-existence` records the strict lift
and coordinate construction.  `lem-trf-scalar-model-roos-zero-lift-factorization-from-coordinates`
records the normalized factorization equality from those coordinates.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorizationExistence": "087ad9604104d611e80f1bdf615ce658cd86db9e", "Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorizationFromCoordinates": "2662de9589f3dd568e2941bc1cc4b84ef962f31e", "Sheaf.TraceFormula.ScalarModelRoosZeroLiftStrictExistence": "2426f6ac2cb10831a3d635c14ab9aabc8bdf81ef"}, "results": {}, "time": "2026-10-28T08:06:17+0800", "transitive": 0, "version": 1}
```

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
