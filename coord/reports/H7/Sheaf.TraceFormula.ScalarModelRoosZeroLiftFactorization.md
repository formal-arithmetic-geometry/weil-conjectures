## What changed

Copied the assigned factorization module into the H7 sandbox and proved
`WeilConjectures.scalarModelRoosZeroLift_factorization` by combining a new
canonical factorized-lift existence interface with the existing strict Roos
uniqueness theorem.  The proof converts the implication-style coordinate
hypotheses into the pairwise nested-tensor equality required by uniqueness.

## Proved and sorry left

Closed the assigned sorry in `scalarModelRoosZeroLift_factorization`.
Added one strictly lower split theorem,
`scalarModelRoosZeroLift_factorization_exists`, whose construction proof remains
`sorry`; it supplies a canonical zero-shift lift, its quotient coordinates, and
its factorization equation.

## No longer needed

None.  The proof uses the core definitions, the new existence interface, and
`scalarModelRoosZeroLift_uniqueness`.

## Where the brief, the DAG or earlier work was wrong

The original node treated the entire factorization as one step, although the
usable proof separates canonical factorized-lift construction from uniqueness.
The DAG copy records that decomposition and the new existence node.

## New nodes

- `lem-trf-scalar-model-roos-zero-lift-factorization-existence`: canonical
  factorized-lift existence interface, stated in
  `lean/Sheaf/TraceFormula/ScalarModelRoosZeroLiftFactorizationExistence.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorization": "e639b952491e3d77238b1078f23ddd29a3c9fd45", "Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorizationExistence": "418b097d2e7009eeec432ac3bfae49f78448a82b"}, "results": {}, "time": "2026-10-28T05:33:23+0800", "transitive": 0, "version": 1}
```

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
