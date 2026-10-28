## What changed

The package theorem in `Sheaf.Paper.ExceptionalRingTransportCoreLawsEvaluation` is
now assembled from three separately stated evaluation clauses.  The proof imports
three new `Sheaf.Paper` modules, each containing one strictly smaller theorem for
the finite evaluated unit, counit, or support comparison, and constructs
`TransportCoreEvaluationLaws` from those fields.  The original package statement
and all its hypotheses are unchanged.  The four-file dependency chain compiles in
import order with `lcompile.py`.

## Proved and sorry left

Closed the original hole in:

- `WeilConjectures.ExceptionalIntegralScalar.exists_exceptional_transport_core_evaluation_laws`.

Added three strictly smaller named theorem holes:

- `WeilConjectures.ExceptionalIntegralScalar.exceptional_transport_core_evaluation_unit`,
  node `new-lem-sf-exceptional-ring-transport-core-evaluation-unit`.
- `WeilConjectures.ExceptionalIntegralScalar.exceptional_transport_core_evaluation_counit`,
  node `new-lem-sf-exceptional-ring-transport-core-evaluation-counit`.
- `WeilConjectures.ExceptionalIntegralScalar.exceptional_transport_core_evaluation_support`,
  node `new-lem-sf-exceptional-ring-transport-core-evaluation-support`.

The item module has zero remaining `sorry`s; the delivery adds three named
`sorry`s, one per independent compatibility clause.  No definition contains a
`sorry`.

## No longer needed

No existing import, module, or node is withdrawn.  The original direct dependency
on `lem-sf-exceptional-ring-transport-core-data` is retained by each split theorem.
The package theorem itself uses only the three new split theorem modules; no other
planned evaluation dependency was found in the library or Mathlib.

## Where the brief, the DAG or earlier work was wrong

The DAG's one-step phrase “the corresponding strict-system transport calculation”
does not expose declarations for any of the three displayed equations.  Since
`TransportCoreData` provides only the underlying functors and isomorphisms, the
three equations cannot be derived by Lean from that record alone.  The delivery
therefore records each equation as a separate, strictly smaller theorem and proves
the requested package by real record assembly.  No target statement or existing
statement was changed.

## New nodes

- `new-lem-sf-exceptional-ring-transport-core-evaluation-unit`: finite evaluated
  unit equation, with its source, proof plan, searches, and Lean declaration.
- `new-lem-sf-exceptional-ring-transport-core-evaluation-counit`: finite evaluated
  counit equation, with its source, proof plan, searches, and Lean declaration.
- `new-lem-sf-exceptional-ring-transport-core-evaluation-support`: finite evaluated
  support comparison, with its source, proof plan, searches, and Lean declaration.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalRingTransportCoreEvaluationCounit": "520a81f5f514b2ce588afa443ef16ef9b5d656ab", "Sheaf.Paper.ExceptionalRingTransportCoreEvaluationSupport": "4a09a7a3107b7cc6cae51e582ea6cb47e92ce0bf", "Sheaf.Paper.ExceptionalRingTransportCoreEvaluationUnit": "64d50027cc635a70b1b31897ca0b9b52477fc3ff", "Sheaf.Paper.ExceptionalRingTransportCoreLawsEvaluation": "bca3f579773ede1a6113fa23dd19db6fa3adb7ed"}, "results": {}, "time": "2026-10-28T07:58:41+0800", "transitive": 0, "version": 1}
```

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
