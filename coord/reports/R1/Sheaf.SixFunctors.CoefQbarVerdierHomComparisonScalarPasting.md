## What changed

Added the private categorical helper
`scalar_evaluation_transport`, a proved transport calculation for a scalar
internal-Hom evaluation square. It is the finite-stage naturality calculation
needed when the specialized `HomScalarCompatibility` equation is pasted into
`stageHomInclusion`. The assigned theorem statement and imports are unchanged.

## Proved and sorry left

The new private helper `scalar_evaluation_transport` is proved by functor
naturality and associativity. No existing holes were closed. The theorem
`WeilConjectures.CoefQbarVerdier.HomComparison.component_extension_of_scalar_compatibility`
remains as its named theorem proof `sorry`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The DAG proof step describes the finite Hom scalar square and common-stage
cancellations but does not state the intermediate naturality calculation used
by the pasted finite evaluation square. The remaining unproved work is the
application of this helper together with the dual and omega transition
identities through `stageHomInclusion` and `homToStage`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarVerdierHomComparisonScalarPasting": "d8db2175b5a2ed17e21d4d5157b7ca76f06e4a65"}, "results": {"Sheaf.SixFunctors.CoefQbarVerdierHomComparisonExtension": {"hash": "07fc8904e746be96946dc114a18ebeada077a569", "status": "OK"}}, "seconds": 13, "time": "2026-10-28T07:01:35+0800", "transitive": 0, "version": 1}
```

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
