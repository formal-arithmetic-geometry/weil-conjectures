## What changed

Restored the assigned module in the Q1 sandbox and decomposed its seven-step proof into two
strictly smaller interfaces, `CoreLaws` and `CoherenceLaws`. The original theorem now assembles
`Laws` from these interfaces. The existing public imports are unchanged.

## Proved and sorry left

The original `adic_ambient_hom_evaluation_comparison` theorem is proved by a real constructor
application. Two strictly smaller named theorem interfaces remain as the only holes:
`adic_ambient_hom_evaluation_comparison_core` (node
`lem-sf-adic-ambient-hom-evaluation-comparison-core`) and
`adic_ambient_hom_evaluation_comparison_coherence` (node
`lem-sf-adic-ambient-hom-evaluation-comparison-coherence`). No definitions contain `sorry`.

## No longer needed

None. Every existing import remains needed by the declarations and the retained proof interfaces.

## Where the brief, the DAG or earlier work was wrong

The build failure recorded for this item was a bad import of `Sheaf.Paper.NativeAdicRealizationData`
while that module was quarantined. The restored source imports and compiles cleanly. The original
DAG proof is mathematically retained, but its seven steps are too large for one direct Lean body;
the delivered interfaces split it at the ambient/finite-stage boundary without weakening the target.

## New nodes

`lem-sf-adic-ambient-hom-evaluation-comparison-core` and
`lem-sf-adic-ambient-hom-evaluation-comparison-coherence` are recorded under
`dag/nodes/sec-six-functors/`.

## Second reading by Q1

The split interfaces are strict projections of `Laws`: `CoreLaws` contains only the ambient
constructibility, Hom-bijection, transpose, naturality and evaluation fields, while
`CoherenceLaws` contains only symmetry and finite-stage/tower fields. The final constructor uses
each field directly and leaves no target theorem hole beyond these two named intermediate nodes.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicAmbientHomEvaluationComparison": "60c65ffd031c06be68c36a2724296b62ba9b71c7"}, "results": {"Sheaf.Paper.AdicQbarConstructibleRealization": {"hash": "7e2ce2076ec6ff2ae7f31dd670b20fca6d09af3f", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T00:49:43+0800", "transitive": 0, "version": 1}
```
