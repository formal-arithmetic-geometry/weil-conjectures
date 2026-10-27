## What changed

Closed the original core comparison theorem by assembling it from two strictly smaller
named obligations in the same module: bounded constructibility and the remaining ambient
adjunction laws. The assembly is a complete Lean structure proof and preserves every
existing declaration and target statement. The finite-stage coherence theorem remains
as the existing planned hole.

## Proved and sorry left

Closed one original hole:
`WeilConjectures.AdicQbarRealization.AmbientHomEvaluation.adic_ambient_hom_evaluation_comparison_core`.
Its proof now applies the two split theorems and constructs `CoreLaws` field by field.

Two strictly smaller split-off holes remain:
`adic_ambient_hom_evaluation_comparison_core_bounded` and
`adic_ambient_hom_evaluation_comparison_core_adjunction`.
The existing `adic_ambient_hom_evaluation_comparison_coherence` hole remains unchanged.
Thus one hole was closed by a genuine decomposition and two holes were added.

## No longer needed

No imports, definitions, or modules were pruned. The core node's proof dependencies now
name the two split obligations, while those obligations retain the three infrastructure
lemmas recorded by the original route.

## Where the brief, the DAG or earlier work was wrong

The prior core node bundled constructibility, invertibility, the Hom bijection, and the
transpose equations into one admitted theorem. Those are separable obligations, so the
node now records the actual strict decomposition used by the Lean assembly. No statement
or unit-level route was changed.

## New nodes

`lem-sf-adic-ambient-hom-evaluation-comparison-core-bounded` records the constructibility
obligation. `lem-sf-adic-ambient-hom-evaluation-comparison-core-adjunction` records the
strictly smaller conjunction of the invertibility, Hom-bijection, transpose, naturality,
and evaluation obligations.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicAmbientHomEvaluationComparison": "b5b02e5c5aeb389e485a56e0557eb34443e7418f"}, "results": {"Sheaf.Paper.AdicQbarConstructibleRealization": {"hash": "7e2ce2076ec6ff2ae7f31dd670b20fca6d09af3f", "status": "OK"}}, "seconds": 59, "time": "2026-10-28T05:21:17+0800", "transitive": 0, "version": 1}
```

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
