## What changed

Proved `WeilConjectures.normalizedCommonEvaluationForStructure_naturality` in
`Sheaf.Paper.NormalizedCommonEvaluationForStructure`. The uniqueness clause of
`podCommonClosed_existsUnique` identifies the supplied normalized structure with
`podCommonClosed`; rewriting reduces the equation to the existing
`normalizedCommonEvaluation_naturality`. Added its module as a private proof import
and updated the item's node to record this route. The statement is unchanged.

## Proved and sorry left

Closed one of one local holes:
`WeilConjectures.normalizedCommonEvaluationForStructure_naturality`.
Zero holes remain in the delivered module; zero new holes or nodes were added.
This is a proof from existing stated dependencies. The imported canonical
`WeilConjectures.normalizedCommonEvaluation_naturality`
(`lem-pod-normalized-common-evaluation-naturality`) and
`WeilConjectures.podCommonClosed_existsUnique`
(`def-sf-adic-closed-reindexing-maps`, also recorded on the owning evaluation node)
remain unproved in the shared source; this delivery does not claim to close them.

## No longer needed

Removed the direct proof import `Sheaf.Paper.NormalizedRationalEvaluationNaturality`
and the direct proof dependency `lem-coef-normalized-rational-evaluation-naturality`:
finite-stage descent is already the responsibility of the canonical naturality
statement. The old direct proof dependencies
`def-weil-algebraically-closed-coefficients` and
`def-weil-derived-pullback-tensor-hom` are not invoked by this proof; their
underlying definitions remain statement dependencies and stay available through
`Sheaf.Paper.DerivedAutomorphismHomEvaluation`. No module is withdrawn, and no
claim is made that rational naturality is globally unnecessary: the canonical
naturality node still depends on it.

## Where the brief, the DAG or earlier work was wrong

The old proof-origin note said the concurrent canonical naturality theorem was
not yet available as an importable dependency. It is now present under the
separate declaration `normalizedCommonEvaluation_naturality`. The canonical
statement requires exactly the same coefficient and scheme assumptions. Its DAG
closure has no path back to this item, and the module import direction is allowed.
The unit record has no realized proof steps altered by this reuse. The current
server queue classifies the item as a one-hole proof item, with no rework row or
build-error file for it.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.NormalizedCommonEvaluationForStructure": "3eb2d293df9d6a041d1833d36e8d3ced442adb24"}, "results": {"Sheaf.Paper.AdicAmbientHomEvaluationComparison": {"hash": "c8e6083b91f0414a8e616904ddfd71dc8e78a50c", "status": "OK"}, "Sheaf.Paper.AdicCommonStageHomTranspose": {"hash": "b1de91655e42ead8ad785ab4154adf04c70baa14", "status": "OK"}}, "seconds": 67, "time": "2026-10-28T14:05:13+0800", "transitive": 0, "version": 1}
```

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
