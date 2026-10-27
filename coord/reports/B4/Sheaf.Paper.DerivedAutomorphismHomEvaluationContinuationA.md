## What changed
Moved the completed integral construction prefix into the public base module
`Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationABase`, preserving the
existing names and imports. The item now assembles
`podIntegralHomComparison_laws` from four strictly smaller field theorems. Added
four component modules for invertibility, naturality, evaluation, and
transposition; their declarations are recorded by the four new DAG nodes.

## Proved and sorry left
Closed `podIntegralHomComparison_laws` by a structure construction from its
four field components. Reviewer FIX (cc, 2026-10-28): two of the four
components are formal and are now proved: `podIntegralHomComparison_evaluation`
(parameter naturality: evaluation is the inverse transpose of the identity, and
the comparison is the transpose of `μ⁻¹ ≫ F ev`) and
`podIntegralHomComparison_transpose` (parameter naturality plus naturality of
`canonicalIntegralPullbackTensor`, taken from `derivedPullbackTensorIso`).
Two split-off sorries remain: `podIntegralHomComparison_isIso`
(node `stage3-derived-automorphism-continuation-a-integral-isIso`) and
`podIntegralHomComparison_naturality`
(node `stage3-derived-automorphism-continuation-a-integral-naturality`).
The item's other pre-existing sorries remain unchanged.

## No longer needed
No proof-dependency import was removed. The declarations formerly written in the
item prefix are supplied by the new public base module; all four component
modules import only that base.

## Where the brief, the DAG or earlier work was wrong
The item source was already a compile-time split. Its integral compatibility
obligation is a four-field structure, so the remaining proof is decomposed into
those four independently sourced field obligations rather than repeated as one
larger statement.

## New nodes
The four integral compatibility field nodes
`stage3-derived-automorphism-continuation-a-integral-{isIso,naturality,evaluation,transpose}`
record the field obligations. Reviewer FIX: their `stmt_deps` and `proof_deps`
cited the parent lemma lem-pod-derived-automorphism-hom-evaluation (whose
declaration `podIntegralHomComparison_laws` is proved from these nodes, a
cycle); they now cite the owners of the declarations in the statements
(def-sf-adic-closed-reindexing-maps, def-pod-partial-closed-interfaces,
def-sf-finite-rational-derived-operations,
def-pur-completed-pullback-tensor-construction, ...) and, in the proofs, the
reindexing lemmas actually used. The existing
`stage3-derived-automorphism-continuation-a` node now records its declaration in
the new base module.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA": "65e0caaa5664272a4fe2badc1486b615570e3218", "Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationABase": "67bf1829cd9c42d3e1b9c245695d0b88c464d133", "Sheaf.Paper.PodIntegralHomComparisonEvaluation": "231d7365d3d43afe540b8513b57db3067626fc26", "Sheaf.Paper.PodIntegralHomComparisonIsIso": "0e4dc553a8e20237c0a1b41f5cb760eb3975902d", "Sheaf.Paper.PodIntegralHomComparisonNaturality": "f700aad0864e165900e8450da19cc0bee1b33cce", "Sheaf.Paper.PodIntegralHomComparisonTranspose": "f85a05b2150173d874eaa5ec14d24b37b9a32adc"}, "results": {"Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationB": {"hash": "509334b55b7c9bc0b756950fac4c23d3b56a7f08", "status": "OK"}}, "seconds": 45, "time": "2026-10-28T04:57:50+0800", "transitive": 0, "version": 1}
```

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
