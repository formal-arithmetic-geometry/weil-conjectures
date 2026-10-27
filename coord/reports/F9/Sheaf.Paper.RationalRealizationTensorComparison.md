## What changed

The tensor-completion presentation theorem is proved from the existing
`constructibleTensorCompletion` existential by packaging its functor, model,
cochain map, comparison, and four normalization clauses.  The declarations
needed by the final comparison were split into two imported modules,
`RationalRealizationTensorComparisonData` and
`RationalRealizationTensorComparisonStructures`, so each file compiles under
the 60-second limit.  Public names and signatures are unchanged; the final
`rational_realization_tensor_comparison` theorem remains in the item module.

## Proved and sorry left

Proved: `WeilConjectures.constructibleTensorCompletionPresentation` (the
completion-presentation hole, previously at line 134).

Sorry left: `WeilConjectures.RationalTensorRealization.rational_realization_tensor_comparison`
in `Sheaf.Paper.RationalRealizationTensorComparison` (blueprint node
`lem-zl-rational-realization-tensor-comparison`).  No new `sorry` was added.

## No longer needed

No proof-dependency node was pruned.  The original proof-only imports are now
carried by the data/structure modules required for their public signatures;
the item module imports the structure module.

## Where the brief, the DAG or earlier work was wrong

The original single module exceeded the 60-second compile limit while checking
the large `At` and `FieldChange` signatures.  Splitting those declarations
from the final theorem module preserves the interface and reduces compile
times to 39.2 seconds (data), 54.6 seconds (structures), and 4.8 seconds
(item) in the sandbox build.

## New nodes

`def-zl-rational-realization-tensor-structures` owns the split `At`, `FieldChange`, and `System` data structures in `RationalRealizationTensorComparisonStructures`.  The existing completion-presentation node now owns the data module, while the comparison theorem node remains attached to the item module.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.RationalRealizationTensorComparison": "da1e99fa2a8b3d8be1db10fee1c76b49c759ded2", "Sheaf.Paper.RationalRealizationTensorComparisonData": "a92caf03f2f2f9b22d3a5c12bf71f89cd5e6a5ac", "Sheaf.Paper.RationalRealizationTensorComparisonStructures": "d294ec68d32cb317218a9a43d6d995f3bd5dfe30"}, "results": {"Sheaf.Paper.AdicHomTensorLisseCriterion": {"hash": "cc7b19b0a9216f74de1cdd19c522455f80263739", "status": "OK"}, "Sheaf.Paper.NativeAdicRealizationData": {"hash": "1c5841337f21707909a7b99a78611e0d05711743", "status": "OK"}}, "seconds": 25, "time": "2026-10-28T01:39:56+0800", "transitive": 0, "version": 1}
```

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
