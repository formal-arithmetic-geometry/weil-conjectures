## What changed

Updated the proof of `AlgebraicGeometry.SingleComplexBaseChange.stalkDerivedExtensionComparison_isIso` to give names to the local `IsIso` hypotheses used by typeclass inference. The theorem statement and imports are unchanged. The sandbox proof compiles cleanly.

## Proved and sorry left

The existing theorem `AlgebraicGeometry.SingleComplexBaseChange.stalkDerivedExtensionComparison_isIso` remains fully proved; no `sorry` declarations remain in the module, and this delivery adds none.

## No longer needed

No imports, nodes, or modules were removed. Every dependency listed by the existing node remains used by the proof.

## Where the brief, the DAG or earlier work was wrong

The rework record identifies the quarantined predecessor as failing because `IsAcyclicTensorKFlat` was unavailable. The current module already includes the required public import `Sheaf.Algebra.Homology.KFlat`, which resolves that source error. No statement or DAG correction is needed.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
