# Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationB proof context

## Reason

Repair the direct-importer check following F8's independently landed split.
The current unmodified ContinuationB compiles without Lean errors but is rejected
at 63.9 seconds, exceeding the 60-second limit. Sequential elaboration brings the
profiled module to 49.8 seconds; with the barriers the clean compile takes
53.9 seconds; the final check against the optimized item takes 41.0 seconds. The retained source changes are the local
module elaboration option and the cached operation barriers below. Every
declaration, proof, definition body,
signature, import, exported attribute and visibility in F8's module stays verbatim.
The added barriers reuse the recorded inverse-image, pullback and reduction
functors without unfolding their constructions during elaboration.
No statement, data construction or target meaning changes. The module is
unclaimed in the current claim snapshot; it was supplied by F8.

## Old

No declaration signature changes. The old module proof context, verbatim:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## New

The same declarations under sequential elaboration:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The existing barrier is extended as follows (all attributes are local):

```lean
attribute [local irreducible] pullbackTensorCalculus
  podCompletedDerivedInverseImage integralDerivedPullback podLimitReindexing
  pullbackTensorIntegralPullbackModel completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
```

## Users

This option is not exported and changes no declaration interface or instance.
Downstream sources need no adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationB | unclaimed (F8 split) | Sequential elaboration and local operation barriers; all declarations and proofs preserved. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed (F8 split) | Re-export retained verbatim and compiled against the adjusted module. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Returned slow consumer checked against the current split. |

## Status

landed 20261027T233952-L-4145821 2026-10-27 (merge of deliver/G8/Sheaf.Paper.PodReindexingHomCoefficientDescent)
