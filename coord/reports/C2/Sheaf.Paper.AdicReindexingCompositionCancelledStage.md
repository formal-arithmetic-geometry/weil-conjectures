## What changed

`Sheaf.Paper.AdicReindexingCompositionCancelledStage` now proves the finite-stage
cancelled equation from the scalar-reindexing composition square. Its private helpers
use the published `zlStagePull_eq` finite localization transport, prove it respects the
published common-stage compositor, insert the completion-unit identifications, and
assemble the three integral normalization formulas using naturality and cancellation.
The existing theorem statement and public imports are unchanged. The two generic
category diagram lemmas avoid unfolding the sheaf models during repeated rewrites.
The full item compiled on the server in 40.3 seconds at the default heartbeat setting;
the profiler and diagnostic modules were removed before delivery.

The new module `Sheaf.Paper.AdicIntegralScalarReindexingComposition` states precisely
the remaining ambient scalar-only square. Its source, complete proof in words and
DAG node are included. No existing definition or other module was changed.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.AdicQbarRealization.normalized_reindexing_composition_cancelled_stage`
(node `lem-sf-adic-reindexing-functoriality-comp-cancelled-stage`). All private helpers
in that module have complete proofs; zero `sorry` remains in the item.

Added one hole in
`WeilConjectures.AdicQbarRealization.integralScalarReindexing_composition`
(node `lem-sf-adic-integral-scalar-reindexing-composition`). This is a decomposition:
one hole closed, one strictly smaller hole added, net zero. The new square contains
neither the common-stage compositor, finite realization comparisons, the integral
normalization hypothesis, completion-unit inverses, nor constructibility. It is the
ambient balanced-scalar subcalculation, not a renamed finite-stage obligation.

## No longer needed

Removed the private proof imports:

- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
  (`lem-pur-cochain-pullback-tensor-coherence`);
- `Sheaf.Paper.IntegralInverseImageComparisonComposition`
  (`lem-trf-integral-inverse-image-comparison-composition`);
- `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization`
  (`lem-weil-isomorphism-derived-pullback-comparison-normalization`).

The completed pullback normalization already recorded by
`podIntegralPullbackComp_normalization` directly supplies the needed integral
composition equation in the exact completed-inverse-image coordinates used by
`IntegralReindex`. This bypasses the separate inverse-image/entire-cone comparison
models. No module is withdrawn, and no claim is made that these modules are unused
elsewhere in the targets' closure. Both original public imports remain necessary.

## Where the brief, the DAG or earlier work was wrong

The earlier node gave one combined instruction to substitute formulas and cancel,
but did not name the scalar-only composition law for the actual `IntegralReindex`
data. The generic cochain tensor theorem alone does not directly give that law
through these universal scalar-extension counits. The revised route reuses the
existing completion-normalized integral compositor and records only this missing
scalar subcalculation. The finite object transport reuses `zlStagePull_eq`; the remaining cancellation is
explicit. The proof documentation cites the explicit inverse-image formula in
Remark 6.8.15, rather than a separate composition paragraph.

The new square was checked on zero inputs, identity isomorphisms and empty schemes:
its two routes use the same pure-tensor formula, with no inversion of a completion
unit or new existence choice. Its arbitrary-ambient-input generality follows from
the universal derived counits, not from an assumption of derived completeness.

## New nodes

`lem-sf-adic-integral-scalar-reindexing-composition` is the ambient balanced-scalar
composition square before any common-stage realization or completion comparison.
Its ordinary pure-section proof and universal derived-counit extension are recorded
in its docstring and node. The change record is
`coord/changes/AdicIntegralScalarReindexingComposition.md`.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 INFRA.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.AdicIntegralScalarReindexingComposition": "8addd10fc3072feead9095717538e0004c8291fa", "Sheaf.Paper.AdicReindexingCompositionCancelledStage": "cef5b5171d3e89ad08213c7b2a5dede020a9548c"}, "results": {"Sheaf.Paper.AdicReindexingCompositionCancelled": {"hash": "23599869d716fdfffa737a59ca6a62e144645916", "status": "INFRA"}, "Sheaf.Paper.AdicReindexingCompositionCancelledDescent": {"hash": "bb8e9fb87434e11793a50b8df48375d88b0f04d0", "status": "INFRA"}}, "seconds": 75, "time": "2026-10-28T11:26:37+0800", "transitive": 0, "version": 1}
```

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
