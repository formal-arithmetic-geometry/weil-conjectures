## What changed

Completed the proof of
`WeilConjectures.IntegralSystemRealization.integralPullEvaluation_cochainSquare_component_core_expanded`
in the assigned module, with its original statement and public imports unchanged.
Its new proof import is
`Sheaf.SixFunctors.IntegralPullEvaluationDirectTransitionSquare`.

The new module proves
`WeilConjectures.IntegralSystemRealization.integralPullEvaluation_directTransitionSquare`.
Direct evaluation and the canonical scalar comparison preserve underlying sections.
The sequence base-change functor preserves the horizontal transition arrow, so these
normalizations prove the direct-image square by sectionwise extensionality. The assigned
module proves the inverse-image square by an abstract adjunction-mate calculation and
then expands its homological-complex components. All supporting helpers are private
and proved. The restriction equality is proved locally from the Mathlib successor-arrow identity.
The DAG now records this implemented route.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.IntegralSystemRealization.integralPullEvaluation_cochainSquare_component_core_expanded`
(node `lem-sf-integral-pull-evaluation-cochain-square-component-core`).

Also proved the new helper theorem
`WeilConjectures.IntegralSystemRealization.integralPullEvaluation_directTransitionSquare`
(node `stage3-integral-pull-evaluation-direct-transition-square`).
No `sorry` remains in either delivered module. Holes closed: 1 of 1; holes added: 0;
unproved statements split off: 0.

## No longer needed

No original import, module or dependency node is pruned. The proof does not need
`Sheaf.SixFunctors.IntegralSystemExpressionDomain`: its elementary adjacent restriction
equality is proved locally, so that higher node is absent from the new proof dependencies. The coefficient-site
calculation remains necessary in the proved direct-transition helper, and the unit
route is retained.

## Where the brief, the DAG or earlier work was wrong

The planned section calculation is valid. It is easier to perform it for direct image
and transpose the result through the adjunctions before expanding cochain components.
The normalized quotient restriction and the constant-coefficient restriction are
propositionally equal presentations: the proof transports their functors explicitly
with a local proof of the adjacent restriction equality before applying the scalar
comparison normalization.
The same section calculation covers n = 0 and zero modules. No hypothesis or target
statement was changed.

The section normalization helper is stated on its actual source section object.
This avoids expensive kernel reduction through concrete coefficient presentations;
all files compile within the required per-file limit.

## New nodes

`stage3-integral-pull-evaluation-direct-transition-square`, realized by
`Sheaf.SixFunctors.IntegralPullEvaluationDirectTransitionSquare`, records the fully
proved direct-image evaluation transition equation. Its source is Zheng,
Construction 4.1 and the calculation preceding Lemma 4.10, together with the existing
sectionwise comparison normalizations. This node adds no proof obligation.

Validation: both delivered modules and the unchanged direct importer
`Sheaf.SixFunctors.IntegralPullEvaluationCochainSquareComponent` compiled in import
order (22.3 s, 23.6 s and 6.3 s). The temporary unchanged importer copy was removed
from the delivery sandbox.

Change record: `coord/changes/integral-pull-evaluation-component-proof.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralPullEvaluationCochainSquareComponentCore": "71291fae50354b6ae9cd05f6f5c5d5895558ce1a", "Sheaf.SixFunctors.IntegralPullEvaluationDirectTransitionSquare": "608c11ac802db061a4ca6889a88a1e14b29746e9"}, "results": {"Sheaf.SixFunctors.IntegralPullEvaluationCochainSquareComponent": {"hash": "942cd266f24310d3549a2a163c59baca32683b68", "status": "OK"}}, "seconds": 30, "time": "2026-10-28T11:41:24+0800", "transitive": 0, "version": 1}
```

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
