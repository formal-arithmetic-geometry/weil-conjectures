## What changed

Added the proof-facing module `Sheaf.SixFunctors.IntegralPullEvaluationCochainSquareComponent`.
It records the ordinary pullback/evaluation comparison as a cochain-level definition and
isolates the equality of its components in one cochain degree. The assigned theorem now
proves the full cochain-map equality by `HomologicalComplex.hom_ext`, unfolding the two
comparison definitions only at the component step. No target signature or existing
shared declaration was changed.

The degreewise theorem remains the only postponed sectionwise geometric calculation. Its
statement is strictly smaller than the item theorem: it fixes one complex and one degree,
while the parent proof assembles all degrees by extensionality. Both files compile in
import order; the component module takes 8.6 seconds and the parent 48.6 seconds.

## Proved and sorry left

Closed the original hole
`WeilConjectures.IntegralSystemRealization.integralPullEvaluation_cochainSquare` by
reducing it to the component theorem and applying `HomologicalComplex.hom_ext`.

One sorry remains in
`WeilConjectures.IntegralSystemRealization.integralPullEvaluation_cochainSquare_component`.
This is the degreewise section calculation described in its docstring. No sorry occurs in
the `ordinaryPullEvaluationComplex` definition.

## No longer needed

No imports were removed and no previously declared dependency was pruned. The parent
still depends on the four ordinary construction and mate interfaces named by its DAG
node; the new component theorem uses exactly those same interfaces.

## Where the brief, the DAG or earlier work was wrong

The original item was too large to prove directly within the available interface: its
mathematical content is an ordinary sectionwise calculation followed by a routine
cochain-extensionality step. The latter can be discharged independently, so the
remaining work is isolated as a degreewise theorem rather than leaving a sorry in the
parent. This decomposition does not alter the target statement or introduce derived,
localization, or K-injective hypotheses.

## New nodes

Added `lem-sf-integral-pull-evaluation-cochain-square-component` for the degreewise
ordinary square. It has its own module and declaration, complete source/proof prose,
and the same edge-case coverage as the parent (zero modules and `n = 0`). The parent node
now lists this node as its proof dependency and its second proof step is the
`HomologicalComplex.hom_ext` assembly.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralPullEvaluationCochainSquare": "982ef542132ea8512c315dce1d8789a7d3422a9e", "Sheaf.SixFunctors.IntegralPullEvaluationCochainSquareComponent": "9ec238c136c6f0541083e851de5568ef67465a3c"}, "results": {}, "time": "2026-10-28T05:24:50+0800", "transitive": 0, "version": 1}
```

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
