## What changed

Proved `WeilConjectures.RationalVerdier.rational_scalar_comp_normalization` by
specializing `sfRationalScalarComp_existsUnique` to the project scalar abbreviation.
Added the proof-only import and split-off module
`Sheaf.SixFunctors.RationalVerdierIntegralCompNormalization`, whose bridge identifies
its intrinsic integral component with `IntegralFiniteExtension.comp`.

## Proved and sorry left

Closed the `rational_scalar_comp_normalization` hole. The new declaration
`integral_comp_normalization_bridge` remains `sorry`; it is the strictly smaller
component-identification step and has node
`lem-coef-rational-verdier-integral-comp-normalization-bridge`.

## No longer needed

None. The scalar extension composition theorem and the integral component bridge are
both used by the delivered proof.

## Where the brief, the DAG or earlier work was wrong

The existing scalar extension composition theorem normalizes through
`sfIntegralScalarComp`, whereas the target statement records
`IntegralFiniteExtension.comp`. The two maps are not definitionally equal, so the
DAG plan omitted a required component-identification lemma.

## New nodes

`lem-coef-rational-verdier-integral-comp-normalization-bridge` records the missing
identification and is stated in
`lean/Sheaf/SixFunctors/RationalVerdierIntegralCompNormalization.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierCompositionNormalization": "7b4256a10346196ba7125f09e178e0c0761a86dc", "Sheaf.SixFunctors.RationalVerdierIntegralCompNormalization": "785777b425b3b8e07f9683392206a2350301bfa0"}, "results": {}, "time": "2026-10-28T06:48:21+0800", "transitive": 0, "version": 1}
```

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
