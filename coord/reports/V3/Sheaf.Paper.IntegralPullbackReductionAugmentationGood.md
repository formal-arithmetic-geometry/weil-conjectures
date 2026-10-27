## What changed

Proved `WeilConjectures.IntegralOrdinary.pullbackReductionAugmentation_good` in
`Sheaf.Paper.IntegralPullbackReductionAugmentationGood`, preserving its exact signature and
both public imports. Added only private, fully proved helpers and private proof imports.
Updated its existing DAG node to describe the proof and its actual dependencies.

The proof takes the natural adjoint mate of the specified completion comparison. On each
good representative, finite evaluation identifies this mate with the ordinary scalar-reduction
pullback square. The identification uses the specified generator formulas, scalar unit,
completion-chain projections, and normalized published Roos realization. These finite maps
are isomorphisms; conservative finite evaluation and full faithfulness of good localization
then give a natural isomorphism. The adjunction unit formula proves the required equation.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.IntegralOrdinary.pullbackReductionAugmentation_good`
(node `lem-sf-pullback-reduction-augmentation-good`).

One of one original holes proved; zero holes added, zero split off, zero left in the module.
Every added private helper is proved. No existing statement or definition was changed.

Validation: the complete proof compiled with `lcompile.py`; the unprofiled run took 46.8 seconds.
The file contains no profiling options. The theorem signature was compared verbatim with the
repository source and is unchanged.

## No longer needed

None of the original imports or DAG dependencies was removed. No module is withdrawn or
claimed pruned. The proof uses conservative finite evaluation instead of establishing equality
of whole maps into a Roos cone; no additional intermediate obligations are needed.

## Where the brief, the DAG or earlier work was wrong

The existing node's proof had no named dependencies and delegated the representative calculation
to its prose description. The required finite pullback isomorphism, generator normalizations,
scalar unit model, and Roos projection identities are already proved in the library. Combining
them closes this obligation directly, without another split. The node now records that route.
No false statement or interface defect was found. The unit's realized route is unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralPullbackReductionAugmentationGood": "9681d39f9104ef9548a5761ef66e6ebb58bae7a3"}, "results": {"Sheaf.Paper.IntegralPullbackReductionAugmentation": {"hash": "beab41e42c31ad37776a8dd78423905ca1de8615", "status": "OK"}}, "seconds": 55, "time": "2026-10-28T06:35:41+0800", "transitive": 0, "version": 1}
```

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
