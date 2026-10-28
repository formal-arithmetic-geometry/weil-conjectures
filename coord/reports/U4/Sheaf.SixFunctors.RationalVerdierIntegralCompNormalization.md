## What changed

Proved `WeilConjectures.RationalVerdier.integral_comp_normalization_bridge` using the existing
`WeilConjectures.completedScalarCanonicalAssociatorFormula`. `ObjectProperty.hom_ext` reduces
the equality in the constructible subcategory to the exact ambient component equation.
The theorem statement is unchanged. The ambient formula is imported only for the proof.

## Proved and sorry left

Closed the one hole in
`WeilConjectures.RationalVerdier.integral_comp_normalization_bridge`.
Zero holes remain in the item module; zero new holes or split-off statements are added.

## No longer needed

The planned direct expansion through `lem-coef-integral-finite-extension` and
`lem-weil-scalar-extension-composition` is replaced by the existing ambient associator formula.
The former remains a statement dependency. Removed the redundant direct proof import
`Sheaf.Paper.SfScalarExtensionComposition`, which the ambient formula module imports publicly.
No module is withdrawn or pruned from the library.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted `lem-sf-completed-scalar-associator-ambient-formula`, which
already gives the required component equation. The node proof and proof dependencies now
record this shorter route.

This is a re-delivery after the source module was quarantined during a red build. The restored
dependency sources are used unchanged; the proof is compiled against the current published
snapshot.

## New nodes

None.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierIntegralCompNormalization": "b41635d3a175f52cfe8f0884f6c02e24a8c67556"}, "results": {"Sheaf.SixFunctors.RationalVerdierCompositionNormalization": {"hash": "7b4256a10346196ba7125f09e178e0c0761a86dc", "status": "OK"}}, "seconds": 53, "time": "2026-10-28T09:39:12+0800", "transitive": 0, "version": 1}
```

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
