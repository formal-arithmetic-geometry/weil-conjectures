## What changed

Restored `RationalVerdierComposition.lean` from its quarantined source and replaced its
single proof hole by a real existential wrapper. The wrapper obtains an associator with
its integral normalization from `rational_scalar_comp_normalization` and combines it with
the separately named normalized associator equation. Added the two split-off theorem
modules and their DAG nodes; both theorem proofs remain explicit, named `sorry`s for
parallel completion. The item imports only the model module and the two proof modules.

## Proved and sorry left

The item declaration `WeilConjectures.RationalVerdier.extension_composition` is proved
from the two strictly smaller intermediate declarations. Two holes were added:
`WeilConjectures.RationalVerdier.rational_scalar_comp_normalization` and
`WeilConjectures.RationalVerdier.extension_composition_equation`, with the corresponding
DAG nodes listed below. No definition contains `sorry`.

## No longer needed

The archived proof plan's direct attempt to construct and verify the rational associator
is split into the normalization and equation statements. No declared proof dependency was
pruned; the private `SfScalarExtensionComposition` imports remain in the split modules
because their planned proofs use the canonical scalar associator declarations.

## Where the brief, the DAG or earlier work was wrong

The quarantined module could not compile against the current published snapshot because
its public import `Sheaf.SixFunctors.RationalVerdierModels` was itself quarantined after a
red global build. Restoring the archived module is therefore required by the rework row.
The original node's one-page proof plan combines two independently nontrivial obligations;
the delivery records them as two strictly smaller named statements while preserving the
original target signature and conclusion exactly.

## New nodes

`lem-coef-rational-verdier-composition-normalization` states the integral normalization of
the rational scalar associator and is declared in
`lean/Sheaf/SixFunctors/RationalVerdierCompositionNormalization.lean`.

`lem-coef-rational-verdier-composition-equation` states the associator equation for an
associator supplied with that normalization and is declared in
`lean/Sheaf/SixFunctors/RationalVerdierCompositionEquation.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierComposition": "c5470d96143d3b2f3cab14db26d0fe4c1286029f", "Sheaf.SixFunctors.RationalVerdierCompositionEquation": "9d2c32680aaa9aea7cbad1edcaf5c084f15dbae4", "Sheaf.SixFunctors.RationalVerdierCompositionNormalization": "d36c1331c1f4af3a344fbec683e86be91f9715a6"}, "results": {}, "time": "2026-10-28T00:53:51+0800", "transitive": 0, "version": 1}
```

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
