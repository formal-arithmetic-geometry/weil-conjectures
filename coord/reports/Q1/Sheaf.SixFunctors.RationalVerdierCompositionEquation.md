## What changed

Filled `WeilConjectures.RationalVerdier.extension_composition_equation`.
The proof obtains the integral comparison cocycle and applies a new
integral-representative localization theorem. The new theorem is in
`Sheaf.SixFunctors.RationalVerdierLocalizedComposition` and records the remaining
localization/normalization calculation as one named intermediate statement.
The proof-only imports are `RationalVerdierIntegralCocycle` and
`RationalVerdierLocalizedComposition`; the unused scalar-extension-composition
import was removed from both modules.

## Proved and sorry left

The item theorem `extension_composition_equation` is proved (1 of 1 original
sorries closed). The new intermediate theorem
`localized_extension_composition` remains a single named `sorry`, with node
`lem-coef-rational-verdier-localized-composition`.

## No longer needed

Removed the proof-only import `Sheaf.Paper.SfScalarExtensionComposition`; the
canonical scalar and associator declarations are already available through the
models and normalization imports. No declared dependency node other than the
three listed in the new node is used.

## Where the brief, the DAG or earlier work was wrong

The recorded proof plan requires the full localization and normalization
calculation, but the current library exposes only the integral cocycle and the
associator normalization interfaces. The missing calculation is therefore
split as `localized_extension_composition`, whose domain is restricted to
integral representatives and whose input is the integral `CompositionConclusion`.

## New nodes

`lem-coef-rational-verdier-localized-composition` records the integral-
representative localization step. Its Lean declaration is
`WeilConjectures.RationalVerdier.localized_extension_composition` in
`lean/Sheaf/SixFunctors/RationalVerdierLocalizedComposition.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierCompositionEquation": "c6a378cee2397dc18299c71361d6a0f6abb6366f", "Sheaf.SixFunctors.RationalVerdierLocalizedComposition": "06c77bc2545270933e40bc226026cba8bb939685"}, "results": {"Sheaf.SixFunctors.RationalVerdierComposition": {"hash": "c5470d96143d3b2f3cab14db26d0fe4c1286029f", "status": "OK"}}, "seconds": 25, "time": "2026-10-28T09:54:02+0800", "transitive": 0, "version": 1}
```

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
