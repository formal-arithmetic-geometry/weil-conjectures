## What changed

The item theorem now proves its naturality conjunct by applying the existing
`localizedTensorBraiding_naturality` theorem with the supplied integral braiding
naturality statement. Its scalar-extension conjunct is reduced to the strictly
smaller theorem `rationalBraidingScalarExtensionSquare`, stated in the new module
`Sheaf.Paper.RationalBraidingScalarSquare` and imported proof-only.

## Proved and sorry left

The original `WeilConjectures.rationalBraidingScalarCompatibility` sorry is closed.
The naturality clause is proved for arbitrary localized arrows. One new sorry remains
in `WeilConjectures.rationalBraidingScalarExtensionSquare`, node
`lem-pur-rational-braiding-scalar-extension-square`; it is exactly the scalar-extension
square, a strict conjunct of the original target, and is documented with its integral
localization route.

## No longer needed

None. The proof uses the localized-braiding naturality module, the integral braiding
naturality module, and the new scalar-square module; all original public statement
imports remain needed.

## Where the brief, the DAG or earlier work was wrong

The existing DAG proof plan treated the rational scalar-extension square as if it
followed immediately from definitions. The reviewed integral square is available, but
the localization and scalar-extension map calculation is a separate nontrivial step.
It has therefore been split into the strictly smaller node
`lem-pur-rational-braiding-scalar-extension-square` rather than left as an anonymous
partial proof.

## New nodes

`lem-pur-rational-braiding-scalar-extension-square` is stated by
`Sheaf.Paper.RationalBraidingScalarSquare.rationalBraidingScalarExtensionSquare` and
records the remaining localized scalar-square argument.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RationalBraidingScalarCompatibility": "70a32f7d1bed1bef7b7ed1d330b0d91c6de1f1f4", "Sheaf.Paper.RationalBraidingScalarSquare": "82ab57e819a125b773cea6a25e89057ea29558d0"}, "results": {}, "time": "2026-10-28T08:09:54+0800", "transitive": 0, "version": 1}
```

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
