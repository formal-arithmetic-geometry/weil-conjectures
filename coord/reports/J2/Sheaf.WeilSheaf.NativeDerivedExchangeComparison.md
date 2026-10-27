## What changed

Filled the comparison argument using the normalized native encoding. The proof identifies
its coefficient isomorphism with the explicit coefficient realization, proves the ordinary
pullback cube, localizes that cube, and applies compatibility of adjunction mates with a
cube. It compares exact and total condensed pullback by their canonical derived comparison,
then uses the fully faithful bounded-constructible inclusion and naturality in the given
input isomorphism. Public definitions and theorem statements of the item are unchanged.

Added `Sheaf.Paper.NativeEncodingPullbackCoherence`, containing the proved ordinary cube.
Its proof checks the normalized direct-image compositors on sections and transposes the
result using `equivalenceAdjunctionComparison_compositor`.

Added `Sheaf.Paper.ExactCondensedExchangeComparison`, containing the fully proved
comparison between the total-derived and exact condensed exchange arrows. Keeping this
self-contained argument separate keeps the item within the per-file compile limit.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.nativeDerivedExchange_condensed_comparison`.
Holes closed: 1. Holes added: 0. Sorries remaining in the item: 0.
Both new helper modules are fully proved and contain zero sorries. This is a proof,
not a decomposition into new sorry statements.

All three delivery modules passed the single-file server compiler within the 60-second
limit. The final item compiled in 42 seconds. Its original public definitions, instance
proofs, attributes, and theorem signature are unchanged. Explicit object equations for
the restricted pullback and pushforward normalize the arrow endpoints before applying
the ambient comparison; this avoids expensive kernel conversion of the full restrictions.
The axiom check for both new helper theorems reports only `propext`, `Classical.choice`,
and `Quot.sound`. The item still inherits `sorryAx` through existing dependencies;
this delivery adds no axiom or sorry to its own proofs.

## No longer needed

This proof does not import or use the planned
`Sheaf.Paper.FiniteSpanModuleDerivedComparison`,
`Sheaf.Paper.NativeEncodingDerivedOperations`, or
`Sheaf.CategoryTheory.DerivedCategory.AdjointSquareComparison` dependencies. Their node edges
`lem-sf-finite-span-module-derived-comparison`,
`lem-sf-native-encoding-derived-operations`, and
`lem-kun-derived-adjoint-square-comparison` were removed from the proof dependencies.
The canonical derived-mate
comparison and exact localization of the ordinary cube give the required compatibility
directly. The Weil operations theorem concerns finite ground fields and Frobenius
transport; the underlying adic comparison here uses the ordinary native core. Their
declarations and modules are preserved for any other consumers.

The exploratory imports of `Sheaf.Paper.NativeAdicEncodingCore` and
`Sheaf.CategoryTheory.CompatibleSquareComponents` were removed. The core is already
available through the ordinary coherence module; elementary associativity pasting supplies
the square calculation without the latter dependency. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original argument referred to several comparison lemmas without supplying the
ordinary compositor coherence for the specified normalized encoding. That coherence is
now proved explicitly. The existing generic localization and mate theorems replace the
longer planned finite-span route. No disputed statement, weakened conclusion, added
hypothesis, or change to the unit route was needed.

## New nodes

`lem-sf-total-derived-exchange-exact-comparison` records the canonical total-to-exact
exchange comparison in `Sheaf.Paper.ExactCondensedExchangeComparison`. Its proof is
complete; this separation adds no sorry.

`lem-sf-native-encoding-pullback-cube` records the ordinary pullback coherence in
`Sheaf.Paper.NativeEncodingPullbackCoherence`. It is a strictly underived compositor
calculation, proved in full, with the same coefficient normalization and the actual
native and condensed inverse-image functors. No change record is needed: no existing
public interface, definition, instance, or attribute was changed.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ExactCondensedExchangeComparison": "ecbdb40f024619aea851095df532eec78f02d1db", "Sheaf.Paper.NativeEncodingPullbackCoherence": "c2410e30d301bfc4bc230c3cf0d6d40199567b76", "Sheaf.WeilSheaf.NativeDerivedExchangeComparison": "66fb09554969cc809f5ecd202d7a572d166c8d02"}, "results": {"Sheaf.WeilSheaf.NativeAffineProperBaseChange": {"hash": "7c5e76a08a33f382d20947f92734f7f4a7400b34", "status": "OK"}, "WeilConjectures.WeilSheaf.VerdierDual": {"hash": "cbd782ced4a4ed0d3932076da1a163a61a8db8c5", "status": "OK"}}, "seconds": 55, "time": "2026-10-28T07:03:10+0800", "transitive": 1, "version": 1}
```

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
