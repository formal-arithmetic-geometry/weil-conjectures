## What changed

Prove `AlgebraicGeometry.Scheme.rationalMixedRawGeometricComposition` from the
published ordinary scalar-pullback composition law and the strict completion-unit
squares. Private categorical lemmas keep the calculation at fixed category instances. The selected integral compositors satisfy the recorded unit
equations, which identify their mixed square after cancelling two invertible
units. Rationalization then preserves the integral square; naturality moves the
initial raw-object transport and the remaining transports cancel.

Add three proved helper modules as proof-only imports:
`Sheaf.Paper.RationalScalarMixedIntegralGeometric`,
`Sheaf.Paper.RationalScalarMixedIntegralTower`, and
`Sheaf.Paper.RationalScalarMixedNormalizationAssoc`. The first contains the new
integral geometric calculation and private categorical pasting lemmas. The
others preserve the existing private integral tower and normalization proofs,
now with named public conclusions. The corresponding three new nodes and the
parent proof dependencies record these calculations. All existing public
signatures, constructions and public imports are preserved.

Large rewrites of normalized beta expressions are replaced by generic equality
transport. Local irreducibility of scheme pullback constructions prevents
unnecessary elaborator unfolding. After these improvements, a full compile
passed in 57.6 seconds, but the delivery's axiom probe took 72.5 seconds; another
transparency experiment took 82.8 seconds and was discarded. The three
self-contained calculations are therefore compiled in their own modules.

## Proved and sorry left

Closed one of the six original holes:
`AlgebraicGeometry.Scheme.rationalMixedRawGeometricComposition`.
No holes added or split off.

Five original holes remain, all on
`lem-per-rational-scalar-mixed-unit-cancellation`:

- `AlgebraicGeometry.Scheme.rationalScalarMixedUnitCancellation`.
- `AlgebraicGeometry.Scheme.rationalMixedGeometricComposition`.
- `AlgebraicGeometry.Scheme.rationalMixedGeometricIdentity`.
- `AlgebraicGeometry.Scheme.rationalMixedCoefficientTower`.
- `AlgebraicGeometry.Scheme.rationalMixedCoefficientIdentity`.

## No longer needed

The item's direct proof imports of
`Mathlib.CategoryTheory.Adjunction.CompositionIso` and
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle` move
to `RationalScalarMixedNormalizationAssoc`; their uses are preserved there.
The temporary direct proof import `Sheaf.Paper.PbcScalarOperationComp` is needed
only in `RationalScalarMixedIntegralGeometric`. No mathematical dependency,
module, node, declaration or unit-route step is withdrawn. The remaining
coherence and existence holes retain their original plan.

## Where the brief, the DAG or earlier work was wrong

The raw geometric composition companion does not require a new K-flat tensor
calculation: the existing ordinary composition law and the normalized integral
compositor unit equations suffice. Realization is not assumed faithful.
The live server queue lists a six-hole proof item; the older rework/build-error
records report failed dependency imports. The item is retained with its original
Lean attachment and dependencies.

The older standing brief forbids splitting for performance, but the worker
prompt explicitly permits it after improving the slow calculations. This
packet follows the worker prompt and preserves every old public declaration.

## New nodes

`lem-per-mixed-integral-geometric-composition` proves the strict integral
geometric compositor equation from the supplied unit equations. Its Lean
module is `Sheaf.Paper.RationalScalarMixedIntegralGeometric`.

`lem-per-mixed-integral-coefficient-tower` records the previously private proved
strict coefficient-tower equation. Its module is
`Sheaf.Paper.RationalScalarMixedIntegralTower`.

`lem-per-mixed-reduction-normalization-assoc` records the previously private
proved associativity equation for the prescribed derived scalar normalizations.
Its module is `Sheaf.Paper.RationalScalarMixedNormalizationAssoc`.

Validation: `lcompile.py --all` compiled the geometric helper in 8.0 seconds,
the integral tower helper in 6.8 seconds, the normalization helper in 4.5 seconds,
and the assigned module in 47.5 seconds, with zero errors or warnings.

All three conclusions are proved; none adds a `sorry`. No change record is
needed: this packet changes only the assigned module and adds new modules and
their nodes.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RationalScalarMixedIntegralGeometric": "d6574d510cf49a37538dd302cb59020171830792", "Sheaf.Paper.RationalScalarMixedIntegralTower": "ec4fa37a48fee63e199ae291b306e46db0bad905", "Sheaf.Paper.RationalScalarMixedNormalizationAssoc": "101a7dbe3087f4d06963b91017f9d322223994f4", "Sheaf.Paper.RationalScalarMixedUnitCancellation": "1000d907bf535f22f73d3b07d9948be8352d5bb5"}, "own_failed": ["Sheaf.Paper.RationalScalarMixedUnitCancellation"], "results": {}, "time": "2026-10-28T01:11:21+0800", "transitive": 0, "version": 1}
```

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
