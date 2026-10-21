## What changed

Proved all five existence/uniqueness theorems in `Sheaf.Paper.PointReductionUnits`.
The module adjunctions follow from ordinary extension/restriction and the universal
mixed-tensor computation. A proved comparison with tensor by the regular module in
degree zero gives the stated generators. The finite sheaf adjunction specializes the
existing normalized coefficient adjunction; a proved comparison between the homotopy
quotient and cochain localization gives its displayed unit equation. Both sections
comparisons are the identity on elements, using naturality of sheafification and, for
integral coefficients, the completed coefficient limit projection equation.

Gave the finite quotient map an explicitly typed wrapper and exposed the existing
scalar-extension object equation as a proved theorem. The finite restriction and its
unit statement use this definitionally equal map. Specified the existing small derived
localizations explicitly in the finite module restriction and factorization. The two
derived sections comparisons retain the original three-factor construction, with
explicit local exactness proofs and congruence to avoid expensive conversion searches.
All proof helpers are private and fully proved. No target signature, public import,
source-library module or downstream module changes.

The existing node records the actual proof and both new coefficient interface
declarations. Change records describe the typed coefficient interface and the explicit
instances in the comparison definitions:
`coord/changes/A9-point-finite-coefficient-map-type.md` and
`coord/changes/A9-point-derived-sections-instance-inference.md`.

The complete module compiles without warnings through `lcompile.py` (48.1 seconds).
A subsequent import-order check compiled it in 55.2 seconds and its unchanged consumer
`Sheaf.Paper.PointReductionUnitNormalization` in 31.0 seconds. The consumer copy is
not included in the delivery.

## Proved and sorry left

Holes closed (5):

- `WeilConjectures.pointUnitIntegralModuleAdjunction`
- `WeilConjectures.pointUnitIntegralSectionsRestriction`
- `WeilConjectures.pointUnitFiniteModuleAdjunction`
- `WeilConjectures.pointUnitFiniteSheafAdjunction`
- `WeilConjectures.pointUnitFiniteSectionsRestriction`

Holes added: 0. Holes remaining in the delivered module: 0. No split-off statements.

## No longer needed

None. No imports, nodes, declarations or modules are withdrawn. The original node had
no numbered proof or proof dependencies to prune. Its existing statement dependencies
remain necessary for the published units and normalization.

## Where the brief, the DAG or earlier work was wrong

The node had an empty proof list. Its proof and proof dependencies now describe the
Lean construction. The existing coefficient presentations needed a typed map and
explicit localization/exactness instances for usable elaboration. These repairs keep
the same maps and comparison isomorphisms. No quotient flatness, boundedness or nonzero
coefficient hypothesis is introduced; the zero-exponent quotient is covered as well.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
