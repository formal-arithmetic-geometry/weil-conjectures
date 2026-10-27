## What changed

Proved the ordinary direct-image, pullback, and open-extension comparison uniqueness lemmas,
the section-normalized coefficient restriction comparison, and the derived scalar
realization comparison in `Sheaf.Paper.RamifiedScalarSystemTranspose`. Proved
private categorical helpers isolate uniqueness of an adjunction square and its
mate, so geometric adjunction constructions do not unfold during simplification.
The only added imports are private proof imports of
`Sheaf.CategoryTheory.ConstantScalarGeometricAdjunctions` and
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`. Local irreducibility
attributes keep the derived functor implementations out of
generated structure eliminator checks. All existing declaration signatures,
definitions, public imports, and the unit route are preserved.

## Proved and sorry left

Closed five of the eight input holes, with no added holes:

- `WeilConjectures.RamifiedScalarSystemTranspose.directOrdinary_existsUnique`
- `WeilConjectures.RamifiedScalarSystemTranspose.pullOrdinary_existsUnique`
- `WeilConjectures.RamifiedScalarSystemTranspose.openOrdinary_existsUnique`
- `WeilConjectures.RamifiedScalarSystemTranspose.restrictionOrdinary_existsUnique`
- `WeilConjectures.RamifiedScalarSystemTranspose.scalarRealization_existsUnique`

Three original holes remain, all attached to node
`lem-coef-ramified-scalar-system-transpose`:

- `WeilConjectures.RamifiedScalarSystemTranspose.scalar_preserves`
- `WeilConjectures.RamifiedScalarSystemTranspose.scalar_transition`
- `WeilConjectures.RamifiedScalarSystemTranspose.ramifiedScalarSystemTranspose`

This is a partial proof delivery, not a decomposition. No new statement with
`sorry` is introduced.

## No longer needed

None. The remaining upper proof still needs its stated dependencies; no node,
module, or original import is withdrawn. The closed normalization lemmas use the
already-proved generic `CategoryTheory.adjunctionSquare`, mate bijectivity, and
naturality of the sheafification unit.

## Where the brief, the DAG or earlier work was wrong

No statement or definition is changed. The existing plan for the full ramified
system theorem remains open. The five closed lemmas are its existing normalization
steps and require no new mathematical dependency or alternate unit route.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
