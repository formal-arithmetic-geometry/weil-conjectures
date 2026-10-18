## What changed

Proved `AlgebraicGeometry.Etale.derivedExchange_identity_pasting` in
`Sheaf.Paper.ExchangeIdentityPasting`, preserving its statement and public imports. The proof
uses the existing source identity, horizontal-pasting, and vertical-pasting theorems for
`derivedBaseChangeMapPlus`. A private comparison lemma identifies the project's
`derivedDirectImageComposition` with the generic bounded-below right-derived composition iso;
its unit equation is exactly `derivedPlus_unit_comp_upperStarCompDerivedPlus`, and the forward
component follows by cancellation. The item compiles cleanly with `lcompile.py`.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Etale.derivedExchange_identity_pasting`
(node `lem-weil-pbc-exchange-identity-pasting`). Holes left in the item: zero. Holes added:
zero. Split-offs: zero.

## No longer needed

Removed proof-only imports `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`,
`Sheaf.AlgebraicGeometry.DerivedSquareIsoPasting`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`, and
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`; the source DerivedPasting modules
provide the declarations actually used. No additional nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The planned mate-calculus route was longer than necessary: the source repository already proves
the three `derivedBaseChangeMapPlus` pasting laws. The only missing bridge was the equality
between `derivedDirectImageComposition` and the generic right-derived composition iso; the
existing derived unit comparison proves it directly. No statement or definition was changed.

## New nodes

None.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
