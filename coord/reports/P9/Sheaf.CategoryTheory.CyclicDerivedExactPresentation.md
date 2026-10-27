## What changed

Proved `CategoryTheory.Endofunctor.IsoAlgebra.cyclicDerivedOffDiagonalPresentation_mapExact`
without changing its statement. The proof applies the exact equivariant functor termwise to
the given short exact complex sequence and its underlying splitting. Naturality of the
commutation isomorphism transports the off-diagonal equation. The mapped endpoint
isomorphisms use the canonical localization factors and inverse shift comparison.
Private proved helpers establish the localization-factor equation, shift cancellation,
transport of the unshifted core, endpoint naturality, and transport of the off-diagonal
class. Mathlib's `DerivedCategory.map_triangleOfSESδ` proves the native boundary equation.

Added proof imports of
`WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor` and
`Mathlib.Algebra.Homology.DerivedCategory.Ext.Map`. No public interface changed. Updated the item node's third proof step to record the
proved private coherence calculations; its dependencies and mathematical route are unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.Endofunctor.IsoAlgebra.cyclicDerivedOffDiagonalPresentation_mapExact`
(node `lem-sf-cyclic-derived-exact-presentation`).
No holes remain in the item; no holes were added or split off. All private helpers are proved.

## No longer needed

None. No imports, modules, or declared node dependencies were removed. The proof follows
the four existing node steps; it uses the presentation definition, exact transport of
fixed pairs, canonical derived comparison data, and the canonical SES boundary formula.
It does not require the separate uniqueness or existence theorems for presentations.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The theorem requires no Grothendieck,
boundedness, or injectivity hypotheses. The source sign is retained through Mathlib's
canonical SES boundary formula. The current blueprint files were read under
`literature/blueprint/latest/`; this is the exact-functor compatibility calculation
serving the exceptional-adjunction sentence, as the node records.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
