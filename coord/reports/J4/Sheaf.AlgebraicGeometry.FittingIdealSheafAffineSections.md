## What changed

Proved `AlgebraicGeometry.Scheme.Modules.fittingIdealSheaf_affine_sections` without changing
its statement. Private helpers identify each presentation supremum, prove its compatibility
with principal localization, apply `IdealSheafData.ofIdeals_ideal`, and identify an arbitrary
ideal sheaf on an affine open with the tilde of its section ideal, over the structure sheaf.
Validation: the complete item compiled cleanly through `lcompile.py` in 28.3 seconds.

Proof imports add `WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion` and
`Mathlib.RingTheory.Finiteness.Cardinality`. The node now records this implementation.

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.Scheme.Modules.fittingIdealSheaf_affine_sections`
(node `lem-trf-fitting-ideal-sheaf-affine-sections`). Added no holes and left no holes in the
item. Presentation independence and arbitrary base change are used through their existing
named theorem; its existing hole is not changed by this delivery. The private helpers `presentationSup_eq`, `presentationFittingIdeal_postcomp`,
`presentationSup_basicOpen`, `fittingIdealSheaf_ideal_eq`, and `ideal_restrict_tilde`
are also proved.

## No longer needed

Removed redundant proof imports `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` and
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, which the retained imports already
provide. No dependency nodes or modules are withdrawn. The explicit construction of a second closed
subscheme and the final affine-cover equality argument in the old plan are unnecessary:
the compatible affine ideal constructor and `IdealSheafData.ofIdeals_ideal` already perform
that maximality comparison. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The previous plan described a valid but longer
implementation of the general ideal-sheaf construction. The final isomorphism needs the
actual `toModules` kernel realization and an inclusion equation; equality of affine ideals
alone would not prove that clause. The proof checks that equation using the tilde-Gamma
adjunction and the canonical section restriction maps. Edge cases (empty affine open,
zero module, n = 0, n <= r, and non-finitely-presented finite-type modules) use the same
argument, with no extra hypotheses.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
