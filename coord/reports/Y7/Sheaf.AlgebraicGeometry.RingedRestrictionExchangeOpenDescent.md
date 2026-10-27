## What changed

Implemented `AlgebraicGeometry.Scheme.RingedRestrictionExchange.open_descent`.
The Cartesian base faces show that the local target opens cover Y'. The existing
`open_restriction` equation, the source and target `open_comparison` isomorphisms,
and cancellation of the canonical pullback comparisons show that native open
pullback of the global exchange is invertible on each member. A new proof-only
import supplies native open-cover detection with the exact coefficient rings and
isomorphisms already carried by OpenCube.

The new module `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenCoverReflectsIso` proves
`AlgebraicGeometry.Scheme.RingedRestrictionExchange.proEtaleRingedOpenCover_reflectsIso`.
It identifies native inverse image with slice restriction, including arbitrary
isomorphic coefficient presentations, using the existing ringed open comparison
and scalar-extension ring-isomorphism theorem. Exact inverse image commutes with
homology. The sheaf cover-local isomorphism theorem then detects invertibility in
each degree, and the unbounded derived homology criterion concludes. A point
indexed subfamily handles the cover-index universe without resizing the theorem.
Empty covers, empty bases and zero complexes are included by the same proof.

All existing declaration signatures, definition bodies, public imports and
attributes are retained. Only a private proof import is added to the item. No
source-library file, target, consumer interface or unit route is changed. The
item node's eighth proof step records the implementation. The new module's
statement is a generic tool for that step, with a complete proof and no holes.

## Proved and sorry left

Closed 1 of the item's original 6 holes:
`AlgebraicGeometry.Scheme.RingedRestrictionExchange.open_descent`.
Added 0 holes; split off 0 holed statements. The new open-cover detection theorem
and both of its private helpers are proved. The new module compiled in 17.9 s.
The final item compiled in 31.7 s through lcompile.py. Both files meet the
60 s limit. The import-direction check and the new dependency closure check
found no cycle. This is a partial proof delivery.

Five original holes remain in the item, all attached to
`lem-sf-ringed-restriction-exchange-open-descent`, in namespace
`AlgebraicGeometry.Scheme.RingedRestrictionExchange`:

- `open_comparison`
- `open_sectionwise`
- `openCube_exists`
- `open_restriction`
- `identity_normalization`

`open_descent` uses the existing `open_comparison` and `open_restriction`
declarations, whose proofs remain holes. No new assumption replaces either one.

## No longer needed

Step 8 no longer needs `lem-weil-pbc-ringed-restriction-local-iso` or a proof
import of `Sheaf.Paper.RingedRestrictionLocalIso`. Its argument is implemented
through native inverse image and homology, avoiding the separate derived-category
instances on all slice sites. The obsolete proof-dependency and top-level
`tool_uses` entry are removed from the item node. This module was not imported by
the initial item, so no Lean import line is removed and no existing module is
withdrawn.

The ringed open comparison and scalar-extension ring-isomorphism theorem remain
needed. The other five unfinished clauses retain their existing dependencies.
The new module imports only the ordinary operations, the two transport tools,
exact derived functor homology, pro-etale open coverings and sheaf locality.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The generic slice-local detection theorem in the
original eighth step does not directly accept the native scheme inverse-image
functors of OpenCube. The new complete proof supplies that transport and applies
the underlying sheaf locality theorem directly. This changes the implementation
below the unit level and preserves the original covering-sieve argument.

## New nodes

`lem-sf-proetale-ringed-open-cover-reflects-iso` states native open-cover detection
for ordinary unbounded derived categories over arbitrary ring sheaves and
isomorphic presentations of inverse-image rings. Its module is
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenCoverReflectsIso`; it has zero holes.
The existing Mathlib leaf `lem-weil-pbc-base-change-image` supplies the
point-lifting formula for both covering arguments. Sources are Stacks 00XZ and
0EYZ (localization) and 05RM (cohomology localization
criterion), as expanded in the inherited eighth proof step. Searches through
LeanSearch, Loogle, LeanFinder, Mathlib, the source library, Sheaf and the blueprint
found generic sheaf/homology tools but no duplicate native arbitrary-ring theorem.
The condensed and completed-coefficient cover detection statements have different
coefficient and geometric hypotheses. No change record is needed because no
existing interface is changed.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
