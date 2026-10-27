## What changed

Proved `AlgebraicGeometry.geometric_pure_fibre_point_dimension` without changing its
statement or imports. Mathlib supplies local finite type, base-change stability and
surjectivity. The proof combines `fibre_dimension_after_base_change` with
`topologicalKrullDimAt_eq_of_equidimensional_open`. Proved private helpers transport
local dimension by homeomorphisms, identify fibres over field spectra with their
underlying schemes, and transfer purity to the top open subtype. Updated the item's
DAG proof to describe these identifications and the direct Mathlib finiteness instance.

## Proved and sorry left

Closed one existing hole: `AlgebraicGeometry.geometric_pure_fibre_point_dimension`
(node `lem-trf-geometric-pure-fibre-point-dimension`). Added zero holes, split off
zero statements, and left zero `sorry`s in the delivery. All four private helpers
are proved. This is a proof, not a decomposition. The server single-file compile
passed cleanly in 3.1 seconds.

## No longer needed

The dependency `lem-weil-pbc-lft-pointwise-criterion` is unnecessary here: Mathlib's
instance deriving `LocallyOfFiniteType` from `LocallyOfFinitePresentation` supplies
this step directly. Removed that dependency and its obsolete tool-use entry from
the item node. No Lean module or import is removed; both existing proof imports
are used, and no other dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The DAG's fibre-dimension comparison
is implemented on the ordinary-fibre structure morphism; the private homeomorphism
argument makes the identifications of its fibres explicit. The nonemptiness needed
by `hpure` comes from the surjective lift, so no nonemptiness or flatness hypothesis
is added. The proof works for d = 0, for any geometric lift, and for arbitrary field
characteristic; an empty source has no point x to consider. The unit route is preserved.

Searches used the launcher's LeanFinder, Loogle and grep services and local searches
in Mathlib and both library roots. No shorter theorem matching the full result was
found. The sources checked were Stacks Algebra 00P4, Morphisms 02FY (1), and Varieties
0A21 (3), (5). No new public declaration or definition is introduced.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
