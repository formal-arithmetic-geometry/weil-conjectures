## What changed

Replaced the single `sorry` in
`AlgebraicGeometry.Monoscheme.toric_realization_finite_type` by a complete Lean proof
from the existing finite-chart and lattice-coordinate declarations and one smaller
component-action obligation. The theorem signature and the two group-object
abbreviations are unchanged. No existing module besides the assigned item is changed.

The proof uses `finite_chart_components_realization` for reducedness, finite type,
quasi-compactness, the component equivalence and integrality, and
`finite_chart_components_algebra` for each finite lattice basis. It uses
`latticeTorus_coordinates` for the group isomorphism and `latticeTorus_finiteType`
for the finite-type conclusions. The canonical-action formula follows from the
choice specification of `existsUnique_torusAction`.

For smoothness, the already proved adopted source theorem
`AlgebraicGeometry.smooth_of_grpObj_of_charZero` applies to the canonical torus group.
The proof explicitly transfers injectivity of natural-number casts from Q to ULift Q.
Smooth base change, geometrically reduced fibres, local Noetherianity of a finite-type
scheme over a field, and Mathlib's reduced flat base-change instance give the product
claims. An explicit section from the Hopf counit proves surjectivity, including empty
bases. This avoids the separate split-lattice projection argument entirely.

Two private helpers also prove the finite-coproduct clause directly from Mathlib and
the existence of the augmentation section. The coproduct proof uses the summand open
cover, compactness, locality of finite type, and a surjection from the finite disjoint
union of the summands' connected-component sets. It does not assume a positive rank,
a nonempty family, or a nonempty base.

Added `Sheaf.AlgebraicGeometry.ComponentTorusActionLaws`, containing only the remaining
component-action statement, with its source and complete monomial/gluing proof in words.
Updated the assigned DAG node to the actual proof route. New proof imports are private;
all original public imports are preserved.

## Proved and sorry left

Closed 1 of the item's 1 original holes:
`AlgebraicGeometry.Monoscheme.toric_realization_finite_type`
(node `lem-trf-toric-realization-finite-type`). Its combining proof compiles without a
`sorry`, as do the three private helpers.

Added 1 hole:
`AlgebraicGeometry.Monoscheme.component_torus_action_laws`
(node `lem-trf-component-torus-action-laws`), in the new module
`Sheaf.AlgebraicGeometry.ComponentTorusActionLaws`.
It asserts only the associative unital action laws for the specified coaction on one
component. It asserts none of the parent's reducedness, finiteness, basis, torus
coordinate, smoothness, surjectivity, product or coproduct conclusions.

This is a decomposition: 1 upper hole closed and 1 strictly smaller hole added, net 0.
The existing finite-chart and lattice-coordinate holes remain in their original
modules; this packet does not modify them. No hole is added to a definition.

## No longer needed

Removed the item's direct private imports
`Sheaf.RingTheory.GeometricallyReducedBaseChange` and
`Sheaf.RingTheory.AffineMonoidAlgebraNormalization`. The proof obtains the chart
results from `MonoschemeFiniteChartComponents`, and product reducedness from smooth
geometrically reduced base change, rather than using these algebra lemmas directly.
This does not assert that those modules have no other users or are globally withdrawn.

The declared proof dependency `lem-trf-split-lattice-torus-projection`, module
`Sheaf.AlgebraicGeometry.SplitLatticeTorusProjection`, is no longer needed by this
proof and is removed from this node's `proof_deps`. Cartier smoothness over the actual
rational base and the explicit counit section give its needed conclusions. None of
the node's other original direct proof dependencies is removed. The subsidiary
square-zero lifting argument, Laurent projection presentation and additive-to-
multiplicative transport are therefore unnecessary here.

The connected-ambient `latticeTorus_action` declaration is not used; the other
coordinate and finite-type declarations of its module remain necessary. No source
library declaration is removed, no module is withdrawn, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing `latticeTorus_action` requires `ConnectedSpace M.space` and asserts that
the component inclusion is an isomorphism. The parent is about arbitrary, possibly
disconnected M. Applying it directly would require an unstated construction of the
restricted connected monoscheme and comparison of its realization and action with
the original component. The new obligation isolates the actual chartwise action laws
on that original component, without the false claim that its inclusion is an isomorphism.
Its proof in words uses only component charts and therefore works for disconnected M.

The recorded projection dependency is a legacy non-`module` file. The first import
probe produced `cannot import non-`module` Sheaf.AlgebraicGeometry.SplitLatticeTorusProjection
from `module``. The final route does not import or modify that dependency. No adaptation
of the module held by E8 is delivered.

The broad historical proof plan in the item's existing docstrings predates its newer
DAG dependencies. The updated node and the Lean body describe the actual shorter route.
The unit record has no realized statement or step that this replacement bypasses.

## New nodes

`lem-trf-component-torus-action-laws` records
`AlgebraicGeometry.Monoscheme.component_torus_action_laws`. Its source is ILO VIII
3.2.2 and 3.2.4, printed p.103, read in the PDF. On each chart the two associativity
comorphisms send a monomial to the same triple tensor, and the unit composite fixes
it. Restriction compatibility and the chart product covers give the global laws.
The docstring and node explain the over-base condition and preservation of chart opens.
Rank zero gives the trivial group; the empty ambient monoscheme has no component;
additional disjoint ambient components never enter the argument.

The searches recorded in the node were actually run through `msearch.py`: LeanSearch,
LeanFinder, corrected fully qualified Loogle, and grep. Project source and DAG searches
found only the connected-ambient action theorem. A whole-blueprint search for
`torus action` found no matching blueprint node; the verified ancestor is
`lem-trf-local-term-locality`. There are no change records, since no existing interface
is changed.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
