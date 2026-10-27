## What changed

Replaced the comparison-equation hole in
`Sheaf.AlgebraicGeometry.EtalePairwiseProductGraphNormalization` by a proof factoring
both displayed lambdas through their literal supporting-neighborhood presentations.
The proper-ambient move identifies the first half of each lambda; the open-shrinking
move identifies its second half. Equating the two composites from the supplied
compactification and cancelling its graph comparison gives the requested formula.
The geometry, all existing definitions and all existing theorem signatures are preserved.

Two new modules state the separate invariance calculations for a Cartesian proper
change of ambient scheme and for a shrinking with ambient scheme fixed. They import
only the explicit graph-comparison API in their public interfaces. The original module
imports them privately. Its DAG proof records this factorization and cancellation.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.Etale.etalePairwiseProductGraphNormalization`
(node `lem-pur-etale-pairwise-product-graph-normalization`) by a complete combination
proof, conditional on two new elementary-move theorems.

Added two holes:

- `AlgebraicGeometry.Etale.etaleGraphComparisonFromOpen_properAmbient`, node
  `lem-pur-etale-graph-comparison-proper-ambient`.
- `AlgebraicGeometry.Etale.etaleGraphComparisonFromOpen_openShrink`, node
  `lem-pur-etale-graph-comparison-open-shrink`.

This is a decomposition, not a net proof: one old hole closed and two new holes added.
There are zero textual holes in the item module and one in each new module.
The product geometry and projection identities were already proved on the base.

## No longer needed

No library module is withdrawn. No existing public import is removed.
The proof does not use the theorem `etaleGraphComparisonBaseChange`: its module remains
necessary for the explicit graph-comparison definitions. It also does not use
`etaleGraphComparisonInterchange`, whose second clause depends on this item; importing
that theorem would make the planned argument circular.

The explicit triple-product construction and total-intersection maps in old proof
steps 2--10 are replaced by the two generic elementary moves. Their geometric and
exchange inputs remain needed below those moves; they are not claimed globally pruned.
The graph-model and compositor dependencies are retained in the new nodes.

## Where the brief, the DAG or earlier work was wrong

The brief's statement that the module contains a hole is current; its product geometry
has already been proved and was left intact. The node's detailed triple-product plan
is valid but hides two reusable invariance calculations behind its projection-grid
substitutions. The delivery exposes precisely those calculations instead of assuming
that they follow from the endpoints of graph isomorphisms.

The required blueprint ancestor command returns `None` for this agent-created chain.
The new nodes preserve that null ancestor and record their exact source steps and the
existing chain's intended blueprint place. Searches for shrinking and proper ambient
changes found no independent existing node with these statements. The existing parent
interchange node discusses shrinking, but its combined theorem also depends on this
item and is not used as a black box.

## New nodes

`lem-pur-etale-graph-comparison-proper-ambient`, in
`Sheaf.AlgebraicGeometry.EtaleGraphComparisonProperAmbient`, is the invariance of the
specified B graph word under a Cartesian proper map of ambient schemes, with no open
shrinking. Its source is the two proper-projection grids in the item's steps 5--7,
using Stacks 0F7C and 0F7D. Its docstring specifies the neighborhood and intersection
pasting calculation and cancellation. The square permits identity or empty maps.

`lem-pur-etale-graph-comparison-open-shrink`, in
`Sheaf.AlgebraicGeometry.EtaleGraphComparisonOpenShrink`, is invariance of B under an
open shrink containing a supplied proper graph lift, with the proper ambient fixed.
Its source is the elementary neighborhood move of the parent interchange argument,
steps 1--3, and Stacks 0F7C/0F7D. The statement specifies the inverse triangle and
canonical open compositor exactly. Identity and empty opens satisfy the same formula;
neither a quasi-compact nor a Noetherian hypothesis has been added.

LeanSearch, LeanFinder, Loogle and Mathlib/project rg searches were run. They returned
mate/pullback pasting, unrelated normalization and ordinary-neighborhood facts, and
isomorphism cancellation. None supplies the two graph-word invariance statements.
No change record is required: no existing public signature or definition was changed.

The shrinking geometry was additionally checked in a scratch module: the two graph
lifts compose with the neighborhood/intersection maps as claimed, both maps are open,
and the neighborhood square is Cartesian by pullback cancellation. This verifies the
geometric first step; the exchange/compositor equations remain in the named theorem.

The purely categorical shrinking-word cancellation was also compiled separately.
The parent node's reviewed decomposition of the shrinking side grid is retained: stack
the neighborhood graph triangle above its Cartesian neighborhood square, then paste
that square horizontally with the old side square. Stacking the original triangle
directly over the old side square would have mismatched edges.

The proper-ambient first step was checked independently in scratch: the induced map
`P_t ×_Y c.Z → P_s ×_Y c.Z` is Cartesian over `pr`, hence proper, and the graph
map commutes with it by the two projection equations. All three packet modules
compile through the server in import order. Existing DAG statement, source and Lean
attachments are unchanged; only its proof route and dependencies are updated.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
