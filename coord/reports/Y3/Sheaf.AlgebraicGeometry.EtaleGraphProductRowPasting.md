## What changed

Replaced the proof hole in `AlgebraicGeometry.Etale.etaleGraphProductRowPasting`
by the combination of the proper ambient and graph shrinking pasting identities.
Its statement and its three existing lambda definitions are unchanged. The only
new import in the item is a private proof import. The old setting disabling
`backward.isDefEq.respectTransparency` is replaced by `true`; the proof uses normal transparency.

The new `EtaleGraphProductAmbientPasting` module constructs the three selected
proper ambient presentations and the mixed neighborhood `N = V_n ×_Z P_m`.
Its B and Q maps, their commutation and graph/projection equations, and all
required proper/open morphism properties are proved from pullback projection
identities and existing geometry. The intermediate interchange is built from
the specified normalized B and Q exchanges and canonical compositors. It is
not chosen from an existence statement or defined using the desired row equality.
The module also factors each existing lambda into its proper ambient factor
and its inverse graph-triangle factor.

`EtaleGraphProductShrinkPasting` states compatibility of the latter factors
with the intermediate and final boundaries. The main proof composes the two
subgrid equalities and uses naturality to commute the two middle factors.
The node proof now records this actual combination.

## Proved and sorry left

Original holes closed: 1, in
`AlgebraicGeometry.Etale.etaleGraphProductRowPasting`.
No sorry remains in the item module.

Holes added: 2, both in named public theorems, each in its own module:

- `AlgebraicGeometry.Etale.etaleGraphProductAmbientPasting`
  (`lem-pur-etale-graph-product-ambient-pasting`).
- `AlgebraicGeometry.Etale.etaleGraphProductShrinkPasting`
  (`lem-pur-etale-graph-product-shrink-pasting`).

This is a decomposition, not an unconditional proof of the original obligation:
one upper hole is closed using two strictly smaller subgrid obligations, so the
local net hole change is +1. The first subgrid contains only proper ambient side
exchanges and the original square; it contains no inverse graph shrinking
triangle. The second contains only graph shrinking triangles and the fixed
product boundary; it contains neither the original supplied square interchange
nor any proper ambient lambda. Each has a complete sourced argument in its
node and docstring, and neither is the original statement with renamed data.
All new definitions have explicit bodies and no holes.

Validation: all three modules compiled on the server. The ambient construction
compiled alone in 15.7 s and in the full sandbox run in 53.8 s; the shrinking
statement compiled in 45.9 s; the completed item proof compiled in 7.2 s.
The item compile's sole empty-line style warning was removed before delivery.
The delivery command performs the final compilation, axiom and packet checks.
The first delivery check caught the unparenthesized match signatures in the new
node records. Parenthesizing each match makes the complete proposition visible
to the checker; both recorded signatures now use its exact extraction, and both
theorem bodies are exactly `:= by sorry`.
Static checks confirm the two named holes, matching DAG dependency unions,
100-character Lean lines, and no forbidden declarations or transparency overrides.

## No longer needed

None. No existing module is withdrawn and no public import is removed. The
original plan dependencies on product geometry, pairwise product constructions,
proper/open exchange, proper and open compositors remain needed by the two
subgrids. The main node now cites those subgrids and the Mathlib whiskering
interchange; this relocates the uses rather than pruning their mathematics.
The unit route and all adopted source-library declarations are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement correction. The listed one-map graph comparison cannot replace
the composition calculation: its downstream composition-coherence consumer
already uses this row theorem, so importing that consumer would be circular.
The original node describes a multi-square pasting calculation rather than a
single directly applicable declaration. The delivery makes its proper ambient
and graph shrinking parts precise without claiming the graph-product extension
is a theorem stated verbatim in Stacks 0F7J.

The edge cases of empty schemes, empty or identity supporting opens, and a zero
finite coefficient ring require no extra assumptions: all maps are actual
pullback maps, and both subgrid arguments use pasting and invertible exchanges.

## New nodes

`lem-pur-etale-graph-product-ambient-pasting`: the proper ambient side-exchange
subgrid with the explicitly constructed mixed neighborhood and boundary.

`lem-pur-etale-graph-product-shrink-pasting`: the graph-triangle subgrid from
those neighborhoods to the intersections, with the fixed product boundary.

Both inherit the item's chapter, unit and blueprint ancestry. Actual LeanSearch,
LeanFinder, Loogle and Mathlib grep queries are recorded; they find geometric
and categorical tools but no exact derived product-grid identity. No existing
definition or declaration signature changes. The file-local transparency change
is documented in `coord/changes/etale-graph-product-row-transparency.md`; there
are no forced adaptations.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
