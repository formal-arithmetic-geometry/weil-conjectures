## What changed

Filled `AlgebraicGeometry.Etale.etaleGraphAmbientSquarePasting` in the assigned
module. Its signature, coefficient universes, both Boolean cases and public import
are unchanged. Added `Sheaf.Paper.DerivedCompactSupportCompositionCoherence` as
a proof-only `import all`, to reuse its proved private `push_derived_assoc` helper. All new helper theorems in this delivery are private
and completely proved.

The proof reads the Cartesian, vertical and horizontal laws for the exact chosen
exchange family. `grid_core` equates the two vertical factorizations of the common
outer square and substitutes the horizontal factorization of the h-side square.
`full_grid` inserts the graph splitter and final proper direct image, moves them
through the exchanges by naturality, and matches the terminal compositors by
associativity. The public theorem specializes this calculation to both ambient
sides. Updated the item's node proof and proof dependencies to this implementation.

Source read: Stacks `more-etale.tex`, labels
`lemma-shriek-proper-and-open-compose` (0F7C),
`lemma-shriek-proper-and-open-compose-horizontal` (0F7D), and the final A--F
comparison of `lemma-shriek-composition` (0F7J). The latest blueprint's
`sk-prop-sf-cbc` and `sk-thm-sf-comp-composition` statements and the cited smooth
base-change coherence proof were also read. The unit route is preserved.

## Proved and sorry left

Closed the original single hole:
`AlgebraicGeometry.Etale.etaleGraphAmbientSquarePasting`
(node `lem-pur-etale-graph-ambient-square-pasting`).

Holes closed: 1. Holes added: 0. Sorries remaining in the delivered module: 0.
No new split-off statements or modules. The single-file server compile succeeded
in 47.8 seconds; the unused statement-let names it warned about were then prefixed
with underscores. The delivery tool checks the final file and its axiom probe.

## No longer needed

Imports removed: none. Modules withdrawn or globally pruned: none.

Removed the direct proof dependencies
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition` and
`lem-cbc-extension-zero-composition`. Their definitions remain available through
the unchanged public geometry import. The required proper-compositor associativity
comes from the proved `push_derived_assoc` helper in
`lem-amb-derived-compact-support-composition-coherence`, used as a generic tool.
Horizontal exchange pasting already includes the needed two-open compositors;
only their naturality is needed in the remaining calculation.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The original proof plan overstates the need
for a separate three-open associativity calculation: the h-side horizontal
pasting law already gives the specified E K compositor. The earlier broad
ringed-topos composition dependency is replaced by the existing concrete proved
étale compositor associativity helper.

The generic grid calculation imposes neither nonemptiness nor boundedness and
uses only the proper/open properties already present. Identity arrows and empty
opens are covered by the same exchange laws. No other existing module or node is
changed, and no public definition, attribute, import or declaration signature is
altered.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
