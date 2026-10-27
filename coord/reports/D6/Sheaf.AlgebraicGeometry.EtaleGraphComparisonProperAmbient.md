## What changed

Replaced the hole in
`AlgebraicGeometry.Etale.etaleGraphComparisonFromOpen_properAmbient` by a proof from
three independent component equations: the first side, the second side, and the
intersection word. The theorem's signature and sole public import are unchanged.
The three component modules are private proof imports of the item.

Added `EtaleGraphProperAmbientData`. It constructs the map between the two products,
the two maps of supporting neighborhoods, and the two transport isomorphisms using
pullback lifts and the specified Cartesian exchange and direct-image compositors.
It proves the product square is Cartesian and the product map proper, both
neighborhood squares Cartesian, and both equations relating the graph lifts.
Every definition is a concrete construction and every geometric theorem is proved.
No data is selected from a new existence theorem.

The final proof expands the specified graph maps into their first side, middle,
and inverse second side. A proved categorical cancellation lemma combines the three
component equations. In particular, the final theorem is not obtained by applying a
renamed version of itself.

The side and middle definitions in the existing `EtaleGraphNeighborhoodWords` module
cannot be imported here: that module imports `EtaleGraphComparisonBaseChange`
transitively, which already imports the assigned item. The new modules refer directly
to the existing `locallyClosedGraphSide₁`, `locallyClosedGraphSide₂`, and
`locallyClosedGraphMiddle`, without duplicating those public definitions.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.etaleGraphComparisonFromOpen_properAmbient`.
The assigned module now has zero holes. This is a decomposition, not a net proof:
one original hole is replaced by two strictly smaller obligations: transport composition
and compatibility of the middle word.

Holes added, and every hole remaining in the delivered Lean files:

- `AlgebraicGeometry.Etale.etaleProperAmbientTransport_comp`
  (`lem-pur-etale-proper-ambient-transport-composition`): the composition law for
  a single Cartesian proper/open transport. This theorem involves no graph,
  compactification, or intersection; the first and second side equations are
  proved from this law by evaluating two equal rectangles.
- `AlgebraicGeometry.Etale.etaleGraphProperAmbientMiddle`
  (`lem-pur-etale-graph-proper-ambient-middle`): middle word only, without either
  side comparison.

Both are public named theorems, one per new module, each with a source,
complete proof in words, and matching node. No other holes are introduced.
The geometry, both side equations, and the cancellation lemma have complete proofs.
All six delivered Lean modules compiled together with `lcompile.py --all`; the latest
reported times were 27.9--32.6 seconds per module, with no warnings or errors.

## No longer needed

No original import or module is removed, and no node is withdrawn. None is claimed
pruned. The old direct proof dependencies are now used through the three component
nodes where applicable, rather than being direct dependencies of the item.
The proper/open exchange cube, graph model, direct-image composition, open composition,
and pullback theory remain needed for those component proofs. Proper base change,
proper-to-separated, and open base change remain implicit in the existing graph model
and the proved geometric constructions; their modules are not withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The previous DAG gave the whole
coherence calculation in a single proof step. It did not give a theorem for any of
the three component equations. Those are now explicit independent components, and
the final combination is Lean code. Both side components are themselves reduced in
Lean to a single general transport composition law.

The edge cases were checked at the level of the constructions: all maps are pullback
lifts, so empty neighborhoods and identity ambient maps are allowed. The first-side
identity insertion is present on both paths. The middle equation cancels only proper/open
exchange isomorphisms for finite coefficients, not an arbitrary base-change map.
No quasi-compactness, Noetherianity, boundedness, or nonemptiness hypothesis was added.
The unit record `sk-prop-sf-cbc` has no realized step or statement node that this
reduction bypasses. The current blueprint composition proof and Stacks vertical and
horizontal pasting proofs were read.

## New nodes

`def-pur-etale-graph-proper-ambient-data` records the explicit proper product map,
its neighborhood maps, their proved equations, and the two transport constructions.
No sorry is attached to this node.

`lem-pur-etale-graph-proper-ambient-first-side` records the proved reduction of the first
side to transport composition and the common identity direct-image normalization.

`lem-pur-etale-graph-proper-ambient-second-side` records the proved comparison of the
two ways of evaluating the proper-projection grid for the second side.

`lem-pur-etale-graph-proper-ambient-middle` records vertical/horizontal pasting on the
intersection and cancellation of the intersection projection exchange.

`lem-pur-etale-proper-ambient-transport-composition` records the sole shared
proper/open transport composition law used to prove both side components.

All five nodes belong to the item's chapter and unit. LeanSearch, Lean Finder,
Loogle, and source grep were run. None gave an independent theorem for these graph
coherences; Loogle supplied the general isomorphism associativity API.
No existing definition, statement, or consumer was changed, so no change record or
forced adaptation is needed.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
