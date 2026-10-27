## What changed

The original theorem statement is unchanged. Its proof cancels two graph-side words in
the shrinking case, and applies pairwise product normalization plus two instances of a
selected-row pasting identity in the two-diagram case. A private categorical lemma
proves the final cancellation and naturality calculation componentwise, using
Mathlib's whiskering API.

The original explicit definitions move verbatim to EtaleGraphInterchangeData, publicly
re-exported by the item. This permits the intermediate statements to depend on those
definitions without an import cycle. The exchange laws remain those of the original cube theorem.

The new geometry modules construct the shrinking-neighborhood map and the products
used by the DAG's argument. The products are explicit pullbacks; their two projections
prove the graph equations, and the separated diagonal proves the two inclusions proper. The product boundary uses the inverse exchange for the
Cartesian square comparing products over Y and Z, followed by the product proper/open
exchange. It is an explicit word, rather than an arbitrary isomorphism with these
endpoints. No source-library module, target statement, or unit route changes.

## Proved and sorry left

This is a decomposition, not a net closure of the mathematical obligation. The original
hole `AlgebraicGeometry.Etale.etaleGraphComparisonInterchange` is replaced by a complete
combining proof. Three strict intermediate holes are added, one per module:

- `AlgebraicGeometry.Etale.etaleGraphShrinkSidePasting`
  (`lem-pur-etale-graph-shrink-side-pasting`): only the second Cartesian side and graph
  triangle, without the intersection or final graph comparison.
- `AlgebraicGeometry.Etale.etaleGraphShrinkMiddlePasting`
  (`lem-pur-etale-graph-shrink-middle-pasting`): only the intersection graph triangles,
  without the second-side exchange.
- `AlgebraicGeometry.Etale.etaleGraphProductRowPasting`
  (`lem-pur-etale-graph-product-row-pasting`): one selected row to the explicitly defined
  common product boundary. It has no comparison between the two interchange maps and
  no auxiliary compactifications cf or ch.

The original file has zero literal holes; the delivery adds three, so one hole is
closed syntactically and three added (net minus two). Definitions contain no holes.
The shrinking geometry and explicit neighborhood words compile. The product geometry,
explicit common boundary, selected-row statement, and original theorem all compile in
import order with no diagnostics. Each compile uses the project's lcompile.py overlay.
The final theorem is a complete Lean combination of the three named substeps and the
existing pairwise-normalization declaration. Existing holes in the graph model, pairwise
normalization and exchange cube are used as their stated dependencies, without changing
them.

## No longer needed

The proof follows the original product-grid route; no unit statement or step is bypassed. The product boundary only needs the
commutative proper/open square B: the chosen exchange is an isomorphism for all such
squares. An unused auxiliary theorem proving B Cartesian was removed; the selected-row
proof can establish that geometric fact locally when matching its Cartesian cells.
The original private imports of EtaleLocallyClosedGraphModel, Pullback.HasPullback,
RingedDerivedMonoidalComparisons, ClosedImmersion, and Whiskering are removed from the
item. The graph-model and pullback declarations remain available through the public
statement dependencies. ClosedImmersion is imported where the product geometry needs
it. Generic category operations are available from the imports already required for
the explicit words.

The node `lem-sfb-ringed-derived-monoidal-comparisons` is no longer a direct dependency:
the final combination uses only functor associators, componentwise naturality and
cancellation; the explicit words use the existing proper and open compositors. It may
remain needed elsewhere. No module is withdrawn or claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The first graph lifts agree propositionally through a' v = a, rather than definitionally.
The intermediate words therefore include the transport between their first-side words.
The products over Y and Z must remain distinct; the maps BV and BW are proper closed
inclusions. The new product maps use explicit pullback types so that dependent rewriting
does not have to unfold the presentation abbreviations. The construction and the inverse B exchange retain
that distinction. No mathematical correction to the original statement was needed.

The retained obligations are the genuine side, intersection and row pasting
calculations already singled out in steps 2 and 6–7 of the DAG, with complete prose
proofs in their modules. Empty sources, identity opens and repeated diagrams preserve
the equations; no quasi-compactness, boundedness or Noetherian hypothesis is introduced.

## New nodes

`def-pur-etale-graph-interchange-data` owns the unchanged moved diagram definitions and
the normalized exchange family.

`lem-pur-etale-graph-neighborhood-geometry` records the induced open map, its Cartesian
square, and the graph and ambient projection identities.

`def-pur-etale-graph-neighborhood-words` gives the explicit side and middle words and the
inverse neighborhood triangle; the graph properness proofs use proper-to-separated.

`lem-pur-etale-graph-shrink-side-pasting` isolates the horizontal/vertical side-square
calculation. `lem-pur-etale-graph-shrink-middle-pasting` isolates cancellation on the
intersection of neighborhoods.

`lem-pur-etale-graph-product-geometry` gives the products, proper inclusions, projection
identities and commutative B square. `def-pur-etale-graph-product-interchange` defines
the fixed boundary through B and Q0 with the stated compositors.

`lem-pur-etale-graph-product-row-pasting` records the single selected row needed twice
in the proved final cancellation. All nodes inherit the original null blueprint
ancestor and the same chapter and unit. Blueprint searches for graph neighborhood and
product graph found no imported blueprint duplicate. Existing graph-model, cube and
pairwise-normalization declarations were read before forming these substeps.

Change record: `coord/changes/etale-graph-interchange-data.md`.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
