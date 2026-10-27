## What changed

Replaced the single proof hole in
`AlgebraicGeometry.Etale.etaleGraphProductShrinkLift` without changing its statement,
its four boundary definitions, or any other existing module. The proof follows the
specified shrinking subgrid and stops before the Q exchanges.

The proved private helpers compare the source/composite graph triangles, compare
the two horizontal B pastings, and move the middle graph triangle across the mixed
square. A private lemma for arbitrary categories assembles these comparisons by
naturality. The final step applies the middle suffix to the result and uses its tail's
naturality. Every private helper has a complete proof; none introduces a new obligation.

Added proof-only `import all` imports of
`Sheaf.AlgebraicGeometry.EtaleGraphProperAmbientMiddle` and
`Sheaf.AlgebraicGeometry.SfExactExchangePasting`. These reuse their existing proved
`graph_sh_id`, `unbounded_sh_comp`, and `unboundedFormalism` helpers to identify the
canonical right unit for the derived open compositor. The original public import
is unchanged. The complete remote compile succeeded in 49.4 seconds; development
profiling options and its style warning were removed before delivery. Updated this item's DAG proof and proof dependencies to describe the
implemented comparisons and these reused normalization helpers.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.etaleGraphProductShrinkLift`
(node `lem-pur-etale-graph-product-shrink-lift`): 1 of the original 1 holes.
Added: 0 holes. Left in the delivered module: 0 holes. Split off: 0 statements.

The proof uses the already stated normalized proper/open exchange cube. Its
independent remaining obligations are not copied or reproved here. This is a proof
from the existing declarations, rather than a claim that all transitive dependencies
of the project targets are now free of holes.

## No longer needed

The separate dependency
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition` is unnecessary for this
proof: the concrete derived pushforward compositors already in the library and
their naturality suffice. Removed that edge from this item's proof dependencies.

The theorem `etaleGraphProductAmbientPasting` is not applied. The ambient geometry
and shrink-word definitions from its public import chain remain necessary, so its
node is retained for those definitions. The already proved `vf_BW` supplies the
small commutative square directly; no fresh cancellation proof is needed.

Neither ambient/product Q exchange, `productSquareInterchange`, nor ambient
`squareInterchange` is used. No existing import was removed, and no module was
withdrawn or made unreachable by this delivery.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was needed. The original plan was usable, but
its abstract ringed-topos composition dependency was broader than necessary.
Graph-triangle normalization, compositor naturality, and cancellation establish
its comparisons directly. The unit normalization for the derived open compositor
is reused from existing proved helpers rather than postulated again.

The argument works uniformly for both selected sides and uses only equality,
commutative squares, and their pasting laws; it imposes no nonemptiness or other
extra hypothesis on the open neighborhoods. No unit route was bypassed.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
