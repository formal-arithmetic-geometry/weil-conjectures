## What changed

Replaced the hole in `AlgebraicGeometry.Etale.etaleGraph_proper_tower` with a
categorical composition proof, keeping its statement and its original public imports.
The proof separates the proper Cartesian interchange from graph composition with an
open first leg. It combines these using the already proved associativity of the chosen
compact-support compositor, naturality, and cancellation of comparison isomorphisms.

Added `EtaleGraphChosenComparisons` with explicitly constructed comparisons for etale,
proper and open maps. These use the existing chosen compactifications and specified
adjunction units; no data is selected from a new existence statement. Added and proved
`graph_compactification_factorization` and `graph_proper_postcomposition` from the
existing every-triangle compositor equation and identity normalization. The item also
contains proved private helpers for congruence, square associativity, and categorical
pasting. No existing module besides the assigned item is changed.

Validation: the five new dependencies compiled together through `lcompile.py`, each
within 60 seconds. The final assigned module then compiled against those dependencies
in 20.5 seconds without warnings. The original theorem signature is unchanged, and
all delivered Lean lines have at most 100 characters.

## Proved and sorry left

The original hole closed is
`AlgebraicGeometry.Etale.etaleGraph_proper_tower` (one of one original holes).
Its proof is a decomposition, not a net reduction in the number of holes: two strictly
smaller geometric comparisons remain, each in a new module:

- `AlgebraicGeometry.Etale.graph_open_etale_composition`, node
  `lem-pur-graph-open-etale-composition`: graph compatibility for an open immersion
  followed by an etale map, without a proper Cartesian square.
- `AlgebraicGeometry.Etale.graph_proper_interchange`, node
  `lem-pur-graph-proper-interchange`: the proper Cartesian interchange, without an
  additional open source leg, its composite etale map, or a terminal compactification.

There are zero holes in the assigned module and two holes added in total. The two model
normalization theorems and all private composition helpers are proved. The three new
comparison definitions contain no holes.

## No longer needed

No original public import was removed: both are needed by the unchanged statement.
No module is claimed globally pruned. The original proof's direct geometric steps have
been replaced by the two separate comparison lemmas. The common-support sheaf
composition and graph sheaf/refinement coherence are still needed by those lemmas and
remain in their dependency records. The item no longer directly applies
`lem-amb-etale-adjoint-locality`; its definitions remain available through the original
statement imports. `def-kun-unbounded-exchange` is now cited by the proper-square
lemma, and `lem-asd-compact-support-graph-derived-isomorphism` still supplies the actual
comparison maps. In particular, `lem-amb-unbounded-compact-support-comparisons`,
`lem-asd-compact-support-graph-coherence`,
`lem-asd-compact-support-graph-sheaf-normalization`, and
`lem-cbc-proper-support-sheaf-composition` remain in the dependency records.
The original seven proof dependencies have thus either been retained
through the new steps or explicitly accounted for here. Nothing in the adopted source
library is removed or changed.

## Where the brief, the DAG or earlier work was wrong

The original DAG correctly describes the geometric argument, but its declared graph
coherence theorem provides base change, refinement and identity, rather than the
open-first composition equation needed here. The proper-support sheaf composition
result does not itself identify the specified derived interchange with the specified
mate. These are the two new geometric statements. The surrounding formal composition
argument and both unit normalizations are made explicit in Lean instead of being
included in another copy of the entire original obligation.

The new statements were checked on identity proper maps, identity and empty open
immersions, empty fibres, and the zero coefficient ring. None requires nonemptiness.
The blueprint unit route and the target signatures are preserved.

## New nodes

`def-pur-graph-chosen-etale-comparison`, `def-pur-graph-chosen-proper-comparison`, and
`def-pur-graph-chosen-open-comparison` record the three constructed comparison maps in
`EtaleGraphChosenComparisons`.

`lem-pur-graph-compactification-factorization` records the proved comparison of an
open/proper model with the chosen compositor.

`lem-pur-graph-proper-postcomposition` records the proved direct-image composition
normalization for postcomposition of a compactification with a proper morphism.

`lem-pur-graph-open-etale-composition` records the remaining open-first graph comparison.

`lem-pur-graph-proper-interchange` records the remaining proper-square mate comparison.

Every new node follows the original source ancestry. There are no change records,
because no existing definition, signature or other module interface changes.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
