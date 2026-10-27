## What changed

Proved `AlgebraicGeometry.Etale.etaleCompactSupportGraph_coherence`, with its statement
unchanged. Its module and the shared normalization-formula definition are edited. Base change reuses the existing arbitrary-base
comparison equation in `GraphExchange`. Refinement follows from graph normalization,
monicity of the inclusion into ordinary direct image, and the derived-unit composition
formula. Identity follows from sheaf normalization and exact-derived identity equations.
All private supporting results are proved.

Repaired return `0b1d3eae651` by removing all five duplicate declarations. The proof imports
and reuses `homotopy_comp_inv` from `EtaleCompactSupportGraphGeometricBaseChange` and
`open_compare_mono` from `UnboundedProperOpenComposition`. Direct image preserves the
latter monomorphism. A generic adjunction calculation handles successive transports of
a right adjoint and the transpose of a section of an invertible counit; its application
to the existing `lowerStarUnit_comp_counit` equation proves the needed open graph
normalization. None of the four downstream comparison lemmas is copied or relocated.
The repaired proof pins the monomorphism and composition-isomorphism arguments and
uses explicit graph-normalization and direct-image-unit rewrites. The open graph
normalization identifies the adjunction constructions by congruence.

The shared `normalizationHomotopyComponent` factors the existing five-arrow formula
through a general abelian-category construction. The corresponding natural
transformation is assembled generically and descended through the same localization. The concrete homotopy comparison
specializes this same formula. This preserves the constructed map and avoids repeated
expansion of concrete sheaf instances when applying general coherence calculations.
The identity comparison uses the same local abelian preadditive projections as
the generic identity calculation. No data is chosen from an existence theorem. The change record records the definition
refactor and the local proof-elaboration settings. The node records describe the
implemented argument and attach the shared formula to the existing definition node.
The two unclaimed consumers `EtaleCompactSupportFiniteGraphIso` and
`EtaleSupportMapCompatibility` explicitly unfold `normalizationHomotopyComponent`
at their existing formula-unfolding steps; all their signatures remain unchanged.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Etale.etaleCompactSupportGraph_coherence`
(node `lem-asd-compact-support-graph-coherence`). All three fields are proved.
Holes added: zero. Sorries left in the delivered module: zero.
No split-off obligations or new axioms are introduced. Existing prerequisites retain
their existing proof obligations.

## No longer needed

The refinement proof does not use the adjoint-projection node
`lem-asd-proper-open-refinement-adjoint-projection` or its module
`Sheaf.Paper.ProperOpenRefinementAdjointProjection`, nor the separate interchange result
`lem-amb-unbounded-proper-open-interchange` in `Sheaf.Paper.UnboundedProperOpenInterchange`.
Graph normalization and monicity give the forward refinement equality directly.
The direct open/closed vanishing proof edge is unnecessary because the existing
`open_compare_mono` supplies monicity.

Direct proof edges to `def-weil-pbc-etale-shriek-base-change-map`,
`def-weil-pbc-adjunction-conjugate`, `lem-weil-pbc-mate-pasting`, and
`def-kun-unbounded-exchange` are replaced by the existing graph base-change result.
The direct composition edge to
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition` is replaced by the generic
composition calculation already proved in `UnboundedProperOpenComposition`.
These are removed direct edges; results still used transitively remain needed.

Removed redundant proof imports `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`,
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`,
`WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`,
`Sheaf.Paper.ProperOpenRefinementAdjointProjection`, and
`Sheaf.Paper.UnboundedProperOpenInterchange` from the earlier packet.
Removed the five duplicate private declarations identified by the return.
The direct normalization-data proof import is retained to order the sandbox's changed
definition before its proof consumer. No module is withdrawn or source declaration removed.

## Where the brief, the DAG or earlier work was wrong

The earlier packet duplicated five existing lemmas, as the return correctly identified.
The downstream module cannot be imported here because that would create a cycle.
Independent prerequisites already provide the monicity and homotopy cancellation needed
by this proof, so relocating those duplicate lemmas is unnecessary.

The planned adjoint-projection and separate interchange argument is longer than needed:
graph normalization determines the sheaf maps inside ordinary direct image, and generic
derived-unit algebra gives the prescribed refinement equation. The existing geometric
base-change module internally proves the arbitrary-base equation needed here.
No statement is weakened, and the blueprint unit route is unchanged.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
