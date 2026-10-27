## What changed

The assigned composition theorem is proved by inverse cancellation from the forward
projection square. All existing public signatures, definitions, naturality proofs and
tensor-associativity proofs are preserved.

SfGraphProjectionData explicitly constructs the successive projection for a
proper/open/proper presentation, the first graph presentation of the existing compositor,
and its remaining tail. The wrappers sfCompactProjection and sfGraphPresentationComparison
share the exact tensor and presentation-functor endpoints in the two squares, avoiding
expensive implicit conversion of the derived constructions. Its factorization theorem is proved by reflexivity against
sfGraphCompactSupportCompIso. No arbitrary data is selected from a postponed theorem.

SfEtaleCompactProjectionForward pastes two strictly separate squares by categorical
rewrites. The assigned module privately imports this proved assembly and cancels the
three invertible forward projections via a proved equality with their endpoint wrappers. Local elaboration attributes keep the large derived
constructions folded. Neither public definitions nor the original graph normalization change.

## Proved and sorry left

The original textual hole in
AlgebraicGeometry.Etale.sfEtaleCompactProjectionInverse_composition is closed by a
DECOMPOSITION, not a completed sorry-free proof: one original hole is replaced by two
strictly separate projection squares, net holes closed minus added -1.

Exactly two new holes remain, each in its own module, with body exactly `:= by sorry`:

- AlgebraicGeometry.Etale.sfGraphCompactificationComparison_projection, node
  lem-sf-etale-graph-word-projection-square, in SfGraphWordProjectionSquare.
- AlgebraicGeometry.Etale.sfGraphCompositionTailIso_projection, node
  lem-sf-etale-graph-composition-tail-projection, in SfGraphCompositionTailProjection.

No sorry remains in the assigned module, the explicit data module, or the forward
assembly module. AlgebraicGeometry.Etale.sfGraphCompactSupportCompIso_factor and
AlgebraicGeometry.Etale.sfEtaleCompactProjectionForward_composition are proved.
There are no definition holes. The graph-model square concerns a single presentation;
the tail square begins at the intermediate graph word and contains no projection for ch.
Both cover identity and empty opens, proper-only presentations, the zero ring, and
unbounded inputs without quasi-compactness assumptions.

## No longer needed

No existing import is removed and no module is withdrawn. The proved compatible-tower
result in CompactificationProjectionComposition was inspected but is not imported:
it uses a tower compositor and does not identify the specified arbitrary-base graph map.
The proof uses no unspecified witness from exists_rightDerivedLowerShriekCompIso.

The parent now uses the forward assembly, which uses the two graph squares. Geometric
and tensor-comparison ingredients of the original steps 3--7 remain dependencies of those
squares. No pruning of their modules is claimed. Removed obsolete direct tool_uses from
the parent: lem-amb-open-projection-composition, lem-sfb-ringed-projection-tensor-composition,
lem-weil-pbc-proper-base-change, lem-weil-pbc-proper-composition,
lem-etale-unbounded-compact-support-composition, lemma-nagata-proper-to-separated-target,
lem-weil-pbc-open-immersion-base-change, and def-weil-proper-morphism. Their remaining
uses are recorded on the new nodes.

## Where the brief, the DAG or earlier work was wrong

No mathematical error is asserted. The graph-model declaration supplies the specified
comparison but not its tensor square. The tower projection theorem does not supply
that missing clause for arbitrary graph factorizations. These are explicit separate
steps retaining the original route. The existing parent's blueprint ancestor is unresolved:
blueprint_refs.py ancestor returns None. New nodes preserve that computed ancestry and
specify the actual paragraph and parent steps in from.place.

## New nodes

`def-sf-etale-graph-word-projection`: explicit graph-word projection, composition graph,
tail isomorphism, and proved factorization in SfGraphProjectionData; no hole.

`lem-sf-etale-graph-word-projection-square`: the single graph-model square, with the
B1/intersection/inverse-B2 proof in words; one named hole.

`lem-sf-etale-graph-composition-tail-projection`: remaining graph replacements and inverse
comparison for cf, with complete proof in words; one named hole.

`lem-sf-etale-graph-forward-projection-square`: direct categorical pasting of those two
squares, proved in SfEtaleCompactProjectionForward; no hole.

No existing statement or definition is repaired, no forced adaptation is made, and no
change record is needed.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
