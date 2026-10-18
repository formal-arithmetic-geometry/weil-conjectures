## What changed

Proved `AlgebraicGeometry.nagataQCOpenEqEventually` in
`Sheaf.AlgebraicGeometry.NagataQCOpenEqEventually`, preserving its signature and imports.
The proof reconstructs precisely the existence proof used by
`nagataQCOpenEqualityStage`, reads its chosen stage and equality witness, and rewrites
that equality using `baseChangeDiagram_map_fst`. The existing
`le_directedFiniteUpperBound` puts the witness index below the selected stage and hence
below any later index. An explicit morphism in the over category pulls the equality back;
compatibility of the first projections identifies it with the required equality.

The item compiled through `lcompile.py` with no errors or warnings (3.6 seconds reported
for Lean). No definitions, statements, visibility, or public imports changed.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.nagataQCOpenEqEventually`
(node `lemma-nagata-qc-open-eq-eventually`). Added 0 holes; split off 0 statements.
There are no remaining sorries in the delivered module.

The proof uses the already stated `le_directedFiniteUpperBound`
(node `lemma-nagata-directed-finite-upper-bound`), whose proof is still a sorry in its
existing module. This delivery does not claim to close that downstream obligation.

## No longer needed

None. All three existing imports and all stated proof dependencies are used.
The geometric equality-witness route in the node is followed without additional nodes.

## Where the brief, the DAG or earlier work was wrong

No repair was needed. The current blueprint describes chartwise radical witnesses,
whereas the landed selected-stage definition and corrected node explicitly use
Mathlib's proved compact-open equality descent theorem (Stacks 01Z4 (2)). The proof
follows that actual definition and the node's existing proof plan; it proves exactly
the unchanged eventual-equality conclusion. The unit's realized statement and step
lists are empty, and no unit route is bypassed.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
