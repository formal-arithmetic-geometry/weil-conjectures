## What changed

Proved `AlgebraicGeometry.closedPoint_of_affineOpen` in
`Sheaf.AlgebraicGeometry.ClosedPointOfAffineOpen`. First install the Jacobson-space
instance from `LocallyOfFiniteType.jacobsonSpace f`, realizing the node's first
step. Then apply `Topology.IsOpenEmbedding.preimage_closedPoints` to the open
subtype inclusion `U.isOpenEmbedding'`, realizing the second step. Mathlib's
open-embedding theorem supplies the locally closed singleton argument already
described in the node. The statement, docstrings and import stay unchanged.

The single-file compile through `lcompile.py` passed without warnings. The proof
works for any open subset; it does not need the given affineness hypothesis.
For an empty open subset there is no point `x`, and for the whole space the
same argument applies. No extra hypotheses or constructions were introduced.

## Proved and sorry left

Closed the one existing hole in
`AlgebraicGeometry.closedPoint_of_affineOpen`
(node `lem-sc-affine-maximal-points-closed-in-lft-scheme`).
Proved 1 of 1 holes; 0 holes remain; 0 holes added; 0 split off.

## No longer needed

None. No imports were added or removed, and no nodes or modules were pruned.
The original proof dependencies remain applicable: the Jacobson property is
the Mathlib leaf `lem-sc-lft-over-field-jacobson-space`, and the affine-spectrum
and closed-point definitions still occur in the statement. Mathlib already
contains the elementary open-embedding step, so no separate intermediate
statement is necessary. The unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

None. The proof follows the two stated steps, with the second discharged by
Mathlib's existing open-embedding theorem. The source Stacks lemma in
`literature/stacks-project/varieties.tex` confirms the required Jacobson property.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
