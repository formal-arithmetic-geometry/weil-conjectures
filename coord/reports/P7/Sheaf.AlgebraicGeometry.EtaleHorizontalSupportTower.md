## What changed

Replaced the proof hole of
`AlgebraicGeometry.Etale.etaleHorizontalSupport_tower` by a calculation through a
common graph compactification. The existing public signature, public imports and
all definitions are preserved. Two private proof imports supply separate geometric
steps:

- `Sheaf.AlgebraicGeometry.EtaleGraphOpenTower` states graph compatibility for the
  etale-first composition through the open leg. It does not involve the second
  compact-support composition, the proper square, sum exchange, or its inverse mate.
- `Sheaf.AlgebraicGeometry.EtaleGraphProperTower` states normalization of the
  proper-first composition. It has no upper open-square comparison or etale-first
  composition. Its only interchange is the proper Cartesian square.

Both use the explicit comparison k formed from the canonical graph map of an
actual compactification e, the proper direct-image compositor, and the usual
model-to-chosen comparison. No object or map is chosen from an existence theorem.
The item constructs e by `ofComp`, identifies the two congruences to the same
composite, substitutes both normalization equations, and cancels inverse maps.
Four proved private helpers establish congruence symmetry, congruence
composition, cancellation of the image of an isomorphism, and the final abstract
category calculation.

Validation: all three modules compile through the remote compiler within the
60-second limit. The final item compile completed without diagnostics in 10.2 s;
the two statement modules compiled in 39.6 s and 36.1 s.

## Proved and sorry left

Closed the original syntactic hole:
`AlgebraicGeometry.Etale.etaleHorizontalSupport_tower`
(`lem-pur-etale-horizontal-support-tower`). The item has zero remaining holes.

Added two holes, each the whole body of one public theorem in its own module:

- `AlgebraicGeometry.Etale.etaleGraph_open_tower`
  (`lem-pur-etale-graph-open-tower`).
- `AlgebraicGeometry.Etale.etaleGraph_proper_tower`
  (`lem-pur-etale-graph-proper-tower`).

This is a decomposition, not a closed geometric proof: one hole closed, two added,
net minus one before any independent downstream pruning. The two statements are
separate parts of the original tower argument, rather than another name for the
original comparison between both composition routes. Their docstrings and nodes
specify the sheaf graph calculations, derived-unit descent and refinement
cancellation that remain.

The edge cases require no extra hypotheses: identity open/proper maps use the
adjunction triangles and direct-image unit; empty graphs and the zero coefficient
ring yield zero sections. All equalities are of actual unbounded derived maps;
no equality is inferred from stalk maps or cohomology maps.

## No longer needed

No existing imports were removed and no module is withdrawn. No old mathematical
dependency is globally pruned: the graph sheaf normalization, graph-derived
comparison, graph refinement coherence, proper-support sheaf composition, exact
exchange and etale adjunction statements remain dependencies of the two geometric
parts. The item's direct proof dependencies now name those parts and the existing
unbounded compact-support comparison package. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The existing proof plan describes the two geometric
normalizations but supplies no declaration stating either one individually. Its
currently declared graph and tower interfaces do not directly state these
composition equations. The new statements isolate those precise steps; the
remaining congruence and cancellation calculation is implemented in Lean.

Mathlib and source searches found abstract mate/composition identities and related
refinement and base-change graph equations, but no theorem directly closing the
open-leg or proper/etale graph composition normalization. The Stacks sources
0F7B, 0F7F, 0F7J and the final item (3) of 0F7L were read in the local source.

## New nodes

`lem-pur-etale-graph-open-tower` is the etale-first open-leg graph normalization,
corresponding to original steps 1, 2, 4 and 5. It quantifies over a commuting
open/etale square and one composition only.

`lem-pur-etale-graph-proper-tower` is the proper-first interchange normalization,
corresponding to original steps 3, 4 and 5. It quantifies over the proper square
and one open extension; the original second open square and other composition
are absent.

Both inherit the parent's chapter, unit and blueprint ancestor, have three kinds
of Mathlib search recorded, and retain the original declared geometric
prerequisites. No existing shared interface is changed, so no consumer adaptation
or change record is needed.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
