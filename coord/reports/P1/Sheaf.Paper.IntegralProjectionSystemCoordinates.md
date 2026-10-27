## What changed

Restored the quarantined item source and preserved the signature and public imports of
`WeilConjectures.FixProjectionCompactification.integralProjectionSystemCoordinates`.
Its proof constructs the endpoint coordinates and combines two smaller coefficient-map
normalizations. Its parent `IntegralProjectionRefinementSquare` continues to use the same
statement. No existing public definition, statement, global attribute, or public import was changed.

`IntegralProjectionCoordinateData` constructs the reconstruction, completed tensor and
pullback comparisons, datum tensor comparison, support-value comparison, support adjunct,
and the projection source and target maps. These are actual composites of specified maps;
no arbitrary object or isomorphism is selected from an existence theorem. Inverses use
named reconstruction and open-effectivity theorems that determine their inverses uniquely.

`IntegralSupportReductionNormalization` isolates invertibility and refinement compatibility
of that support adjunct for one input. `IntegralProjectionReductionNormalization` isolates
one projection square for the explicit coefficient maps. They are proof imports of the
item. The completed assembly includes naturality of systemComparison, naturality of the
binary tensor comparison, and transport of coefficient squares along the actual
reduction/limit unit. The lower assertions contain neither the original existential
coordinate choice nor its combined projection and refinement conclusion.

Validation: the clean `lcompile.py --all` run accepted all four delivered modules with
no errors or warnings. The service enforces its 60-second limit on each Lean process;
its displayed batch times also include artifact setup and cache work. The assembled
item also compiled individually in 13.8 seconds during profiling. The archived and
current shared signatures and public imports were compared with the delivery and match.
The delivered DAG references exist, and no delivered node introduces a cycle.

## Proved and sorry left

The item's original single hole, in
`WeilConjectures.FixProjectionCompactification.integralProjectionSystemCoordinates`, is
replaced by a complete proof from two named lower assertions. There are zero holes in the
item and zero holes in the coordinate-data definitions and private assembly lemmas.

Two holes are added, each with proof body exactly `by sorry`, a source, a natural-language
proof, and its own node:

- `WeilConjectures.FixProjectionCompactification.integralSupportReductionNormalization`
  (`lem-sf-integral-support-reduction-normalization`): one-input support invertibility and
  its directed-refinement equation, with no tensor or projection.
- `WeilConjectures.FixProjectionCompactification.integralProjectionReductionNormalization`
  (`lem-sf-integral-projection-reduction-normalization`): one-compactification projection
  coefficient square, with no refinement or existential coordinates.

This is a decomposition: one original hole closed and two strictly smaller holes added,
not a proof of the original result without additional admitted dependencies. No axiom or
hole in a definition is introduced.

## No longer needed

No existing module is withdrawn. Neither original public import is removed: both are
needed by the unchanged statement. No source-library declaration is removed or altered.
The item's old direct proof plan is replaced by the explicit-coordinate construction,
one-input support normalization and one-projection normalization. Its old direct proof
edges for residue Tor, open tensor normalization, direct-image constructibility,
constructible preservation, etale origins and completed open comparison remain needed by
the coordinate construction or the two lower nodes, rather than being asserted pruned.
The old Noetherian and quasi-separatedness proof edges are not needed for constructing
these coordinates: quasi-compactness of a compactification open follows from
`Compactification.quasiCompact_openImmersion` under the given quasi-compactness of f.
The nodes are `lem-weil-pbc-finite-type-over-noetherian` and
`lem-weil-pbc-locally-noetherian-quasi-separated`; they have no attached project module.
No global withdrawal is requested.

## Where the brief, the DAG or earlier work was wrong

The item was quarantined, not withdrawn; its archived statement and dependencies were
preserved. No mathematical counterexample or target-statement correction was found.
The existing interfaces expose whole-system realization and datum normalizations but do
not directly state the two explicit coefficient-map identities used here. Rather than
repeat the original existential assertion under a new name, the new statements separate
its independent support/refinement and projection-generator obligations. The existing
`integralProjection_operationPresentation` gives an arrow isomorphism to another ordinary
presentation; it does not identify the fixed endpoint maps needed for both refinement
equations, so it does not directly supply either missing normalization.
The unit route
and the source's proper-counit/open-tensor construction are preserved. No compatibility is
inferred merely from equality of finite evaluations.

## New nodes

`def-sf-integral-projection-coordinate-data` records the actual reconstruction, tensor,
pullback and support coefficient maps in `IntegralProjectionCoordinateData`. Its support
map is the adjoint of the explicitly composed inverse support-value isomorphism, so data
is fixed before any new invertibility or coherence assertion.

`lem-sf-integral-support-reduction-normalization` records the one-input support adjunct's
invertibility and refinement equation. Its proof plan uses normalized constructible
systems, the reconstruction counit, and the proper/open realization generators.

`lem-sf-integral-projection-reduction-normalization` records the single projection square
for those fixed maps. Its proof plan transposes the proper and open factors and pastes
their prescribed tensor/counit comparisons. It contains no refinement assertion.

All three inherit the item's chapter, unit and exact blueprint proof location. Their
records include leanfinder, leansearch and grep searches; no matching Mathlib result or
blueprint node was found. No shared interface repair or forced adaptation is included,
so no change record is required.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
