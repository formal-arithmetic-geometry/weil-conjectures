## What changed

Retired Sheaf.AlgebraicGeometry.Modules.ExteriorTensorLocalPairing in favour of its upstream twin,
as assigned by coord/queue.tsv and coord/retire-items.tsv. Listed the withdrawn file in deleted.txt
and redirected lem-sc-exterior-tensor-local-pairing's Lean record to
WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorLocalPairing.

Adapted the one direct consumer, Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearMaps: it
imports the upstream pairing, constructs the private presheaf isomorphism exteriorPresheafComparison
by the uniqueness of exteriorSheafRestriction, sheafifies it to exteriorComparison and proves both
directions preserve wedges. The private exteriorPairing_transport conjugates the upstream pairing by
these maps, with its tensor formula and naturality proved explicitly. Its public statements and
definitions are unchanged. Qualified ordinary exteriorPower namespace references with _root_.

Validation: the adapted consumer compiled with no warnings in 36.3 seconds through lcompile.py. A
source import/name scan found exactly the one consumer listed above. The delivered Lean has zero
sorry bodies and no new public declarations.

Change record: coord/changes/Q6-retire-exterior-tensor-local-pairing.md.

## Proved and sorry left

This retirement repair starts with zero sorries in the assigned module. Holes closed: 0 of 0. Holes
added: 0. No split-off statements and no remaining sorry in delivered Lean. The consumer's private
comparison helpers and exteriorPairing_transport are completely proved; its existing
AlgebraicGeometry.Scheme.Modules.determinant_split_linear_maps_exists stays completely proved by
transport of the already-proved upstream exteriorTensor_local_pairing.

## No longer needed

Pruned module Sheaf.AlgebraicGeometry.Modules.ExteriorTensorLocalPairing and removed its import from
Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearMaps. The upstream twin supplies the same
mathematical pairing; the DAG node remains and points to that twin. No other node or dependency is
claimed pruned. The exterior sheaf definition and local bilinear sheafification tensor result remain
needed by the upstream proof or the consumer.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an unfinished proof, but this item is a retirement repair with
zero holes. Its existing proof was complete. Directly changing the consumer's import is insufficient
because upstream uses exteriorPower/wedge rather than exteriorSheaf/exteriorSheafSection.
Constructing the canonical isomorphism of their presheaves fixes that API difference without
changing statements, adding assumptions or adding holes. The unit's mathematical proof route is
preserved, and no source-library file is edited.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
