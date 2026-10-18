## What changed

Formalized the compact-open descent clause of `Topology.spectralLimit_descend_opens`.
The proof constructs the compact-open basis for the infimum topology, combines finitely
many stage opens at a common directed stage, and applies compactness to obtain a single
stage compact open. The remaining inclusion and finite equality clauses are delegated to
the strict lower-level theorem `Topology.spectralLimit_descend_inclusion_relations` in
`Sheaf.Topology.SpectralLimitDescendInclusionRelations`.

The direct import of `Sheaf.Topology.SpectralLimitConstructibleClosedNonempty` was removed;
it remains an indirect dependency of the new core module.

## Proved and sorry left

Proved `Topology.spectralLimit_descend_opens` (the item theorem) with no `sorry` in its
module. Added one strictly lower-level theorem, with one `sorry`,
`Topology.spectralLimit_descend_inclusion_relations`, node
`lem-weil-pbc-spectral-limit-descend-inclusion-relations`.

## No longer needed

The item module no longer directly imports
`Sheaf.Topology.SpectralLimitConstructibleClosedNonempty`; the core module imports it for
its constructible closed compatible-point argument. No DAG node is pruned: that theorem is
still needed transitively by the new core node.

## Where the brief, the DAG or earlier work was wrong

The stated five-step route is mathematically sound. The Lean proof makes the finite-stage
basis and finite-union construction explicit; the long inclusion argument is isolated as a
strict lower-level statement so the item theorem itself compiles and retains the exact target
statement.

## New nodes

`lem-weil-pbc-spectral-limit-descend-inclusion-relations` records the strict lower-level
inclusion and finite union/intersection clauses used by the item theorem. Its Lean declaration
is `Topology.spectralLimit_descend_inclusion_relations` in
`lean/Sheaf/Topology/SpectralLimitDescendInclusionRelations.lean`.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
