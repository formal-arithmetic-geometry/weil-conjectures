## What changed

Repaired the landing-conflict return for delivery `d585699ab6`, whose base
was `e0d550965`. Re-read `coord/rework.tsv` and the current source after that
return: the module remains absent from `lean/`, and the current quarantined
source matches the saved current-source baseline byte for byte. Reconstructed
the module from that current quarantined source and reapplied the retained
private arbitrary-ring scalar construction. Refreshed the node copy from the
current repository before applying only the proof-route changes. The public
row theorem and private matching-lift helper retain their signatures and
visibility, including the latter's `import all` consumer.

Restored the quarantined `Sheaf.Paper.HypercoverInjectiveModuleRow` and repaired its
`Ring R` proof without changing the upstream `CommRing` interface. Added private,
explicit scalar-extension and restriction functors, with proved unit, counit and
equivalence. The original matching-lift and injective-row exactness argument then
applies unchanged. The public theorem's signature and public import stay identical.

Replaced the proof import of the adopted scalar equivalence with the Mathlib
module-sheafification and constant-sheaf APIs. Updated the item's DAG proof to name
the private construction and its actual remaining proof dependency. Change record:
`coord/changes/C9-hypercover-private-ring-realization.md`.

## Proved and sorry left

This is a compilation repair of an already proved theorem:
`AlgebraicGeometry.FiniteSplitEtaleHypercover.injective_module_row_quasiIso`.
The quarantined original has zero holes, and the restored module has zero holes.
Holes closed: none. Holes added: none. Split off: none. Every new helper is private
and fully constructed or proved.

Fresh compilation against the current published server build passes in 15.8
seconds. The consumer probe compiles in 1.4 seconds: its `import all` resolves
`matching_local_lifting`, and both that helper and the public row theorem use
exactly `propext`, `Classical.choice`, and `Quot.sound`. The probe stays in the
scratchpad and is not delivered.

## No longer needed

Removed the direct proof import
`WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`; its
`CommRing` equivalence cannot supply the needed arbitrary-ring specialization.
Consequently `lem-weil-pbc-etale-constant-ring-module-equivalence` is no longer a
proof dependency of this item. Its upstream declarations remain untouched and
continue to serve their other users. No globally unused module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The assigned file was in `quarantine/Sheaf/Paper/`, rather than `lean/Sheaf/Paper/`,
following the upstream sync. The queue's compiler error correctly identifies the
regression: the formerly generalized scalar equivalence again requires `CommRing`.
The DAG still describes arbitrary-ring coefficients; adding commutativity to this
item would change its statement. The repair instead proves the needed private
construction using only left modules and rings, including the zero ring and an
empty base. The unit and counit use identity functions on sections and require
neither nonzero scalars nor nonempty covers.

The return was a stale-base landing conflict, not a proof rejection. The
current source comparison and fresh compilation check the restoration
against the present tree. The earlier consumer inventory omitted the
`import all` consumer; the change record now includes all three consumers.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
