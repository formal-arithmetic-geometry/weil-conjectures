## What changed

Restored `Sheaf.AlgebraicGeometry.AffineFreeResidueSectionsCohomology` from the
quarantine path recorded in `coord/rework.tsv`. The live module was absent; its
archived theorem `AlgebraicGeometry.Scheme.affineFree_residueSections_cohomologyLinearEquiv`
already had a complete proof. The restoration preserves that theorem's exact
signature, public imports, Lean attachment, and proof dependencies.

Simplified its final comparison of complexes: apply
`NatIso.mapHomologicalComplex` directly to `tilde.toTildeΓNatIso.symm`, then compose
with the identity-functor comparison. This has the same endpoints as the archived
composition-functor comparison and compiles against the current library.
The existing node's proof and proof-origin fields describe this construction.

The proof evaluates the supplied finite free terms, proves their section complex
K-flat using the existing bounded-flat theorem, applies
`affineFree_residueSections_derivedModel`, and transports homology through exact
sections on the residue-field spectrum. No free model or residue witness is
chosen from an existence theorem. Rank-zero terms and the zero complex are
covered by the same linear equivalences; an empty open cannot satisfy `hwU`.

Change record:
`coord/changes/A6-affine-free-residue-sections-cohomology-restoration.md`.
It records the archived and restored signature and all 16 transitive consumers
found when quarantined sources are included. The two direct consumers are
`AffineBettiModelResidueMinimality` and `ResidueRankModelDifferential`.

## Proved and sorry left

`AlgebraicGeometry.Scheme.affineFree_residueSections_cohomologyLinearEquiv` is
restored with a complete proof. Actual archived holes: **0**. Remaining holes in
the restored module: **0**. Holes closed: **0**. Holes added: **0**. Split off: **0**.
This is the assigned quarantine repair, not a new hole-closure claim.

The restored theorem compiled unchanged against the current derived-model source;
the simplified proof then compiled in 24.8 seconds. A source comparison confirms
identical theorem signatures, public imports, Lean attachments and dependency
lists. All Lean lines meet the 100-character limit.

The final theorem and both unchanged archived direct consumers compiled together:
`AffineFreeResidueSectionsCohomology` in 27.6 seconds,
`AffineBettiModelResidueMinimality` in 22.4 seconds, and
`ResidueRankModelDifferential` in 17.0 seconds. Only the assigned module is delivered;
the consumer copies were diagnostic checks.

## No longer needed

None. No import, node, dependency or module is pruned. All three original proof
dependencies remain: `def-sc-derived-fiber-betti`,
`lem-pc-module-bounded-flat-kflat`, and
`lem-sc-affine-free-residue-sections-derived-model`.
The direct induced natural isomorphism replaces only an extra comparison inside
the proof; it does not remove a mathematical dependency or change the unit route.

## Where the brief, the DAG or earlier work was wrong

The item is a restoration with zero archived holes, rather than a theorem that
still contains `sorry`. Its current rework row explicitly preserves the source
in quarantine. The already restored R1 derived-model theorem supplies the
required object comparison, so no further intermediate statement is needed.

The first compile against published artifacts encountered a duplicate declaration
from the old `Sheaf.AlgebraicGeometry.DerivedFiberBetti` and its adopted
`WeilConjectures` replacement. Recompiling the current, unchanged derived-model
source in the sandbox resolved that stale-artifact mismatch. That diagnostic
copy is not part of this delivery. No launcher or project tool was modified.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
