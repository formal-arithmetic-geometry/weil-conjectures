## What changed

Restored `Sheaf.CategoryTheory.BrownRepresentabilityConstruction` from its assigned
quarantine archive. Replaced its public import of the retired, empty
`Sheaf.CategoryTheory.CompactObject` with
`WeilConjectures.CategoryTheory.CompactObject`, the canonical source of
`CategoryTheory.IsCompactObject`. Everything else in the archived module is unchanged.
The change record is `coord/changes/E3-brown-construction-canonical-compactness.md`.

The construction still applies `brownStageSequence` and `brownTelescopeAssembly`,
then proves injectivity by factoring a difference through a stage and killing its
kernel at the next stage; initial-stage surjectivity proves surjectivity. This
matches the existing DAG proof and preserves both declared proof dependencies.
The unit route and existing Lean attachment remain intact; no node changes are needed.

## Proved and sorry left

This is a zero-hole rework repair. Holes closed: 0 of 0. Holes added: 0.
No `sorry` remains in the delivered module, and no new theorem is split off.
`CategoryTheory.brownRepresentabilityConstruction` retains its complete proof.
Its axiom probe reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The original archive reproduces the reported private-import error; the repaired
module compiles cleanly. Its sole direct consumer, the unmodified quarantined
`Sheaf.CategoryTheory.BrownCohomologicalRepresentability`, also compiles against the
restored module; the consumer is not included in this delivery.

## No longer needed

Removed the public import of `Sheaf.CategoryTheory.CompactObject`, already withdrawn
to an empty module, in favor of the canonical source compactness import.
No mathematical nodes or proof dependencies are pruned. In particular,
`lem-pc-brown-stage-sequence`, `lem-pc-brown-telescope-assembly`, and the parent
`lem-pc-brown-cohomological-representability` remain needed.

## Where the brief, the DAG or earlier work was wrong

The assigned module has zero holes and was quarantined because retiring the duplicate
compactness module left its public compactness import unusable. This packet repairs
that import and restores the genuine construction; it neither withdraws the archived
statement nor replaces it with an empty module. The general proof brief's description
of unfinished proofs does not apply to this zero-hole repair.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
