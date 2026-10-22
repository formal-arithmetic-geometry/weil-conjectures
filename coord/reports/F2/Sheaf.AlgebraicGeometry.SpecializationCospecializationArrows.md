## What changed

Restored Sheaf.AlgebraicGeometry.SpecializationCospecializationArrows from its quarantine
archive and repaired etaleStalkSpecialization_naturality. The old proof used the retired
specialized restriction API. It now uses the existing strictLocalSectionCone's unique
restriction, component restriction, and strictLocalNeighbourhoodSection. A final rfl
closes the component naturality calculation after the terminal-section comparison.

All declaration signatures, attributes, public imports, docstrings and definition bodies
are preserved verbatim. The proof still uses colimit extensionality, naturality of the
inverse-image unit, sheaf restriction and the global-sections comparison, followed by
naturality of globalGerm and the pullback-stalk isomorphism. No other module is edited.
No DAG route changes: the existing definition node and all Lean attachments remain.

The full restored module compiles via lcompile.py in 18.0 seconds. Searches of the library,
Lean Finder and Loogle found no ready-made specialization naturality theorem. Loogle
confirmed the existing toPresheafFiber_naturality lemma used by the proof. Read the
specialization construction and cospecialization formula in the cited local Stacks source.

Change record: coord/changes/F2-specialization-cospecialization-restoration.md.

## Proved and sorry left

This is a zero-hole quarantine repair. Holes closed: 0 of 0. Holes added: 0.
No sorry remains in any delivered declaration. No theorem is split off.

The complete proof of AlgebraicGeometry.Etale.etaleStalkSpecialization_naturality is
restored against the current API. The other instance proofs and all canonical arrow
constructions are retained. This is a compilation repair, not a newly closed proof hole.

## No longer needed

None. All six original public imports remain. No node, declaration, dependency or module
is withdrawn or pruned. In particular the quarantined parent statements remain needed
and are not treated as unused merely because their current Lean paths are absent.

The retired names existsUnique_strictHenselizationStalkRestriction,
strictHenselizationSectionRestriction and strictHenselizationNeighbourhoodSection are no
longer called in this proof; the generic API already imported by EtaleStalkSpecialization
supplies exactly those operations on the same small strict-local model.

## Where the brief, the DAG or earlier work was wrong

The module has no existing sorry: it is a rework assignment for an archived module whose
proof stopped compiling after dependency API retirement. The archive's naturality proof
had not been migrated along with EtaleStalkSpecialization. The theorem, canonical arrows,
node statement, mathematical route and original Lean attachment remain correct.

The generic section-cone nodes belong to another unit and are used only as the existing
model-independent restriction API, not to bypass any unit's argument. There are no new
nodes or forced adaptations. The unrelated old return in coord/returns/F2.md concerns a
different item and does not authorize withdrawing this archive.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
