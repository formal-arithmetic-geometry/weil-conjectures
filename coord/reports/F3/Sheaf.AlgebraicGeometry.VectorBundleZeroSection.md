## What changed

Restored `lean/Sheaf/AlgebraicGeometry/VectorBundleZeroSection.lean` from the quarantine
path named in `coord/rework.tsv`. Promoted the existing import of
`WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec` to a public import because
`antiEquivalence` and `algebraIso` use its theorem in exposed definition bodies.
The original archive fails at both references; the repaired file compiles in 26 seconds.
All declarations and the DAG attachment and dependencies are preserved verbatim.
The delivery parser confirms identical declaration records and no new holes. A separate
consumer module importing only this module compiles with an exposed definition using
`antiEquivalence`; its axiom print lists only `propext`, `Classical.choice`, `Quot.sound`.
It also checks the exported `algebraIso` and `zero_spec` signatures. This scratch consumer
is excluded from the packet.
Change record: `coord/changes/F3-vector-bundle-relative-spec-public-import.md`.

Consumer review includes all nine direct archived importers and all archived textual
users, listed in the change record. There are no live importers. This additive visibility
repair needs no consumer source adaptation. Searches via leanfinder, loogle and grep
found the ring symmetric-algebra augmentation and topological zero sections, with no
replacement for this relative-spectrum construction.

## Proved and sorry left

This is the assigned quarantine/import repair, not a decomposition or a new proof.
Holes closed: 0 of the 3 holes in the archived module. Holes added: 0. Split off: 0.
The existing proved `augmentation_spec`, `zero_spec` and `affineChart_naturality` proofs
are restored unchanged. The three remaining whole-theorem holes, all attached to
`def-asd-vector-bundle-zero-section`, are:

- `AlgebraicGeometry.VectorBundleZeroSection.affineChart_spec`;
- `AlgebraicGeometry.VectorBundleZeroSection.trivializationMap_spec`;
- `AlgebraicGeometry.VectorBundleZeroSection.transition_spec`.

No definition contains a hole. No new theorem or node is introduced.

## No longer needed

None. No import, declaration, node or module is pruned. The formerly private relative-
spectrum import is retained as a public import. The quarantined archive is preserved.

## Where the brief, the DAG or earlier work was wrong

The upstream-sync migration left the relative-spectrum theorem imported privately even
though this module uses it in exposed definitions. The listed rework diagnostic correctly
identified this visibility defect. Restoring its public visibility repairs the assigned
error without changing the mathematical construction or the unit route.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
