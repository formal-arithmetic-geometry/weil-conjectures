## What changed

Restored lean/Sheaf/AlgebraicGeometry/PicardDirectImageDerivedTranspose.lean
byte for byte from its quarantine path in coord/rework.tsv. The live path had
been removed by the recorded 2026-10-20 cluster-restore rollback. The complete
explicit construction is restored, with its original pinned adjunction and
base-change maps, signature, shared derived-category parameter, public import,
irreducibility attribute and elaboration settings.

Updated only the existing node's lean.by, lean.date and lean.note to document
restoration. Statement, dependencies, source, proof fields and unit route stay
as recorded. Change record:
coord/changes/E4-picard-direct-image-derived-transpose-restoration.md.

Validation: the unchanged archived module compiles against the current published
interfaces in 27.8 seconds, with no warnings or errors. Searches of Mathlib,
WeilConjectures and Sheaf found the canonical adjunction ingredients, but no
replacement for the required explicit Picard construction. Consumer inventory
includes the quarantined sources: three direct importers and 19 transitive
consumers. A byte comparison confirms exact restoration and all Lean lines
have at most 100 characters.

All three original direct consumer proofs compile unchanged against the restored
module in a separate scratch sandbox: PicardDirectImageDerivedTransposeFactorization
(25.8 s), PicardDirectImageDerivedTransposeSingle (48.0 s) and
PicardDirectImageDerivedTransposePasting (37.7 s). The set also recompiled the
restored definition (26.7 s). The single and factorization proofs unfold the
restored definition, checking its body as well as its public signature. Scratch
copies are validation artifacts, not part of the delivery.

## Proved and sorry left

This is an assigned zero-hole definition restoration. The repaired declaration
is AlgebraicGeometry.Scheme.picardDirectImageDerivedTranspose, attached to
node def-sc-picard-direct-image-derived-transpose. Its complete morphism data
is constructed explicitly, with no sorry in its body.

Original holes: 0. Holes closed: 0. Holes added: 0. Sorries left: none.
No theorem is split off and no unrelated hole closure is claimed.

## No longer needed

None. Preserve the public import of PicardDirectImageUnitMorphism, every
statement dependency and the Lean attachment. The three parent nodes and the
quarantined consumers still use this definition; zero live importers does not
authorize withdrawal. No module or node is pruned.

## Where the brief, the DAG or earlier work was wrong

The initial description of stage 3 as proving sorry bodies does not describe
this item's concrete state: the preserved definition has zero holes and its
live module is missing. The brief's explicit definition-repair exception and
coord/rework.tsv identify the required work as full restoration. The archive
is retained, not deleted, and no empty module replaces it. No mathematical
statement dispute or defect in the original construction was found.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
