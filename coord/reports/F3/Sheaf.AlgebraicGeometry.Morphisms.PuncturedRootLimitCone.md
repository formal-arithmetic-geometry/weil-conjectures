## What changed

Retired the zero-hole duplicate Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootLimitCone,
as assigned in coord/retire-items.tsv. Its node now points to the proved official twin.
Adapted the only direct consumer, PuncturedRootLimitPresentation, while preserving its
complete theorem signature. The private proved strictHenselization_colimit_comparison
identifies the two ring models and their structural maps, then transports the official
theorem's colimit isomorphism back to the consumer's original ring. No definition,
target statement, or source-library file changes.

Change record: coord/changes/F3-retire-punctured-root-limit-cone.md.

## Proved and sorry left

This is a retirement repair with zero initial holes: 0 of 0 closed, 0 added, 0 left.
The retained punctured_root_limit_presentation is completely proved. The new private
strictHenselization_colimit_comparison is completely proved. No statements are split off.
The official pointed_etale_ring_colimit is already proved and reused, not claimed as new work.

Validation: the adapted presentation compiles cleanly; the unchanged transitive consumer
PuncturedRootSectionEtaleDescent compiles against it. A separate axiom probe confirms that both
the official ring-colimit theorem and the retained punctured-root theorem use only
propext, Classical.choice and Quot.sound. The three files were compiled together
in import order so both probes used the adapted consumer, not its published predecessor.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootLimitCone.
Its consumer replaces that private import with the official WeilConjectures twin.
It also replaces the public Sheaf.StrictHenselizationStructuralMap wrapper by its two
upstream statement dependencies to avoid mixing the two structural-map equation APIs.

The separate lem-sbc-pointed-etale-ring-colimit-base-map-naturality and its module
PuncturedRootLimitBaseMapNaturality are no longer needed by this route: the adopted
ring-colimit proof proves naturality directly from GammaSpecIso and the over-category
triangle. Its dependency edge is removed; the separately proved declaration remains
available. The ring-colimit node and the root-continuity node themselves remain used;
no unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an open proof, but the live queue explicitly assigns
twin retirement and the item already compiles with zero holes. The retirement inventory
correctly flags an API difference: the two ring models are not definitionally equal.
A proved comparison with its structural-map equation is necessary. The original
consumer statement is preserved by transporting along that isomorphism.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
