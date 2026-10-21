## What changed

Restored `Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveRepresentation`
from the quarantine path listed in `coord/rework.tsv`. The existing proof was
already complete; this is a zero-hole restoration repair, not a new proof or a
rebase-only delivery.

Migrated its private open-restriction import to the proved upstream twin and
replaced the removed `restriction_additive q` application by `inferInstance`,
as required for this archive by the landed A4 retirement record. Replaced
`import all WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`
by the direct private import of
`WeilConjectures.AlgebraicGeometry.Modules.RestrictPushforward` for the actual
`Modules.pushforwardRestrictIso` used by the proof.

The existing theorem signature, private transport construction, public imports,
mathematical argument and all stated dependencies remain unchanged. The node's
first proof step now cites the direct source of the open-square isomorphism.
The parent `PicardAffineStructureProjectiveModel` remains in quarantine and
continues to need this theorem; no withdrawal or parent-route change is made.
The restored module compiles with no errors or warnings via `lcompile.py`
(45.1 seconds). A source comparison confirms the public signature and public
imports are byte-identical to the archive.

Change record:
`coord/changes/Q2-picard-affine-structure-projective-representation-restoration.md`.

## Proved and sorry left

The restored declaration
`AlgebraicGeometry.Scheme.picard_affine_structure_projective_representation`
(node `lem-sc-picard-affine-structure-projective-representation`) has a complete
proof, using the already declared proper-flat perfectness and affine
bounded-projective results and explicit derived open-square transport.
Its existing private helper `open_trivialized_image_spectrum_comparison` also
remains fully proved. The affine transport equivalence is explicitly constructed.

Original holes: 0. Holes closed: 0. Holes added or split off: 0.
Sorries left in the item: none. New modules: none.

## No longer needed

Removed the broad private import
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`; the proof
uses only the open-square comparison supplied directly by
`WeilConjectures.AlgebraicGeometry.Modules.RestrictPushforward`.
Removed the private import of the retired duplicate
`Sheaf.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties` in favor
of its unchanged upstream twin. The old named `restriction_additive` helper is
replaced by the existing upstream instance.

No mathematical DAG dependency, node, source-library declaration or module is
withdrawn. All listed proof dependencies remain used. The affine module-model
import still provides `affinePerfectSheafification` in the public statement;
its existence theorem is not applied by this argument. Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The item is an assigned restoration repair with zero archived sorries. Its
absence from `lean/` does not indicate unused mathematics: its quarantined
parent imports it and cites it in the DAG. The archive predates the A4
restriction-twin retirement and still calls the removed helper. This delivery
implements that record's explicit restoration instruction.

The first DAG proof step incorrectly called the open-square comparison
`pushforward_restrict_square` and located it in `Cohomology.DirectImage.Sections`.
The existing Lean proof actually uses `Modules.pushforwardRestrictIso`, now
imported directly from `Modules.RestrictPushforward`; the node is corrected
without changing its dependencies or mathematical route.

Searches through `msearch.py` found no shorter Mathlib replacement: the
LeanFinder query for an affine perfect bounded-projective representative returned
K-projectivity tools; Loogle returned no exact derived-factorization match, and
the Mathlib grep returned no project-specific affine/open-square declarations.
The existing proved library dependencies supply the required argument.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
