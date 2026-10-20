## What changed

Restored Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm from its rework assignment
as a public re-export of the complete adopted source implementation. This replaces
the two incompatible old-model restriction definitions by the existing coherent source
definitions. All five recorded public names and the main theorem signature are retained.
The original quarantine archive and every source-library file are untouched.

The item's node retains its Lean attachment, statement, stmt_deps and proof_deps.
Its proof and proof_origin now record reuse of the adopted cocycle proof, and lean.note
explains the re-export. The unit route and all five parent dependencies remain intact.
Change record: coord/changes/K1-strict-local-localized-hom-germ-source-reuse.md.

## Proved and sorry left

This is a zero-hole definition/interface repair: 0 holes before, 0 after, 0 closed,
0 added, 0 split off. No sorry is left in any delivered Lean file.

Reused the complete adopted proofs of
AlgebraicGeometry.Etale.strictHenselizationSectionRestriction_naturality and
AlgebraicGeometry.Etale.sourceLocalizedSectionsIso_germ, and the concrete definitions
AlgebraicGeometry.Etale.sourceLocalizedSectionsIso,
AlgebraicGeometry.Etale.strictLocalSectionRestrictionNat, and
AlgebraicGeometry.Etale.strictLocalComplexSectionRestriction.
All five exported declarations have only propext, Classical.choice and Quot.sound.

Validation: compiling the archive reproduced the recorded model mismatch at line 57
and further mismatches in the definition data and comparison theorem. The restored
module compiles. A separate importer checks all five names, the restriction app equation,
and the full comparison statement without extra hypotheses. The published cache still
has pre-sync source signatures; current source uses the canonical strictLocalization
model. Re-exporting the source API works without mixing models in either case.

## No longer needed

Removed the private import Sheaf.AlgebraicGeometry.SourceCocycleExactRestriction and
the direct public import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceComparison.
The latter remains publicly available through the adopted implementation. The exact
cocycle restriction argument is still needed and proved in the source module
WeilConjectures.AlgebraicGeometry.SourceCocycleExactRestriction, imported privately
by the adopted implementation. No mathematical dependency, node, parent, unit step,
or module is withdrawn. No whole-module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The assignment is a rework repair with zero holes, not another unresolved proof split.
The quarantine archive combined old-model definitions with the canonical-model
restriction/source-leg API after upstream synchronization, and could not typecheck.
The source library already contains the entire corrected implementation with the same
public names and proof. Reusing it avoids maintaining a second definition of each notion.

The item has no live importers. Three direct archived importers and two additional DAG
parents remain explicitly accounted for in the change record. Their existing rework
assignments and Lean attachments are preserved; their absence from lean/ was not used
to justify withdrawal. No targets or mathematical node statements change.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
