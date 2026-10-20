## What changed

Restored Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality from its
coord/rework.tsv quarantine archive. Added the direct public import
Sheaf.Algebra.Homology.KFlat for the existing IsAcyclicTensorKFlat hypotheses,
and removed four obsolete or redundant private imports. Every line after the
imports is identical to the archive, including comparisonIntoPullback and the
complete comparisonIntoPullback_naturality proof.

The proof still combines exists_stalkDerivedExtensionComparison,
baseDerivedTensor_localized_naturality and the exact-stalk source transport.
The existing node lem-pc-stalk-comparison-pullback-naturality, its attachment,
all three proof dependencies and the unit route are preserved unchanged.
No source-library module or consumer is edited.

Change record: coord/changes/V4-stalk-pullback-naturality-imports.md.

Validation: the archived original reproduces the duplicate derivedPullback
import failure. The repaired module compiles without diagnostics through
lcompile.py (12.3 seconds; 11.6 seconds in the consumer check). A separate
public importer restates the entire theorem signature and applies it unchanged
(3.3 seconds). #print axioms for both comparisonIntoPullback and
comparisonIntoPullback_naturality lists only propext, Classical.choice and
Quot.sound. Both new imports pass import_direction.py may.

## Proved and sorry left

This is a zero-hole quarantine repair. The archive contains zero sorries;
the restored item contains zero sorries. Holes closed: none (0).
Holes added: none (0). Split off: none (0).

AlgebraicGeometry.SingleComplexBaseChange.comparisonIntoPullback remains a
concrete constructed map. AlgebraicGeometry.SingleComplexBaseChange.
comparisonIntoPullback_naturality retains its complete proof and now compiles
against the current dependency interface. Both have only the allowed axioms.

## No longer needed

Removed these direct private imports:

- Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel: retired twin;
  canonical model declarations are already exported by upstream stalk transport.
- Sheaf.Algebra.Homology.KFlatStalkCriterion: not used directly here;
  stalk K-flatness is supplied inside the retained extension-comparison theorem.
- Sheaf.AlgebraicGeometry.DerivedPullback: obsolete twin causing the reproduced
  duplicate declaration error; canonical derived pullback is already available.
- Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition: retired twin;
  canonical stalk rings and comparison data are already publicly available.

No mathematical node or dependency module is withdrawn. All declared proof
nodes remain needed; there is no claimed global mathematical pruning.

## Where the brief, the DAG or earlier work was wrong

The assigned defect is the stale import interface, not an unfinished proof.
The archive's existing complete proof remains valid after correcting imports.
Its public signature uses IsAcyclicTensorKFlat, so it must publicly import the
existing defining module instead of relying on private dependency visibility.

The upstream parallel module has the same comparison names but uses the
separately named IsKFlatTensor predicate. It is left untouched; the archived
item's exact predicate and all ten quarantined consumer interfaces are retained.
No node, definition or target statement is weakened or removed.

LeanFinder found generic pullback/stalk naturality lemmas, no replacement for
this comparison. Loogle NatTrans.naturality and the remote grep search found no
exact match. Local rg found the existing upstream parallel proof and the stated
algebraic naturality theorem. The existing three-part proof is retained.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
