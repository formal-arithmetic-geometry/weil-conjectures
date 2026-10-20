## What changed

Retired the zero-hole duplicate
Sheaf.Algebra.Homology.LocalizedTensorComparisonDirectSumSquare in favor of
WeilConjectures.Algebra.Homology.LocalizedTensorComparisonDirectSumSquare.
The official theorem proves the identical conclusion without hC, hQ or hU.
Changed the sole consumer, LocalizedTensorComparisonClosureCoproduct, to import
that module and call its stronger API. Its declaration signatures and public
imports remain unchanged. Scoped the unused-variable linter off for its first
theorem because the retained hC premise is no longer used.

The existing node now names the official module and exact declaration signature.
Its mathematical statement, proof dependencies and proof plan are unchanged:
the official proof performs the same source-coproduct, target-homology coproduct,
and tensorator-naturality argument. No source-library or target file changes.

Change record:
coord/changes/C5-retire-localized-tensor-comparison-direct-sum-square.md.

## Proved and sorry left

This is a retirement, not new proof work: closed 0 of 0 local holes; added 0;
split off 0. No sorry remains in any delivered module. The already proved
ModuleCat.exists_localizedTensorComparison_direct_sum_square is supplied by the
adopted source library. The consumer's two closure theorems retain complete proofs.

## No longer needed

Withdrawn module:
Sheaf.Algebra.Homology.LocalizedTensorComparisonDirectSumSquare.
Removed its sole consumer import and replaced it with the adopted source import.
All imports of the duplicate disappear with that file; its dependencies remain
needed by the unchanged official proof, so none is claimed globally pruned.
The original node remains needed by its closure-coproduct parent and now resolves
to the official theorem. No DAG dependency, unit statement or unit step is deleted.
Searches of library and quarantine found no other import or application to adapt.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes repeated splitting, but the current item already
contains a complete proof with zero holes. coord/retire-items.tsv explicitly lists
it as a retirement item. Its official twin has the same conclusion and drops
only unused flatness and K-flatness premises. The old Lean attachment still
pointed to the duplicate, and the consumer still passed those obsolete arguments.
The retirement fixes both. Library search found the exact stronger theorem;
LeanFinder found only general homological-complex tools, and Loogle supplied the
standard Sigma.map API. No further intermediate theorem is needed.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
