## What changed

Restored `Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestrictionAux` from its
quarantine archive, as assigned by `coord/rework.tsv`. The module had been removed
by the cluster restore rollback. It contains the complete T2 construction and
proof, with all four public declarations, their signatures, the canonical source
isomorphism construction, and all imports preserved verbatim from the archive.
The equality hypothesis fixing the source isomorphism to
`standardSingleBaseChange_topRestriction_sourceIso p M` is retained.

The compatibility proof constructs inverse pullback lifts using `Y.topIso`,
obtains the coefficient isomorphism and its equation from
`exists_openSingle_coefficient_transport`, constructs the target isomorphism
using the invertible apex adjunction unit and direct-image composition, applies
`derivedBaseChange_source_transport`, and cancels the target isomorphism.
No new proof obligation is introduced. No dependency source is changed.

Validation used the prescribed single-file compiler and unchanged 60-second
limit. The item compiled without warnings in 13.1 seconds. An unchanged copy of
the current, already landed `OpenSingleCoefficientTransport` was compiled first
for verification (43.2 seconds), because the published dependency artifact still
imported a retired pre-sync module. That copy is not delivered. A separate axiom
check found exactly `propext`, `Classical.choice`, and `Quot.sound` for each of the
four public declarations, including the source isomorphism definition. The
unchanged quarantined direct consumer `StandardSingleBaseChangeTopRestriction`
also compiled (3.7 seconds) and its comparison theorem uses only those three
axioms. Its verification copy is not delivered. After moving all sandbox build
artifacts out of the compile path, the item passed a fresh standalone compile
against the published library in 11.6 seconds, without errors or warnings.

## Proved and sorry left

This is a zero-hole restoration repair: 0 direct holes before, 0 after; 0 holes
closed and 0 holes added or split off. No textual `sorry` remains in the item.
The restored complete theorems are:

- `AlgebraicGeometry.standardSingleBaseChange_topRestriction_iso_pullback_unit`
  (`lem-pc-standard-single-base-change-top-restriction-iso-pullback-unit`).
- `AlgebraicGeometry.standardSingleBaseChange_topRestriction_source`
  (`lem-pc-standard-single-base-change-top-restriction-source`).
- `AlgebraicGeometry.standardSingleBaseChange_topRestriction_compatibility`
  (`lem-pc-standard-single-base-change-top-restriction-compatibility`).

`AlgebraicGeometry.standardSingleBaseChange_topRestriction_sourceIso`
(`def-pc-standard-single-base-change-top-restriction-source-iso`) remains the
explicit composition of the adjunction unit, direct-image comparison, and
single-complex restriction isomorphism. No arbitrary coefficient data is chosen
from an unproved existence theorem. No target or statement is changed.

## No longer needed

None. All three public imports support the existing signatures or canonical
source construction. Both proof-only imports are used by the compatibility
proof. The DAG proof records and proof dependencies already describe exactly
this complete route and are preserved. No node, module, or shared generic API
is withdrawn or claimed pruned. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The assignment is a quarantine restoration rather than an open compatibility
hole: the archived T2 proof is complete. The repaired canonical-source statement
must be preserved; the old statement for arbitrary source isomorphisms is false.
The first compile exposed a cached import conflict between the retired
`Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap` and its adopted upstream
replacement. Compiling the already landed coefficient dependency from its
current source resolved this for verification, with no change to its source or
statement. This delivery makes no global-build or comparator claim.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
