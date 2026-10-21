## What changed

Restored `Sheaf.AlgebraicGeometry.StandardSingleStalkFlatCounitModel` from its
quarantine archive. Replaced the public import of the withdrawn empty module
`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel` with its upstream
replacement `WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel`.
Its proved additive instance repairs both scalar-extension homotopy functors in
the existing public theorem signature. Every other byte of the archive is preserved.

Change record: `coord/changes/T7-standard-single-stalk-flat-counit-model-restoration.md`.

The repaired item compiles cleanly in 4.9 seconds. An explicit axiom check reports
only `propext`, `Classical.choice`, and `Quot.sound`. The original archived direct
consumer `Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeEpi` also compiles
unchanged against the repaired item (0.4 seconds). The consumer and axiom command
were used only for validation and are not delivered. Source inspection finds zero
live importers and one direct archived importer; the change record lists all 75
archived transitive consumers and their holders.

## Proved and sorry left

This is a repair of a zero-hole module. Holes closed: 0 of 0. Holes added: 0.
Holes split off: 0. Sorries left: none.

`AlgebraicGeometry.exists_standardSingle_stalk_flat_counit_model`
(node `lem-pc-standard-single-stalk-flat-counit-model`) retains its complete archived
proof. Its transitive axiom list contains no `sorryAx`.

## No longer needed

Removed the obsolete public import
`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel`, whose file has no
declarations. Reused its upstream replacement for the public signature.

No mathematical node or proof dependency is pruned. The existing affine,
Mayer--Vietoris union, localization, and quasi-compact-open induction dependencies
are all used and remain imported. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The assigned module was quarantined after a global build failure; it had no holes.
Its old scalar-extension model import had become empty during upstream migration,
which caused the two missing `Additive` instance errors reproduced before repair.
The archived theorem statement, proof, DAG attachment, and unit route were already
correct. No new lemma, node, definition repair, or consumer adaptation is needed.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
