## What changed

Restored `lean/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalization.lean`
verbatim from its exact quarantine path in `coord/rework.tsv`. This repairs the
missing proved theorem `AlgebraicGeometry.standardSingleFlatCounit_localization`.
The source path is absent in the live library; the preserved archive is not a
withdrawn or obsolete statement. Its public interface, docstring and complete
proof are unchanged. No definitions or target statements change.

The proof uses both declared dependencies: presentation-data gives affine opens
S,V, point membership, affine instances, containment, and an actual presentation;
completion applied to exactly these witnesses gives the original existential
bounded flat stalk complex, universal scalar-extension pair, and all integer
degree counit equations. It does not select data for a definition. The existing
DAG proof and dependency list already match this argument, so no node is changed.
The unit route is preserved.

Validation: the restored item compiles without errors or warnings in 5.6 seconds.
A separate import-and-axiom probe reports only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`. A source comparison confirms byte-for-byte
identity with the archive and exact agreement with the node's Lean signature.

Consumer inventory: zero live source consumers; one direct archived caller,
`Sheaf.AlgebraicGeometry.StandardSingleStalkFlatCounitModel`, and 76 total
transitive consumers including archives. The unmodified archived caller fails
in its own public statement at lines 79 and 92 because its scalar-extension
additivity instance provider was withdrawn from its old module path. Adding the
current upstream provider in a scratch copy makes the entire original signature
and proof compile against the restored theorem in 4.5 seconds. The caller's
separate rework is preserved; no consumer requires a signature or proof change
because of this restoration. Scratch files are excluded from delivery.

Change record:
`coord/changes/D4-standard-single-flat-counit-localization-restoration.md`.

## Proved and sorry left

The archived item has zero holes. Restored the already complete theorem
`AlgebraicGeometry.standardSingleFlatCounit_localization`
(node `lem-pc-standard-single-flat-counit-localization`).
Holes closed: 0. Holes added: 0. Sorries left in the item: none.
Split-off statements: none. This is source restoration, not a new proof or
hole-reducing decomposition.

## No longer needed

None. Both private proof imports are used directly, and the sole public import
supplies the statement's presentation predicate and public types. No imports,
nodes, modules or tool approvals are removed. The archived parent still imports
this module and its DAG proof still cites this node, so withdrawal would be wrong.

The required searches were run: LeanFinder on local affine flat sheaf
presentations and stalk scalar-extension counits returned ordinary sheaf
presentation and stalk facts; Loogle on `IsLeftDerivedFunctor` returned generic
universal-property results; Mathlib grep on `stalk.*counit|counit.*stalk` returned
skyscraper adjunction facts. Library searches identify the two already proved
dependencies used by the archived proof. No shorter replacement is needed.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a holed module, but this assigned rework is a
zero-hole restoration after a cluster rollback. The missing live file does not
justify removing its Lean attachment or pruning its parents. No mathematical
statement or DAG route correction was needed.

The archived direct caller still publicly imports the withdrawn empty
`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel`; its existing proved
instance provider is now upstream under `WeilConjectures`. This independent stale
import was diagnosed and checked in scratch, without adding it to this packet.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
