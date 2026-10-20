## What changed

Restored the complete archived module
`Sheaf.AlgebraicGeometry.KFlatPullbackAdjunctionComparison` from the quarantine
path recorded in `coord/rework.tsv`. Added
`public import Sheaf.Algebra.Homology.KFlat`, the existing module defining the
K-flat predicate in the public theorem's unchanged statement. Its original
private helper, public theorem, proof bodies, docstring, and DAG attachment are
preserved. No source-library file is changed.

The restored module compiles with `lcompile.py` (33.2 seconds). The current
upstream `derivedPullback_spec` uses `IsKFlatTensor`; its hypothesis is
definitionally the same as the existing `IsAcyclicTensorKFlat` predicate, so the
original counit-uniqueness and adjunction calculation still applies directly.
The declaration is uniform in the target complex and chain map, and adds no
boundedness, K-injectivity, or geometric hypotheses. The argument is valid for
zero complexes, empty schemes, and identity morphisms.

The full archived direct consumer was also compiled unchanged. It stops on an
independent duplicate-import error: `Sheaf.AlgebraicGeometry.DerivedPullback`
reintroduces `AlgebraicGeometry.derivedPullback`, already loaded from the adopted
source library. No consumer edits are forced by this import-only restoration.
A scratch consumer compiles (4.0 seconds), checking the unchanged theorem
signature and the definitional conversion from its K-flat hypothesis to the
upstream predicate. `#print axioms kFlat_pullback_adjunction_comparison` reports
only `propext`, `Classical.choice`, and `Quot.sound`. The scratch check explicitly
imports the upstream K-flat definition as well as the restored module.

Change record: `coord/changes/G2-kflat-pullback-adjunction-import.md`.

## Proved and sorry left

This is a zero-hole quarantine repair. The archived source has zero `sorry`s;
the restored source has zero `sorry`s. Holes closed: 0. Holes added: 0.
`AlgebraicGeometry.kFlat_pullback_adjunction_comparison`
(node `lem-pc-kflat-pullback-adjunction-comparison`) and its private
`counit_isIso` helper retain their complete proofs. No statements were split off.

## No longer needed

None. Both original public imports are still needed, and the added public import
is needed by the statement. No nodes, modules, declarations, or proof-dependency
edges are pruned. The quarantined direct consumer and the parent DAG node remain
needed and are preserved. No unit route changes.

## Where the brief, the DAG or earlier work was wrong

The queued item is a quarantine repair rather than an open proof obligation.
The sync removed the K-flat predicate from this module's transitive public
imports while retaining its existing public statement and complete proof in
quarantine. The repair makes that statement dependency explicit. The source
search and Mathlib searches did not reveal a shorter combined pinned Hom
comparison; the already complete component-based proof remains suitable.
The node's mathematical statement and proof plan are unchanged.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
