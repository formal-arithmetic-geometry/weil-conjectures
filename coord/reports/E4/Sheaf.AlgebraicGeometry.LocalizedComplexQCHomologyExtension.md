## What changed

Withdrew the duplicate Sheaf module through `deleted.txt`, changed the sole consumer
`Sheaf.AlgebraicGeometry.FiniteFreeHomComplexQCCohomology` to import the adopted
`WeilConjectures.AlgebraicGeometry.LocalizedComplexQCHomologyExtension`, and repointed the
DAG node `lem-sc-localized-complex-qc-homology-extension` to the existing source module.
The source theorem and all consumer declarations and proofs are unchanged.
Change record: `coord/changes/retire-localized-complex-qc-homology-extension-E4.md`.

## Proved and sorry left

The current item module had zero local `sorry`s before withdrawal, and this delivery adds
zero `sorry`s. Holes closed: 0. Holes added: 0. Split off: 0. The retained source twin's
`AlgebraicGeometry.localized_complex_qc_homology_extension` is already compiled and
sorry-free; no new statement is introduced.

## No longer needed

The duplicate module and its direct Sheaf import are no longer needed. No proof dependency,
unit statement, or mathematical route is removed: the source twin provides the identical
public theorem. No other module imports the withdrawn path.

## Where the brief, the DAG or earlier work was wrong

The retirement inventory still listed this already-proved duplicate as a one-hole Sheaf
item after the source twin had been adopted. The Sheaf and source files differ only in
copyright text and the local heartbeat comment; their theorem statements and proof
constructions agree. This is therefore an import/module retirement repair, not a new proof.

## New nodes

None.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
