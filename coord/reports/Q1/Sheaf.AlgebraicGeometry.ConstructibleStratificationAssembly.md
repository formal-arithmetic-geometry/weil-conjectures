## What changed

Retired `Sheaf.AlgebraicGeometry.ConstructibleStratificationAssembly`, the zero-hole
retirement repair listed in `coord/retire-items.tsv`. After the copyright header its
entire contents are byte-for-byte identical to the adopted-source module
`WeilConjectures.AlgebraicGeometry.ConstructibleStratificationAssembly`.

Changed the sole direct consumer `Sheaf.AlgebraicGeometry.EtaleStratifiedFinite` to
privately import the upstream module. Its public imports, signatures, docstrings, and
proof bodies are unchanged. No adopted-source file is edited. Reattached node
`lem-weil-pbc-constructible-stratification-assembly` to the upstream module/file; its
statement, declaration name, proof, dependencies, and unit route are unchanged.

Change record: `coord/changes/Q1-retire-constructible-stratification-assembly.md`.

## Proved and sorry left

Original holes: 0. Holes closed: 0. Holes added: 0. Holes split off: 0.
No `sorry` remains in any delivered Lean source. This is a duplicate retirement,
not a new proof of an open theorem. The already-proved
`AlgebraicGeometry.Scheme.exists_stratification_of_stratified_partition` remains
available with the identical full statement and proof in the upstream module.
The migrated consumer's `AlgebraicGeometry.Scheme.exists_etale_stratified_finite`
and its private helpers retain their complete proofs.

The original item compiled cleanly through `lcompile.py` (1.8 seconds). The migrated
consumer also compiled cleanly through `lcompile.py`. The delivery tools additionally
check transitive axioms and importer compatibility before pushing.

## No longer needed

- Module `Sheaf.AlgebraicGeometry.ConstructibleStratificationAssembly` is withdrawn
  using `deleted.txt`.
- The sole private import of that module in `Sheaf.AlgebraicGeometry.EtaleStratifiedFinite`
  is replaced by `WeilConjectures.AlgebraicGeometry.ConstructibleStratificationAssembly`.
- No mathematical DAG node or proof dependency is pruned. The assembly node remains
  needed by its parent and the approved curve-family tool use, with its exact theorem
  provided upstream. Its stratification, immersion, and constructible-subspace
  dependencies remain used by the upstream proof. No unit statement or step is bypassed.

The downstream search lists 11 modules; only the direct consumer mentions the theorem.
All are recorded in the change record. A quarantine search finds no additional importer.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a module with holes or an assigned repair. This
item has zero holes and is listed specifically for retirement. The retirement inventory
labels the twin DIFFERENT and mentions the old locally-closed-stratification import;
a subsequent reviewed migration has already made the modules identical apart from the
copyright header. The present delivery reconciles that inventory with the live sources.

The shortest route is the existing complete upstream proof. Direct searches in both
library roots found it; full-text comparison confirmed identical statement and proof.
LeanFinder returned finite-partition and scheme-cover ingredients, Loogle found no
indexed theorem under this name, and the Mathlib grep search found no assembly theorem.
No new mathematical result is required. Empty outer and local index sets remain covered
by the same dependent-sum construction, with no added nonemptiness assumptions.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
