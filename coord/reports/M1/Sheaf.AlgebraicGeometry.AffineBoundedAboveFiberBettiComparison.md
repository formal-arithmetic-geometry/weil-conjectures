## What changed

Restored the quarantined module
`Sheaf.AlgebraicGeometry.AffineBoundedAboveFiberBettiComparison` at its original
Lean attachment. This is the rework assignment listed in `coord/rework.tsv`:
the module was removed following a cluster restore and red global build.
Its complete archived proof now compiles against the repaired and proved
`Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel` and current adopted
source modules. The delivered module is byte-for-byte identical to the current
quarantine archive; restoring the missing library module is the repair.
No definition or theorem signature changes. No auxiliary module is delivered.

The proof obtains K-flatness from the supplied upper bound and free terms,
applies the canonical affine residue-pullback comparison, then applies derived
homology and exact global sections on the field spectrum. The tilde/sections
unit identifies the resulting complex, restriction of scalars commutes with
homology, and cardinal rank transport across the explicit residue-field
isomorphism gives equality of finranks, including infinite dimension.

Validation: the module compiled through `lcompile.py`, with no errors or
warnings. The geometric dependency was also compiled from the current library
source as a temporary sandbox copy; that unchanged copy was removed from the
delivery. The delivery tool performs the declaration axiom probe and preflight.

## Proved and sorry left

This is a restoration of an already proved quarantined declaration, not a new
hole closure: 0 original holes, 0 holes closed, 0 added, 0 split off, 0 remaining.
`AlgebraicGeometry.Scheme.affine_boundedAbove_fiberBetti_eq`
(node `lem-sc-affine-bounded-above-fiber-betti-comparison`) has its complete proof.
The existing geometric dependency
`AlgebraicGeometry.Scheme.affine_kFlat_residuePullback_model` is now proved in
the library and is not split off again. No `sorry` occurs in the delivered module.

## No longer needed

None. No module, declaration, import or node is withdrawn. All five current DAG
proof dependencies remain used, and the current proof already matches the
node's three steps. The unit `sk-prop-av-cube` route is preserved.

The historical retired Sheaf import names were migrated in the quarantine
archive already; the restored file keeps those current WeilConjectures imports.
They are replacements for the same declarations, not pruned mathematics.

## Where the brief, the DAG or earlier work was wrong

The assignment describes an obligation that has been split off repeatedly, but
the current item is a quarantined zero-hole module, not an unfinished theorem.
Its missing source is accounted for by the explicit rework row. The missing
compiled artifact for its geometric dependency initially prevented compiling
it alone; compiling that unchanged current dependency into the sandbox overlay
allowed the full archived proof to compile. There is no mathematical defect or
reason to change the statement, its definitions, or its DAG dependencies.

Search: repository searches found the exact completed archived proof and the
current proved geometric comparison. Loogle with finrank/restrictScalars
returned no hits; msearch grep for kFlat_of_isStrictlyLE_of_flat returned no hits,
while direct source search located that categorical bounded-flat criterion.
The existing acyclic-tensor proof implements the same criterion and is retained.
No new statement was needed. Empty opens have no z; zero or infinite-dimensional
homology is covered by the cardinal-rank calculation without finiteness assumptions.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
