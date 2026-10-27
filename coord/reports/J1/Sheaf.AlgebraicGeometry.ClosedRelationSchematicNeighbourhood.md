## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.exists_closed_relation_schematic_neighbourhood` from the finite clopen neighbourhood, finite flat affine quotient, finding-opens, and schematic-image declarations. Added proved private helpers for transporting affine quotients, kernel-pair descent on the large site, and field-valued point images. The neighbourhood statement and definitions are unchanged.

Repair of return 38b16b42f: removed the duplicate private theorem
`local_surjectivity_of_universal`. The existing `universal_locally_surjective` in
`Sheaf.AlgebraicGeometry.EtaleRelationFindingOpens` is now public and reused through
the existing private proof import. Its type and proof are unchanged; the module is
unclaimed. The visibility change is recorded in
`coord/changes/J1-universal-locally-surjective-reuse.md`.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.AlgebraicSpace.exists_closed_relation_schematic_neighbourhood`. Added zero holes and split off zero statements. The delivered module contains zero `sorry`.

## No longer needed

`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers` and node `lem-trf-space-fibre-products-etale-covers` are unnecessary for this proof. Pullbacks and their quotient universal property are established directly by the presheaf pullback API and sheaf gluing. The remaining geometric route follows the assigned node. Removed the unused private proof import `Mathlib.AlgebraicGeometry.Morphisms.Proper`. No module is withdrawn. Removed the duplicate helper
`local_surjectivity_of_universal`; the proof now uses the existing
`universal_locally_surjective`. No additional geometric dependency is pruned by this repair.

## Where the brief, the DAG or earlier work was wrong

The planned appeal to `etale_atlas_presentation` on the base change does not itself produce the quotient universal property: that declaration takes the universal property as a hypothesis. The proof supplies it directly by local surjectivity and descent along the kernel pair. The affine quotient declaration is stated for literal spectra; a proved private transport helper handles arbitrary affine schemes. The descended T′-structure is obtained from the quotient universal property on the same fppf site over S.

The returned duplicate check correctly identified identical helpers. The existing helper
was private, so it had to be exposed in its original module before it could be reused.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
