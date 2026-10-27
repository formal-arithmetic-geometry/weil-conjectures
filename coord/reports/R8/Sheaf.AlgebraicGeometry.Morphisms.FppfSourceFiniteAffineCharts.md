## What changed

Replaced the proof of `AlgebraicGeometry.exists_fppf_source_finite_affine_charts`
with a complete proof following the existing four-step DAG plan, using only Mathlib.
Choose affine neighbourhoods V and W using `Scheme.isBasis_affineOpens`.
Index the source charts by affine opens contained in the inverse image of W.
Surjectivity gives coverage by their images; `Scheme.Hom.isOpenMap` makes those
images open. Apply `IsAffineOpen.isCompact` and `IsCompact.elim_finite_subcover`,
then reindex the selected finite family using `Fintype.equivFin`.
The affine-pair `flat_appLE`, `finitePresentation_appLE`, and `finiteType_appLE`
criteria give the coordinate properties, and `appLE_comp_appLE` identifies the
composite coordinate map. The theorem signature and public imports are unchanged.

The complete proof compiled with lcompile.py in 3.4 seconds before import cleanup.
The final delivery compile and axiom probe check the cleaned version.
No new declarations, modules, or nodes are introduced. The existing DAG proof,
proof dependencies, and source remain accurate without edits.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.exists_fppf_source_finite_affine_charts`
(node `lem-a1-fppf-source-finite-affine-charts`).
Added 0 holes. Remaining holes: none. Split-off statements: none.
This is a complete proof, not a decomposition into unproved statements.

## No longer needed

Removed the unused private imports
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` and
`Mathlib.Topology.Defs.Filter`. Compactness is already available from AffineScheme;
quasi-separatedness is not used. All nine existing proof-dependency nodes remain
used as recorded, including the compactness clause of
`lem-weil-pbc-affine-scheme-qcqs`. No Sheaf dependency, DAG node, or library module
is withdrawn or made unnecessary by a replacement route.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The Stacks proof at Descent Tag 02KL
(`lemma-flat-finitely-presented-permanence`) agrees with the finite-image-subcover
argument. The selected affine opens need only have images covering W; the proof
does not claim that they cover its entire inverse image. No separation or
quasi-compactness assumption on the original morphisms was added.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
