## What changed

The target theorem is proved from the existing module-cohomology basic-linearity theorem and a
strictly smaller underlying additive surjectivity theorem. The scalar map is assembled by
restricting scalars along `k → Γ(X, O_X)` and transporting along
`ModuleCat.restrictScalarsComp'App`. The sandbox adds three support modules for the topological
neighborhood argument, abelian Mayer--Vietoris surjectivity, and the module/abelian comparison.

## Proved and sorry left

Proved: `AlgebraicGeometry.Scheme.Modules.top_degree_open_restriction_surjective`.
The support declarations left as named holes are
`TopCat.top_degree_abelian_neighborhood_zero`,
`TopCat.top_degree_abelian_open_restriction_surjective`, and
`AlgebraicGeometry.Scheme.Modules.module_cohomology_restriction_surjective`.
They are strict intermediate statements and are each recorded as a new DAG node below.

## No longer needed

The target proof no longer uses the original direct module Mayer--Vietoris route, zero-dimensional
finite-discrete route, restriction-injective-resolution route, module Cech acyclicity imports,
Leray acyclicity import, or the old module augmented-lift imports. The target file now imports only
its statement dependencies, the additive restriction split, and the basic-linearity theorem.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the full module/abelian resolution comparison, punctured-neighborhood
colimit argument, and scalar assembly into one target proof. The available library interfaces make
the scalar assembly independent once the underlying additive surjectivity is stated, so the proof
was split into the three named intermediate statements below without changing the target statement.

## New nodes

`lem-weil-pbc-top-degree-abelian-neighborhood-zero` in
`lean/Sheaf/Topology/TopDegreeAbelianNeighborhoodZero.lean`.

`lem-weil-pbc-top-degree-abelian-open-restriction` in
`lean/Sheaf/Topology/TopDegreeAbelianOpenRestriction.lean`.

`lem-weil-pbc-top-degree-module-restriction-surjective` in
`lean/Sheaf/AlgebraicGeometry/ModuleCohomologyRestrictionSurjective.lean`.

Change records: `coord/changes/lem-weil-pbc-top-degree-abelian-neighborhood-zero.md`, `coord/changes/lem-weil-pbc-top-degree-abelian-open-restriction.md`, and `coord/changes/lem-weil-pbc-top-degree-module-restriction-surjective.md`.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
