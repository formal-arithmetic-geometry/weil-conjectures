## What changed

Proved `AlgebraicGeometry.RingedSpace.exists_finitePresentation_representatives` without
changing its statement. Construct local models as cokernels of maps between finite free
module sheaves, indexed by two natural numbers and a morphism. A proved private helper
reindexes any finite presentation by lifted finite ordinals and transports its cokernel
universal property. Apply the existing local-model gluing-data theorem, construct the
cocycle from local presentation isomorphisms, and glue the comparisons and their inverses.
Finally restrict the type of data to modules of finite presentation. An irreducible private
overlap-isomorphism definition and its proved section-map formula keep restriction
computations from unfolding the entire composite during cocycle checking. Updated the node and
docstring to this specialization of Stacks 01BC using 01BN. Added private proof imports
of `Sheaf.Topology.ModuleLocalModelGluingDataSet` and `Mathlib.Data.Fintype.EquivFin`.

Validation: the complete module compiled cleanly through `lcompile.py` in 37.6 seconds.
All helpers are proved; the original public imports and theorem signature are preserved.
The static gate requested a change record for the new top-level proof commands:
`coord/changes/finite-presentation-representatives-proof-commands.md` documents all
downstream users and confirms that no consumer adaptation is needed.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.RingedSpace.exists_finitePresentation_representatives`
(node `lem-weil-pbc-module-finite-presentation-representatives`). Added 0 holes; no sorry
remains in this module. The proof uses the already stated
`AlgebraicGeometry.module_local_model_gluing_data_set`; its existing sorry is unchanged.
This is a proof from the stated dependencies, not a decomposition into new statements.

## No longer needed

Removed the unused direct proof import `Sheaf.CategoryTheory.RingedSiteModules`; it is
already provided by the gluing-data definitions.

The route does not need `lem-weil-pbc-module-quotient-map-small-models` or its module
`Sheaf.Algebra.Category.ModuleCat.Sheaf.QuotientMapSmallModels`. Finite presentation
already supplies maps between finite free modules and their cokernel universal properties,
so arbitrary quotient parametrization and literal kernel-subsheaf data can be omitted.
The original finite-type detour, kernel computation, and epi-as-cokernel argument are
also unnecessary here. This does not withdraw the quotient module, which other nodes
may still need. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The existing plan is mathematically valid but unnecessarily passes through finite type
and arbitrary quotients. Direct finite-presentation cokernels avoid that step and avoid
transporting quotient families between a restricted ringed space and the localized site
`Over U`. The local gluing-data type is already in universe u, so its finite-presentation
subtype itself is a valid index type. Empty spaces/covers and zero ranks are allowed;
repeated opens are removed by taking the range of the presentation cover.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
