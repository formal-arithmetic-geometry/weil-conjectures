## What changed

Proved `AlgebraicGeometry.Scheme.Modules.moduleAbelianCohomologyLarge_hmap` by combining
the existing edge comparison and coefficient transport with canonical Ext universe
change. The item privately imports three new proved theorem modules:
`Sheaf.AlgebraicGeometry.ModuleCohomologyExtHMap` and
`Sheaf.AlgebraicGeometry.ModuleAbelianLargeResolutionFormula` and
`Sheaf.AlgebraicGeometry.ModuleAbelianUniverseHMap`.
They prove small-Ext h-map compatibility from the adopted edge and transport
lemmas, evaluate the constructed large comparison through its fixed resolution
equivalence, and prove abelian h-map compatibility of canonical universe change.
`Sheaf.AlgebraicGeometry.ModuleAbelianUniverseEquiv` constructs an irreducible
function specialization of the existing universe equivalence with the bundled cohomology
codomain. It caches the representation; its data is exactly the underlying function of coherentExtUniverseEquiv,
with no existence choice or postponed proof. Private generic lemmas handle evaluation of additive
equivalences, universe transport for exact functors, and the explicit abelian map.

Profiling identified substantial kernel conversion time in these constructions.
After improving the local packaging and making universe choices explicit, the
small-Ext argument and comparison formula are checked in separate modules.
Existing public signatures, definitions, attributes and public imports are unchanged.
Only the item's existing module and node, the five new modules and their nodes, and
this report are delivered. No shared definition or adopted-source file is changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.moduleAbelianCohomologyLarge_hmap`
(node `lem-pbc-module-abelian-hmap`). Added 0 holes; split off 0 unproved statements.
Also proved `moduleCohomologyExtResolutionEquiv_hmap` and
`moduleAbelianCohomologyLarge_resolutionFormula`, and
`moduleAbelianUniverseMap_hmap` and `zariskiModuleHMap_formula` in the new modules. The definition
`moduleAbelianUniverseMap` has a complete concrete body.
No sorry remains in the delivered modules. Dependencies are reused as stated; this
report does not claim that all their transitive proof dependencies are sorry-free.

## No longer needed

No original import was removed. No module is withdrawn or claimed globally pruned.
The direct proof no longer reconstructs arbitrary-resolution normalization
(`new-module-cohomology-ext-resolution-normalization`, module
`WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization`) or
forgotten-injective acyclicity (`lem-sc-injective-module-abelian-acyclic-zariski`, module
`WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic`). Both remain needed
transitively by the reused edge comparison; neither obligation is withdrawn.
Coefficient naturality (`new-module-cohomology-ext-resolution-naturality`), the edge
comparison (`new-module-cohomology-ext-resolution-edge`), coefficient transport
(`new-module-cohomology-coefficient-transport`), the fixed large comparison and the
explicit abelian map definitions remain needed. The unit's realized route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original proof plan repeated existing adopted-source machinery.
`moduleCohomologyExtResolutionEquiv_edge` handles arbitrary scheme morphisms, and
`moduleCohomology_transport_coefficient` extends its identity coefficient to the
required arbitrary coefficient. Universe compatibility follows by comparing represented
derived morphisms with `Ext.mapExactFunctor_hom` and `Ext.homEquiv_chgUniv`.
No new unproved mathematical statement or definition repair is needed.
Searches used LeanFinder, Loogle and grep via msearch, followed by rg searches of
both library roots, Mathlib and the dependency nodes. No exact exposed formula for
this project-specific comparison was found; the existing components give the proof.
The argument makes no degree-positivity, nonempty-scheme, quasi-coherence or nonzero
coefficient assumption, so degree zero, empty schemes and zero modules stay included.

## New nodes

`lem-pbc-module-abelian-large-resolution-formula` records the proved evaluation formula
in `Sheaf.AlgebraicGeometry.ModuleAbelianLargeResolutionFormula`. It evaluates the same
fixed natural-isomorphism component, packaged as an additive equivalence, followed by
Ext universe change. It has no scheme map or functoriality assertion and no sorry.

`lem-pbc-module-ext-resolution-hmap` records the proved small-Ext compatibility in
`Sheaf.AlgebraicGeometry.ModuleCohomologyExtHMap`. It applies the existing coefficient
transport to coefficient naturality and edge compatibility. It contains no universe
change and no sorry. Together the two proved statements supply distinct steps of the
item's argument; neither moves the original hole to another name.

`def-pbc-module-abelian-universe-equiv` records the concrete cached specialization of
canonical Ext universe change, in `Sheaf.AlgebraicGeometry.ModuleAbelianUniverseEquiv`.
The domain is the existing small Ext group and the codomain is the existing bundled
large cohomology group. Its concrete function applies coherentExtUniverseEquiv to its input.

`lem-pbc-module-abelian-universe-hmap` records the proved compatibility of this cached
universe change with the explicit abelian Ext h-map, in
`Sheaf.AlgebraicGeometry.ModuleAbelianUniverseHMap`. Its input is an arbitrary small
Ext class, and its statement has no module-cohomology map or resolution equivalence.
It has no sorry. The item combines these APIs without unfolding the cached equivalence.

`lem-pbc-zariski-module-hmap-formula` records the proved evaluation identity in
`Sheaf.AlgebraicGeometry.ZariskiModuleHMapFormula`. It unfolds the existing explicit
Zariski h-map into its inverse-image, constant-integer and adjoint-coefficient factors.
Its proof is complete. Keeping this conversion separate from the universe-transport
specialization avoids repeating the bundled/raw Ext conversion in one compile.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
