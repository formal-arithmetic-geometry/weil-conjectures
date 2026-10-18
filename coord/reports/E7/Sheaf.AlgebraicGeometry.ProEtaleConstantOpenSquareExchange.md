## What changed

Proved `AlgebraicGeometry.Scheme.openSquarePullbackModel_existsUnique` in
`Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange`, with its signature unchanged.
The two private helpers prove that transposing the specified inverse-image coefficient
map recovers the specified direct-image coefficient map, then use
`SheafOfModules.pushforwardCongr` to identify the right adjoints by identity on sections.
Transport the tensor-normalized adjunction along that comparison and apply
`Adjunction.leftAdjointUniq` to the existing realization-normalized adjunction.
`unit_leftAdjointUniq_hom_app` proves the required sectionwise normalization.
For uniqueness, the assumed section equations identify the adjoint of every component;
injectivity of `homEquiv` and extensionality identify the natural isomorphisms.
No public statements, definitions, imports or visibility changed.

This follows the module's existing normalized-mate proof plan. The general open-square
exchange and its derived normalization/pasting data remain supplied by the existing
`ProEtaleOpenSquareExchange` module. No unit route is bypassed.

LeanFinder returned `Adjunction.leftAdjointUniq` and its unit equations; Loogle confirmed
`Adjunction.unit_leftAdjointUniq_hom_app`; Mathlib grep confirmed those equations and
`pushforwardCongr_hom_app_val_app`. Their types and source were checked. The final module
compiled through `lcompile.py` in 2.4 seconds with no errors or warnings.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.openSquarePullbackModel_existsUnique`
(node `lem-trf-open-square-exchange`). Added 0 holes; split off 0 statements.
There are no `sorry`s left in the delivered module. The existing imported declarations
may still depend on `sorry`; this delivery uses their published statements as required.

## No longer needed

None. All three existing public imports remain necessary for the module's public
statements and definitions: `ProEtaleOpenSquareExchange`, `ProEtaleConstantRingOperations`
and `SfIntrinsicRealizationTransport`. No module or node is pruned. The general
open-square exchange still uses the original node's geometric and derived dependencies;
this delivery closes only the coordinate-identification obligation by the adjunction
uniqueness input already named in that node.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The two direct-image functors have the same
section maps but are not definitionally equal: their scalar maps differ syntactically
by transposition followed by its inverse. The adjunction Hom-equivalence inverse law
proves equality of those coefficient maps, and the identity-on-sections pushforward
comparison resolves the difference without changing either interface.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
