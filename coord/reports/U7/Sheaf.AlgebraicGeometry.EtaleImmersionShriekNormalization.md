## What changed

Proved `AlgebraicGeometry.Etale.etaleImmersionShriekNormalization` in
`Sheaf.AlgebraicGeometry.EtaleImmersionShriekNormalization`, preserving its signature and both
specified normalization definitions. Exact finite direct image already works for `ModuleCat A`.
The existing exact-functor cohomology and lower-bound API proves the next four conjuncts.
Reassociation, cancellation of the inclusion compatibility isomorphisms, and the existing
bounded-below comparison cocycle prove both normalization compatibility equations.
Updated the node's proof and proof dependencies to this route. No public imports changed.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Etale.etaleImmersionShriekNormalization`
(node `lem-sf-etale-immersion-shriek-normalization`). Added 0 holes; split off 0 statements.
No `sorry` remains in the item. Both existing definitions are unchanged.
The complete proof compiled through `lcompile.py`; delivery preflight performs the axiom checks.

## No longer needed

Removed these unused private proof imports:

- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`

Removed proof dependencies `lem-weil-pbc-module-direct-image-left-exact` and
`lem-weil-pbc-module-sheaves-colimits-forgetful`: finite direct image is already exact for the
actual coefficient category. Removed `def-weil-pbc-sheafification`,
`lem-weil-pbc-localization-universal-property`, and
`lem-weil-pbc-exact-functor-derived-functor`: the existing source identity comparisons and finite
exact-derived comparison already supply the normalization constituents; no reconstruction via
those general statements is needed here. Removed the three corresponding obsolete `tool_uses`
entries (the two module-transfer nodes and the general exact-derived node). No declarations or modules are withdrawn, and no claim
is made that these dependencies are unused by other targets. The blueprint unit's route stays.

## Where the brief, the DAG or earlier work was wrong

The DAG's optional module-sheaf transfer is unnecessary: the source theorem for finite direct
image is already generic in the abelian coefficient category and applies directly to
`ModuleCat A`. The cohomology API is oriented opposite to the displayed conjuncts, so its inverse
is used. The ambient cocycle follows directly from the existing D+ cocycle by cancellation of
compatibility isomorphisms. No statement or definition repair was needed. No new nodes.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
