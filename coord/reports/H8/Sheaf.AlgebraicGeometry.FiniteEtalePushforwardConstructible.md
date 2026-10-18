## What changed

Proved `AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_lowerStar_of_finite_etale`.
The proof converts the module constructibility predicate to `IsConstructibleSheaf`, uses finite
étale local splitting and the split-cover direct-image product theorem, proves finite products
constructible, refines the resulting finite affine étale cover by the global stratification
factoring lemma, and descends constructibility along the resulting surjective coproduct map.
Unused proof imports were removed from the module.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_lowerStar_of_finite_etale`
(node `lem-weil-pbc-finite-etale-pushforward-constructible`). Added 0 holes and split off 0.
No `sorry` remains in the delivered module and no new theorem with
`sorry` was added.

## No longer needed

Removed imports:

- `WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules`: generic ModuleCat restriction
  and base change already give the required module-linear isomorphisms.
- `Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleQcqsAffineLocal`: the existing global
  stratification-factoring theorem proves the gluing step directly.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`: the upstream definition is already
  public and used unchanged.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`: redundant direct import;
  its restriction comparison remains used through `WeilConjectures.SixFunctors.BaseChange.Etale`.

No longer direct proof dependencies: `lem-weil-pbc-constructible-qcqs-affine-local`,
`lemma-weil-pbc-etale-pullback-forget-modules`,
`lem-weil-pbc-quasi-separated-affine-cover-criterion`, and
`lem-weil-pbc-etale-local-on-source`. The finite coproduct of affine schemes is affine, so the
separate source-local etaleness and intersection argument is unnecessary. The coproduct-family
and affine-qcqs nodes remain used through Mathlib's instances. The direct-image definition,
coefficient predicate and scheme etale-composition facts remain statement/import infrastructure.
No claim is made that modules independently used by other parents leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan expands an affine-local restriction argument and constructs a coproduct by hand.
The existing global stratification-factoring theorem and the finite affine étale covering theorem
make that expansion unnecessary. The theorem statement itself is unchanged.

The item is below the unit's own realized statements and steps. The proof retains the finite
étale splitting/product/descent argument of Stacks 095H. The module compiles through `lcompile.py`
and its `--all` mode; the delivery dry run also passed the axiom probe and preflight. The only
unproved inputs are existing dependencies; in particular the surjective-pullback equivalence
remains an existing named theorem with `sorry`. No new dependency is restated.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
