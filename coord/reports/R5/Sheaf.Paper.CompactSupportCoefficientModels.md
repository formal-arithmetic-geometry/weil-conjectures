## What changed

Reduced `WeilConjectures.compactSupportCoefficientModels_ordinary` to objectwise
constant/completed coefficient isomorphisms with their pure-tensor section formulas.
The parent constructs the natural isomorphism using tensor-generator extensionality
and naturality of scalar extension, then proves uniqueness by the same generators.
The remaining construction is in
`Sheaf.Paper.CompactSupportCoefficientModelsOrdinaryExistence`.

The arithmetic basis and quotient basis are proved locally from the public local-field
integral-basis theorem and Mathlib's basis-change and quotient-tensor APIs. The existing
private normalized scalar-comparison API is retained. The initial proof context now
respects transparency. Every original theorem signature and public definition is unchanged.
Both modules passed a paired compile, including generated artifacts; the parent took
58.8 seconds.

## Proved and sorry left

Original hole closed: `WeilConjectures.compactSupportCoefficientModels_ordinary`.
New hole: `WeilConjectures.compactSupportCoefficientModels_ordinary_exists`, recorded by
`lem-pur-compact-support-coefficient-models-ordinary-existence`.
There was 1 original hole and there is 1 remaining hole. This is a decomposition,
with net zero holes closed. The new statement asserts only objectwise isomorphisms;
it asserts neither naturality nor uniqueness, which are proved in the parent.

## No longer needed

The ordinary clause no longer directly needs `lem-sfb-finite-free-scalar-coordinates`
or `lem-sfb-ringed-derived-monoidal-comparisons`: it uses the objectwise comparison
and tensor-generator API. Those two obsolete direct DAG edges are removed.

The broad private imports of `AdicBasisLimit` and `CompletedIntegralFiniteFree` are
removed. Their direct DAG edges are replaced by the explicit quotient-basis argument
and `lem-sfb-local-field-integral-basis`. The remaining objectwise construction still
uses the basis-limit and completed-freeness nodes transitively. The public and private
imports of `FiniteFreeCompletedScalarComparison` remain needed for its normalized API.
The unit route is retained; no module or source-library declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is changed. Explicit sheafification instances and the site's
distinct object and morphism universes are needed for tensor extensionality.
Detailed profiling showed that the long final "linting" interval included waiting
for earlier asynchronous kernel checks; the final linter itself was fast. In particular,
unfolding the scalar-comparison specifications was expensive, so the existing proved
specification lemmas are retained. Two generic rewrites are replaced by explicit equality transitivity and functor
composition under the transparency-respecting context. No linter is disabled or
compilation limit changed.

## New nodes

`lem-pur-compact-support-coefficient-models-ordinary-existence` records the componentwise
basis comparison, with declaration
`WeilConjectures.compactSupportCoefficientModels_ordinary_exists` in
`Sheaf.Paper.CompactSupportCoefficientModelsOrdinaryExistence`.

Change record: `coord/changes/R5-compact-support-coefficient-proof-context.md`.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
