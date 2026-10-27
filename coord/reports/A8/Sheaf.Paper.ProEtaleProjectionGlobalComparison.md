## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleProjectionGlobalComparison` with its original
signature and public imports. Resolving descent lifts the representative comparisons to
tensor isomorphisms. The coefficient equality identifies the operation with the existing
constructive `globalOperation`; pure-section extensionality identifies the ordinary tensor
comparison with the existing constructive `globalOrdinaryTensor`. Its explicit transport
formula gives the ordinary tensor square. Exact-derived factorization and the proved
`proEtaleTensorComparisonTransport` give the derived tensor square. Conjugate the pullback
isomorphism under the actual adjunctions and apply the existing abstract mate-square theorem
to construct the requested two isomorphisms and their equation.

Added two fully proved modules: `Sheaf.Paper.ProEtaleTensorTotalTransport` and
`Sheaf.Paper.ProEtaleTensorComparisonTransport`. The total square is checked on each
bidegree summand using naturality. The derived square is checked on resolving pairs and
reflected through the existing fully faithful restriction. Their hypotheses are general
comparison data; neither statement mentions a private canonical package. These modules
separate the checking of the signed-total and resolving-localization arguments after a
single-file version elaborated without errors but exceeded 60 seconds. Before splitting,
profiling, local irreducibility of the large sheaf constructions, and abstract categorical
path lemmas reduced unwanted unfolding and proof size. All new modules contain zero holes.

Only the item, its own node, the two new modules and their nodes are changed. No existing
shared interface or definition changes, so no change record or importer adaptations are
needed. Validation: `lcompile.py --all` compiled all three files with no warnings or errors: total transport 19.3 s, derived tensor transport 39.5 s, and the item 17.7 s. Every file is below 60 seconds. The theorem signature and original public imports were checked against the repository and match exactly.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.proEtaleProjectionGlobalComparison`
(node `lem-weil-pbc-proetale-projection-global-comparison`).

Also fully proved `AlgebraicGeometry.Scheme.proEtaleTensorTotalTransport` and
`AlgebraicGeometry.Scheme.proEtaleTensorComparisonTransport`, with the corresponding new
nodes below. All private helpers are proved. Zero `sorry`s remain in the three modules;
zero holes and zero unfinished split-off statements are added.

## No longer needed

No original imports are removed and no modules or nodes are pruned. The old direct
reference to `lem-weil-pbc-resolving-representative-whiskering` is replaced by the existing
pro-etale specialization `lem-weil-pbc-proetale-tensor-descent-data`; the general result
remains transitively needed. The parent now cites the two transport steps through the
new comparison theorem. The existing RingedProjectionTensorComparison module remains
needed by the unchanged GlobalModel construction. Neither slice data nor tensor-shift
compatibility is used. Conjugation under the actual adjunctions supplies the right-adjoint
comparison, so no separate K-injective counit-comparison statement is introduced.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The DAG's planned independent comparison of derived
counits is replaced by conjugation of the exact-derived ordinary pullback isomorphism.
The total-complex square also proves invertibility of the supplied total comparison,
because its other three sides are invertible. This avoids a second tensor-instance
comparison. The unit route is preserved.

## New nodes

`lem-weil-pbc-proetale-tensor-total-transport`, implemented by
`Sheaf.Paper.ProEtaleTensorTotalTransport`: the ordinary tensor square implies the square
of the actual signed total-complex comparisons. Fully proved; no `sorry`. The argument
covers unbounded and zero complexes and empty degree sums.

`lem-weil-pbc-proetale-tensor-comparison-transport`, implemented by
`Sheaf.Paper.ProEtaleTensorComparisonTransport`: normalized ordinary and exact-derived
pullback comparisons, together with tensor-model representative equations, imply the
derived tensor square. Fully proved; no `sorry`. This is strictly the tensor-comparison
step and does not assert a right-adjoint comparison or any projection-mate identity.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
