## What changed

Reduced `WeilConjectures.SfOpenRoos.geometry_products` to the genuinely separate
Tag 09BP product comparison with independent coefficient universes. Proved the
finite-type geometry, quasi-compactness of the open immersion, stalkwise scalar
invertibility, and exact countable products in both the ambient and slice module
categories. The slice assertion transports an arbitrary restricted ring sheaf
along `ProEt.sliceEquiv`, using `ProEt.sliceDense` and a fully proved private
module transport equivalence. The private transport helper returns only the
equivalence its caller needs. No public signature changed. The existing
specification caches propositional limit-existence instances; proof irrelevance
keeps its predicate
definitionally equal to the original.

Added `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProductsOfUniverses`,
with the precise larger-universe form of the existing ringed product theorem.
Its proof remains the separate task. The old product theorem is tied to
`Scheme.{t}` / `CommRingCat.{t+1}` and cannot instantiate the required
`max u (t+1)` coefficient universe.

Completed `WeilConjectures.SfOpenRoos.comparison` from the existing
`exactProductFunctorStrictLimit` theorem. A proved private normalization lemma
identifies every signed augmentation with its ordinary strict-limit map followed
by the canonical signed Roos inclusion. Derived-unit naturality and invertibility
on K-injectives then give both actual-induced-map clauses for arbitrary
K-injective resolutions. The same witnesses satisfy every clause of the original
`ComparisonAssertions`; no public statement changed. The comparison specification caches propositional existence instances. In the
existing strict-limit module, the verbatim previous conclusion is now the named
predicate `StrictLimitAssertions`; its construction and every normalization
clause are retained. This avoids repeatedly specializing a large anonymous
existential proposition. No source-library module is changed.

## Proved and sorry left

Original holes: 2. Closed `WeilConjectures.SfOpenRoos.comparison` by proof from
existing declarations. Closed `WeilConjectures.SfOpenRoos.geometry_products` by
decomposition: its finite-type, scalar-invertibility and exact-products parts
are proved, and its product-preservation part uses the new separate source lemma.
The item module has zero remaining holes. The complete packet compiled in import
order: the new product statement in 3.4 seconds, the strict-limit module in
59.0 seconds, and the item in 42.3 seconds. The final comment-only cleanup is
checked again by delivery. The adapted strict-limit module also has zero holes.

Added hole (1):
`AlgebraicGeometry.Scheme.proEtaleRingedExtensionByZero_products_of_universes`,
node `lem-sf-ringed-open-extension-products-of-universes`.
Thus two upper holes close and one strictly smaller geometric hole is added:
one proof and one decomposition, net one hole closed. All private helpers are
proved. No sorry occurs inside a definition or a partial proof. The new theorem
has a complete proof in words, source and blueprint node.

## No longer needed

Removed proof imports `Sheaf.Paper.SfClopenCoefficientComparison`,
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts` and
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact` from the item.
The slice's own coefficient sheaf is already `B_X.over U`; its exact products
follow by transporting this arbitrary ring sheaf along the slice equivalence.
No comparison with the independently constructed completed ring on U is needed.
The direct exact-products theorem `det-pe-products-exact` replaces the longer
countable-product epi argument. The tied-universe ringed product result is
replaced in the item by its independent-universe refinement, whose proof still
follows that result's recollement argument. Consequently the new node still
records the original product node as a proof dependency; this packet does not
claim that its module is globally pruned. No library module is withdrawn.

Nodes no longer directly used by this item's proof: `lem-sf-clopen-coefficient-comparison`,
`lem-weil-proetale-countable-products-exact`, and
`lem-weil-pbc-noetherian-open-subscheme-noetherian` (the open morphism is
quasi-compact directly because its source is Noetherian). The unit's projection
formula route is retained. The normalized comparison is proved from its existing
strict-limit interface, with the extra actual-augmentation clauses established
by a proved private argument using the Roos resolution module's canonical
inclusion and derived-unit lemmas.

## Where the brief, the DAG or earlier work was wrong

The stage-2 review already noted the two genuine interface gaps: the ringed open
product theorem fixes the coefficient universe to t+1, and the existing exact
product theorem is on a scheme site rather than the slice. The latter is proved
here by module transport; the former is isolated as the separate Tag 09BP
universe refinement. Applying the old tied-universe theorem directly would
silently impose the forbidden equality `max u (t+1) = t+1`.

The original geometric plan unnecessarily compared completed coefficient rings
on U; exactness for the actual slice coefficient only needs an arbitrary ring
sheaf transported to the equivalent site. Empty schemes, empty opens, identity
opens, zero rings and nonseparated finite-type schemes require no added
hypotheses in the delivered statements.

## New nodes

`lem-sf-ringed-open-extension-products-of-universes` is the independent-universe
form of the sourced Tag 09BP ringed extension product assertion, strictly the
product component of `geometry_products`. Its Lean statement quantifies over
arbitrary commutative ring sheaves and uses the actual sheafified direct-sum
extension and canonical `piComparison`. No target or existing signature changes. The new lemma remains unproved
because the available recollement and closed inverse-image preservation APIs
all fix the section universe to t+1; a genuine generalization of that sourced
argument is still needed. It is not a renaming of either item theorem.

Change record: `coord/changes/T4-open-roos-comparison-proof-instances.md`.
The downstream consumers keep their original source; the predicate is
definitionally equal and the reduction barriers are local to this module.

Additional definition repair record: `coord/changes/T4-strict-limit-named-specification.md`.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
