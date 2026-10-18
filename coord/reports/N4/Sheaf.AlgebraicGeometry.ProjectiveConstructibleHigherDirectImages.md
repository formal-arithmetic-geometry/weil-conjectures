## What changed

Proved `AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_of_isProjective`
in `Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages` without changing
its statement, definitions, visibility, or imports. The proof applies
`hasConstructibleHigherDirectImages_of_projectiveLine` and supplies its universal
projective-line hypothesis from
`isConstructibleEtaleModuleSheaf_higherDirectImage_projectiveLine`.

The line theorem requires coefficients invertible on `Spec k`, whereas the reduction
provides invertibility on each finite-type base `T`. For empty `T`, constructibility
is witnessed directly by the stratification with zero strata. For nonempty `T`, choose
a point. If `N` vanished in `k`, its image in the global sections of `T` and then in
that point's stalk would vanish. This contradicts the given invertibility in the
nonzero stalk. Thus `N` is a unit in `k`, and the global-sections isomorphism for
`Spec k` provides the line theorem's coefficient hypothesis. The theorem's integer
degree specializes to the natural degree required by property `C`.

The final file compiled cleanly through `lcompile.py` in 8.9 seconds. No new theorem,
node, or statement/definition change was needed: this is the existing two-step route
with its coefficient and empty-base glue made explicit. The current blueprint proof
was checked at `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-prop-sf-cbc/thm-fin-projective-constructibility-complete.proof.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_of_isProjective`
(node `thm-fin-projective-constructibility-complete`).

Holes added: 0. Split off: 0. Sorries left in the delivered module: 0.
The proof uses the existing stated projective-line theorem and projective-from-line
reduction; their existing proof obligations are not closed by this delivery.

## No longer needed

None. Both proof imports are used, and both public imports are needed for the unchanged
statement. All four original proof dependencies remain in use:
`thm-fin-projective-line-constructible`, `def-finrepair-property-c`,
`lem-finrepair-projective-from-line`, and `def-pc-projective-morphism`.
No module or node is pruned. Searches through `msearch.py` (LeanFinder, Loogle, grep)
and the existing source modules found no shorter exact theorem.

## Where the brief, the DAG or earlier work was wrong

The node's first step treats the coefficient hypotheses as matching immediately.
Their Lean interfaces require the explicit empty/nonempty distinction described
above: invertibility on an empty scheme does not imply invertibility in the base
field. This is glue within the stated route, not a changed statement or proof route.
The source in the existing node names the older `sec-smooth-purity` blueprint path;
the current snapshot places this theorem under `sec-six-functors-basics`.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
