## What changed

Proved `AlgebraicGeometry.ProEtale.finite_field_stratified_perfect_models` with its
statement, universes and public imports unchanged. All edits are in its module and
its existing DAG node; no definition or source-library module changed.

The proof has private proved helpers for finite common stratifications, finite local
models on arbitrary etale objects, the coefficient-realization comparison with
pullback, and preservation of actual constant complexes by comparison. It uses the
existing bounded constant-model theorem on each stratum. The chosen complexes
already have finite terms and bounded support; vector-space projectivity makes the
same complexes perfect. The canonical derived comparison transports their actual
constant differentials to the pro-etale site.

LeanFinder, Loogle and Mathlib grep searches found no replacement for the stratified
statement. Library searches found the source finite-value comparison and finite
local-constancy APIs, which avoid rebuilding their stalk and descent arguments.
Read Stacks 094G's induction proof and the recorded six-step DAG proof. The unit's
statement and three realized proof steps are unchanged.

Validation: the complete file compiles cleanly using `lcompile.py` (7.3 seconds).
The proof covers empty schemes and empty strata, zero complexes, and a = b: no
nonempty stratum, nonzero module, coefficient invertibility or integral lift is used.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.finite_field_stratified_perfect_models`
(node `lem-weil-pbc-finite-field-stratified-perfect-models`).

Added 0 holes; split off 0 theorems. There are no `sorry`s in the delivered module.
Existing imported statements are used as the stage permits; this is not a claim that
their entire transitive dependency closure is axiom-free.

## No longer needed

Removed these private proof imports:

- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.SixFunctors.GeometricInverseImageConstantModule`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `Mathlib.AlgebraicGeometry.Sites.Proetale`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`

The specialized fixed-ring exact upperStar, source finite-local-constancy APIs,
and natural `comparisonUpperStarConstantSheafIso` suffice. Thus this proof no longer
uses the general ringed-site witness theorems
`prop-weil-pbc-inverse-image-modules-exact`,
`lem-sfb-geometric-inverse-image-constant-module`,
`lem-pe-constant-left-module-inverse-image`, or
`prop-weil-pbc-proetale-constant-ring-map`. It also does not require the separately
stated site-comparison morphism or bounded-subcategory predicates:
`def-weil-pbc-site-comparison-morphism` and
`def-weil-pbc-bounded-derived-subcategories`.

`lem-pur-etale-proetale-cover` is unnecessary: the conclusion asks for an etale
cover, which is retained directly. Removed these unused nodes from proof_deps and
removed all three old tool_uses entries. The comparison-pullback node remains:
its existing canonical `comparisonUpperStarCompUpperStarIso` is used directly.
No declaration or module is withdrawn, and no global unreachability is asserted.

## Where the brief, the DAG or earlier work was wrong

The six-step mathematical plan works. Its general ringed-site inverse-image
witnesses are unnecessary for the fixed-scalar module functors already in the
statement. The source library supplies the needed exactness, finite-value
conversion, and natural constant comparisons. In particular, the proof needs no
extra conversion of the concluding cover to a pro-etale cover. The revised proof
steps and dependencies record the actual Lean argument. No statement correction
or new node was needed.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
