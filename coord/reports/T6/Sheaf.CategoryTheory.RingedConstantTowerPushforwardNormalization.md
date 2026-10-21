## What changed

Proved `CategoryTheory.ringedConstantTowerPushforwardNormalization` without changing its
statement or the public definitions. Private proved helpers construct the evaluation-at-zero
adjunction, show constants preserve K-injectives, apply uniqueness of right derived functors,
and calculate the localization factorizations. The complete calculation is a private
theorem over general abelian categories; the public theorem supplies the module-sheaf
instances, avoiding expensive unfolding of sheaf constructions during rewriting. The comparison and both constant-limit
isomorphisms are normalized on all complexes; evaluation, limit, and counit compatibility
then follow on K-injectives and extend by naturality. Updated the existing node's proof route.

## Proved and sorry left

Closed the single hole in `CategoryTheory.ringedConstantTowerPushforwardNormalization`
(node `lem-weil-pbc-constant-tower-pushforward-normalization`). Added no holes and no new
public statements. No `sorry` remains in the delivered module.

## No longer needed

The proof does not use the total-derived-functor construction or the strict-tower
homotopy-limit theorem: it uses the supplied derived operations and derives the ordinary
constant-limit unit directly. Removed the unused proof import `Sheaf.CategoryTheory.KInjectiveTotalDerived` and removed
`lem-weil-pbc-kinjective-total-derived` and
`lem-weil-pbc-ringed-strict-tower-homotopy-limit` from this node's proof dependencies.
The existing public imports are retained. No modules are
withdrawn; the node's statement dependencies and the blueprint unit route stay intact.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The old proof plan unnecessarily
asked for preservation of K-injectivity by direct image. Constants preserving K-injectives
suffices: any additive functor preserves homotopy equivalences between K-injectives, which
makes its specified right-derived unit invertible on them. The existing localization
uniqueness API constructs the comparisons without choosing additional resolutions or
additional derived functors.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
