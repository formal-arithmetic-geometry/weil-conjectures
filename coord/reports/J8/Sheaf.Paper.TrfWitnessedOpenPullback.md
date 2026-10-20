## What changed

Proved `WeilConjectures.witnessed_open_pullback` by deriving the canonical sheaf
comparisons, restricting along the bounded-below inclusion, and explicitly composing
with the retained witness isomorphism. All antecedents and normalization fields are
constructed directly. The proof first works locally over an arbitrary commutative ring
and then specializes to the given coefficient ring, avoiding repeated elaboration of
its quotient-ring construction. The theorem and conclusion structure are unchanged. Updated the node to the actual
seven-step proof, and recorded redundant public import removal in
`coord/changes/J8-witnessed-open-pullback-imports.md`.

## Proved and sorry left

Closed the single original hole: `WeilConjectures.witnessed_open_pullback`
(blueprint: `lem-trf-witnessed-open-pullback`). No holes remain in the item and no holes
are added elsewhere. This is one hole proved, zero split off.

## No longer needed

Removed redundant imports:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`

The direct proof no longer uses the separate abelian-coefficient exactness nodes
`prop-weil-pbc-inverse-image-exact` and `lem-weil-pbc-site-pullback-abelian-exact`,
or the intrinsic extension exactness node `lem-weil-extension-by-zero-exact`.
Their obsolete top-level tool approvals were removed from the node. The exact
fixed-scalar functors already have the required instances. The node's statement
dependencies and the trace-formula unit route are unchanged. No claim is made that
these modules disappear from the whole target closure; some remain transitively imported.
No new intermediate nodes or assumptions are needed.

## Where the brief, the DAG or earlier work was wrong

The earlier candidate repeatedly unfolded the concrete finite coefficient ring while
elaborating compositions. Generalizing that coefficient locally makes the full proof
compile within the single-file limit. No mathematical statement or definition changes.

Validation: the final module compiled without warnings in 15.3 seconds.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
