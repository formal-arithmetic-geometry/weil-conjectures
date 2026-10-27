## What changed

Proved `AlgebraicGeometry.ProEtale.integralConstantModelHeart` in
`lean/Sheaf/Paper/IntegralConstantModelHeart.lean`. The coefficient abbreviation,
public imports and public theorem signature are unchanged. Proved private helpers
identify the small spectral valuation coefficient ring with the universe-lifted
coefficient ring, transfer the finite-presentation comparison, and assemble the
weak Serre heart argument. Updated the existing DAG node to this shorter route.

The integral finite-presentation comparison identifies constant-model constructibility
with the general constructible module-object predicate. Existing integral weak Serre
closure then supplies kernels, cokernels and extensions. The derived homology-property
API supplies triangulation and truncations. Mathlib supplies the fully faithful single
functor, the concentrated-complex criterion and the abelian full-subcategory instance.
Essential smallness transfers from the already proved constructible-module theorem.

## Proved and sorry left

Closed the sole hole in `AlgebraicGeometry.ProEtale.integralConstantModelHeart`
(node `det-lem-int-integral-heart-triangulated`): 1 of 1 original holes closed.
No holes remain in the item. Added 0 holes and split off 0 statements.
The item compiled cleanly through `lcompile.py` in 12.4 seconds.
All private helpers are proved. Existing imported statements may still contain holes;
this delivery neither adds nor changes their holes.

## No longer needed

Removed proof imports (none of the public imports was removed):

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.DerivedNakayamaFirstReduction`
- `Sheaf.Paper.IntegralHeartLocalModel`

`Sheaf.Paper.CartesianCoefficients` and `Sheaf.Paper.IntegralModels` remain imported
to preserve the unit route, although this assembly proof does not invoke their theorems.

Removed direct proof dependencies from the assembly node:

- `sk-lem-integral-models`
- `lem-sfb-integral-residue-class-triangle-closure`
- `det-lem-int-integral-heart-local-model`
- `lem-sfb-derived-degree-zero-abelian-criterion`
- `lem-sfb-stratified-constant-model-product-bound`

The residue-completeness route, degree-zero extracted criterion and separate stratified
product bound are unnecessary for this assembly: the existing integral Serre comparison,
Mathlib heart lemmas and proved module-object size theorem give these conclusions.
Truncation stability follows directly from homology of truncations and the boundedness
instances, so the local-model theorem is not used here. These are dependency removals,
not withdrawals: no module or upstream declaration is deleted, and these modules may
remain needed by other consumers (including proof imports of retained dependencies).

Removed obsolete top-level tool approvals:

- `det-pe-derived-nakayama-first-reduction`
- `lem-pur-derived-change-of-rings`
- `lem-weil-proetale-dbc-triangulated`
- `lem-weil-pbc-finite-ring-constructible-derived-origin`
- `lem-sf-derived-homology-long-exact`
- `lem-weil-pbc-complex-ses-triangle`
- `sk-prop-sfb-cartesian-coefficients`
- `lem-weil-pbc-noetherian-stratum-detection`

## Where the brief, the DAG or earlier work was wrong

The current four-step DAG assembly suggested a separate constant-model product bound
because of a missing bridge to the general constructible-module predicate. The existing
integral local finite-presentation comparison supplies that bridge after explicitly
transporting the small coefficient ring across a continuous ring isomorphism. This
also avoids assuming equality between coefficient and scheme universes or choosing
an arbitrary coefficient embedding. No statement or definition repair was needed.
The unit record has no assigned realized steps to bypass; its statements and route
records are preserved. The two unit-route imports flagged by preflight are retained.
The proof-context change record is
`coord/changes/Z8-integral-constant-model-heart-proof-context.md`.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
