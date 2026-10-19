## What changed

Proved `AlgebraicGeometry.ProEtale.proEtale_openExtension_products_derivedLimits`,
including its natural triangle, derived products, sequential Roos limits, and sheaf
products. All original statements and definition bodies are preserved.

Added two proved helper modules:
`Sheaf.CategoryTheory.ExactLocalizationDerivedTriangle` constructs the natural
triangle for an abstract exact localization sequence; it lifts derived morphisms
between K-injective representatives to chain maps, verifies all three comparison
naturality identities, and transports the canonical short-exact-sequence triangle.
`Sheaf.AlgebraicGeometry.ProEtaleModuleObjectProductsExact` transfers exact products
from sectionwise modules to the actual arbitrary monoid-module category. Its proof
passes through modules over the tensor unit and then the exact conservative
forgetful functor, without requiring commutativity of the given coefficients.

The retained draft's remaining naturality rewrite was repaired by expressing the
termwise identity and composite functors explicitly. The earlier split-off is now
proved. The three sandbox modules compile together, in import order, with no errors
or warnings (0.1 s, 2.5 s, and 18.9 s respectively in the final development compile).

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.proEtale_openExtension_products_derivedLimits`
(node `det-sf-open-closed-extension-zero-limits`).

Also proved both new helper statements:
`CategoryTheory.exactLocalization_derived_triangle`
(node `lem-sf-exact-localization-derived-triangle`) and
`AlgebraicGeometry.ProEtale.proEtale_moduleObject_products_exact`
(node `lem-sf-proetale-module-object-products-exact`).

No `sorry` remains in any of the three delivered modules. Holes closed: 1.
Holes added: 0. Split-offs with unfinished proofs: 0. The proofs use the existing
stated library dependencies, whose proofs are separate stage-3 obligations.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`;
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`;
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact` from the item module;
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective` from the item module;
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`.

`det-pe-products-derived` and its module are replaced by exact products in the actual
module-object category and the existing general localization-preserves-products instance.
Its upstream input `det-pe-products-exact` remains needed by the proved helper.
`lem-weil-derived-limit-existence` and its module are unnecessary: the hypothesis
already supplies a Roos triangle, and preservation constructs the image product and
transports that triangle. No separate choice or uniqueness of a cone is needed.
`lem-weil-pbc-complex-ses-triangle` and `lem-weil-pbc-kinjective-hom-derived` remain
needed under the proved natural-triangle helper, rather than directly in the item.
The corresponding Mathlib modules remain available to that helper.
No unit statement or realized proof step is bypassed (the unit realization lists are empty).
Public imports are retained to preserve existing visibility. Removed the obsolete top-level
`tool_uses` approvals for `det-pe-products-derived` and
`lem-weil-derived-limit-existence`; remaining approvals retain their order.

## Where the brief, the DAG or earlier work was wrong

The declared `products_derived` interface uses sectionwise `SheafOfModules` over RingCat,
whereas the assigned theorem uses `Mod` of arbitrary monoids in abelian sheaves. The
existing section equivalence requires commutativity. Applying it directly to B would
add an illegitimate hypothesis. The proved helper instead applies it to the tensor
unit, transfers exact products to abelian sheaves, then forgets arbitrary B-actions.

For the unit-module proof, the canonical unit action can override the stored action
in instance search. The proof explicitly supplies each module's stored action.
The retained exact-products node had unrelated triangle searches; these were replaced
with relevant logged searches for exact products and exactness transfer.
The initial dry run refused the retained unfinished split-off before 72 minutes;
its proof is now complete, so no early split-off is delivered.

## New nodes

`lem-sf-exact-localization-derived-triangle`: proved natural triangle for an exact
localization sequence in abelian categories. Its source is the original blueprint
triangle step and the canonical Stacks constructions (0152, 070I, 070K, 070Y).
The node records the implemented representative lifting and naturality argument.
Zero categories and zero functors cause no exception; no product, boundedness or
degreewise injectivity assumption was introduced.

`lem-sf-proetale-module-object-products-exact`: proved transfer of exact products to
the arbitrary module-object category. The source is the original blueprint product
step, using the existing section equivalence and exact-products theorem. Searches
identify the Mathlib transfer API actually used. Empty index sets and the zero ring
are covered by the categorical universal properties.
No change record is needed because no existing signature or definition changed.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
