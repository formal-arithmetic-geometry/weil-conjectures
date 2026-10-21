## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleRingedOpenDerived_products_roos` in
`lean/Sheaf/AlgebraicGeometry/ProEtaleRingedOpenRoosPreservation.lean`, preserving its
signature, its public imports, and the definition of `proEtaleRingedOpenDerived`.

A proved private helper `derived_preserves_products` passes product preservation
through exact derived functors using degreewise evaluation, the existing
`DerivedCategory.isLimitFanQ`, `mapDerivedCategoryFactors`, and essential
surjectivity of localization. The main proof obtains full faithfulness from the
invertible adjunction unit. Exact countable products on the ambient pro-etale
module category then transfer to the slice module category by
`HasExactLimitsOfShape.domain_of_functor`. Both module categories have K-injective
resolutions by their existing Grothendieck-abelian theorem. The product isomorphism
is exactly `PreservesProduct.iso`, hence its hom is the canonical comparison.
Projection extensionality verifies the tower transition identity. A triangle
isomorphism transports the distinguished image triangle, including the prescribed
shift comparison, and functoriality gives the first-arrow component equations.

Replaced the private import of
`Sheaf.AlgebraicGeometry.ProEtaleProductsDerived` with private imports of
`Sheaf.AlgebraicGeometry.ProEtaleProductsExact`,
`Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`, and
`WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit`.
Updated only `proof`, `proof_deps`, `proof_origin`, and removal of the obsolete
`det-pe-products-derived` tool approval in the existing DAG node
`lem-sf-ringed-open-roos-preservation`. The proof caches the abelian, countable-product, additive, shift, and triangulated
structures it repeatedly uses, and locally marks `proEtaleRingedExtensionByZero`
irreducible to avoid unfolding its sheafification composite. This local attribute
has no effect on importing modules. No public interface or source-library file
changes. The conservative static command gate requires the local attribute to be
recorded; see
`coord/changes/T3-proEtaleRingedOpenRoosPreservation-local-transparency.md`.
The downstream check lists no consumers of the item module.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.proEtaleRingedOpenDerived_products_roos`
(node `lem-sf-ringed-open-roos-preservation`). Added 0 holes and split off 0
statements. No `sorry` remains in the delivered Lean module. The private helper
`derived_preserves_products` is fully proved.

Validation: the proof first compiled with `lcompile.py` in 43.9 seconds without
warnings. The first delivery axiom-probe compile exceeded 60 seconds. Profiling
identified repeated instance synthesis and unfolding; the local reduction barrier
and cached structures compiled in 49.2 seconds with the development profiler on.
The profiler has been removed for delivery. The revised compile with the axiom
probe passed; the server structural preflight then requested a change record for
the local attribute, now supplied. All Lean lines are at most 100 characters.

## No longer needed

The private import `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived` and its node
`det-pe-products-derived` are unnecessary for this proof. Its scheme-site
specialization is replaced by the existing general exact-product localization API,
which applies directly to the slice module category after reflecting exactness.
No coefficient transport to a second presentation of the open site is needed.
This reports a dependency removed from this item; it does not withdraw that module
or claim that other consumers no longer need it.

The initially considered direct imports
`Mathlib.CategoryTheory.Adjunction.FullyFaithful`,
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`, and
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution` were
removed because their interfaces are already publicly available through retained
imports. All original public imports remain unchanged. No further declared
proof dependencies or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The planned transport of arbitrary
coefficient sheaves from the open slice to its scheme-site presentation is
unnecessary: the fully faithful, exact, product-preserving extension functor
reflects exactness of countable products from the ambient category. The DAG now
records this shorter route, together with the exact-products, Grothendieck-abelian,
and K-injective-resolution dependencies that the Lean proof actually uses.
The unit statement and route are preserved. Empty opens, identity opens, empty
schemes, zero coefficient rings, and zero transition maps require no extra
hypotheses and are covered by the same categorical argument.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
