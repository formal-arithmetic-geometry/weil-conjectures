## What changed

Proved `CochainComplex.termwise_product_isKInjective_and_isLimit` in
`Sheaf.Algebra.Homology.KInjectiveProductsTermwise`, with its exact statement and
universes unchanged. Reused `HomotopyCategory.isLimitFanQuotient` under the stated
family-specific degreewise limit assumptions. Closure of the right orthogonal of
acyclic complexes proves K-injectivity. Essential surjectivity of `Qh` and the
K-injective Hom bijections transport the universal property to the derived category;
`quotientCompQhIso` identifies the actual localized projections.

Added proof-only imports of `Mathlib.Algebra.Homology.DerivedCategory.KInjective`,
`WeilConjectures.Algebra.Homology.HomotopyCategory.Products`, and
`WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products`. Updated the existing
node's proof, proof dependencies, and proof origin to match the implementation.
Public-import pruning is documented in
`coord/changes/P3-termwise-product-import-pruning.md`, including all 14 transitive
importers and the unchanged public declarations. No downstream adaptation is needed.
The module compiles without warnings. No signature, definition, or target changed.
The proof handles empty families, arbitrary indexing universes, and arbitrary
localization universes without extra product or resolution assumptions.

## Proved and sorry left

Closed the one original hole:
`CochainComplex.termwise_product_isKInjective_and_isLimit`
(node `lem-pc-ringed-space-product-kinjective`).

Holes closed: 1. Holes added: 0. Holes left in the item: 0. No decomposition.
No new modules or intermediate sorry statements.

## No longer needed

Removed imports `Sheaf.Algebra.Homology.KInjectiveProducts`,
`Sheaf.CategoryTheory.KInjectiveBridge`, and
`WeilConjectures.CategoryTheory.KInjectiveBridge`.
The first is an empty compatibility module whose public imports are already imported
explicitly here. The other two supply chosen-resolution constructions unused by this
proof. The original three explicit public Mathlib imports remain, so the public
interface is preserved. No declaration from any removed module is needed.

Removed `def-sp-kinjective-bridge` from the proof dependencies: its resolution choice,
Grothendieck existence, and derived-functor constructions are unnecessary. The
statement dependency recording the K-injectivity convention remains unchanged;
Mathlib's existing `IsKInjective` predicate supplies that convention.
`def-weil-category-product` and `lem-weil-pbc-kinjective-hom-derived` remain needed.
No other planned dependency is pruned. No unit statement or realized proof step is
bypassed. These removals do not assert that other callers of these modules disappear.

## Where the brief, the DAG or earlier work was wrong

The existing node's proof record described retirement of the older duplicate and
claimed the arbitrary-family statement lacked a verified realization. The assigned
module now provides that realization. The library's proved homotopy-product lemma
already accepts preservation for this one family, which Mathlib derives from the
stated degreewise products; products of every family in the coefficient category
are unnecessary. No canonical theorem from an unavailable upstream snapshot was
assumed or redeclared. No mathematical statement correction was needed.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
