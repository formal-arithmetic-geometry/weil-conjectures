## What changed

Replaced the item theorem's single `sorry` by a complete product-comparison argument
from two strictly smaller geometric statements. The original theorem signature, its
coefficient universes, all public imports and the actual localized extension are unchanged.
No other existing Lean module or node is changed.

The open unit is proved privately using the adjoint triple consisting of extension,
slice restriction and slice direct image. Subterminality of the open object makes the
slice-forgetful functor full, hence the slice direct-image counit invertible. Mathlib's
adjoint-triple criterion gives the extension/restriction unit isomorphism. A generic private
lemma identifies the restricted product comparison through those units by its projections.
For the complementary closed immersion, module forgetful preserves products and closed
abelian inverse image preserves countable products. Both closed restrictions are zero;
the support detection theorem then proves the original comparison invertible.

The closed functor is Mathlib's actual left-Kan-extension/sheafification construction
with AddCommGrpCat in max u (t+1). It is not a chosen functor supplied by a mere existence
claim. The closed subscheme is the actual vanishing-ideal construction.

## Proved and sorry left

This is a decomposition: one original hole is removed, two holes are added (net -1).
The item has zero remaining direct `sorry` occurrences, but its proof uses these new
geometric obligations. It is not an axiom-free proof of the product theorem yet.

- Closed original hole:
  `AlgebraicGeometry.Scheme.proEtaleRingedExtensionByZero_products_of_universes`.
- Added and left `sorry`:
  `AlgebraicGeometry.Scheme.proEtaleClosedAbelianProductsOfUniverses`
  (lem-sf-closed-abelian-products-of-universes).
- Added and left `sorry`:
  `AlgebraicGeometry.Scheme.proEtaleOpenClosedModuleSupportOfUniverses`
  (lem-sf-open-closed-module-support-of-universes).

The private open-unit and restricted-product lemmas are fully proved. Every new hole
is an entire public named theorem with source, proof in words, and matching DAG node.
The first new theorem contains no extension functor or module coefficients. The second
contains no products, product comparison or countable family. Neither restates the item.

## No longer needed

No original Lean import was removed and no module was withdrawn. The original imports
are statement dependencies and remain public. New imports are private proof imports.

The item's proof no longer directly invokes these planned tied-universe interfaces:
`lem-cbc-ringed-open-extension-products`,
`lem-weil-pbc-proetale-ringed-open-closed`,
`lem-weil-pbc-proetale-immersion-limit-preservation`, and
`lem-cbc-exact-pair-detects-isomorphisms`. The first would require identifying independent
universes, which is invalid. The next two are replaced by the two named geometric
refinements. The last is unnecessary because the support theorem detects isomorphisms
by the localization sequence's short five lemma. These results remain in the library;
this delivery does not claim that other consumers no longer need them.

The reduced closed-complement node and normalized localized adjunction node remain
actual proof dependencies. No UNIT statement or realized step is bypassed: this is
below the open-factor paragraph of sk-prop-sf-pf-coherence.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The plan cites already stated geometric
results, but their Lean interfaces fix coefficients to t+1, while the item requires
max u (t+1). They cannot simply be applied with the larger coefficient universe without
also changing the scheme universe. The two new statements isolate the precise geometric
refinements needed; the closed theorem uses the general Mathlib pullback construction,
whose category universes remain independent.

Sources read: Stacks proetale.tex, lemma-closed-immersion (09AA),
lemma-closed-immersion-affines-apply (09BL), lemma-jshriek-zero (09AG),
lemma-ses-associated-to-open (09AH), and lemma-j-shriek-limits (09BP), together with the
existing ringed open/closed and product proofs. Searches used LeanFinder, Loogle and
Mathlib grep through msearch.py, plus repository searches; searches.jsonl records the
actual queries. The returned condensed-sheaf results do not give this geometric theorem.

Edge cases checked in the two statements: empty X or Z, identity closed immersion,
empty or identity open U, zero coefficient rings and zero modules. Closed inverse image
is a functor to the zero sheaf category for empty Z; for identity i it is naturally the
identity. The complementary support assertions reduce to the corresponding single
restriction in the empty/identity cases. No qcqs hypothesis on X has been introduced.

## New nodes

`lem-sf-closed-abelian-products-of-universes`, in
`dag/nodes/sec-six-functors/lem-sf-closed-abelian-products-of-universes.json`, is the
coefficient-universe refinement of the closed part of Tag 09AA, restricted to countable
abelian products. Its module is
`Sheaf.AlgebraicGeometry.ProEtaleClosedAbelianProductsOfUniverses`.

`lem-sf-open-closed-module-support-of-universes`, in
`dag/nodes/sec-six-functors/lem-sf-open-closed-module-support-of-universes.json`, states
closed annihilation and complementary restriction detection, independently of products.
Its module is `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedModuleSupportOfUniverses`.
Both nodes inherit the item's chapter and unit and record their source, searches and
complete proof plan. No change record is required: no existing interface was changed.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
