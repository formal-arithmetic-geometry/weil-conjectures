## What changed

Proved `ModuleCat.surjective_moduleComplexTower_limit`, with its statement and
`restrictedComplexTower` unchanged. The proof follows the existing five-step DAG plan:
restrict the tower, identify its limit as the kernel of one minus shift, prove that
map degreewise surjective by recursive lifting, apply the short-exact-sequence triangle,
and identify the localized termwise product with the derived product. Product
extensionality verifies both arrows and preserves the original limit projections.

Two proved private helpers handle the independent ring/module universes: exact
countable products are pulled back from abelian groups, and surjectivity of one minus
shift is checked after identifying an arbitrary product fan with the concrete product.
The kernel argument uses the existing generic fan API from
`WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit`; its main homotopy-limit
theorem specializes ring and module universes together, so cannot directly instantiate
this module's unchanged signature. The short exact triangle uses Mathlib's
`DerivedCategory.triangleOfSES_distinguished`, which implements the planned cone
quasi-isomorphism. The derived product uses the stated
`CategoryTheory.derivedCategory_countableProducts_core` dependency.

Added proof imports of `Mathlib.Algebra.Category.ModuleCat.Products` and
`WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit`. Public imports are unchanged.
No statements, definitions, or other modules were changed. No new public declarations
or nodes were needed. Read Stacks `more-algebra.tex`, lemma-compute-Rlim-modules
(091D), lemma-distinguished-triangle-Rlim-modules (0CQD) and its abelian-group proof;
`derived.tex`, lemma-products (07KC).

## Proved and sorry left

Closed 1 of 1 original holes:
`ModuleCat.surjective_moduleComplexTower_limit`
(node `lem-weil-pbc-surjective-module-complex-tower-limit`).

Added holes: 0. Remaining holes in the delivery: 0. No decomposition.
Server compilation passes without warnings. A separate `#print axioms` check reports
only `propext`, `Classical.choice`, and `Quot.sound` for the theorem.

## No longer needed

Removed direct proof imports:

- `Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts`: retired re-export; the
  existing direct import of `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`
  provides the actual dependency.
- `Mathlib.Algebra.Homology.HomotopyCategory.ShortExact`: its cone result remains
  used through `DerivedCategory.triangleOfSES_distinguished`, available from the
  TowerLimit proof import; no separate direct import is necessary.

No mathematical dependency nodes are pruned: all five planned steps are realized,
including the cone comparison and derived-product dependencies. No library modules
are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement errors found. The source library already supplies the
generic fan kernel argument and the short-exact-sequence triangle, avoiding a new
cone construction. Its surjective-tower theorem has a narrower universe arrangement,
so the proof retains independent ring, module, and derived-category universes.
The conclusion in fact uses only the ring cone, not its universality; the existing
`hc : IsLimit c` hypothesis is retained unchanged.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
