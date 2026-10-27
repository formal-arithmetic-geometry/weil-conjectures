## What changed

Filled the six theorem proofs in
`Sheaf.AlgebraicGeometry.OpenCoefficientSquareActionIdentification`, preserving all
statements and concrete definitions. The quotient normalization uses the existing
`Mod.extensionIso_quotient_formula`. The inverse coefficient square follows by
cancelling the two coefficient isomorphisms. The action computations use monoidal
naturality; expansion of the prescribed comparison and naturality of
`Mod.extendScalarsIsoComapInv` give both normalized component identities. Collapse
naturality gives the morphism formulas. Faithfulness and cancellation identify the
ordinary isomorphisms, and `Functor.mapDerivedCategoryNatIso_symm` gives the derived
equality with the original composition factorization isomorphisms.

Added two proved private categorical cancellation helpers to keep the concrete
scalar-extension definitions out of the final cancellation steps. Added the private proof import
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` for that
proved derived-isomorphism API. Updated the existing node's proof, proof dependencies,
proof origin, and pruned obsolete tool approvals to match the implementation.

## Proved and sorry left

Six original holes closed, by declaration in
`AlgebraicGeometry.ProEtale.CondensedRing`:

- `openCoefficientCollapse_quotient`.
- `openCoefficient_inverse_square`.
- `openCoefficientSquare_actions_components`.
- `openCoefficientSquare_maps`.
- `comapUpperStarIso_symm_eq_openCoefficientIdentityIso`.
- `openCoefficientSquare_action_identification`.

Zero holes remain in the item; zero holes added; zero statements split off.
The final full sandbox compile passed without warnings in 43.6 seconds under the
default heartbeat and 60-second time limits. No public signature or definition changed.

## No longer needed

Removed private proof imports `Sheaf.CategoryTheory.SheafTensor` and
`Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`. The proof does not use the
aggregate statements `sfbSheafTensor_properties` (node `sk-def-sfb-sheaf-tensor`)
or `module_pullback_additive_exact` (node
`det-prop-sfb-module-pullback-exact-main`). Existing ambient sheaf instances and the
pullback construction's exactness instances suffice. Both nodes were removed from
this item's proof dependencies; the latter was also removed from its `tool_uses`.
No module or node is withdrawn, and other consumers may still need these modules.

## Where the brief, the DAG or earlier work was wrong

No statement correction. The original plan's separate aggregate tensor and pullback
exactness applications are redundant for this concrete implementation. The existing
localization API already preserves inverses on the whole unbounded derived category,
so a new degreewise construction is unnecessary. The prescribed coefficient-square
construction and the unit route are retained.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
