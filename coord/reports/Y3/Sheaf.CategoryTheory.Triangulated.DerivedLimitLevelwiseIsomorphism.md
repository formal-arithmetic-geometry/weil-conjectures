## What changed

Replaced the sole `sorry` in
`Sheaf.CategoryTheory.Triangulated.DerivedLimitLevelwiseIsomorphism` with a complete
proof of `CategoryTheory.isIso_derivedLimit_of_levelwise`, following the existing
DAG plan. Constructed the inverse to `Limits.Pi.map φ` as the product of the
component inverses; `Pi.map_comp_map` verifies both inverse equations. Used
`towerTransitionEndomorphism_natural_backward` with the reversed compatibility
identity to construct the morphism of the specified Roos triangles. Applied
`Pretriangulated.isIso₁_of_isIso₂₃` to its two invertible product components.
The signature, docstrings, definitions and imports are unchanged.

The assigned module compiles cleanly through `lcompile.py` (2.1 seconds).
LeanFinder and Loogle both found the cited Mathlib five lemma; the grep search
found the product-map composition lemma. No additional theory is necessary.

## Proved and sorry left

Closed 1 of 1 holes:
`CategoryTheory.isIso_derivedLimit_of_levelwise`
(node `lemma-weil-pbc-r-lim-levelwise-isomorphism`).
Added 0 holes; no `sorry` remains in the delivered module. Nothing was split off.

## No longer needed

None. Both existing imports remain necessary for the statement. Both declared
proof dependencies are used: `def-weil-derived-limit` supplies the specified
triangles, and `lem-weil-derived-limit-levelwise-iso` is realized by its Mathlib
match `Pretriangulated.isIso₁_of_isIso₂₃`. No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The Mathlib instance `Pi.map_isIso`
requires products of every family of the index shape, which the statement does
not assume; the explicit product inverse proves the required assertion under
exactly the two stated product hypotheses. The proof does not choose a
completion or assert its uniqueness. The unit route and existing DAG plan are
unchanged, so no node edit is required.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
