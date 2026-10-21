## What changed

Proved `ModuleCat.localization_away_colimit` in
`Sheaf.RingTheory.ModuleLocalizationFilteredColimit`, preserving its exact
signature and all three public imports. Added two private proof imports:
`Mathlib.Algebra.Category.Grp.FilteredColimits` and
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`.

The proof constructs the shift endomorphism of the sequential colimit. It
inverts multiplication by f, while the stage transition formula and the
filtered-colimit equality criterion establish `IsLocalizedModule` for the
stage-zero map. `IsLocalizedModule.iso` then supplies the required linear
equivalence, and `iso_symm_apply'` gives its formula on every stage.

Updated the existing node's proof and proof_origin to this universal-property
argument. Its proof dependencies are unchanged. No definitions, other modules,
or public interfaces changed. The single-file remote compile succeeds in
3.1 seconds without errors or warnings.

## Proved and sorry left

Closed one of one original holes:
`ModuleCat.localization_away_colimit`
(node `lem-sc-module-localization-filtered-colimit`).

No sorry remains in the delivered module. No holes were added, no statements
were split off, and no new declarations or nodes were introduced.

## No longer needed

None. No existing imports, nodes, or library modules were removed or pruned.
The proof uses all three recorded Mathlib-leaf dependencies:
`def-weil-pbc-category-colimit`, `def-weil-pbc-module-localization-away`, and
`lem-weil-pbc-filtered-colimit-modules-elementwise`.

The Mathlib localization universal-property API avoids constructing a separate
fraction-valued cocone and proving its bijectivity directly; it uses the same
localization and filtered-colimit facts already recorded in the DAG.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was necessary. The direct ModuleCat
filtered-colimit preservation instance ties the ring and module universes,
whereas this theorem keeps them independent. The proof obtains preservation
through the forgetful functor to additive commutative groups and shrinks
additive-group filtered-colimit preservation to the natural-number index
universe. Explicit transition-map equalities avoid unnecessary unfolding of
the chosen colimit when simplifying morphism coercions.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
