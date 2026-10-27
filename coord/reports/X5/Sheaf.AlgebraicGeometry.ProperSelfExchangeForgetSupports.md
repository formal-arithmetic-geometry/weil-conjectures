## What changed

Filled `AlgebraicGeometry.Etale.proper_self_exchange_forget_supports` without changing
its statement or public imports. Proved private helpers expose the proper
forget-supports hom, combine the existing compactification exchange and refinement
identities, and transport between the raw derived functors and the ordinary
finite-coefficient abbreviations. The typed comparison pattern is reused from
`Sheaf.SixFunctors.ProjectiveLinePresentedTraceExchange`. Local irreducibility
and cached instances keep these conversions from expanding the derived-category
constructions; no shared definition or global attribute changes. The main proof specializes to
the flipped self-product and derives the inverse identity by cancellation.

Proof imports now use the already proved source modules
`WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar`,
`WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence`, and
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange`.
The item's DAG proof and proof dependencies record this route.
No existing module other than the assigned item is edited; no definition changes.

Validation: the complete profiled proof compiled through `lcompile.py` in 18.3 s.
Development profiling and inspection commands were removed for the final
delivery check.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.proper_self_exchange_forget_supports`
(node `lem-sf-proper-self-exchange-forget-supports`). Both conjuncts are proved.
All private helpers are proved: `proper_hom_app`,
`proper_compactification_hom`, `raw_exchange_combined`, `exchange_of_forget`,
`comp_whisker_app`, `primed_exchange_app`, `proper_exchange_raw`, `replace_first`,
`proper_exchange_compactification`, `replace_arrow`, `proper_exchange_raw_model`,
`proper_exchange_transport_raw`, `proper_exchange_transport_ordinary`,
`proper_exchange`, and `inverse_exchange`.
Holes closed: 1 of 1. Holes added: 0. Sorries left in this delivery: none.

## No longer needed

Removed these unused proof imports:

- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization`
- `Sheaf.Paper.FiniteDirectImageComposition`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal`
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`

The corresponding direct proof dependencies, and their obsolete top-level
`tool_uses` approvals, are removed from this item's node:
`prop-weil-pbc-inverse-image-modules-exact`,
`lem-weil-pbc-inverse-image-composition-module-linear`,
`lem-weil-pbc-module-sheaves-grothendieck-abelian`,
`lem-sfb-derived-composition-adjunction-normalization`,
`lem-weil-derived-direct-image-composition`, `lem-weil-pbc-mate-pasting`,
`lem-kun-derived-pullback-composition-monoidal`,
`lem-asd-open-base-change-unit-mate`, and `def-weil-pbc-adjunction-mate`.
Their general calculations need not be reconstructed here: the source theorem
`rightDerivedLowerShriekOfCompactificationBaseChangeMap'_app_comp_toLowerStar`
already proves the required open/proper pasting identity. Properness by base
change and torsion-ring proper base change remain dependencies and their tool
approvals stay. The statement-level imports stay unchanged.

Comparing this item's old and new import closures, these five modules are no
longer reachable from the item:

- `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinearCore`
- `Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization`
- `Sheaf.Paper.FiniteDirectImageComposition`

This is item-relative pruning; other consumers can still require them.
These removals concern this item's direct proof requirements; no upstream
module or declaration is withdrawn. Some removed imports remain transitively
available through the unchanged public imports or the source proof modules.
The unit statement and its realized steps are preserved.

## Where the brief, the DAG or earlier work was wrong

The long generic normalization calculation planned by the DAG was unnecessary:
the source library already proves the specific compactification exchange and
refinement identities, including the actual chosen-map comparisons. Its proved
`exchangeCompatible` calculation provides the same pattern for a self-map
square; the present helper applies it to distinct proper vertical arrows.
The claimed statement itself is unchanged and needs no repair.

No new nodes and no change records are required.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
