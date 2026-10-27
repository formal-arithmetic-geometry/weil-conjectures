## What changed

Proved `etaleOpenCounitFlatModels` from the existing bounded-flat coefficient/site-square, finite coefficient input models, constructible comparison, sheetwise coefficient computation, and canonical open tensor comparison APIs. The theorem statement and public imports are unchanged. Two model-map definition bodies are simplified to equivalent direct complex maps, with change records and generic equality proofs in the module. The other nine public definitions are unchanged. Private helpers assemble the finite-Tor comparison equivalence, preserve the domains under restriction, extension and scalar extension, construct models in every Tor interval, and identify the actual coefficient and evaluation maps.

## Proved and sorry left

The original hole in `AlgebraicGeometry.Etale.OpenCounitFlatModels.etaleOpenCounitFlatModels` is closed. No holes are added; no `sorry` remains in the delivery. The model and counit packages are proved private helpers, not new statement items. The file compiled cleanly in 54.9 seconds with zero written holes. Delivery preflight rechecks the final imports. Change records: `coord/changes/coefficientComplexMap-normalization.md` and `coord/changes/evaluationComplexMap-normalization.md`.

## No longer needed

The specialized pullback-line and compact-support Tor-window routes are replaced by exact restriction and extension stability on the source library and direct termwise flatness/constructibility preservation. The source declarations remain intact. Removed the following original proof imports, which are unused by the final route or supplied by the necessary existing public API:

- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.AlgebraicGeometry.ComparisonTorInterval`
- `Sheaf.Paper.ConstructibleCoefficientSiteSquare`
- `Sheaf.AlgebraicGeometry.EtalePullbackLineFlatModel`
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportTorWindow`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.Paper.PurEtaleScalarMateProjection`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`

The direct proof dependency list drops the following planned nodes; their declarations remain in the library and may still be used transitively elsewhere:

- `sk-thm-pe-constructible-comparison`
- `lem-sf-comparison-pullback-exact`
- `lem-sp-constructible-coefficient-site-square`
- `lem-sp-etale-pullback-line-flat-model`
- `lem-sp-etale-compact-support-tor-window`
- `lem-pur-site-restriction-module-adjunction-exact`
- `def-pur-etale-scalar-pullback-iso`
- `def-weil-pbc-extension-by-zero`
- `def-pur-sheaf-tensor-product`
- `lem-pur-derived-change-of-rings`

Removed the redundant proof import `Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalObjectComparison` after reusing the existing private finite-Tor object comparison in exceptional transport. That object-comparison result remains needed transitively. The constructible sheaf equivalence retains its explicit source proof import. The direct dependency `new-etale-proetale-exceptional-object-comparison` is supplied through the existing private finite-Tor comparison in `lem-sf-etale-proetale-exceptional-transport`; it remains needed transitively. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The theorem statement and all public imports are preserved. `coefficientComplexMap` drops an identity complex boundary, and `evaluationComplexMap` uses the induced complex-adjunction counit directly. These equivalent definition repairs address the fixed compile limit; the generic equality proofs explain both identifications. Consumer search reports only this module; no external adaptation is required.

The proof requires explicit compatibility of the two canonical identity-direct-image boundaries. The existing direct-image scalar identity law and exact-derived natural-isomorphism compatibility supply it. The ordinary open and etale sum extensions share their construction and adjunction, so the existing sheetwise formula applies after identifying these functors. Empty Tor intervals are handled by the zero complex.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
