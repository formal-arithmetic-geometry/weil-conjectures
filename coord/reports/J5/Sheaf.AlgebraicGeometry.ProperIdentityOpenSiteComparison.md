## What changed

Proved `AlgebraicGeometry.ProEtale.properIdentityOpenSiteComparison` in the assigned module,
without changing any existing signature or definition. Two proved private helpers identify
canonical adjunction identity isomorphisms and transport the sheaf identity square to D+.
The final calculation expands the specified compact-support comparison and uses naturality
of the inverse specified direct-image mate. Updated the existing node proof and dependencies.

The proof imports `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison` and
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` privately.
All existing public imports are retained to preserve the exported interface.
The local proof commands are documented in
`coord/changes/proper-identity-open-proof-scope.md`; the consumer check found no downstream
modules and no adaptations are required.
Remote single-file compilation passed without warnings (23.7 seconds).

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.ProEtale.properIdentityOpenSiteComparison`
(node `lem-coef-proper-identity-open-site-comparison`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module or its private helpers.

## No longer needed

Removed private imports `Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization` and
`Mathlib.CategoryTheory.Localization.Predicate`. The latter remains available transitively
through the exact-derived API, whose proved coherence laws implement the localization step.

The direct proof no longer needs `lem-sf-open-comparison-unit-normalization` or a new
sheafification calculation (`def-weil-pbc-sheafification`): the already-proved identity
clause of `lem-cbc-proetale-extension-zero-comparison` supplies the exact equation.
`def-weil-pbc-site-comparison-morphism` is not used as a separate proof step.
`lem-sf-class-compact-support-comparison` supplies no additional theorem needed here:
the specific construction `def-sf-compact-support-site-comparison-construction` is expanded.
Their statement/definition interfaces and existing public imports remain available.
No module is withdrawn, and no claim is made that these nodes have no other consumers.

## Where the brief, the DAG or earlier work was wrong

The original proof plan needlessly rederived the identity-open sheaf equation through
open-unit normalization. It is already the third conjunct of the recorded coherence theorem.
The isomorphisms there use `leftAdjointIdIso`, whereas this item's canonical maps use
`leftAdjointUniq` against a transported identity adjunction; the proved private equality
connects these constructions without changing either one. The termwise open comparison's
existing owner `def-weil-pbc-proper-open-site-extension` is now recorded as a proof dependency.
No mathematical statement was changed; the unit route is preserved. Empty schemes, zero
complexes and zero coefficient rings cause no exceptional cases in these categorical laws.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
