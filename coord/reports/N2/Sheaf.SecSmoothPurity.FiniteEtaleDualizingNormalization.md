## What changed

Prove `AlgebraicGeometry.ProEtale.finite_etale_dualizing_normalization` by assembling the
existing sum-adjoint tensor/coherence, dualizing-composite and horizontal-double-counit
results. Construct `graphSupportModel` directly as the canonical graph-derived
isomorphism, replacing selection of the uniquely graph-normalized witness. Its signature
and mathematical map are unchanged. The change record is
`coord/changes/N2-finite-etale-graph-model-construction.md`; the consumer scan finds no
external direct use. Private helpers compare adjunctions, tensor transposes and
exact/left-derived pullback squares. The DAG follows the actual assembly.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.finite_etale_dualizing_normalization`
(`lem-pur-finite-etale-dualizing-normalization`): all nine normalization laws are proved.
Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0. No statement is
split off and no new public theorem is added. The proof uses the existing declared
intermediate results as intended by stage 3. The complete module compiled cleanly in 44.2 seconds; final delivery validation follows.

## No longer needed

`lem-pur-finite-site-counit-projection-transport` is unnecessary for this assembly:
the existing Lean statement already uses the ordinary etale-origin coordinates and
the specified etale maps. No module is withdrawn. The Noetherian hypothesis is assembled
directly from Mathlib finite-type and quasi-compact results rather than importing
`lem-weil-pbc-finite-type-over-noetherian`.

The graph-uniqueness detour and its direct import
`Sheaf.AlgebraicGeometry.OpenExtensionProperSupportRange` are unnecessary after the
canonical construction. The following old private imports are removed. Their declarations are either available
through the actual proof dependencies or belong to the unused site-comparison route:

- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`
- `Sheaf.Paper.CompactSupportSiteCoherence`
- `Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact`
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.GlobalFiniteLevelCompactSupportBaseChange`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`
- `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`

The obsolete top-level tool-use approvals for the unused site-transport route are removed
(the retained approvals keep their original order):

- `lem-amb-etale-adjoint-locality`
- `lem-cbc-proetale-extension-zero-comparison`
- `lem-pur-compact-support-site-coherence`
- `lem-sf-proetale-constructible-origin`
- `lem-weil-pbc-comparison-direct-image-canonical-mate`
- `lem-weil-pbc-comparison-pullback`
- `lem-weil-pbc-etale-shriek-base-change-modules`
- `lem-weil-pbc-finite-type-over-noetherian`
- `thm-cbc-finite-level-proetale`
- `thm-weil-pbc-site-comparison`

All nine proof clauses typecheck; the complete module compiles within the 60-second limit.

## Where the brief, the DAG or earlier work was wrong

The source module's nine-step proof docstring predates the current five-step DAG assembly.
The statement itself and its specified maps remain unchanged. The two published derived
sum adjunctions have equal counits but are not definitionally equal, so an explicit
localization comparison is required before using the coherence results.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
