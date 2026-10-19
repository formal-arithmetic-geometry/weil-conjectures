## What changed

Proved `etaleProEtaleCoefficientCompatibility_composition` without changing its signature.
The étale equation follows from compact scalar coherence, conjugated through the three
compactification comparisons. The pro-étale equation follows by pasting the main theorem's
site squares, naturality, and the explicit bounded-below composition boundary calculation.
All new helper lemmas are proved. No new statements with sorry were introduced.
The local proof attributes are documented in
`coord/changes/etale-proetale-coefficient-compatibility-proof-options.md`.

## Proved and sorry left

Closed one of the three original holes:
`AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility_composition`.

Two original holes remain, both attached to node
`lem-sp-et-proet-coefficient-compatibility`:
`AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility`
and
`AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility_sum`.
Holes added: zero. This is a proof from the existing main site square and the existing
compact scalar coherence declarations, not a decomposition into new holes.

## No longer needed

The composition proof reuses `Etale.etaleCompactScalarComposition` and its refinement
coherence instead of rebuilding the compatible tower and proper/open interchange.
The removed proof-only imports are `Sheaf.AlgebraicGeometry.EtaleSumStalks`,
`Sheaf.Paper.AcyclicFlatProperCoefficientModel`, and
`Sheaf.Paper.RefinementCoefficientMate`; the retained code does not reference declarations
from those modules.
Also removed unused private imports of `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`,
`Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`,
`Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`,
`Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`,
`Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel`,
`Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`,
`Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`,
`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`,
`Sheaf.CategoryTheory.RingedSliceExtensionTensor`,
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`,
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`,
`Sheaf.Paper.ProperOpenCoefficientMate`,
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`, and
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
The compatible-tower and interchange work is supplied by the existing scalar coherence
theorems. Dependencies needed by the retained main and sum plans remain logically needed;
removing their unused direct imports does not claim to prove or prune those plans.

## Where the brief, the DAG or earlier work was wrong

The previous report incorrectly described an abandoned split theorem. That split was
removed: this packet contains no new nodes or split statements. All existing definitions
and theorem signatures are unchanged. The existing node copy updates composition steps 8
and 9 and their dependency union to match the proved route. The composition boundary needs naturality with
respect to the bounded-below inclusion isomorphism; it is not a bare definitional equality.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
