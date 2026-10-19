## What changed

Completed `AlgebraicGeometry.Etale.isIso_finiteCompactProjection` using the source library's
finite proper projection formula and its canonical etale-to-pro-etale transport theorem.
The witness helper constructs the required isomorphism using the coefficient-realization
equivalence unit and the retained witness alpha. The pro-etale helper checks boundedness
and Tor amplitude before applying transport. Existing public imports and signatures stay
identical. Proof-only imports are pruned below.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.isIso_finiteCompactProjection` (node
`lem-weil-finite-compact-projection-formula`), the module's only original hole.
Added: zero holes. Remaining: zero holes. The two private theorem helpers are proved;
the private witness-isomorphism definition is a construction without holes.
This uses existing declared theorems, whose own dependencies remain separate obligations.

## No longer needed

The previous explicit stalk devissage is replaced by the already stated finite proper
projection theorem. The explicit site-comparison calculation is replaced by the source
library's theorem for the actual canonical projection map. Removed direct proof imports:

- `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel` (trial proof import)
- `Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`
- `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`
- `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`
- `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`
- `Sheaf.AlgebraicGeometry.OpenComparisonTensorNormalization`
- `Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection`
- `Sheaf.AlgebraicGeometry.StalkFaithfulDerived`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Sheaf.EtaleCohomology.SepClosedFieldVanishing`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.Paper.EtaleKFlatCriteria`
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`
- `Sheaf.Paper.FiniteCoefficientFlatModel`
- `Sheaf.Paper.GeometricStalkPerfect`
- `Sheaf.Paper.PbcActualScalarPullback`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.Compactification.Noetherian`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`

These removals concern this proof's direct imports; public dependencies remain available
and some of the listed modules can still occur transitively elsewhere.

Direct DAG dependencies no longer needed by this proof (their results may still be
used transitively by the source theorems):

- `pqf-def-locnoeth`
- `def-weil-finite-type-morphism`
- `def-weil-proper-morphism`
- `sk-thm-nagata-sketch-noetherian`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `pqf-lem-qs-intersection-qc`
- `lem-amb-etale-compact-comparisons`
- `def-amb-etale-compact-support`
- `lem-sf-flat-model`
- `lem-kun-kflat-criteria`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `def-weil-pbc-direct-image`
- `lem-weil-pbc-extension-by-zero-adjunction`
- `lem-weil-pbc-extension-by-zero-stalks`
- `lem-pod-etale-stalk-tensor-scalar`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `lem-kun-stalk-as-pullback`
- `lem-kun-0ezp`
- `lem-kun-inverse-image-monoidal`
- `thm-cbc-finite-torsion`
- `def-cbc-exchange-map`
- `lem-weil-pbc-ringed-exchange-tensor-coherence`
- `lem-cbc-extension-zero-base-change`
- `cor-cbc-derived-extension-zero-base-change`
- `fix-lem-finite-tor-perfect`
- `lem-weil-pbc-ringed-projection-mate-exact`
- `lem-weil-pbc-degreewise-split-derived-triangle`
- `lem-sf-triangle-morphism-iso`
- `lem-kun-stalk-faithful-derived`
- `lem-sf-comparison-pullback-exact`
- `lem-weil-pbc-comparison-pullback`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-pc-separated-quasi-separated`
- `lem-sf-class-compact-support-comparison`
- `lem-sf-open-comparison-unit-normalization`
- `lem-sf-open-comparison-tensor-normalization`
- `lem-sf-open-tensor-normalization`
- `lem-cbc-proetale-extension-zero`

The obsolete tool-use approvals for the unused dependencies listed here are removed,
including `lem-sf-flat-model`; the four approvals still used by this proof are retained.

Further obsolete dependencies and tool-use approvals removed:

- `lem-weil-extension-by-zero-adjunction`

## Where the brief, the DAG or earlier work was wrong

Validation after resumption: the final module compiled without warnings in 8.6 seconds.
A diagnostic comparison found that the concrete quotient's direct Ring instance and the
Ring obtained from its CommRing instance caused the generic-helper application to unfold
large derived tensor constructions. A local priority on CommRing.toRing makes the two
specialized types syntactically identical; a local priority on isNoetherian_of_finite
avoids searching through the quotient's coefficient presentation. Both attributes are
local. The public declarations and public import list remain unchanged. The preflight
conservatively classifies attribute commands as an interface change, so its required record
is coord/changes/finite-compact-projection-local-instances.md. No definition or statement
repair and no consumer adaptation is needed. The main proof passes the
coefficient ring directly to its generic helpers.

The earlier sandbox had a syntax error in the boundedness application and attempted a
Tor-amplitude conversion by elaborating two equivalent tensor predicates inline.
The source library supplies both the finite proper projection formula and a canonical
comparison theorem, so rebuilding geometric stalk devissage in this module is unnecessary.
The theorem statement is unchanged, and no Tor-amplitude assumption is added on K.

The preflight requires the unit-route import
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`; it is retained.

The requested downstream.py scan waited in the shared delivery cache and was interrupted
without a result. A source search of both library roots finds no user of
isIso_finiteCompactProjection except its own declaration. Seven modules import the item;
no adaptation is needed because all new attributes are local and the public signature
and public import list are unchanged.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
