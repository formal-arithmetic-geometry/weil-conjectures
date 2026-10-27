## What changed

Proved `AlgebraicGeometry.ProEtale.geoP1Cohomology` from the existing ordinary étale
projective-line decomposition, normalized trace data, and bounded-below comparison.
All existing declaration signatures are preserved. Three projective-line maps now
supply explicit definitionally equal arguments. The ordinary finite-line abbreviation
and signed-twist object use a common degree-zero wrapper, and two dependency interfaces supply explicit
projective-line endpoints to avoid repeated kernel conversion. Added proved private
helpers for comparison naturality, exchange restriction, biproduct transport and trace
projection. Updated the main node's proof route and removed unused proof imports. The Kummer
module directly reexports its coefficient interface, already transitively public in
the current source; this also supports the older published scalar-comparison umbrella.

## Proved and sorry left

Closed one existing hole: `AlgebraicGeometry.ProEtale.geoP1Cohomology`
(`sk-lem-geo-p1-cohomology`). Added zero holes and split off zero statements.
No `sorry` remains in this module or the four adapted dependency modules. Imported
theorems retain their own existing obligations.

All five final modules compiled cleanly in the ordered packet check
`final-wrapper-compile.log`, with zero errors or warnings. Earlier consumer checks passed 34 modules, while four
stopped at the compile limit and the remaining checks were not reached. Those
consumer timeouts are unresolved performance concerns and are not claimed as passes.

## No longer needed

The geometry, stalk, genus, cohomology, Kummer and scalar-extension calculations are
already packaged in the ordinary étale theorem. They are not reproved in this module.
The following old direct proof dependencies are no longer used directly; their own
uses elsewhere in the library remain authoritative:

- `def-weil-proper-morphism`
- `def-weil-finite-type-morphism`
- `lem-pc-separated-quasi-separated`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-asd-etale-finite-twist-pullback`
- `def-nagata-affine-proj`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `def-pc-divisor-line-bundle`
- `def-pc-projective-space-twist`
- `def-asd-ordinary-finite-p1-kummer-class`
- `def-kun-unbounded-exchange`
- `lem-amb-kummer-any-base`
- `lem-sc-line-bundle-torsor`
- `lem-amb-relative-torsor-cohomology`
- `cor-weil-pbc-geometric-fiber-finite`
- `lem-weil-pbc-derived-stalk-conservative`
- `lem-asd-projective-line-genus-zero`
- `lem-sc-primitive-root`
- `thm-sc-proper-cohomology`
- `lem-sc-constant-proper-degree-coordinates`
- `lem-pc-degree-agrees-sc`
- `lem-pur-derived-change-of-rings`
- `lem-pur-etale-scalar-mate-projection`
- `lem-amb-proper-coproducts-projection`
- `lem-weil-pbc-ringed-exchange-tensor-coherence`
- `lem-sf-comparison-pullback-exact`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `sk-prop-sf-comparison`
- `sk-thm-pe-direct-image-comparison`
- `sk-lem-geo-cartier`
- `lem-weil-pbc-coefficient-exchange-mates`
- `sk-def-sfb-finite-derived-functors`

Removed proof-only imports (all original public imports retained):

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`
- `Sheaf.Paper.RingedTopoiDerivedTensorPullback`
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer`
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`
- `WeilConjectures.AlgebraicGeometry.Sites.GmPicard`
- `Sheaf.AlgebraicGeometry.RelativeTorsorCohomology`
- `Sheaf.CategoryTheory.Sites.TorsorWithSection`
- `Mathlib.Algebra.Homology.Embedding.ExtendHomology`
- `Mathlib.Algebra.Homology.HomologySequence`
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`
- `Sheaf.AlgebraicGeometry.GeometricFiberFinite`
- `Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative`
- `Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero`
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`
- `WeilConjectures.AlgebraicGeometry.Curve.Estimate`
- `Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates`
- `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Paper.PurEtaleScalarMateProjection`
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`
- `Mathlib.Topology.Defs.Filter`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`
- `Sheaf.CategoryTheory.Adjunction.CoefficientExchange`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek`

Removed obsolete tool approvals from the old duplicated calculation: `lem-asd-etale-finite-twist-pullback`, `lem-weil-pbc-fibre-product-affine-spectra`, `lem-amb-kummer-any-base`, `lem-sc-line-bundle-torsor`, `lem-amb-relative-torsor-cohomology`, `cor-weil-pbc-geometric-fiber-finite`, `lem-weil-pbc-derived-stalk-conservative`, `lem-asd-projective-line-genus-zero`, `lem-pc-degree-agrees-sc`, `lem-amb-proper-coproducts-projection`, `lem-pur-derived-change-of-rings`, `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, `lem-weil-pbc-ringed-exchange-tensor-coherence`, `lem-sf-comparison-pullback-exact`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `sk-prop-sf-comparison`, `sk-thm-pe-direct-image-comparison`, `thm-sc-proper-cohomology`, `lem-sc-constant-proper-degree-coordinates`, `lem-sc-primitive-root`, `lem-pur-etale-scalar-mate-projection`, `lem-weil-pbc-coefficient-exchange-mates`.

No module is withdrawn. No source-library declaration is removed or altered.

## Where the brief, the DAG or earlier work was wrong

The previous plan repeated the ordinary étale calculation even though its existing
normalized decomposition and trace results already supply that part of the argument.
The existing comparison/exchange theorem and its exact D+ restriction are used as tools;
no statement of this unit packages those categorical normalization equations.
The comparison and exchange coherence still require explicit transport between D+,
the exact derived inverse image, and the left-derived inverse image. The public maps
and the unit's mathematical route are preserved.

Performance repairs and consumer inventories are recorded in:

- `coord/changes/u8-geop1cohomology-explicit-endpoints.md`
- `coord/changes/u8-ordinaryfinitep1data-explicit-endpoints.md`
- `coord/changes/u8-ordinaryfinitep1decomposition-explicit-endpoints.md`
- `coord/changes/u8-ordinaryfiniteline-signed-encoding.md`
- `coord/changes/u8-p1twist-degreezero-interface.md`

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer corrections (2026-10-24)

- `OrdinaryFiniteP1Kummer`: `ordinaryFiniteDegreeZero` is a plain `def`, so the
  Mathlib `IsGE`/`IsLE` instances for `(singleFunctor _ 0).obj F` were no longer
  found through `ordinaryFiniteLine`. Three consumers failed (`SpP1NormalizedFamilyCore`,
  `BaseChangedLineTraceEvaluation`, `ProEtaleProjectiveLineTrace`). Added public
  instances `ordinaryFiniteDegreeZero_isGE` and `ordinaryFiniteDegreeZero_isLE`. With
  them all 100 modules that mention a changed name or import a changed module compile.
- `GeoP1Cohomology`: removed the private copy `degreeZero_isGE`. Removed the unused
  imports `Mathlib.AlgebraicGeometry.Noetherian` and
  `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`. Changed
  `import all Sheaf.Paper.SpDirectImageEtaleMate` to a plain `import`.
- `OrdinaryFiniteP1DecompositionMaps`: restored the original file-level
  `backward.isDefEq.respectTransparency true`. The flip to `false` is not needed once
  the instances exist.
- Node `thm-amb-p1-decomposition`: `lean.statement` is now the delivered signature
  verbatim. Node `def-asd-ordinary-finite-p1-kummer-class` lists the two instances.
