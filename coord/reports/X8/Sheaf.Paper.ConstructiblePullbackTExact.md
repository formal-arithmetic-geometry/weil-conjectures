## What changed

Proved `WeilConjectures.constructible_pullback_t_exact` by extracting its finite and
common-stage witnesses from the existing stronger scalar-compatibility assertion.
Moved it after that prerequisite without changing its signature or docstring.

Proved `WeilConjectures.constructible_pullback_point_fibre` from the existing pullback
and point scalar packages. The natural cohomology isomorphism is the whiskered pullback
comparison composed with the point comparison, with functor associators inserted.
A proved private helper checks its component formula. Another helper uses both exact
heart-factorization equalities to identify the output as a standard module-category
heart object. Negative and positive homology vanishing then prove the degree-zero clause.
Moved this theorem after its prerequisites. All public statements and definitions are unchanged.
Three proved private helpers and a private shift-additivity theorem registered only as a local instance support the proof.
The command-only change record is
`coord/changes/X8-constructible-pullback-proof-elaboration.md`.
Updated the node's proof-origin note to record implementation of its existing Step 11.

Validation: the baseline compiled in 32.9 seconds. The implemented two-hole reduction
compiled in 45.3 seconds. Final import-pruned compile and delivery preflight are run below.
No source-library module, consumer, target statement or definition is modified.

## Proved and sorry left

Closed two of the four holes present in the item source at the start of this session:

- `WeilConjectures.constructible_pullback_t_exact`.
- `WeilConjectures.constructible_pullback_point_fibre`.

Two existing holes remain, both attached to `lem-a1-constructible-pullback-t-exact`:

- `WeilConjectures.constructible_pullback_scalar_compatibility`.
- `WeilConjectures.constructible_point_scalar_compatibility`.

Holes closed: 2. Holes added: 0. Split off: 0. The proved consequences still depend
on the existing scalar-package holes. This is a partial proof delivery, with no new
postponed statement and no sorry inside a private helper or definition.

## No longer needed

No module or node is withdrawn. The scalar packages retain their existing proof plans;
this delivery does not claim to prune their mathematical dependencies. The implemented
consequences require none of the following old private imports, which are removed:

- `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`.
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`.
- `Sheaf.Paper.SfImmersionCompletedPullbackComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `WeilConjectures.AlgebraicGeometry.SiteRestrictionExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`.
- `Sheaf.Paper.CompletedConstantSheafReduction`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `WeilConjectures.ConstructibleSheaf.Pullback`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.Paper.ConstantModuleSectionProperties`.
- `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`.
- `Sheaf.Paper.CompletedPullbackTriangles`.
- `Sheaf.CategoryTheory.SemilinearScalarLocalization`.
- `Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison`.
- `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`.
- `Sheaf.Paper.PointProEtaleSectionsExact`.
- `Sheaf.Paper.PointSectionsScalarExtension`.
- `Sheaf.Paper.LocalizedTStructure`.
- `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `Mathlib.Algebra.Module.LocalizedModule.Exact`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Paper.IntegralPullbackCompletedComparison`.
- `Sheaf.Paper.IntegralPullbackComposition`.

Public imports are preserved. Existing generic heart and homology APIs arrive through
those public imports. No additional proof dependency is needed for the two consequences.

## Where the brief, the DAG or earlier work was wrong

The item source has four holes, although the C8 report and reviewed-proof records say
the same two consequences were previously closed. This packet proves them against the
actual source supplied for this assignment and does not count the record as a proof.
The current node's Step 11 already describes exactly the witness-extraction route used here.

Two dependencies named by the current node have Lean attachments but no source file in
the current read-only tree: `Sheaf.Paper.IntegralStratumChartRestrictions` and
`Sheaf.Paper.PointRealizationStandardCohomology`. Their older compiled interfaces can be
inspected by lcompile probes, but they cannot be newly imported in a source-complete
delivery. `coord/returns/Q81.md` records that the point-realization landing was taken out
after a failed global build. This packet neither withdraws nor replaces either dependency.
The generic `CoefficientStageDescent` declaration exists, but requires the integral
exactness and bound-preservation input; it alone does not prove the scalar packages.

Searches: msearch LeanFinder for t-exact derived functors returned generic exact-derived
functor declarations; Loogle for `IsTExact` and msearch grep found no exact match.
Repository and Mathlib searches identified the stronger local scalar assertions,
functor associators/whiskering, and `DerivedCategory.isZero_of_isGE`/`isZero_of_isLE`.
Edge cases: the proof uses no nonemptiness or relative-flatness assumption, applies to
arbitrary point morphisms, and treats every negative and positive integer; the only
excluded index is the stated j=0. Coefficient-stage identity cases need no new choices.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
