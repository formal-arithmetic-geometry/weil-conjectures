## What changed

Proved both original holes in `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`.
Invertibility uses the existing proved canonical underived comparison and the existing
proved direct-image acyclicity result, followed by the generic derived base-change theorem.
The counit equation uses fully proved private categorical calculations following
`Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonCounit`: underived iterated mates,
right-derived uniqueness, the derived mate counit equation, and faithful comparison of
inverse natural isomorphisms. These private helpers introduce no obligations.
The source's helper is private, so it is reproduced locally rather than imported as
an unavailable public lemma. The exact named map and all original public signatures
and definition bodies are preserved. The two proof docstrings and the node's proof,
proof dependencies and proof origin now describe the proof actually checked by Lean.

Replaced the unused public import `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
with `Mathlib.Algebra.Category.ModuleCat.AB`, and added the proof-only import
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
Change record: `coord/changes/F2-fixed-comparison-mate-import-pruning.md`.

## Proved and sorry left

Closed 2 of 2 original holes:

- `AlgebraicGeometry.ProEtale.isIso_fixedComparisonDirectImageMatePlus`.
- `AlgebraicGeometry.ProEtale.fixedComparisonDirectImageMatePlus_counit`.

Both realize `lem-weil-pbc-comparison-direct-image-canonical-mate`.
Added holes: zero. Remaining holes in the delivered module: zero. No split-offs.
The axiom check of each public theorem reports exactly `propext`, `Classical.choice`,
and `Quot.sound`; neither theorem depends on `sorryAx`.
The retained proof compiled cleanly again in 5.6 seconds on 2026-10-19.
All four public signatures and both definition bodies were compared with current
sources and remain unchanged. The module has no `sorry` tokens or lines over 100 characters.
All eight retained direct consumer checks compiled against it, including the current proved
`ProperOpenComparisonSiteNormalization` (a stale retained copy was refreshed before checking).
Unchanged consumer copies were then removed from the delivery sandbox.

## No longer needed

Removed import: `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`. It is not used by
any statement or proof of this module; direct coefficient support comes from Mathlib.
The current audit finds 538 transitive consumers. Two use the wrapper's set-valued
adjunction and retain independent public import paths; none uses its other two declarations.
The updated change record lists all consumers and the alternate paths. The rerun of
`tools/downstream.py --uses` terminated with exit 137; the source-import audit used `rg`. The Etale coherence import is needed by the unchanged
`Etale.rightDerivedLowerStarPlus` signatures and remains.

The current source also has proof-dependency imports added since the earlier attempt.
The complete removed-import list at this recheck is:

- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`.
- `Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized`.
- `Sheaf.AlgebraicGeometry.DerivedCohomologyContinuity`.
- `Sheaf.AlgebraicGeometry.ProEtale.BasisDerivedDetection`.
- `Sheaf.AlgebraicGeometry.ProEtaleComparisonSections`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.
- `Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`.
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`.
- `Sheaf.RingTheory.IndEtaleStability`.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`.
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`.

The retained proof uses the proved underlying library APIs supplied by its public imports.

The following former proof dependencies are no longer needed as separate obligations
of this node: the existing library comparison/acyclicity APIs already perform the
geometric and resolution argument. This is pruning of this node's direct route;
other library results may still use these nodes internally, and statement dependencies
remain recorded unchanged.

- `def-pc-fibre-product` (`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`).
- `def-weil-pbc-direct-image` (`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`).
- `def-weil-pbc-ind-etale-algebra` (`Sheaf.RingTheory.IndEtaleUniverseTransport`).
- `def-weil-pbc-ind-etale-basis` (`WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`).
- `def-weil-pbc-proetale-operations` (`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`).
- `def-weil-sheaf-of-modules-category` (`Sheaf.CategoryTheory.RingedSiteModules`).
- `lem-pc-pre-derived-adjoint-functors-general` (`Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`).
- `lem-sp-grothendieck-enough-injectives` (Mathlib leaf).
- `lem-sp-right-adjoint-preserves-injectives` (`WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`).
- `lem-weil-pbc-affine-morphism-permanence` (Mathlib leaf).
- `lem-weil-pbc-affine-scheme-qcqs` (Mathlib leaf).
- `lem-weil-pbc-basis-derived-detection` (`Sheaf.AlgebraicGeometry.ProEtale.BasisDerivedDetection`).
- `lem-weil-pbc-comparison-global-cohomology` (`Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized`).
- `lem-weil-pbc-comparison-sections` (`Sheaf.AlgebraicGeometry.ProEtaleComparisonSections`).
- `lem-weil-pbc-derived-cohomology-continuity` (`Sheaf.AlgebraicGeometry.DerivedCohomologyContinuity`).
- `lem-weil-pbc-dplus-injective-representative` (Mathlib leaf).
- `lem-weil-pbc-etale-restriction-injectives` (`WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`).
- `lem-weil-pbc-filtered-colimit-abelian-groups-exact` (Mathlib leaf).
- `lem-weil-pbc-ind-etale-stability` (`Sheaf.RingTheory.IndEtaleStability`).
- `lem-weil-pbc-kinjective-hom-derived` (Mathlib leaf).
- `lem-weil-pbc-proetale-restriction-injectives` (`Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives`).
- `lem-weil-pbc-qcqs-morphism-permanence` (Mathlib leaf).
- `lem-weil-pbc-ring-modules-enough-injectives` (Mathlib leaf).
- `lem-weil-pbc-ring-sheaves-grothendieck` (`Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`).
- `lemma-weil-pbc-leray-acyclicity` (`WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`).
- `prop-weil-pbc-inverse-image-modules-exact` (`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`).
- `prop-weil-pbc-proetale-constant-exact` (`Sheaf.AlgebraicGeometry.ProEtaleConstantExact`).

Removed the obsolete top-level `tool_uses` approval for
`lem-pc-pre-derived-adjoint-functors-general`: no use of its fraction-formula theorem
remains. The categorical argument uses proved derived-mate and uniqueness APIs directly.
No blueprint unit statement or realized step is bypassed: this node is below the
proper-base-change unit's realized steps, and the existing comparison theorem supplies
the same named transformation.

## Where the brief, the DAG or earlier work was wrong

The DAG planned a fresh thirteen-step geometric continuity and injective-resolution
proof, but the current library already proves the requisite underived isomorphism
and direct-image acyclicity. Reusing them closes invertibility with no new statements.
The library's already proved ComparisonCounit module contains precisely the generic
normalization calculation, but its D+ intermediate theorem is private. The present
proof reuses its source calculation and explicitly checks the inverse orientation
of the pullback comparison used here. No statement was found false.

Earlier sessions encountered two temporary-worktree checkout timeouts before preflight
could read the completed item. This session retained the work and resumed with the
required dry run. No launcher script was changed or bypassed. The Lean file itself
compiles in 5.6 seconds; the earlier eight consumer checks also compiled.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
