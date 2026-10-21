## What changed

Proved `AlgebraicGeometry.ProEtale.projection_section_normalization` directly in the
internal-module derived categories. Private lemmas identify the canonical identity
comparison, prove its unit coherence, combine the two projection mates, and reverse
the resulting identity under the two given invertibility assumptions. The target
signature and all existing mathematical constructions are preserved.

Repaired inference and repeated checking of canonical structure data in the five
delivered modules. Each declaration locally disables `CategoryTheory.catToReflQuiver`.
Each module also locally selects the seven canonical structure aliases already
provided by `Sheaf.Paper.IntegralResidueDerivedMonoidal`: `projectionDerivedMonoidal`,
`projectionModuleAbelian`, `projectionModuleMonoidal`, `projectionModuleHasDerived`,
`projectionSheafMonoidal`, `projectionCoefficientMonObj`, and `projectionModuleCategory`.
These aliases contain the existing inferred data; the construction text of all
nine public definitions remains verbatim. The derived-functor aliases remain
abbreviations. No global instances are added. `ModuleProjectionSectionArrows` adds
a public import of the existing cache module because its public types use these
names; the other four modules receive it through their existing public imports.
All four support modules were unclaimed when adapted, and no module held by another
group was edited. No source-library declaration is changed.

Updated the item's DAG proof, proof dependencies and proof origin to follow the
direct calculation. No new nodes or public mathematical declarations were added.
The inference-repair change records are:

- `coord/changes/projection-section-quiver-backward.md`
- `coord/changes/projection-section-quiver-forward.md`
- `coord/changes/projection-section-quiver-normalized.md`
- `coord/changes/projection-section-quiver-projection.md`
- `coord/changes/projection-section-quiver-pullback-section.md`
- `coord/changes/projection-section-quiver-pullback.md`
- `coord/changes/projection-section-quiver-pushforward-section.md`
- `coord/changes/projection-section-quiver-pushforward.md`
- `coord/changes/projection-section-quiver-section-arrow.md`

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.projection_section_normalization` (1 of 1).
Added zero holes; no `sorry` remains in the delivery. No statements are split off.
All adapted definitions have zero holes before and after. The final clean five-file
compile passed without errors or warnings: arrows 19.0 s, section arrow 2.2 s,
forward composite 2.0 s, inverse composite 2.0 s, normalization 28.8 s. Development
profiling and all diagnostic source modules have been removed from the delivery.
The submission checks are recorded by the delivery tool.

## No longer needed

The direct adjunction argument removes these original proof imports:
`Sheaf.Paper.RingedProjectionTensorComposition`,
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.Paper.CondensedModuleDerivedPushpull`,
`Sheaf.Paper.ModuleRingedToposDerivedComparison`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`.
The last two are already provided by retained public imports.

Removed proof dependencies
`lem-pd-module-ringed-topos-derived-comparison`,
`lem-sfb-ringed-projection-tensor-composition`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: the calculation uses the
canonical internal-module adjunction and unit coherence directly. Removed the
three obsolete top-level ringed-topos `tool_uses` entries under
coord/brief-stage3.md §6; the historical split report is preserved. No source-library
declaration or module is withdrawn. Statement dependencies remain unchanged.

The following 27 source modules leave this item's import closure:

- `Sheaf.Algebra.Homology.KFlatModuleObject`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleObjects`
- `Sheaf.CategoryTheory.AdjunctionSquareExchange`
- `Sheaf.CategoryTheory.DerivedCategory.KFlatDerivability`
- `Sheaf.CategoryTheory.InternalSectionModuleFlat`
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`
- `Sheaf.Paper.InverseImageModuleFlat`
- `Sheaf.Paper.ModuleRingedToposDerivedComparison`
- `Sheaf.Paper.ProEtaleSectionModuleFunctors`
- `Sheaf.Paper.RingedProjectionCanonicalNormalization`
- `Sheaf.Paper.RingedProjectionCoherenceData`
- `Sheaf.Paper.RingedProjectionPullbackComparisons`
- `Sheaf.Paper.RingedProjectionSectionSpecialization`
- `Sheaf.Paper.RingedProjectionTensorAssociativity`
- `Sheaf.Paper.RingedProjectionTensorCompatibility`
- `Sheaf.Paper.RingedProjectionTensorComposition`
- `Sheaf.Paper.RingedProjectionTensorStructure`
- `Sheaf.Paper.SectionDerivedRealization`
- `Sheaf.Paper.SectionDerivedTensorData`
- `Sheaf.Paper.SectionModuleAlgebraicInverseImage`
- `Sheaf.Paper.SectionModuleOperationsData`
- `Sheaf.Topology.ProfiniteCondensedRing`
- `WeilConjectures.CategoryTheory.Adjunction.ExchangeMate`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs`

## Where the brief, the DAG or earlier work was wrong

The planned transport through ringed topoi is unnecessary. Tensor compatibility
only at `(M, unit)` suffices, and follows from canonical unit coherence and
naturality with the right unitor. All geometric and constructibility hypotheses
remain verbatim, although the formal equality does not use them.

Profiling found two causes of the compile bottleneck. A meta-level comparison
identified `CategoryStruct.toQuiver` on identities and `ReflQuiver.toQuiver` in
morphism annotations; the scoped instance repair removes this diamond. That repair
alone was insufficient: the kernel repeatedly checked the large canonical
internal-module instances. Selecting the existing named structures consistently
in the five public interfaces fixes that second cost. The support composites fell
to about 3 seconds each, and the entire normalization proof compiled in 41.1 seconds.
This preserves the actual categories, localization model, tensors, functors and
all canonical comparison maps; it changes their inferred names, not their data.
The imports and local instance selection follow the existing source-library use
of the same cache in `WeilConjectures.PoincareDuality.ProjectionFormula`.

Searches before choosing the route: LeanFinder for a monoidal projection composite
with a section (8 unrelated hits), Loogle for
`CategoryTheory.Monoidal.Adjunction` (no match), and grep for
`projection.*comp|projection.*section` (25 unrelated Mathlib hits). Repository
search found the proved composition and conjugation equations in
`WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat` and the unit
coherence in `ModuleObject.Derived.UpperStarUnitCoherence`.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
