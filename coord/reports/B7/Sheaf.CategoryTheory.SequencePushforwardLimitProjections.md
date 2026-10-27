## What changed

Proved `SheafOfModules.SequenceProjection.pushforwardLimitProjections` in
`Sheaf.CategoryTheory.SequencePushforwardLimitProjections`, with its original statement
factored through a definitionally equal predicate.
The ordinary compatible-family universal property identifies the right adjoint with
inverse limit after the actual scalar-restriction tower. Acyclicity on restricted
K-injective resolutions and uniqueness of right derived functors give the comparison.
Universal descent derives the limit projections. Normalized scalar adjunctions and
absolute resolving comparisons supply the level derived adjunctions; right-derived
uniqueness proves the counit projection, from which the unit projection follows.
The inverse-adjunct and triangle formulas are formal consequences of the transported
adjunction. All proof helpers are private and completely proved. The public predicate
`derivedLimitProperties` is exactly the original derived normalization conjunction,
including its scalar clause in its original position. The derived assembly is proved for
abstract abelian categories before specializing it, so the proof does not repeatedly
unfold the concrete sheaf and strict-system category structures.

Updated the item's DAG proof and proof dependencies to describe that argument.
All added imports are private proof imports. No public signatures, definitions,
attributes or imports of the source library were changed. No other item was adapted.

## Proved and sorry left

Closed the one original hole in
`SheafOfModules.SequenceProjection.pushforwardLimitProjections`
(node `lem-coef-sequence-pushforward-limit-projections`).
The item has zero remaining `sorry`; zero holes were added and zero were split off.
The proof uses `restrictionFunctor_exact` and `acyclicity` of
`Sheaf.CategoryTheory.RestrictedTowerResolutionAcyclicity` as declared dependencies
of node `lem-coef-restricted-tower-resolution-acyclicity`. That dependency is not
modified by this delivery; its existing theorem holes remain assigned to their item.

## No longer needed

The direct use of `lem-coef-sequence-adjunction-cochain-transposes` and its module
`Sheaf.CategoryTheory.SequenceAdjunctionCochainTransposes` is unnecessary: the
normalized ordinary and derived Hom equivalences already supplied by the sequence
adjunction prove the level counit identity by universal right-derived uniqueness.
No additional K-injective resolution theorem is called directly: the total-limit
pair supplies its resolutions, and the existing Grothendieck/K-injective derivability
criterion establishes universality. Thus `prop-pur-kinjective-resolutions-exist` is
not a direct proof dependency; it remains needed within the used library results.

Removed unused proof imports:
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
`Sheaf.CategoryTheory.DerivedCategory.ResolvingAdjunction`,
`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`, and
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
Their interfaces are not called; the argument uses scalar models, resolving
comparisons and the total-limit pair instead.

No whole module is withdrawn. The composition node remains used for its generic
K-injective derivability criterion, rather than its ringed-topos composition theorem.
The K-flat resolution node remains needed to preserve the universal left-derived
property under exact level evaluation.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. Repeated elaboration of the expanded
normalization conjunction exceeded the compile limit; the public predicate records
that conjunction once over abstract categories. This changes no hypotheses, witnesses
or equations. See `coord/changes/sequence-pushforward-limit-properties.md`. The planned cochain calculations can be
replaced by normalized Hom equivalences and universal uniqueness, which work on all
complexes without requiring a level object or scalar restriction to be K-injective.
The actual complex comparison is retained explicitly to avoid unfolding the chosen
limit cone during elaboration. The latest blueprint unit was read; its recorded
`realized.statement` and `realized.steps` are empty, and its route is preserved.

The item compiled cleanly in 37.2 seconds; the combined consumer check compiled it
in 41.7 seconds. A separate probe imported that compiled result and proved the exact
original expanded statement by `exact pushforwardLimitProjections A B α` (17.7 seconds).
The active consumer `CoefficientSequenceSectionsLimit` compiled unchanged in 44.2
seconds. Five other direct importers compiled unchanged. The remaining importer,
`EnrichedSequenceProjectionFormula`, reached the 60-second limit against both the
changed module and the unchanged library baseline. No importer source is adapted or delivered.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
