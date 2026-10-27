## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.SpTowerP1.exists_towerP1Adjunction`
by the stated comparison and triangle argument. The two normalized scalar contractions
are identities; their factorization gives the actual tower triangle identities.
The recorded natural transformations and these identities construct the adjunction,
including its specified unit and counit. Finite-level assembly is separated from this
construction, and the uniform restriction is transported through the realization
counits from `towerP1_uniform_ctf_domains`.

Moved the existing presentation, map, domain and adjunction-data declarations, with
their existing names and signatures, to `SmoothPurityTowerP1Data`. The item publicly
reexports this module. `TowerP1TensorOrdinaryCoordinates` now imports the data module
rather than the existence theorem. This removes the real import cycle which otherwise
prevents use of the already stated comparison lemmas. The other copied comparison
modules, including the refreshed upstream proof/data splits, are unchanged source, included solely for recompilation of that dependency
closure against the relocated data. The data module imports `RingedSiteDualityMaps` directly for its tensor model,
removing the unused perfect-duality theorem dependency. No adopted-source module
is changed.

Made the scheme morphisms explicit in `Presentation.exchange`: the former inferred
`pullback.fst _ _`/`pullback.snd _ _` elaboration was a measured 17.7-second hotspot.
This is the same definition after elaboration, not a change of its mathematical data.

## Proved and sorry left

The original module had one hole, in
`AlgebraicGeometry.ProEtale.SpTowerP1.exists_towerP1Adjunction`. Its body is now a
complete proof from the stated dependencies and the two new substeps below.
This is a decomposition of that hole, not a claim of net hole reduction.

The uniform restriction theorem
`AlgebraicGeometry.ProEtale.SpTowerP1.towerP1_uniform_in_presentation`
(node `lem-sp-tower-p1-uniform-presentation`) is proved. Its private helpers prove
isomorphism invariance of constructibility, Tor amplitude, the uniform predicate,
and the bounded-below etale-origin domain.

New holes, each exactly a named public theorem with source and proof in words:

- `AlgebraicGeometry.ProEtale.SpTowerP1.towerP1_projectionTrace_eq`
  (`lem-sp-tower-p1-projection-trace-identification`): identifies the actual
  projection/exchange trace with the normalized kernel splitting trace.
- `AlgebraicGeometry.ProEtale.SpTowerP1.towerP1_finite_adjunction_assembly`
  (`lem-sp-tower-p1-finite-adjunction-assembly`): assembles finite adjunctions and
  their precise evaluation equations from the actual tower triangles.

Validation: the complete 22-module dependency set compiled successfully through
`lcompile.py --all`, including the relocated data, all comparison modules, both new
substep statements, the fully proved uniform transport module and the main theorem.
No warnings were reported. The only main-proof errors on the earlier pass were two
generic `Functor.map_id` references; qualifying them as
`CategoryTheory.Functor.map_id` fixed both. Delivery preflight then caught a
concurrently proved `TowerP1ComparisonsWithLine` in the source repository; its
compilation copy was refreshed verbatim to preserve the landed proof.

A subsequent refreshed delivery compile hit the limit in the unchanged
`TowerP1CoefficientCoordinates`. Profiling identified kernel checking of the
large derived isomorphisms; local transparency and reducibility controls now
keep the same functors folded during elaboration, with all definitions and
signatures retained.

The item has zero remaining holes. The delivery closes one original hole and adds
two holes. The concurrently landed proof of
`towerP1EtaleOriginComparisonsWithLine` is preserved verbatim. The concurrently landed scalar-normalization, triangle-factorization and
single-level-triangle proofs and their new data modules are also preserved
verbatim. Remaining holes in their imported substeps and the uniform-domain
theorem are unchanged; none is duplicated or restated.

## No longer needed

No existing DAG dependency or mathematical module is withdrawn. The five original
planned dependencies are retained, directly or through the smaller assembly lemmas.
The unit route remains intact. The former import of the existence theorem in
`TowerP1TensorOrdinaryCoordinates` is replaced by its data-only dependency.

The following original proof imports are removed from the item and are not needed
by the relocated data statements. Some remain transitively required by the retained
comparison proofs, so this list does not claim their global withdrawal:

- `Sheaf.CategoryTheory.RingedSitePerfectDuality`
- `Sheaf.Paper.SmoothPurityTowerLevels`
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion`
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`
- `Sheaf.Paper.SemilinearDerivedSections`
- `Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.AlgebraicGeometry.ArbitraryBaseP1Integrals`
- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`
- `Sheaf.Paper.SmoothPurityTowerShriekLevels`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.Paper.SmoothPurityCoefficientTowers`
- `Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`
- `Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence`
- `Sheaf.AlgebraicGeometry.ComparisonTorInterval`
- `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`

## Where the brief, the DAG or earlier work was wrong

The stated proof dependencies imported the item through their ordinary tensor
coordinates. The item therefore could not import those dependencies before the
separation of data from its existence theorem. The change preserves all public
declaration names, signatures and mathematical meanings. The data-owner node now
points at the data module, and the theorem node records the proof actually used.

The existing full projective-line finite adjunction result assumes a Noetherian
base; the assigned theorem permits an arbitrary base with ell invertible. It cannot
replace the arbitrary-base scalar and singleton argument here.

## New nodes

`lem-sp-tower-p1-projection-trace-identification` records only identification of the
two trace constructions. It asserts no triangles or adjunction.

`lem-sp-tower-p1-finite-adjunction-assembly` records only the finite-level assembly,
conditional on both actual tower triangles. It asserts no tower adjunction or
constructible restriction.

`lem-sp-tower-p1-uniform-presentation` records the transport of the already stated
uniform-domain theorem to the presentation coordinates. It is proved in this delivery.

Change records: `coord/changes/F9-projective-line-proof-data.md` and
`coord/changes/F9-coefficient-coordinate-elaboration.md`.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
