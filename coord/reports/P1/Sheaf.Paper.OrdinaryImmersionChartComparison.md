## What changed

Reduced `WeilConjectures.OrdinaryImmersionChart.ordinaryImmersionChartComparison`
to ordinary left exactness and the normalized underived chart square. The main
proof constructs the module direct-image composition comparison from
`completedRingMap_comp`, checks its section map, and takes its adjunction mate.
Exact functor descent constructs the five universal ordinary derived pullbacks.
The exact-derived square comparison and its factorization equations prove both
normalization formulas; whiskering and reassociation give the final comparison.

`OrdinaryImmersionChartModels` extracts the twenty existing model declarations
with definitionally equal types and values. The item publicly re-exports them. This
breaks the dependency cycle between the model vocabulary and the two lower
statements. `Rings`, `pull` and `adj` are irreducible to prevent elaboration from expanding
the free-presentation chosen adjunction; the original pullback and adjunction values are preserved. `Rings` is written
as the existing completed ring sheaf, definitionally equal to the previous
forgetful image of the completed commutative ring sheaf.
See `coord/changes/ordinary-immersion-chart-model-interface.md`.

`OrdinaryCompletedChartComparison` also proves `restrictExact` from the continuous
and cocontinuous Over.map functor and the existing module-forgetting API.
Finite-colimit preservation of `pull` follows directly from `adj`, so it is not
included in a remaining hole. All changes are under Sheaf; no source-library file
or target signature is changed.

## Proved and sorry left

All four modules compile with the project compiler. The main assembly compiled
cleanly in 27.3 seconds. Its section calculation uses a sectionwise pushforward
comparison for equal scheme maps, avoiding the kernel-expensive transport of an
entire module functor.

Closed the original one hole:
`WeilConjectures.OrdinaryImmersionChart.ordinaryImmersionChartComparison`
(node `lem-tw-ordinary-immersion-chart-comparison`). The item has zero remaining
holes. This is a decomposition, not a net hole reduction.

Added two strictly lower, underived holes, one theorem per module:

- `WeilConjectures.OrdinaryImmersionChart.ordinaryCompletedPullbackExact`
  (`lem-tw-ordinary-completed-pullback-exact`): only finite-limit preservation of
  the specified pullback. Finite colimits are proved from the adjunction.
- `WeilConjectures.OrdinaryImmersionChart.ordinaryCompletedChartComparison`
  (`lem-tw-ordinary-completed-chart-comparison`): only the ordinary chart direct
  comparison, section formula, pullback comparison and adjunction mate. Exactness
  of chart restriction and every derived assertion are proved in this delivery.

Both bodies are exactly `by sorry`, with source and full proof in words. The new
Models module has zero holes and no arbitrary choice from a mere existence result.
The theorem assembles the normalized comparisons within a proposition; it does
not define public data by choosing a witness of the new existence theorem.

Edge cases checked mathematically: identity morphisms, empty schemes and charts,
zero coefficient sections/modules, and unbounded complexes. Exact pullback needs
no immersion or geometric finiteness hypothesis. For independent coefficient
universes the finite coefficient sets can be shrunk before forming representing
schemes, then lifted in the sheaf-value universe. Neither lower statement repeats
the derived conclusion of the item.

## No longer needed

Removed these proof-only imports from the item (some remain available transitively
through statement imports; no claim of whole-library removal is made):

- `Sheaf.Paper.SfImmersionCompletedPullbackComparison`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable`
- `Sheaf.Paper.SheafSliceDerivedComparison`
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`

The main proof no longer calls the separate derived composition, completed
immersion comparison, K-flat resolution existence, immersion base-change,
representable algebraic pullback, or arbitrary-sheaf-slice derived comparison
arguments. In particular its old direct proof dependencies
`lem-weil-pbc-proetale-derived-pullback-composition`,
`lem-weil-pbc-immersion-base-change-lft`,
`lem-sf-immersion-completed-pullback-comparison`,
`lem-weil-pbc-ringed-topoi-derived-pullback`,
`def-weil-pbc-proetale-operations`, `lem-pc-kflat-resolution`,
`lem-weil-pbc-proetale-subcanonical`,
`lem-pur-site-representable-algebraic-pullback`,
`lem-weil-pbc-localized-sheaves-over-representable`,
`lem-sbc-ringed-topos-sheaf-slice-derived-comparison`, and
`lem-tw-representable-slice-localized-ringed-morphism` are not used by the new
assembly. The existing statement dependencies and publicly exported model
vocabulary are preserved. Finite-quotient and profinite inverse-image facts remain
needed by the new ordinary exactness lemma; coefficient coherence remains needed
by both the main proof and the chart lemma. These are not declared pruned from
the entire target closure. No module is withdrawn, and no adopted source-library
declaration is removed.

The unit `sk-r-real-linear` has no realized statement or proof-step attachment
requiring the old lower route. Its elementary weight-operation argument is
preserved. The node's obsolete tool_uses entries are removed along with the old
proof steps; no new maintainer approval is manufactured.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. Several planned interfaces use scheme universe u
and coefficient universe u+1, whereas the item's existing signature allows an
independent coefficient universe. They cannot simply be applied to its actual
pullback. The exactness lemma isolates that genuine universe transport, including
identification with the projection-defined coefficient map. The other remaining
transport is from abstract over-site module localization to the represented
scheme charts with the fixed chartRingIso; a bare topos isomorphism would not
prove the required scalar and mate equations.

The main theorem can use the exact special case of derived descent. It therefore
needs no separate identification between two K-flat constructions of the derived
pullback. The coefficient and ordinary section comparisons still fix the maps.

## New nodes

`def-tw-ordinary-immersion-chart-models` attaches the extracted existing model
vocabulary, with zero holes; this is an extraction, not a replacement definition.

`lem-tw-ordinary-completed-pullback-exact` is finite-limit preservation of the
ordinary pullback, with its geometric/profinite argument and independent universe
transport stated explicitly.

`lem-tw-ordinary-completed-chart-comparison` is the ordinary represented chart
localization and its specified unit/direct-comparison/counit normalization. The
remaining result contains no derived construction.

Change record: `coord/changes/ordinary-immersion-chart-model-interface.md`.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
