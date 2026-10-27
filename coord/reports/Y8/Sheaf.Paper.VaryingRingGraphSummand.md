## What changed

Partial proof delivery in `Sheaf.Paper.VaryingRingGraphSummand`. All existing public
signatures, definitions and public imports remain unchanged. Proved continuity by
vertical-slice gluing, coefficient naturality by the sheafification adjunction,
existence of the sum adjoint by the existing universe-independent module pullback
theorem, clopenness of graphs by the etale section factorization and separated
projection, and the two derived descent statements by full faithfulness of
precomposition with the localization. Two proved private helpers carry sheaf gluing
and coefficient naturality. The node records this implemented part of the route.

## Proved and sorry left

Closed 7 of the original 20 holes; added 0 holes and split off 0 statements.
All names below have prefix `AlgebraicGeometry.ProEtale.VaryingRingGraph.`.

Proved:

- `sumSite_continuous`
- `coefficientMap_naturality`
- `sumRestriction_isRightAdjoint`
- `graph_clopen`
- `theta_existsUnique`
- `levelSite_continuous`
- `levelTheta_existsUnique`

Remaining original holes, all attached to node
`lem-sp-varying-ring-graph-summand` with their existing source/proof docstrings:

- `sum_exact`
- `restrictionPushAdjunction_existsUnique`
- `graphMap_existsUnique`
- `levelPull_isRightAdjoint`
- `levelSum_exact`
- `levelRestrictionAdjunction_existsUnique`
- `levelGraphMap_existsUnique`
- `sumEvaluationInv_isIso`
- `openEvaluationInv_isIso`
- `pushEvaluation_isIso`
- `varyingRingGraphSummand`
- `siteSumInv_isIso`
- `finite_normalization`

The adjoint existence proof uses the already proved
`SheafOfModules.module_pushforward_isRightAdjoint_of_universes`.
The new proofs introduce no additional unproved dependency. The retained graph,
exactness, normalization and comparison holes remain future work.

## No longer needed

Removed unused private proof imports:

- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`

Their public declarations are preserved in their own modules. No module is
withdrawn: the remaining graph and comparison holes still need the node's original
proof dependencies. No unit-route step is pruned. Replaced the localization proof
import by the narrower `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`
for the composition-continuity instance. Added private imports of the existing
formally-unramified section lemma and universe-independent module pullback theorem.

## Where the brief, the DAG or earlier work was wrong

Rephrased the existing graph-map docstring from “sheaf axiom” to “sheaf condition”
to avoid a lexical false positive in the delivery gate. No statement error found. The existing proof plan's intermediate graph constructions
use different normalized adjunction coordinates from this module; transporting them
requires additional work beyond this partial delivery. For continuity, coefficient
naturality, graph clopenness and unique derived descent, the direct existing APIs
suffice. Empty schemes and empty sources are included by the same categorical proofs.
The coefficient naturality argument uses no flatness assumption on the transitions.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
