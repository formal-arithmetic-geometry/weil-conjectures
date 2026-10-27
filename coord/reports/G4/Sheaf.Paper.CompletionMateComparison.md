## What changed

Filled three existing comparison-existence proofs in
`Sheaf.Paper.CompletionMateComparison`. Each uses the existing
`ConstantCompletion.resolving_square_iso` descent theorem on flat-term K-flat
complexes and `module_flat_kFlat_resolution` for uniqueness.

- Reduction/pullback descends `moduleReductionPullComplexIso`, using exact
  pullback factorizations and preservation of flat-term K-flat complexes.
- Finite evaluation descends `quotientEvaluationComplexIso`, then cancels the
  scalar-restriction factorization to obtain the prescribed normalization.
- Finite pullback descends `ordinaryFinitePull`, using the universal finite
  scalar-extension comparison and exact pullback factorizations.

These follow the existing docstring arguments and the DAG's representative and
localization steps. All existing public declaration signatures and imports remain unchanged. The
three normalizations now use abstract predicates whose unfoldings give their
original equations, including their original equality directions. Proved private
descent wrappers avoid repeated concrete tensor conversions. The existing
definition node records the three additional public predicates. See
`coord/changes/G4-abstract-reduction-comparison-normalization.md`.

The final item passed the server compile in 32.9 seconds without profiling.
The adapted completion-unit consumer passed in 47.7 seconds under profiling;
the finite-evaluation consumer passed in 24.9 seconds under profiling. All profiling
options are removed. Delivery preflight checks the complete packet again.

## Proved and sorry left

Closed three of the module's seven original holes:

- `CategoryTheory.AdicSites.Morphism.reductionPullIso_existsUnique`
- `CategoryTheory.AdicSites.Site.finiteEvaluationIso_existsUnique`
- `CategoryTheory.AdicSites.Morphism.finitePullIso_existsUnique`

No holes added or split off. Four existing holes remain untouched, all attached
by their docstrings to `lem-sp-completion-mate-comparison`:

- `CategoryTheory.AdicSites.moduleSquare_existsUnique`
- `CategoryTheory.AdicSites.Morphism.moduleReductionPullIso_existsUnique`
- `CategoryTheory.AdicSites.Morphism.finiteModuleRestrictionPullIso_existsUnique`
- `CategoryTheory.AdicSites.completionMateComparison`

The reduction proof uses the existing, still unproved ordinary
`moduleReductionPullIso_existsUnique`; this delivery closes the derived descent
step, not that ordinary comparison or the final mate theorem.

## No longer needed

None. The proofs use interfaces already imported by this module, follow its
existing route, and do not make any current dependency or public import obsolete.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The generic descent theorem already provides
the existence and uniqueness needed here; no new holed mathematical dependencies are
necessary.

## Forced adaptations

`Sheaf.Paper.CompletionUnitFiniteProjection` is unclaimed. Its original source,
compiled against the changed item, failed at line 235: rewriting
`quotientEvaluationComplexIso_hom_id` found no component inside the new
`evaluationSquareFormula`-headed hypothesis. Added only
`dsimp only [evaluationSquareFormula] at he` before that rewrite. All existing
signatures and imports remain identical. This consumer has zero sorry bodies.

`Sheaf.Paper.ReductionPullFiniteEvaluation` is also unclaimed. The original
source typechecks against the new item but exceeded the time limit (78.6 s;
60.4 s under profiling, with 24.1 s in the concrete model specialization).
Added the proved private `finite_model_abstract_normalized` adapter and changed
that specialization's call to it. Its four normalization hypotheses unfold to
exactly the existing equations, but are compared as abstract predicates before
specialization. The private `finiteCubeFormula` likewise retains the shape of the
ordinary complex and derived cube equations through specialization and transport;
the private complex, model and transport lemmas have definitionally identical result types. A proved private finishing lemma
performs the final isomorphism cancellation with abstract functors. The existing private complex-square abbreviations stay unchanged; redundant local
instances of the global `reductionTower_additive` instance are removed. Public
signatures, visibility and imports remain unchanged.
This consumer has zero sorry bodies.

The first delivery check rejected this consumer for exceeding 60 seconds. The
additional private abstraction addresses that conversion cost; the consumer now passes in 24.9 seconds under profiling. Delivery preflight checks
the final packet without profiling.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
