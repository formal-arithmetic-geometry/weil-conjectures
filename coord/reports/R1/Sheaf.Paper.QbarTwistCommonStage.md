## What changed

Proved `WeilConjectures.qbar_twist_common_stage` in
`Sheaf.Paper.QbarTwistCommonStage`, preserving its complete signature and both integral
normalization definitions. Import the already proved upstream
`WeilConjectures.CategoryTheory.StageSystem.Functor` API. Bundle each sign as a coherent
stage-system morphism; descend the finite evaluation as a compatible transformation;
use invertibility and the generic composition/identity comparisons to construct both
natural isomorphisms. Their components simplify to exactly the required formula.

The original seven-step common-stage calculation is already implemented by the upstream
quotient descent. Updated the node proof to record this specialization. The unit's route
is retained: common-stage twists and both inverse evaluations are still constructed.
The proof is uniform in both signs, arbitrary schemes, independent coefficient universes,
repeated fields, negative twists and the zero twist. No statement or definition changed.

## Proved and sorry left

Closed 1 of 1 original holes: `WeilConjectures.qbar_twist_common_stage`
(node `lem-weil-qbar-twist-common-stage`). Added 0 holes and 0 split-offs.
No `sorry` remains in the delivered Lean module. Existing imported mathematical
obligations are unchanged; this delivery does not claim to close those dependencies.

Validation: the complete proof compiled through the required remote `lcompile.py`.
Final import-pruned compile and delivery preflight are recorded by the delivery tool.

## No longer needed

Removed the four direct proof imports `Sheaf.Paper.SfScalarExtensionComposition`,
`Sheaf.Paper.IntegralTwistBaseChange`, `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`,
and `Sheaf.Paper.SfRationalizationKaroubi`. The proof does not apply their theorems.
The statement and definitions continue to expose their existing coefficient constructions
through the retained public imports, so these removals do not establish that those modules
are globally unreachable.

Removed from this node's proof dependencies: `lem-weil-scalar-extension-composition`,
`lem-weil-integral-twist-derived-scalar`, `def-weil-rationalization-karoubi`,
`lem-weil-integral-twist-scalar-coherence`, `lem-weil-integral-twist-base-change`, and
`def-coefficient-twists-detailed`. Their relevant comparisons, tower equation and evaluation
compatibility are already supplied as hypotheses. Their statement dependencies stay
unchanged. Withdrew the obsolete scalar-extension-composition tool-use approval.
No entire module is withdrawn, and no global reachability pruning is claimed.

The proof also does not use `coefficientPairFunctor_exists` or any other holed descent
construction in `Sheaf.CategoryTheory.StageSystemFunctorDescent`; its public import stays
because the unchanged signature uses `pairFunctorCoherent`. The upstream generic descent
used here is proved directly on the actual StageSystem quotient, including descent of
natural transformations and the composition/identity comparisons.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG expanded a common-stage argument already proved
by the source library's `StageSystem.Morphism` API. The integral object/map/beta and
identity normalizations are stronger input than that generic descent requires; they
remain unchanged in the theorem. The tower and evaluation-compatibility hypotheses
suffice for the conclusion.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
