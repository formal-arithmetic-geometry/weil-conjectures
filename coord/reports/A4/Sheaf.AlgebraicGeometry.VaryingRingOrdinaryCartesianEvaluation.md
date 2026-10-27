## What changed

Replaced the sorry in ordinaryCartesianEvaluation by the full cartesian mate calculation.
The original theorem signature and its sole public import are unchanged. Added private
proof imports of VaryingRingOrdinaryComparisonNormalization and the new
VaryingRingOrdinaryOpenUnit, plus the adopted-source Mathlib adjunction-mates API.
No other existing Lean module is changed. Existing declaration docstrings, attributes,
and public imports are retained.

The proof first establishes the square calculation for pullback comparison families
satisfying the existing OrdinaryPullComposition predicate, then instantiates this
with ordinaryComparisonNormalization. It uses the original predicate directly, avoiding
a costly definitionally equivalent repackaging. The calculation uses component morphisms. Equality elimination handles the commutative-square transport.
The explicit squareG hom formulas and inverse-isomorphism cancellation then give the inverse
square equation. Both inverse
beta transformations have the required mates directly by their defining Hom transposes.
Mathlib mateEquiv_vcomp and whiskering naturality identify the pasted inverse-beta
comparisons. Finally inverse-isomorphism cancellation yields the original forward
OrdinarySquareComparison equation.

The only new unfinished theorem is a one-open unit normalization, used twice by that
calculation. It has no cartesian square, pullback witness, beta comparison, clopen
projection, properness assumption, or square conclusion. The main proof establishes
all the square/compositor, pasting, and cancellation steps; it does not merely rename
the assigned obligation.

## Proved and sorry left

Closed the original textual hole in
AlgebraicGeometry.ProEtale.VaryingRing.ordinaryCartesianEvaluation
(node lem-sp-varying-ring-ordinary-cartesian-evaluation): 1 of 1 original holes.
Its proof is complete from the imported declarations, including the previously stated
ordinaryComparisonNormalization.

Added one hole:
AlgebraicGeometry.ProEtale.VaryingRing.ordinaryOpen_mate
in Sheaf.AlgebraicGeometry.VaryingRingOrdinaryOpenUnit
(node lem-sp-varying-ring-ordinary-open-unit). Its entire proof is exactly `by sorry`;
its docstring and node give the source and the full one-open argument.

This delivery is a decomposition, with one original hole closed and one strictly
simpler hole added, not a net sorry reduction. No other sorry is left or added by this
delivery. In particular the original cartesian theorem has no internal sorry. The
existing imported ordinaryComparisonNormalization remains unproved in its own module.

## No longer needed

No original import is removed and no module is withdrawn. The already public
VaryingRingOrdinaryEvaluationComparisons import remains necessary for the statement.

The proof does not use the theorem normalizedProperOpenCalculus from
lem-cbc-strict-tower-proper-open-calculus: its former proof-dependency entry is replaced
by def-cbc-strict-tower-proper-open-arrows, whose betaInv and squareG definitions are
actually used. This is dependency-level pruning only; the calculus module remains
transitively publicly reachable through the existing comparison API, so no claim of
module pruning is made. The other original dependencies remain necessary.

No cartesian/clopen evaluation or proper/open pasting theorem is imported as a shortcut.
VaryingRingOpenBaseChangeEvaluation cannot be imported here: it already imports the
ordinary clopen consumer, which imports this item. Its generic iso calculations were
reused as local proved private helpers without adding that cycle. The whiskering identity
uses the adopted-source mateEquiv_whiskerTop_whiskerBottom theorem directly, avoiding
re-expansion of mates. All private helpers are proved. The final conversion from an inverse-beta equation
to OrdinarySquareComparison is also proved generically, before instantiating the
explicit realization functors. The compositor calculation operates on component morphisms, and every compositor
argument is explicit. This avoids expensive kernel reductions from inferred component
isomorphisms. Validation: lcompile --all compiled the final clean packet successfully: the new
VaryingRingOrdinaryOpenUnit module in 42.3 seconds and the assigned cartesian module
in 47.5 seconds. Both are below the per-file 60-second limit. No profiler, trace,
heartbeat override, or temporary probe remains in the packet.

## Where the brief, the DAG or earlier work was wrong

The existing ordinaryComparisonNormalization theorem states only pullback-composition
and open-composition equations. Its informal proof describes the one-open mate
normalization as an internal step, but its Lean conclusion does not expose that fact.
Consequently it cannot directly discharge the unit-normalization step requested by the
assigned node. The new node states precisely that missing smaller step.

The assigned theorem and all underlying definitions retain their exact meanings.
The route stays below the unit level and changes no unit statement or realized step.
The edge cases of the new statement require no extra assumptions: identity open
immersions, empty opens, zero coefficient rings, and infinite coefficient rings use the
same adjunction/mate identity; the proof plan uses no nonzero or finiteness premise.

## New nodes

lem-sp-varying-ring-ordinary-open-unit is the one-open adjunction normalization
in VaryingRingOrdinaryOpenUnit. Zheng Construction 4.22, equation (4.22.1), supplies
the explicit open-extension/evaluation source alongside Construction 4.1. It isolates the unit subargument already described in
the proof of lem-sp-varying-ring-ordinary-comparison-normalization. Its statement uses
only one open immersion and the original explicit realization comparisons, and is
strictly simpler than cartesian evaluation. The item node now records the actual
square-compositor calculation followed by mate pasting and cancellation. No existing
interface changed, so no change record or forced consumer adaptation is needed.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
