## What changed

Proved `WeilConjectures.pbc_integral_actual_unit_roos_normalization` without
changing its statement or public imports. The proof transports K-flatness through
the coefficient-sheaf isomorphism, computes the completed comparison on the whole
strict tower, and identifies the resulting chain map by both Roos coordinates.
It never infers an equality of derived tower morphisms from level evaluations.

The generic normalization calculation is fully proved in the new module
`Sheaf.Paper.CompletedPullbackStrictNormalization`, as
`WeilConjectures.completedPullbackComparison_strict_normalization`. Its public
statement spells out the actual strict module augmentation. It combines the
specified reduction and constant/pullback unit normalizations with naturality
of the universal derived counits and the constant/Rlim unit. The original item
then supplies coefficient transport and the separate coordinate argument.

The calculation was extracted only after profiling and improving the slow
conversions: a generic counit lemma, generic composition lemma, and local
irreducibility of large definitions prevent repeated unfolding. The combined
file nevertheless exceeded the 60-second limit on a clean compile. Separating
this proved calculation preserves the unit's route and adds no open obligation.

The item's proof imports `RingIsomorphismTensorTransport` and the new module.
`RightDerivedFunctor.ShortExactPullback` and `CompletedPullbackReductionData`
are proof imports of the new module. All remaining helpers and instance
adjustments are private or local. No other existing module is changed.
The DAG proof and dependencies now follow this argument.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.pbc_integral_actual_unit_roos_normalization`
(node `lem-weil-pbc-integral-actual-unit-roos-normalization`).
Also fully proved the new intermediate theorem
`WeilConjectures.completedPullbackComparison_strict_normalization`
(node `lem-weil-pbc-completed-pullback-strict-normalization`).

One original hole closed, zero holes added, zero holes left in either module.
No unfinished statements are split off.

Validation: both modules compiled on the project server without errors or
warnings: `CompletedPullbackStrictNormalization` in 59.5 seconds and the assigned
item in 42.2 seconds. The required delivery command runs the remaining preflight
checks.

## No longer needed

No original public imports were removed and no modules are withdrawn. The item's
proof no longer directly imports `ShortExactPullback` or
`CompletedPullbackReductionData`; the new proved helper uses both.

Removed the redundant direct proof dependencies
`lem-weil-pbc-integral-coefficient-presentation-comparison` and
`def-sf-ordinary-integral-pullback-construction`: the coefficient comparison and
actual augmentation are already exposed by `ProperIntegralOrdinaryData`.
The normalization dependencies `def-weil-pbc-completed-pullback`,
`def-weil-pbc-reduction-augmentation`, `prop-weil-pbc-rlim-functoriality`, and
`def-weil-pbc-completed-pullback-reduction-functor` are recorded on the new helper
node. This removes or relocates edges only; none of these modules is claimed
globally unused.

The proof does not need flatness of the individual terms, the quasi-isomorphism
hypothesis on `r`, or invertibility of the termwise-limit-to-Roos map. The original
hypotheses are retained verbatim.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was necessary. The specified normalization
and naturality APIs suffice to prove the obligation without further holes.
Only K-flatness of the transported representative is needed. The coordinate
argument also covers zero complexes, empty schemes and zero coefficient rings:
it uses only adjunction and product/cocone equations.

## New nodes

`lem-weil-pbc-completed-pullback-strict-normalization` records the fully proved
strict representative computation before coefficient transport and Roos
coordinates. Its module is
`lean/Sheaf/Paper/CompletedPullbackStrictNormalization.lean`. The statement is a
proper intermediate step, valid for any adic datum, K-flat representative, input
morphism and map to a K-injective strict tower. Its proof contains no `sorry`.
No change record is needed: only the assigned module and its node, this new
module and its new node are delivered.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
