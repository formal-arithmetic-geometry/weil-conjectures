## What changed

In Sheaf.Paper.LevelwiseAdicTruncations, replace the hole in
AlgebraicGeometry.Scheme.pbc_reduction_adic_tower_laws with the full all-pair
strict-transition equation and quotient cocycle proof. Four private proved helpers
establish coherence of exact derived restriction, the adjunction cocycle, the
ordinary tower's arbitrary-pair transition formula, and K-flat evaluation
compatibility. The identity case is included in the ordinary transition induction.

Add one proof-only import, Sheaf.Paper.ActualCompletedReductionReconstruction,
using its already proved scalar-counit, balancing, restriction-factorization and
naturality computations. Its completed-reconstruction conclusion is not applied.
Its node lem-weil-pbc-actual-completed-reduction-reconstruction is used as a generic
tool for those computations; the item's existing dependencies do not expose these
particular computations. Any new tool-use approval is for the maintainer to record.
Update the item's DAG proof and proof dependencies to reflect this route.

All public signatures, definition bodies, existing public imports and instances
are preserved. The temporary proof transparency commands are documented in
coord/changes/K4-levelwise-reduction-law-proof-commands.md, including downstream
consumer checks. No other Lean module is modified. The complete item passed the server single-file
compile; the two unused simp arguments reported there were then removed.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.pbc_reduction_adic_tower_laws.
One of the five original holes is closed; no holes are added or split off.

The following four original holes remain unchanged. All belong to
prop-weil-pbc-levelwise-truncations:

- AlgebraicGeometry.Scheme.pbc_levelwise_tor_of_uniformizer_injective.
- AlgebraicGeometry.Scheme.pbc_levelwise_truncations_constructible.
- AlgebraicGeometry.Scheme.pbc_levelwise_truncation_counterexample.
- AlgebraicGeometry.Scheme.pbc_levelwise_truncation_compatible_origins.

## No longer needed

None. No imports, nodes or modules are withdrawn. The dependencies of the
remaining clauses are retained; no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement correction. A direct definitional simplification cannot identify
an arbitrary-pair map in completedReductionModuleTower with the direct quotient
transition: that tower is built from its adjacent maps by Functor.ofOpSequence.
The proof therefore supplies an explicit induction, with the identity case and
quotient composition checked on tensor generators. The full derived cocycle also
requires coherence of the selected restriction-composition isomorphisms; it is
proved from their ordinary section formula and derived factorization.

The later PbcUniformLocalModelCohomology theorem cannot supply the lower bound
for this item's constructibility hole: its existing proof uses that same hole.
It is not imported or used here.

A possible route for the remaining compatible-origins clause is to take adjuncts
of pbcLevelwiseEtaleStepLE/GE and pbcLevelwiseProEtaleStepLE/GE. The unconditional
origin theorem already gives their semilinear comparison squares. The unit law
for the recorded tensor mates should turn these into normalization squares.
Conservativity of exact derived comparison suffices to test the etale maps for
invertibility; full faithfulness on unbounded objects is unnecessary. This route
has not been implemented or counted as a proof in this delivery.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
