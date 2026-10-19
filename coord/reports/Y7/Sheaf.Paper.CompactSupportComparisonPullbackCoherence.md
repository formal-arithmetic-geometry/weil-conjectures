## What changed

Prove `AlgebraicGeometry.ProEtale.cbcComparison_pullback_coherent` in
`lean/Sheaf/Paper/CompactSupportComparisonPullbackCoherence.lean` by applying the
existing `AlgebraicGeometry.ProEtale.comparison_pullback_coherent` from
`Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`.

The expanded compact-support coherence predicate caused the direct specialization
proof to exceed 60 seconds. Make `cbcComparisonPullbackCoherent` an abbreviation
of the existing canonical `ComparisonPullbackCoherent`, following the already
reviewed support-site realization's identical refactor. The import is public
because the shared predicate is used in a public definition. The existing theorem
signature, all canonical maps, universes, and coefficient hypotheses are unchanged.

The comparison site base-change isomorphisms use the same componentwise identity;
the direct-image comparisons compose the same restriction isomorphisms; hence the
conjugate inverse-image comparisons agree. The identity and composition maps are
identical constructions. The square clause unfolds through
`ComparisonSquareComponent` and `comparisonSquareData` to the original equation,
with exactly the given Cartesian square and its commutativity transport. No
hypothesis or conclusion changes, including for empty schemes, identities,
arbitrary composable maps, and every specified square.

Update the existing node's fourth proof step and proof origin to record this
compact-support specialization. Preserve its current support-site `lean` attachment
and four-step proof route. The change record is
`coord/changes/Y7-cbc-comparison-pullback-coherence-sharing.md`.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.ProEtale.cbcComparison_pullback_coherent`
(blueprint node `lem-weil-pbc-comparison-pullback`).

No holes added; no `sorry` remains in the delivered module. No result is split off.

Validation: the item compiles cleanly against the current sources in 4.5 seconds.
A separate validation tree compiles the delivered item first, then the unchanged
`FiniteConstantCoefficientTransport` and `PbcUniformCompleteTriangulated` consumers
and a map-agreement diagnostic against that item's sandbox artifacts. All pass.
The diagnostic proves by `rfl` equality of the compact-support and canonical
site-base-change, direct-image, inverse-image, identity, composition, and square
isomorphisms. It also checks `#print axioms cbcComparison_pullback_coherent`, which
reports exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
The validation tree is kept only under `scratchpad`, not delivered.

The required delivery dry run passes. Two initial diagnostic compile requests
received no answer from the server; the subsequent validation set completed cleanly.

## No longer needed

No existing imports removed and no nodes or modules withdrawn. The added canonical
comparison import supplies the shared predicate and its proved theorem. The existing
public imports are retained for compatibility. No fresh mate-coherence calculation
or intermediate theorem is needed: the canonical comparison theorem already proves
all four planned steps for these constructions. The abandoned private conversion
helper and profiling option from the interrupted attempt are removed.

## Where the brief, the DAG or earlier work was wrong

The interrupted attempt had written a direct specialization proof but had no report
and left profiling enabled. That proof timed out while Lean compared the expanded
predicates. Sharing the existing canonical predicate repairs this definition-level
performance issue; neither a file split nor an increased compile limit is used.

The current node `lem-weil-pbc-comparison-pullback` attaches its `lean` record to the
support-site realization rather than this duplicate compact-support realization.
Its existing four-step proof is the proof reused here, so its attachment and unit
route remain. No mathematical statement is disputed.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
