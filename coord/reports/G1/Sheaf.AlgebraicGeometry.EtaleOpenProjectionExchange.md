## What changed

Proved `AlgebraicGeometry.Etale.ordinaryOpenProjectionExchange_forward` in
`lean/Sheaf/AlgebraicGeometry/EtaleOpenProjectionExchange.lean`, without changing its
signature or its public imports. Specialized the existing, proved generic theorem
`derivedOpenImmersionLowerShriekProjectionIso_inv_baseChange` to `ModuleCat C` and
`IsPullback.of_hasPullback j a`. Precomposed by the inverse tensor comparison at `a`,
used the source theorem, and cancelled the tensor comparison at `pullback.fst j a`
and the square comparison under the extension-by-zero and tensor functors.

This uses the established implementation of the node's mate argument (steps 1–4)
and performs the final change of normal form in Lean. No new construction,
statement, definition, module, or node is introduced.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Etale.ordinaryOpenProjectionExchange_forward`
(node `lem-asd-open-projection-exchange`).

Holes added: zero. Holes remaining in the delivered module: zero.
No split-offs and no decomposition.

## No longer needed

No imports removed; both original public imports supply the displayed statement
and its coefficient instances. No nodes or modules withdrawn. The existing source
proof already supplies the unit-mate, tensor-coherence and categorical-mate steps;
no separate imports of `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal`
or `Sheaf.AlgebraicGeometry.OpenImmersionExtensionZeroBaseChange` are necessary.
Those modules were not imported by the original item, so this delivery claims no
closure pruning for them.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The node's existing candidate
`derivedOpenImmersionLowerShriekProjectionIso_inv_baseChange` provides a shorter
Lean implementation of its recorded proof plan: its remaining difference from the
item is only conjugation by the canonical isomorphisms. The original signatures,
coefficient universes, arbitrary base-change map, and unbounded derived objects
are preserved. There are no hypotheses concerning boundedness, flatness of the
base-change map, constructibility, or finiteness of the coefficient ring.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
